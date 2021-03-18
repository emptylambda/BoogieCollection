// Dafny 3.0.0.30204
// Command Line Options: -compile:0 -noVerify /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy -print:./Rippling.bpl

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
function #_module.Bool.False() : DatatypeType;

const unique ##_module.Bool.False: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#_module.Bool.False()) == ##_module.Bool.False;

function _module.Bool.False_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Bool.False_q(d) } 
  _module.Bool.False_q(d) <==> DatatypeCtorId(d) == ##_module.Bool.False);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Bool.False_q(d) } 
  _module.Bool.False_q(d) ==> d == #_module.Bool.False());

function Tclass._module.Bool() : Ty;

const unique Tagclass._module.Bool: TyTag;

// Tclass._module.Bool Tag
axiom Tag(Tclass._module.Bool()) == Tagclass._module.Bool
   && TagFamily(Tclass._module.Bool()) == tytagFamily$Bool;

// Box/unbox axiom for Tclass._module.Bool
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Bool()) } 
  $IsBox(bx, Tclass._module.Bool())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Bool()));

// Constructor $Is
axiom $Is(#_module.Bool.False(), Tclass._module.Bool());

// Constructor $IsAlloc
axiom (forall $h: Heap :: 
  { $IsAlloc(#_module.Bool.False(), Tclass._module.Bool(), $h) } 
  $IsGoodHeap($h) ==> $IsAlloc(#_module.Bool.False(), Tclass._module.Bool(), $h));

// Constructor literal
axiom #_module.Bool.False() == Lit(#_module.Bool.False());

// Constructor function declaration
function #_module.Bool.True() : DatatypeType;

const unique ##_module.Bool.True: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#_module.Bool.True()) == ##_module.Bool.True;

function _module.Bool.True_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Bool.True_q(d) } 
  _module.Bool.True_q(d) <==> DatatypeCtorId(d) == ##_module.Bool.True);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Bool.True_q(d) } 
  _module.Bool.True_q(d) ==> d == #_module.Bool.True());

// Constructor $Is
axiom $Is(#_module.Bool.True(), Tclass._module.Bool());

// Constructor $IsAlloc
axiom (forall $h: Heap :: 
  { $IsAlloc(#_module.Bool.True(), Tclass._module.Bool(), $h) } 
  $IsGoodHeap($h) ==> $IsAlloc(#_module.Bool.True(), Tclass._module.Bool(), $h));

// Constructor literal
axiom #_module.Bool.True() == Lit(#_module.Bool.True());

// Depth-one case-split function
function $IsA#_module.Bool(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.Bool(d) } 
  $IsA#_module.Bool(d) ==> _module.Bool.False_q(d) || _module.Bool.True_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.Bool.True_q(d), $Is(d, Tclass._module.Bool()) } 
    { _module.Bool.False_q(d), $Is(d, Tclass._module.Bool()) } 
  $Is(d, Tclass._module.Bool())
     ==> _module.Bool.False_q(d) || _module.Bool.True_q(d));

// Datatype extensional equality declaration
function _module.Bool#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.Bool.False
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Bool#Equal(a, b), _module.Bool.False_q(a) } 
    { _module.Bool#Equal(a, b), _module.Bool.False_q(b) } 
  _module.Bool.False_q(a) && _module.Bool.False_q(b)
     ==> (_module.Bool#Equal(a, b) <==> true));

// Datatype extensional equality definition: #_module.Bool.True
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Bool#Equal(a, b), _module.Bool.True_q(a) } 
    { _module.Bool#Equal(a, b), _module.Bool.True_q(b) } 
  _module.Bool.True_q(a) && _module.Bool.True_q(b)
     ==> (_module.Bool#Equal(a, b) <==> true));

// Datatype extensionality axiom: _module.Bool
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Bool#Equal(a, b) } 
  _module.Bool#Equal(a, b) <==> a == b);

const unique class._module.Bool: ClassName;

// Constructor function declaration
function #_module.Nat.Zero() : DatatypeType;

const unique ##_module.Nat.Zero: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#_module.Nat.Zero()) == ##_module.Nat.Zero;

function _module.Nat.Zero_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Nat.Zero_q(d) } 
  _module.Nat.Zero_q(d) <==> DatatypeCtorId(d) == ##_module.Nat.Zero);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Nat.Zero_q(d) } 
  _module.Nat.Zero_q(d) ==> d == #_module.Nat.Zero());

function Tclass._module.Nat() : Ty;

const unique Tagclass._module.Nat: TyTag;

// Tclass._module.Nat Tag
axiom Tag(Tclass._module.Nat()) == Tagclass._module.Nat
   && TagFamily(Tclass._module.Nat()) == tytagFamily$Nat;

// Box/unbox axiom for Tclass._module.Nat
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Nat()) } 
  $IsBox(bx, Tclass._module.Nat())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Nat()));

// Constructor $Is
axiom $Is(#_module.Nat.Zero(), Tclass._module.Nat());

// Constructor $IsAlloc
axiom (forall $h: Heap :: 
  { $IsAlloc(#_module.Nat.Zero(), Tclass._module.Nat(), $h) } 
  $IsGoodHeap($h) ==> $IsAlloc(#_module.Nat.Zero(), Tclass._module.Nat(), $h));

// Constructor literal
axiom #_module.Nat.Zero() == Lit(#_module.Nat.Zero());

// Constructor function declaration
function #_module.Nat.Suc(DatatypeType) : DatatypeType;

const unique ##_module.Nat.Suc: DtCtorId;

// Constructor identifier
axiom (forall a#29#0#0: DatatypeType :: 
  { #_module.Nat.Suc(a#29#0#0) } 
  DatatypeCtorId(#_module.Nat.Suc(a#29#0#0)) == ##_module.Nat.Suc);

function _module.Nat.Suc_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Nat.Suc_q(d) } 
  _module.Nat.Suc_q(d) <==> DatatypeCtorId(d) == ##_module.Nat.Suc);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Nat.Suc_q(d) } 
  _module.Nat.Suc_q(d)
     ==> (exists a#30#0#0: DatatypeType :: d == #_module.Nat.Suc(a#30#0#0)));

// Constructor $Is
axiom (forall a#31#0#0: DatatypeType :: 
  { $Is(#_module.Nat.Suc(a#31#0#0), Tclass._module.Nat()) } 
  $Is(#_module.Nat.Suc(a#31#0#0), Tclass._module.Nat())
     <==> $Is(a#31#0#0, Tclass._module.Nat()));

// Constructor $IsAlloc
axiom (forall a#32#0#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#_module.Nat.Suc(a#32#0#0), Tclass._module.Nat(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Nat.Suc(a#32#0#0), Tclass._module.Nat(), $h)
       <==> $IsAlloc(a#32#0#0, Tclass._module.Nat(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Nat._h0(d), Tclass._module.Nat(), $h) } 
  $IsGoodHeap($h) && _module.Nat.Suc_q(d) && $IsAlloc(d, Tclass._module.Nat(), $h)
     ==> $IsAlloc(_module.Nat._h0(d), Tclass._module.Nat(), $h));

// Constructor literal
axiom (forall a#33#0#0: DatatypeType :: 
  { #_module.Nat.Suc(Lit(a#33#0#0)) } 
  #_module.Nat.Suc(Lit(a#33#0#0)) == Lit(#_module.Nat.Suc(a#33#0#0)));

function _module.Nat._h0(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#34#0#0: DatatypeType :: 
  { #_module.Nat.Suc(a#34#0#0) } 
  _module.Nat._h0(#_module.Nat.Suc(a#34#0#0)) == a#34#0#0);

// Inductive rank
axiom (forall a#35#0#0: DatatypeType :: 
  { #_module.Nat.Suc(a#35#0#0) } 
  DtRank(a#35#0#0) < DtRank(#_module.Nat.Suc(a#35#0#0)));

// Depth-one case-split function
function $IsA#_module.Nat(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.Nat(d) } 
  $IsA#_module.Nat(d) ==> _module.Nat.Zero_q(d) || _module.Nat.Suc_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.Nat.Suc_q(d), $Is(d, Tclass._module.Nat()) } 
    { _module.Nat.Zero_q(d), $Is(d, Tclass._module.Nat()) } 
  $Is(d, Tclass._module.Nat()) ==> _module.Nat.Zero_q(d) || _module.Nat.Suc_q(d));

// Datatype extensional equality declaration
function _module.Nat#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.Nat.Zero
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Nat#Equal(a, b), _module.Nat.Zero_q(a) } 
    { _module.Nat#Equal(a, b), _module.Nat.Zero_q(b) } 
  _module.Nat.Zero_q(a) && _module.Nat.Zero_q(b)
     ==> (_module.Nat#Equal(a, b) <==> true));

// Datatype extensional equality definition: #_module.Nat.Suc
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Nat#Equal(a, b), _module.Nat.Suc_q(a) } 
    { _module.Nat#Equal(a, b), _module.Nat.Suc_q(b) } 
  _module.Nat.Suc_q(a) && _module.Nat.Suc_q(b)
     ==> (_module.Nat#Equal(a, b)
       <==> _module.Nat#Equal(_module.Nat._h0(a), _module.Nat._h0(b))));

// Datatype extensionality axiom: _module.Nat
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Nat#Equal(a, b) } 
  _module.Nat#Equal(a, b) <==> a == b);

const unique class._module.Nat: ClassName;

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

function Tclass._module.List() : Ty;

const unique Tagclass._module.List: TyTag;

// Tclass._module.List Tag
axiom Tag(Tclass._module.List()) == Tagclass._module.List
   && TagFamily(Tclass._module.List()) == tytagFamily$List;

// Box/unbox axiom for Tclass._module.List
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.List()) } 
  $IsBox(bx, Tclass._module.List())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.List()));

// Constructor $Is
axiom $Is(#_module.List.Nil(), Tclass._module.List());

// Constructor $IsAlloc
axiom (forall $h: Heap :: 
  { $IsAlloc(#_module.List.Nil(), Tclass._module.List(), $h) } 
  $IsGoodHeap($h) ==> $IsAlloc(#_module.List.Nil(), Tclass._module.List(), $h));

// Constructor literal
axiom #_module.List.Nil() == Lit(#_module.List.Nil());

// Constructor function declaration
function #_module.List.Cons(DatatypeType, DatatypeType) : DatatypeType;

const unique ##_module.List.Cons: DtCtorId;

// Constructor identifier
axiom (forall a#41#0#0: DatatypeType, a#41#1#0: DatatypeType :: 
  { #_module.List.Cons(a#41#0#0, a#41#1#0) } 
  DatatypeCtorId(#_module.List.Cons(a#41#0#0, a#41#1#0)) == ##_module.List.Cons);

function _module.List.Cons_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.List.Cons_q(d) } 
  _module.List.Cons_q(d) <==> DatatypeCtorId(d) == ##_module.List.Cons);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.List.Cons_q(d) } 
  _module.List.Cons_q(d)
     ==> (exists a#42#0#0: DatatypeType, a#42#1#0: DatatypeType :: 
      d == #_module.List.Cons(a#42#0#0, a#42#1#0)));

// Constructor $Is
axiom (forall a#43#0#0: DatatypeType, a#43#1#0: DatatypeType :: 
  { $Is(#_module.List.Cons(a#43#0#0, a#43#1#0), Tclass._module.List()) } 
  $Is(#_module.List.Cons(a#43#0#0, a#43#1#0), Tclass._module.List())
     <==> $Is(a#43#0#0, Tclass._module.Nat()) && $Is(a#43#1#0, Tclass._module.List()));

// Constructor $IsAlloc
axiom (forall a#44#0#0: DatatypeType, a#44#1#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#_module.List.Cons(a#44#0#0, a#44#1#0), Tclass._module.List(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.List.Cons(a#44#0#0, a#44#1#0), Tclass._module.List(), $h)
       <==> $IsAlloc(a#44#0#0, Tclass._module.Nat(), $h)
         && $IsAlloc(a#44#1#0, Tclass._module.List(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.List._h1(d), Tclass._module.Nat(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.List.Cons_q(d)
       && $IsAlloc(d, Tclass._module.List(), $h)
     ==> $IsAlloc(_module.List._h1(d), Tclass._module.Nat(), $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.List._h2(d), Tclass._module.List(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.List.Cons_q(d)
       && $IsAlloc(d, Tclass._module.List(), $h)
     ==> $IsAlloc(_module.List._h2(d), Tclass._module.List(), $h));

// Constructor literal
axiom (forall a#45#0#0: DatatypeType, a#45#1#0: DatatypeType :: 
  { #_module.List.Cons(Lit(a#45#0#0), Lit(a#45#1#0)) } 
  #_module.List.Cons(Lit(a#45#0#0), Lit(a#45#1#0))
     == Lit(#_module.List.Cons(a#45#0#0, a#45#1#0)));

function _module.List._h1(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#46#0#0: DatatypeType, a#46#1#0: DatatypeType :: 
  { #_module.List.Cons(a#46#0#0, a#46#1#0) } 
  _module.List._h1(#_module.List.Cons(a#46#0#0, a#46#1#0)) == a#46#0#0);

// Inductive rank
axiom (forall a#47#0#0: DatatypeType, a#47#1#0: DatatypeType :: 
  { #_module.List.Cons(a#47#0#0, a#47#1#0) } 
  DtRank(a#47#0#0) < DtRank(#_module.List.Cons(a#47#0#0, a#47#1#0)));

function _module.List._h2(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#48#0#0: DatatypeType, a#48#1#0: DatatypeType :: 
  { #_module.List.Cons(a#48#0#0, a#48#1#0) } 
  _module.List._h2(#_module.List.Cons(a#48#0#0, a#48#1#0)) == a#48#1#0);

// Inductive rank
axiom (forall a#49#0#0: DatatypeType, a#49#1#0: DatatypeType :: 
  { #_module.List.Cons(a#49#0#0, a#49#1#0) } 
  DtRank(a#49#1#0) < DtRank(#_module.List.Cons(a#49#0#0, a#49#1#0)));

// Depth-one case-split function
function $IsA#_module.List(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.List(d) } 
  $IsA#_module.List(d) ==> _module.List.Nil_q(d) || _module.List.Cons_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.List.Cons_q(d), $Is(d, Tclass._module.List()) } 
    { _module.List.Nil_q(d), $Is(d, Tclass._module.List()) } 
  $Is(d, Tclass._module.List())
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
       <==> _module.Nat#Equal(_module.List._h1(a), _module.List._h1(b))
         && _module.List#Equal(_module.List._h2(a), _module.List._h2(b))));

// Datatype extensionality axiom: _module.List
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.List#Equal(a, b) } 
  _module.List#Equal(a, b) <==> a == b);

const unique class._module.List: ClassName;

// Constructor function declaration
function #_module.Pair.Pair(DatatypeType, DatatypeType) : DatatypeType;

const unique ##_module.Pair.Pair: DtCtorId;

// Constructor identifier
axiom (forall a#50#0#0: DatatypeType, a#50#1#0: DatatypeType :: 
  { #_module.Pair.Pair(a#50#0#0, a#50#1#0) } 
  DatatypeCtorId(#_module.Pair.Pair(a#50#0#0, a#50#1#0)) == ##_module.Pair.Pair);

function _module.Pair.Pair_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Pair.Pair_q(d) } 
  _module.Pair.Pair_q(d) <==> DatatypeCtorId(d) == ##_module.Pair.Pair);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Pair.Pair_q(d) } 
  _module.Pair.Pair_q(d)
     ==> (exists a#51#0#0: DatatypeType, a#51#1#0: DatatypeType :: 
      d == #_module.Pair.Pair(a#51#0#0, a#51#1#0)));

function Tclass._module.Pair() : Ty;

const unique Tagclass._module.Pair: TyTag;

// Tclass._module.Pair Tag
axiom Tag(Tclass._module.Pair()) == Tagclass._module.Pair
   && TagFamily(Tclass._module.Pair()) == tytagFamily$Pair;

// Box/unbox axiom for Tclass._module.Pair
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Pair()) } 
  $IsBox(bx, Tclass._module.Pair())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Pair()));

// Constructor $Is
axiom (forall a#52#0#0: DatatypeType, a#52#1#0: DatatypeType :: 
  { $Is(#_module.Pair.Pair(a#52#0#0, a#52#1#0), Tclass._module.Pair()) } 
  $Is(#_module.Pair.Pair(a#52#0#0, a#52#1#0), Tclass._module.Pair())
     <==> $Is(a#52#0#0, Tclass._module.Nat()) && $Is(a#52#1#0, Tclass._module.Nat()));

// Constructor $IsAlloc
axiom (forall a#53#0#0: DatatypeType, a#53#1#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#_module.Pair.Pair(a#53#0#0, a#53#1#0), Tclass._module.Pair(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Pair.Pair(a#53#0#0, a#53#1#0), Tclass._module.Pair(), $h)
       <==> $IsAlloc(a#53#0#0, Tclass._module.Nat(), $h)
         && $IsAlloc(a#53#1#0, Tclass._module.Nat(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Pair._h3(d), Tclass._module.Nat(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.Pair.Pair_q(d)
       && $IsAlloc(d, Tclass._module.Pair(), $h)
     ==> $IsAlloc(_module.Pair._h3(d), Tclass._module.Nat(), $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Pair._h4(d), Tclass._module.Nat(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.Pair.Pair_q(d)
       && $IsAlloc(d, Tclass._module.Pair(), $h)
     ==> $IsAlloc(_module.Pair._h4(d), Tclass._module.Nat(), $h));

// Constructor literal
axiom (forall a#54#0#0: DatatypeType, a#54#1#0: DatatypeType :: 
  { #_module.Pair.Pair(Lit(a#54#0#0), Lit(a#54#1#0)) } 
  #_module.Pair.Pair(Lit(a#54#0#0), Lit(a#54#1#0))
     == Lit(#_module.Pair.Pair(a#54#0#0, a#54#1#0)));

function _module.Pair._h3(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#55#0#0: DatatypeType, a#55#1#0: DatatypeType :: 
  { #_module.Pair.Pair(a#55#0#0, a#55#1#0) } 
  _module.Pair._h3(#_module.Pair.Pair(a#55#0#0, a#55#1#0)) == a#55#0#0);

// Inductive rank
axiom (forall a#56#0#0: DatatypeType, a#56#1#0: DatatypeType :: 
  { #_module.Pair.Pair(a#56#0#0, a#56#1#0) } 
  DtRank(a#56#0#0) < DtRank(#_module.Pair.Pair(a#56#0#0, a#56#1#0)));

function _module.Pair._h4(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#57#0#0: DatatypeType, a#57#1#0: DatatypeType :: 
  { #_module.Pair.Pair(a#57#0#0, a#57#1#0) } 
  _module.Pair._h4(#_module.Pair.Pair(a#57#0#0, a#57#1#0)) == a#57#1#0);

// Inductive rank
axiom (forall a#58#0#0: DatatypeType, a#58#1#0: DatatypeType :: 
  { #_module.Pair.Pair(a#58#0#0, a#58#1#0) } 
  DtRank(a#58#1#0) < DtRank(#_module.Pair.Pair(a#58#0#0, a#58#1#0)));

// Depth-one case-split function
function $IsA#_module.Pair(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.Pair(d) } 
  $IsA#_module.Pair(d) ==> _module.Pair.Pair_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.Pair.Pair_q(d), $Is(d, Tclass._module.Pair()) } 
  $Is(d, Tclass._module.Pair()) ==> _module.Pair.Pair_q(d));

// Datatype extensional equality declaration
function _module.Pair#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.Pair.Pair
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Pair#Equal(a, b) } 
  true
     ==> (_module.Pair#Equal(a, b)
       <==> _module.Nat#Equal(_module.Pair._h3(a), _module.Pair._h3(b))
         && _module.Nat#Equal(_module.Pair._h4(a), _module.Pair._h4(b))));

// Datatype extensionality axiom: _module.Pair
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Pair#Equal(a, b) } 
  _module.Pair#Equal(a, b) <==> a == b);

const unique class._module.Pair: ClassName;

// Constructor function declaration
function #_module.PList.PNil() : DatatypeType;

const unique ##_module.PList.PNil: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#_module.PList.PNil()) == ##_module.PList.PNil;

function _module.PList.PNil_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.PList.PNil_q(d) } 
  _module.PList.PNil_q(d) <==> DatatypeCtorId(d) == ##_module.PList.PNil);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.PList.PNil_q(d) } 
  _module.PList.PNil_q(d) ==> d == #_module.PList.PNil());

function Tclass._module.PList() : Ty;

const unique Tagclass._module.PList: TyTag;

// Tclass._module.PList Tag
axiom Tag(Tclass._module.PList()) == Tagclass._module.PList
   && TagFamily(Tclass._module.PList()) == tytagFamily$PList;

// Box/unbox axiom for Tclass._module.PList
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.PList()) } 
  $IsBox(bx, Tclass._module.PList())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.PList()));

// Constructor $Is
axiom $Is(#_module.PList.PNil(), Tclass._module.PList());

// Constructor $IsAlloc
axiom (forall $h: Heap :: 
  { $IsAlloc(#_module.PList.PNil(), Tclass._module.PList(), $h) } 
  $IsGoodHeap($h) ==> $IsAlloc(#_module.PList.PNil(), Tclass._module.PList(), $h));

// Constructor literal
axiom #_module.PList.PNil() == Lit(#_module.PList.PNil());

// Constructor function declaration
function #_module.PList.PCons(DatatypeType, DatatypeType) : DatatypeType;

const unique ##_module.PList.PCons: DtCtorId;

// Constructor identifier
axiom (forall a#64#0#0: DatatypeType, a#64#1#0: DatatypeType :: 
  { #_module.PList.PCons(a#64#0#0, a#64#1#0) } 
  DatatypeCtorId(#_module.PList.PCons(a#64#0#0, a#64#1#0))
     == ##_module.PList.PCons);

function _module.PList.PCons_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.PList.PCons_q(d) } 
  _module.PList.PCons_q(d) <==> DatatypeCtorId(d) == ##_module.PList.PCons);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.PList.PCons_q(d) } 
  _module.PList.PCons_q(d)
     ==> (exists a#65#0#0: DatatypeType, a#65#1#0: DatatypeType :: 
      d == #_module.PList.PCons(a#65#0#0, a#65#1#0)));

// Constructor $Is
axiom (forall a#66#0#0: DatatypeType, a#66#1#0: DatatypeType :: 
  { $Is(#_module.PList.PCons(a#66#0#0, a#66#1#0), Tclass._module.PList()) } 
  $Is(#_module.PList.PCons(a#66#0#0, a#66#1#0), Tclass._module.PList())
     <==> $Is(a#66#0#0, Tclass._module.Pair()) && $Is(a#66#1#0, Tclass._module.PList()));

// Constructor $IsAlloc
axiom (forall a#67#0#0: DatatypeType, a#67#1#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#_module.PList.PCons(a#67#0#0, a#67#1#0), Tclass._module.PList(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.PList.PCons(a#67#0#0, a#67#1#0), Tclass._module.PList(), $h)
       <==> $IsAlloc(a#67#0#0, Tclass._module.Pair(), $h)
         && $IsAlloc(a#67#1#0, Tclass._module.PList(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.PList._h5(d), Tclass._module.Pair(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.PList.PCons_q(d)
       && $IsAlloc(d, Tclass._module.PList(), $h)
     ==> $IsAlloc(_module.PList._h5(d), Tclass._module.Pair(), $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.PList._h6(d), Tclass._module.PList(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.PList.PCons_q(d)
       && $IsAlloc(d, Tclass._module.PList(), $h)
     ==> $IsAlloc(_module.PList._h6(d), Tclass._module.PList(), $h));

// Constructor literal
axiom (forall a#68#0#0: DatatypeType, a#68#1#0: DatatypeType :: 
  { #_module.PList.PCons(Lit(a#68#0#0), Lit(a#68#1#0)) } 
  #_module.PList.PCons(Lit(a#68#0#0), Lit(a#68#1#0))
     == Lit(#_module.PList.PCons(a#68#0#0, a#68#1#0)));

function _module.PList._h5(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#69#0#0: DatatypeType, a#69#1#0: DatatypeType :: 
  { #_module.PList.PCons(a#69#0#0, a#69#1#0) } 
  _module.PList._h5(#_module.PList.PCons(a#69#0#0, a#69#1#0)) == a#69#0#0);

// Inductive rank
axiom (forall a#70#0#0: DatatypeType, a#70#1#0: DatatypeType :: 
  { #_module.PList.PCons(a#70#0#0, a#70#1#0) } 
  DtRank(a#70#0#0) < DtRank(#_module.PList.PCons(a#70#0#0, a#70#1#0)));

function _module.PList._h6(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#71#0#0: DatatypeType, a#71#1#0: DatatypeType :: 
  { #_module.PList.PCons(a#71#0#0, a#71#1#0) } 
  _module.PList._h6(#_module.PList.PCons(a#71#0#0, a#71#1#0)) == a#71#1#0);

// Inductive rank
axiom (forall a#72#0#0: DatatypeType, a#72#1#0: DatatypeType :: 
  { #_module.PList.PCons(a#72#0#0, a#72#1#0) } 
  DtRank(a#72#1#0) < DtRank(#_module.PList.PCons(a#72#0#0, a#72#1#0)));

// Depth-one case-split function
function $IsA#_module.PList(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.PList(d) } 
  $IsA#_module.PList(d) ==> _module.PList.PNil_q(d) || _module.PList.PCons_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.PList.PCons_q(d), $Is(d, Tclass._module.PList()) } 
    { _module.PList.PNil_q(d), $Is(d, Tclass._module.PList()) } 
  $Is(d, Tclass._module.PList())
     ==> _module.PList.PNil_q(d) || _module.PList.PCons_q(d));

// Datatype extensional equality declaration
function _module.PList#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.PList.PNil
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.PList#Equal(a, b), _module.PList.PNil_q(a) } 
    { _module.PList#Equal(a, b), _module.PList.PNil_q(b) } 
  _module.PList.PNil_q(a) && _module.PList.PNil_q(b)
     ==> (_module.PList#Equal(a, b) <==> true));

// Datatype extensional equality definition: #_module.PList.PCons
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.PList#Equal(a, b), _module.PList.PCons_q(a) } 
    { _module.PList#Equal(a, b), _module.PList.PCons_q(b) } 
  _module.PList.PCons_q(a) && _module.PList.PCons_q(b)
     ==> (_module.PList#Equal(a, b)
       <==> _module.Pair#Equal(_module.PList._h5(a), _module.PList._h5(b))
         && _module.PList#Equal(_module.PList._h6(a), _module.PList._h6(b))));

// Datatype extensionality axiom: _module.PList
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.PList#Equal(a, b) } 
  _module.PList#Equal(a, b) <==> a == b);

const unique class._module.PList: ClassName;

// Constructor function declaration
function #_module.Tree.Leaf() : DatatypeType;

const unique ##_module.Tree.Leaf: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#_module.Tree.Leaf()) == ##_module.Tree.Leaf;

function _module.Tree.Leaf_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Tree.Leaf_q(d) } 
  _module.Tree.Leaf_q(d) <==> DatatypeCtorId(d) == ##_module.Tree.Leaf);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Tree.Leaf_q(d) } 
  _module.Tree.Leaf_q(d) ==> d == #_module.Tree.Leaf());

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
axiom $Is(#_module.Tree.Leaf(), Tclass._module.Tree());

// Constructor $IsAlloc
axiom (forall $h: Heap :: 
  { $IsAlloc(#_module.Tree.Leaf(), Tclass._module.Tree(), $h) } 
  $IsGoodHeap($h) ==> $IsAlloc(#_module.Tree.Leaf(), Tclass._module.Tree(), $h));

// Constructor literal
axiom #_module.Tree.Leaf() == Lit(#_module.Tree.Leaf());

// Constructor function declaration
function #_module.Tree.Node(DatatypeType, DatatypeType, DatatypeType) : DatatypeType;

const unique ##_module.Tree.Node: DtCtorId;

// Constructor identifier
axiom (forall a#78#0#0: DatatypeType, a#78#1#0: DatatypeType, a#78#2#0: DatatypeType :: 
  { #_module.Tree.Node(a#78#0#0, a#78#1#0, a#78#2#0) } 
  DatatypeCtorId(#_module.Tree.Node(a#78#0#0, a#78#1#0, a#78#2#0))
     == ##_module.Tree.Node);

function _module.Tree.Node_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Tree.Node_q(d) } 
  _module.Tree.Node_q(d) <==> DatatypeCtorId(d) == ##_module.Tree.Node);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Tree.Node_q(d) } 
  _module.Tree.Node_q(d)
     ==> (exists a#79#0#0: DatatypeType, a#79#1#0: DatatypeType, a#79#2#0: DatatypeType :: 
      d == #_module.Tree.Node(a#79#0#0, a#79#1#0, a#79#2#0)));

// Constructor $Is
axiom (forall a#80#0#0: DatatypeType, a#80#1#0: DatatypeType, a#80#2#0: DatatypeType :: 
  { $Is(#_module.Tree.Node(a#80#0#0, a#80#1#0, a#80#2#0), Tclass._module.Tree()) } 
  $Is(#_module.Tree.Node(a#80#0#0, a#80#1#0, a#80#2#0), Tclass._module.Tree())
     <==> $Is(a#80#0#0, Tclass._module.Tree())
       && $Is(a#80#1#0, Tclass._module.Nat())
       && $Is(a#80#2#0, Tclass._module.Tree()));

// Constructor $IsAlloc
axiom (forall a#81#0#0: DatatypeType, a#81#1#0: DatatypeType, a#81#2#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#_module.Tree.Node(a#81#0#0, a#81#1#0, a#81#2#0), Tclass._module.Tree(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Tree.Node(a#81#0#0, a#81#1#0, a#81#2#0), Tclass._module.Tree(), $h)
       <==> $IsAlloc(a#81#0#0, Tclass._module.Tree(), $h)
         && $IsAlloc(a#81#1#0, Tclass._module.Nat(), $h)
         && $IsAlloc(a#81#2#0, Tclass._module.Tree(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Tree._h7(d), Tclass._module.Tree(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.Tree.Node_q(d)
       && $IsAlloc(d, Tclass._module.Tree(), $h)
     ==> $IsAlloc(_module.Tree._h7(d), Tclass._module.Tree(), $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Tree._h8(d), Tclass._module.Nat(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.Tree.Node_q(d)
       && $IsAlloc(d, Tclass._module.Tree(), $h)
     ==> $IsAlloc(_module.Tree._h8(d), Tclass._module.Nat(), $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Tree._h9(d), Tclass._module.Tree(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.Tree.Node_q(d)
       && $IsAlloc(d, Tclass._module.Tree(), $h)
     ==> $IsAlloc(_module.Tree._h9(d), Tclass._module.Tree(), $h));

// Constructor literal
axiom (forall a#82#0#0: DatatypeType, a#82#1#0: DatatypeType, a#82#2#0: DatatypeType :: 
  { #_module.Tree.Node(Lit(a#82#0#0), Lit(a#82#1#0), Lit(a#82#2#0)) } 
  #_module.Tree.Node(Lit(a#82#0#0), Lit(a#82#1#0), Lit(a#82#2#0))
     == Lit(#_module.Tree.Node(a#82#0#0, a#82#1#0, a#82#2#0)));

function _module.Tree._h7(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#83#0#0: DatatypeType, a#83#1#0: DatatypeType, a#83#2#0: DatatypeType :: 
  { #_module.Tree.Node(a#83#0#0, a#83#1#0, a#83#2#0) } 
  _module.Tree._h7(#_module.Tree.Node(a#83#0#0, a#83#1#0, a#83#2#0)) == a#83#0#0);

// Inductive rank
axiom (forall a#84#0#0: DatatypeType, a#84#1#0: DatatypeType, a#84#2#0: DatatypeType :: 
  { #_module.Tree.Node(a#84#0#0, a#84#1#0, a#84#2#0) } 
  DtRank(a#84#0#0) < DtRank(#_module.Tree.Node(a#84#0#0, a#84#1#0, a#84#2#0)));

function _module.Tree._h8(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#85#0#0: DatatypeType, a#85#1#0: DatatypeType, a#85#2#0: DatatypeType :: 
  { #_module.Tree.Node(a#85#0#0, a#85#1#0, a#85#2#0) } 
  _module.Tree._h8(#_module.Tree.Node(a#85#0#0, a#85#1#0, a#85#2#0)) == a#85#1#0);

// Inductive rank
axiom (forall a#86#0#0: DatatypeType, a#86#1#0: DatatypeType, a#86#2#0: DatatypeType :: 
  { #_module.Tree.Node(a#86#0#0, a#86#1#0, a#86#2#0) } 
  DtRank(a#86#1#0) < DtRank(#_module.Tree.Node(a#86#0#0, a#86#1#0, a#86#2#0)));

function _module.Tree._h9(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#87#0#0: DatatypeType, a#87#1#0: DatatypeType, a#87#2#0: DatatypeType :: 
  { #_module.Tree.Node(a#87#0#0, a#87#1#0, a#87#2#0) } 
  _module.Tree._h9(#_module.Tree.Node(a#87#0#0, a#87#1#0, a#87#2#0)) == a#87#2#0);

// Inductive rank
axiom (forall a#88#0#0: DatatypeType, a#88#1#0: DatatypeType, a#88#2#0: DatatypeType :: 
  { #_module.Tree.Node(a#88#0#0, a#88#1#0, a#88#2#0) } 
  DtRank(a#88#2#0) < DtRank(#_module.Tree.Node(a#88#0#0, a#88#1#0, a#88#2#0)));

// Depth-one case-split function
function $IsA#_module.Tree(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.Tree(d) } 
  $IsA#_module.Tree(d) ==> _module.Tree.Leaf_q(d) || _module.Tree.Node_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.Tree.Node_q(d), $Is(d, Tclass._module.Tree()) } 
    { _module.Tree.Leaf_q(d), $Is(d, Tclass._module.Tree()) } 
  $Is(d, Tclass._module.Tree())
     ==> _module.Tree.Leaf_q(d) || _module.Tree.Node_q(d));

// Datatype extensional equality declaration
function _module.Tree#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.Tree.Leaf
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Tree#Equal(a, b), _module.Tree.Leaf_q(a) } 
    { _module.Tree#Equal(a, b), _module.Tree.Leaf_q(b) } 
  _module.Tree.Leaf_q(a) && _module.Tree.Leaf_q(b)
     ==> (_module.Tree#Equal(a, b) <==> true));

// Datatype extensional equality definition: #_module.Tree.Node
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Tree#Equal(a, b), _module.Tree.Node_q(a) } 
    { _module.Tree#Equal(a, b), _module.Tree.Node_q(b) } 
  _module.Tree.Node_q(a) && _module.Tree.Node_q(b)
     ==> (_module.Tree#Equal(a, b)
       <==> _module.Tree#Equal(_module.Tree._h7(a), _module.Tree._h7(b))
         && _module.Nat#Equal(_module.Tree._h8(a), _module.Tree._h8(b))
         && _module.Tree#Equal(_module.Tree._h9(a), _module.Tree._h9(b))));

// Datatype extensionality axiom: _module.Tree
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Tree#Equal(a, b) } 
  _module.Tree#Equal(a, b) <==> a == b);

const unique class._module.Tree: ClassName;

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

// function declaration for _module._default.not
function _module.__default.not(b#0: DatatypeType) : DatatypeType;

function _module.__default.not#canCall(b#0: DatatypeType) : bool;

// consequence axiom for _module.__default.not
axiom 6 <= $FunctionContextHeight
   ==> (forall b#0: DatatypeType :: 
    { _module.__default.not(b#0) } 
    _module.__default.not#canCall(b#0)
         || (6 != $FunctionContextHeight && $Is(b#0, Tclass._module.Bool()))
       ==> $Is(_module.__default.not(b#0), Tclass._module.Bool()));

function _module.__default.not#requires(DatatypeType) : bool;

// #requires axiom for _module.__default.not
axiom (forall b#0: DatatypeType :: 
  { _module.__default.not#requires(b#0) } 
  $Is(b#0, Tclass._module.Bool()) ==> _module.__default.not#requires(b#0) == true);

// definition axiom for _module.__default.not (revealed)
axiom 6 <= $FunctionContextHeight
   ==> (forall b#0: DatatypeType :: 
    { _module.__default.not(b#0) } 
    _module.__default.not#canCall(b#0)
         || (6 != $FunctionContextHeight && $Is(b#0, Tclass._module.Bool()))
       ==> _module.__default.not(b#0)
         == (if _module.Bool.False_q(b#0)
           then #_module.Bool.True()
           else #_module.Bool.False()));

// definition axiom for _module.__default.not for all literals (revealed)
axiom 6 <= $FunctionContextHeight
   ==> (forall b#0: DatatypeType :: 
    {:weight 3} { _module.__default.not(Lit(b#0)) } 
    _module.__default.not#canCall(Lit(b#0))
         || (6 != $FunctionContextHeight && $Is(b#0, Tclass._module.Bool()))
       ==> _module.__default.not(Lit(b#0))
         == (if _module.Bool.False_q(Lit(b#0))
           then #_module.Bool.True()
           else #_module.Bool.False()));

procedure CheckWellformed$$_module.__default.not(b#0: DatatypeType where $Is(b#0, Tclass._module.Bool()));
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;



// function declaration for _module._default.and
function _module.__default.and(a#0: DatatypeType, b#0: DatatypeType) : DatatypeType;

function _module.__default.and#canCall(a#0: DatatypeType, b#0: DatatypeType) : bool;

// consequence axiom for _module.__default.and
axiom 7 <= $FunctionContextHeight
   ==> (forall a#0: DatatypeType, b#0: DatatypeType :: 
    { _module.__default.and(a#0, b#0) } 
    _module.__default.and#canCall(a#0, b#0)
         || (7 != $FunctionContextHeight
           && 
          $Is(a#0, Tclass._module.Bool())
           && $Is(b#0, Tclass._module.Bool()))
       ==> $Is(_module.__default.and(a#0, b#0), Tclass._module.Bool()));

function _module.__default.and#requires(DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.and
axiom (forall a#0: DatatypeType, b#0: DatatypeType :: 
  { _module.__default.and#requires(a#0, b#0) } 
  $Is(a#0, Tclass._module.Bool()) && $Is(b#0, Tclass._module.Bool())
     ==> _module.__default.and#requires(a#0, b#0) == true);

// definition axiom for _module.__default.and (revealed)
axiom 7 <= $FunctionContextHeight
   ==> (forall a#0: DatatypeType, b#0: DatatypeType :: 
    { _module.__default.and(a#0, b#0) } 
    _module.__default.and#canCall(a#0, b#0)
         || (7 != $FunctionContextHeight
           && 
          $Is(a#0, Tclass._module.Bool())
           && $Is(b#0, Tclass._module.Bool()))
       ==> $IsA#_module.Bool(a#0)
         && (_module.Bool#Equal(a#0, #_module.Bool.True()) ==> $IsA#_module.Bool(b#0))
         && _module.__default.and(a#0, b#0)
           == (if _module.Bool#Equal(a#0, #_module.Bool.True())
               && _module.Bool#Equal(b#0, #_module.Bool.True())
             then #_module.Bool.True()
             else #_module.Bool.False()));

// definition axiom for _module.__default.and for all literals (revealed)
axiom 7 <= $FunctionContextHeight
   ==> (forall a#0: DatatypeType, b#0: DatatypeType :: 
    {:weight 3} { _module.__default.and(Lit(a#0), Lit(b#0)) } 
    _module.__default.and#canCall(Lit(a#0), Lit(b#0))
         || (7 != $FunctionContextHeight
           && 
          $Is(a#0, Tclass._module.Bool())
           && $Is(b#0, Tclass._module.Bool()))
       ==> $IsA#_module.Bool(Lit(a#0))
         && (_module.Bool#Equal(a#0, #_module.Bool.True()) ==> $IsA#_module.Bool(Lit(b#0)))
         && _module.__default.and(Lit(a#0), Lit(b#0))
           == (if _module.Bool#Equal(a#0, #_module.Bool.True())
               && _module.Bool#Equal(b#0, #_module.Bool.True())
             then #_module.Bool.True()
             else #_module.Bool.False()));

procedure CheckWellformed$$_module.__default.and(a#0: DatatypeType where $Is(a#0, Tclass._module.Bool()), 
    b#0: DatatypeType where $Is(b#0, Tclass._module.Bool()));
  free requires 7 == $FunctionContextHeight;
  modifies $Heap, $Tick;



// function declaration for _module._default.add
function _module.__default.add($ly: LayerType, x#0: DatatypeType, y#0: DatatypeType) : DatatypeType;

function _module.__default.add#canCall(x#0: DatatypeType, y#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, x#0: DatatypeType, y#0: DatatypeType :: 
  { _module.__default.add($LS($ly), x#0, y#0) } 
  _module.__default.add($LS($ly), x#0, y#0)
     == _module.__default.add($ly, x#0, y#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, x#0: DatatypeType, y#0: DatatypeType :: 
  { _module.__default.add(AsFuelBottom($ly), x#0, y#0) } 
  _module.__default.add($ly, x#0, y#0) == _module.__default.add($LZ, x#0, y#0));

// consequence axiom for _module.__default.add
axiom 8 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, x#0: DatatypeType, y#0: DatatypeType :: 
    { _module.__default.add($ly, x#0, y#0) } 
    _module.__default.add#canCall(x#0, y#0)
         || (8 != $FunctionContextHeight
           && 
          $Is(x#0, Tclass._module.Nat())
           && $Is(y#0, Tclass._module.Nat()))
       ==> $Is(_module.__default.add($ly, x#0, y#0), Tclass._module.Nat()));

function _module.__default.add#requires(LayerType, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.add
axiom (forall $ly: LayerType, x#0: DatatypeType, y#0: DatatypeType :: 
  { _module.__default.add#requires($ly, x#0, y#0) } 
  $Is(x#0, Tclass._module.Nat()) && $Is(y#0, Tclass._module.Nat())
     ==> _module.__default.add#requires($ly, x#0, y#0) == true);

// definition axiom for _module.__default.add (revealed)
axiom 8 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, x#0: DatatypeType, y#0: DatatypeType :: 
    { _module.__default.add($LS($ly), x#0, y#0) } 
    _module.__default.add#canCall(x#0, y#0)
         || (8 != $FunctionContextHeight
           && 
          $Is(x#0, Tclass._module.Nat())
           && $Is(y#0, Tclass._module.Nat()))
       ==> (!_module.Nat.Zero_q(x#0)
           ==> (var w#1 := _module.Nat._h0(x#0); _module.__default.add#canCall(w#1, y#0)))
         && _module.__default.add($LS($ly), x#0, y#0)
           == (if _module.Nat.Zero_q(x#0)
             then y#0
             else (var w#0 := _module.Nat._h0(x#0); 
              #_module.Nat.Suc(_module.__default.add($ly, w#0, y#0)))));

// definition axiom for _module.__default.add for all literals (revealed)
axiom 8 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, x#0: DatatypeType, y#0: DatatypeType :: 
    {:weight 3} { _module.__default.add($LS($ly), Lit(x#0), Lit(y#0)) } 
    _module.__default.add#canCall(Lit(x#0), Lit(y#0))
         || (8 != $FunctionContextHeight
           && 
          $Is(x#0, Tclass._module.Nat())
           && $Is(y#0, Tclass._module.Nat()))
       ==> (!Lit(_module.Nat.Zero_q(Lit(x#0)))
           ==> (var w#3 := Lit(_module.Nat._h0(Lit(x#0))); 
            _module.__default.add#canCall(w#3, Lit(y#0))))
         && _module.__default.add($LS($ly), Lit(x#0), Lit(y#0))
           == (if _module.Nat.Zero_q(Lit(x#0))
             then y#0
             else (var w#2 := Lit(_module.Nat._h0(Lit(x#0))); 
              Lit(#_module.Nat.Suc(Lit(_module.__default.add($LS($ly), w#2, Lit(y#0))))))));

procedure CheckWellformed$$_module.__default.add(x#0: DatatypeType where $Is(x#0, Tclass._module.Nat()), 
    y#0: DatatypeType where $Is(y#0, Tclass._module.Nat()));
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.add(x#0: DatatypeType, y#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: DatatypeType;
  var w#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var ##x#0: DatatypeType;
  var ##y#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function add
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(34,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.add($LS($LZ), x#0, y#0), Tclass._module.Nat());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (x#0 == #_module.Nat.Zero())
        {
            assume _module.__default.add($LS($LZ), x#0, y#0) == y#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.add($LS($LZ), x#0, y#0), Tclass._module.Nat());
        }
        else if (x#0 == #_module.Nat.Suc(_mcc#0#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.Nat());
            havoc w#Z#0;
            assume $Is(w#Z#0, Tclass._module.Nat());
            assume let#0#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.Nat());
            assume w#Z#0 == let#0#0#0;
            ##x#0 := w#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##x#0, Tclass._module.Nat(), $Heap);
            ##y#0 := y#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##y#0, Tclass._module.Nat(), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(##x#0) < DtRank(x#0)
               || (DtRank(##x#0) == DtRank(x#0) && DtRank(##y#0) < DtRank(y#0));
            assume _module.__default.add#canCall(w#Z#0, y#0);
            assume _module.__default.add($LS($LZ), x#0, y#0)
               == #_module.Nat.Suc(_module.__default.add($LS($LZ), w#Z#0, y#0));
            assume _module.__default.add#canCall(w#Z#0, y#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.add($LS($LZ), x#0, y#0), Tclass._module.Nat());
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
    }
}



// function declaration for _module._default.minus
function _module.__default.minus($ly: LayerType, x#0: DatatypeType, y#0: DatatypeType) : DatatypeType;

function _module.__default.minus#canCall(x#0: DatatypeType, y#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, x#0: DatatypeType, y#0: DatatypeType :: 
  { _module.__default.minus($LS($ly), x#0, y#0) } 
  _module.__default.minus($LS($ly), x#0, y#0)
     == _module.__default.minus($ly, x#0, y#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, x#0: DatatypeType, y#0: DatatypeType :: 
  { _module.__default.minus(AsFuelBottom($ly), x#0, y#0) } 
  _module.__default.minus($ly, x#0, y#0) == _module.__default.minus($LZ, x#0, y#0));

// consequence axiom for _module.__default.minus
axiom 9 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, x#0: DatatypeType, y#0: DatatypeType :: 
    { _module.__default.minus($ly, x#0, y#0) } 
    _module.__default.minus#canCall(x#0, y#0)
         || (9 != $FunctionContextHeight
           && 
          $Is(x#0, Tclass._module.Nat())
           && $Is(y#0, Tclass._module.Nat()))
       ==> $Is(_module.__default.minus($ly, x#0, y#0), Tclass._module.Nat()));

function _module.__default.minus#requires(LayerType, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.minus
axiom (forall $ly: LayerType, x#0: DatatypeType, y#0: DatatypeType :: 
  { _module.__default.minus#requires($ly, x#0, y#0) } 
  $Is(x#0, Tclass._module.Nat()) && $Is(y#0, Tclass._module.Nat())
     ==> _module.__default.minus#requires($ly, x#0, y#0) == true);

// definition axiom for _module.__default.minus (revealed)
axiom 9 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, x#0: DatatypeType, y#0: DatatypeType :: 
    { _module.__default.minus($LS($ly), x#0, y#0) } 
    _module.__default.minus#canCall(x#0, y#0)
         || (9 != $FunctionContextHeight
           && 
          $Is(x#0, Tclass._module.Nat())
           && $Is(y#0, Tclass._module.Nat()))
       ==> (!_module.Nat.Zero_q(x#0)
           ==> (var a#1 := _module.Nat._h0(x#0); 
            !_module.Nat.Zero_q(y#0)
               ==> (var b#1 := _module.Nat._h0(y#0); _module.__default.minus#canCall(a#1, b#1))))
         && _module.__default.minus($LS($ly), x#0, y#0)
           == (if _module.Nat.Zero_q(x#0)
             then #_module.Nat.Zero()
             else (var a#0 := _module.Nat._h0(x#0); 
              (if _module.Nat.Zero_q(y#0)
                 then x#0
                 else (var b#0 := _module.Nat._h0(y#0); _module.__default.minus($ly, a#0, b#0))))));

// definition axiom for _module.__default.minus for all literals (revealed)
axiom 9 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, x#0: DatatypeType, y#0: DatatypeType :: 
    {:weight 3} { _module.__default.minus($LS($ly), Lit(x#0), Lit(y#0)) } 
    _module.__default.minus#canCall(Lit(x#0), Lit(y#0))
         || (9 != $FunctionContextHeight
           && 
          $Is(x#0, Tclass._module.Nat())
           && $Is(y#0, Tclass._module.Nat()))
       ==> (!Lit(_module.Nat.Zero_q(Lit(x#0)))
           ==> (var a#3 := Lit(_module.Nat._h0(Lit(x#0))); 
            !Lit(_module.Nat.Zero_q(Lit(y#0)))
               ==> (var b#3 := Lit(_module.Nat._h0(Lit(y#0))); 
                _module.__default.minus#canCall(a#3, b#3))))
         && _module.__default.minus($LS($ly), Lit(x#0), Lit(y#0))
           == (if _module.Nat.Zero_q(Lit(x#0))
             then #_module.Nat.Zero()
             else (var a#2 := Lit(_module.Nat._h0(Lit(x#0))); 
              (if _module.Nat.Zero_q(Lit(y#0))
                 then x#0
                 else (var b#2 := Lit(_module.Nat._h0(Lit(y#0))); 
                  Lit(_module.__default.minus($LS($ly), a#2, b#2)))))));

procedure CheckWellformed$$_module.__default.minus(x#0: DatatypeType where $Is(x#0, Tclass._module.Nat()), 
    y#0: DatatypeType where $Is(y#0, Tclass._module.Nat()));
  free requires 9 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.minus(x#0: DatatypeType, y#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: DatatypeType;
  var a#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var _mcc#1#0: DatatypeType;
  var b#Z#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var ##x#0: DatatypeType;
  var ##y#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function minus
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(41,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.minus($LS($LZ), x#0, y#0), Tclass._module.Nat());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (x#0 == #_module.Nat.Zero())
        {
            assume _module.__default.minus($LS($LZ), x#0, y#0) == Lit(#_module.Nat.Zero());
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.minus($LS($LZ), x#0, y#0), Tclass._module.Nat());
        }
        else if (x#0 == #_module.Nat.Suc(_mcc#0#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.Nat());
            havoc a#Z#0;
            assume $Is(a#Z#0, Tclass._module.Nat());
            assume let#0#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.Nat());
            assume a#Z#0 == let#0#0#0;
            if (y#0 == #_module.Nat.Zero())
            {
                assume _module.__default.minus($LS($LZ), x#0, y#0) == x#0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.minus($LS($LZ), x#0, y#0), Tclass._module.Nat());
            }
            else if (y#0 == #_module.Nat.Suc(_mcc#1#0))
            {
                assume $Is(_mcc#1#0, Tclass._module.Nat());
                havoc b#Z#0;
                assume $Is(b#Z#0, Tclass._module.Nat());
                assume let#1#0#0 == _mcc#1#0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(let#1#0#0, Tclass._module.Nat());
                assume b#Z#0 == let#1#0#0;
                ##x#0 := a#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##x#0, Tclass._module.Nat(), $Heap);
                ##y#0 := b#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##y#0, Tclass._module.Nat(), $Heap);
                b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assert DtRank(##x#0) < DtRank(x#0)
                   || (DtRank(##x#0) == DtRank(x#0) && DtRank(##y#0) < DtRank(y#0));
                assume _module.__default.minus#canCall(a#Z#0, b#Z#0);
                assume _module.__default.minus($LS($LZ), x#0, y#0)
                   == _module.__default.minus($LS($LZ), a#Z#0, b#Z#0);
                assume _module.__default.minus#canCall(a#Z#0, b#Z#0);
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.minus($LS($LZ), x#0, y#0), Tclass._module.Nat());
            }
            else
            {
                assume false;
            }
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
    }
}



// function declaration for _module._default.eq
function _module.__default.eq($ly: LayerType, x#0: DatatypeType, y#0: DatatypeType) : DatatypeType;

function _module.__default.eq#canCall(x#0: DatatypeType, y#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, x#0: DatatypeType, y#0: DatatypeType :: 
  { _module.__default.eq($LS($ly), x#0, y#0) } 
  _module.__default.eq($LS($ly), x#0, y#0) == _module.__default.eq($ly, x#0, y#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, x#0: DatatypeType, y#0: DatatypeType :: 
  { _module.__default.eq(AsFuelBottom($ly), x#0, y#0) } 
  _module.__default.eq($ly, x#0, y#0) == _module.__default.eq($LZ, x#0, y#0));

// consequence axiom for _module.__default.eq
axiom 10 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, x#0: DatatypeType, y#0: DatatypeType :: 
    { _module.__default.eq($ly, x#0, y#0) } 
    _module.__default.eq#canCall(x#0, y#0)
         || (10 != $FunctionContextHeight
           && 
          $Is(x#0, Tclass._module.Nat())
           && $Is(y#0, Tclass._module.Nat()))
       ==> $Is(_module.__default.eq($ly, x#0, y#0), Tclass._module.Bool()));

function _module.__default.eq#requires(LayerType, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.eq
axiom (forall $ly: LayerType, x#0: DatatypeType, y#0: DatatypeType :: 
  { _module.__default.eq#requires($ly, x#0, y#0) } 
  $Is(x#0, Tclass._module.Nat()) && $Is(y#0, Tclass._module.Nat())
     ==> _module.__default.eq#requires($ly, x#0, y#0) == true);

// definition axiom for _module.__default.eq (revealed)
axiom 10 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, x#0: DatatypeType, y#0: DatatypeType :: 
    { _module.__default.eq($LS($ly), x#0, y#0) } 
    _module.__default.eq#canCall(x#0, y#0)
         || (10 != $FunctionContextHeight
           && 
          $Is(x#0, Tclass._module.Nat())
           && $Is(y#0, Tclass._module.Nat()))
       ==> (!_module.Nat.Zero_q(x#0)
           ==> (var a#1 := _module.Nat._h0(x#0); 
            !_module.Nat.Zero_q(y#0)
               ==> (var b#3 := _module.Nat._h0(y#0); _module.__default.eq#canCall(a#1, b#3))))
         && _module.__default.eq($LS($ly), x#0, y#0)
           == (if _module.Nat.Zero_q(x#0)
             then (if _module.Nat.Zero_q(y#0)
               then #_module.Bool.True()
               else (var b#0 := _module.Nat._h0(y#0); Lit(#_module.Bool.False())))
             else (var a#0 := _module.Nat._h0(x#0); 
              (if _module.Nat.Zero_q(y#0)
                 then #_module.Bool.False()
                 else (var b#1 := _module.Nat._h0(y#0); _module.__default.eq($ly, a#0, b#1))))));

// definition axiom for _module.__default.eq for all literals (revealed)
axiom 10 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, x#0: DatatypeType, y#0: DatatypeType :: 
    {:weight 3} { _module.__default.eq($LS($ly), Lit(x#0), Lit(y#0)) } 
    _module.__default.eq#canCall(Lit(x#0), Lit(y#0))
         || (10 != $FunctionContextHeight
           && 
          $Is(x#0, Tclass._module.Nat())
           && $Is(y#0, Tclass._module.Nat()))
       ==> (!Lit(_module.Nat.Zero_q(Lit(x#0)))
           ==> (var a#3 := Lit(_module.Nat._h0(Lit(x#0))); 
            !Lit(_module.Nat.Zero_q(Lit(y#0)))
               ==> (var b#7 := Lit(_module.Nat._h0(Lit(y#0))); 
                _module.__default.eq#canCall(a#3, b#7))))
         && _module.__default.eq($LS($ly), Lit(x#0), Lit(y#0))
           == (if _module.Nat.Zero_q(Lit(x#0))
             then (if _module.Nat.Zero_q(Lit(y#0))
               then #_module.Bool.True()
               else (var b#4 := Lit(_module.Nat._h0(Lit(y#0))); Lit(#_module.Bool.False())))
             else (var a#2 := Lit(_module.Nat._h0(Lit(x#0))); 
              (if _module.Nat.Zero_q(Lit(y#0))
                 then #_module.Bool.False()
                 else (var b#5 := Lit(_module.Nat._h0(Lit(y#0))); 
                  Lit(_module.__default.eq($LS($ly), a#2, b#5)))))));

procedure CheckWellformed$$_module.__default.eq(x#0: DatatypeType where $Is(x#0, Tclass._module.Nat()), 
    y#0: DatatypeType where $Is(y#0, Tclass._module.Nat()));
  free requires 10 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.eq(x#0: DatatypeType, y#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: DatatypeType;
  var a#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var _mcc#2#0: DatatypeType;
  var b#Z#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var ##x#0: DatatypeType;
  var ##y#0: DatatypeType;
  var _mcc#1#0: DatatypeType;
  var b#Z#1: DatatypeType;
  var let#2#0#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function eq
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(50,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.eq($LS($LZ), x#0, y#0), Tclass._module.Bool());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (x#0 == #_module.Nat.Zero())
        {
            if (y#0 == #_module.Nat.Zero())
            {
                assume _module.__default.eq($LS($LZ), x#0, y#0) == Lit(#_module.Bool.True());
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.eq($LS($LZ), x#0, y#0), Tclass._module.Bool());
            }
            else if (y#0 == #_module.Nat.Suc(_mcc#1#0))
            {
                assume $Is(_mcc#1#0, Tclass._module.Nat());
                havoc b#Z#1;
                assume $Is(b#Z#1, Tclass._module.Nat());
                assume let#2#0#0 == _mcc#1#0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(let#2#0#0, Tclass._module.Nat());
                assume b#Z#1 == let#2#0#0;
                assume _module.__default.eq($LS($LZ), x#0, y#0) == Lit(#_module.Bool.False());
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.eq($LS($LZ), x#0, y#0), Tclass._module.Bool());
            }
            else
            {
                assume false;
            }
        }
        else if (x#0 == #_module.Nat.Suc(_mcc#0#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.Nat());
            havoc a#Z#0;
            assume $Is(a#Z#0, Tclass._module.Nat());
            assume let#0#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.Nat());
            assume a#Z#0 == let#0#0#0;
            if (y#0 == #_module.Nat.Zero())
            {
                assume _module.__default.eq($LS($LZ), x#0, y#0) == Lit(#_module.Bool.False());
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.eq($LS($LZ), x#0, y#0), Tclass._module.Bool());
            }
            else if (y#0 == #_module.Nat.Suc(_mcc#2#0))
            {
                assume $Is(_mcc#2#0, Tclass._module.Nat());
                havoc b#Z#0;
                assume $Is(b#Z#0, Tclass._module.Nat());
                assume let#1#0#0 == _mcc#2#0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(let#1#0#0, Tclass._module.Nat());
                assume b#Z#0 == let#1#0#0;
                ##x#0 := a#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##x#0, Tclass._module.Nat(), $Heap);
                ##y#0 := b#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##y#0, Tclass._module.Nat(), $Heap);
                b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assert DtRank(##x#0) < DtRank(x#0)
                   || (DtRank(##x#0) == DtRank(x#0) && DtRank(##y#0) < DtRank(y#0));
                assume _module.__default.eq#canCall(a#Z#0, b#Z#0);
                assume _module.__default.eq($LS($LZ), x#0, y#0)
                   == _module.__default.eq($LS($LZ), a#Z#0, b#Z#0);
                assume _module.__default.eq#canCall(a#Z#0, b#Z#0);
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.eq($LS($LZ), x#0, y#0), Tclass._module.Bool());
            }
            else
            {
                assume false;
            }
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
    }
}



// function declaration for _module._default.leq
function _module.__default.leq($ly: LayerType, x#0: DatatypeType, y#0: DatatypeType) : DatatypeType;

function _module.__default.leq#canCall(x#0: DatatypeType, y#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, x#0: DatatypeType, y#0: DatatypeType :: 
  { _module.__default.leq($LS($ly), x#0, y#0) } 
  _module.__default.leq($LS($ly), x#0, y#0)
     == _module.__default.leq($ly, x#0, y#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, x#0: DatatypeType, y#0: DatatypeType :: 
  { _module.__default.leq(AsFuelBottom($ly), x#0, y#0) } 
  _module.__default.leq($ly, x#0, y#0) == _module.__default.leq($LZ, x#0, y#0));

// consequence axiom for _module.__default.leq
axiom 11 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, x#0: DatatypeType, y#0: DatatypeType :: 
    { _module.__default.leq($ly, x#0, y#0) } 
    _module.__default.leq#canCall(x#0, y#0)
         || (11 != $FunctionContextHeight
           && 
          $Is(x#0, Tclass._module.Nat())
           && $Is(y#0, Tclass._module.Nat()))
       ==> $Is(_module.__default.leq($ly, x#0, y#0), Tclass._module.Bool()));

function _module.__default.leq#requires(LayerType, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.leq
axiom (forall $ly: LayerType, x#0: DatatypeType, y#0: DatatypeType :: 
  { _module.__default.leq#requires($ly, x#0, y#0) } 
  $Is(x#0, Tclass._module.Nat()) && $Is(y#0, Tclass._module.Nat())
     ==> _module.__default.leq#requires($ly, x#0, y#0) == true);

// definition axiom for _module.__default.leq (revealed)
axiom 11 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, x#0: DatatypeType, y#0: DatatypeType :: 
    { _module.__default.leq($LS($ly), x#0, y#0) } 
    _module.__default.leq#canCall(x#0, y#0)
         || (11 != $FunctionContextHeight
           && 
          $Is(x#0, Tclass._module.Nat())
           && $Is(y#0, Tclass._module.Nat()))
       ==> (!_module.Nat.Zero_q(x#0)
           ==> (var a#1 := _module.Nat._h0(x#0); 
            !_module.Nat.Zero_q(y#0)
               ==> (var b#1 := _module.Nat._h0(y#0); _module.__default.leq#canCall(a#1, b#1))))
         && _module.__default.leq($LS($ly), x#0, y#0)
           == (if _module.Nat.Zero_q(x#0)
             then #_module.Bool.True()
             else (var a#0 := _module.Nat._h0(x#0); 
              (if _module.Nat.Zero_q(y#0)
                 then #_module.Bool.False()
                 else (var b#0 := _module.Nat._h0(y#0); _module.__default.leq($ly, a#0, b#0))))));

// definition axiom for _module.__default.leq for all literals (revealed)
axiom 11 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, x#0: DatatypeType, y#0: DatatypeType :: 
    {:weight 3} { _module.__default.leq($LS($ly), Lit(x#0), Lit(y#0)) } 
    _module.__default.leq#canCall(Lit(x#0), Lit(y#0))
         || (11 != $FunctionContextHeight
           && 
          $Is(x#0, Tclass._module.Nat())
           && $Is(y#0, Tclass._module.Nat()))
       ==> (!Lit(_module.Nat.Zero_q(Lit(x#0)))
           ==> (var a#3 := Lit(_module.Nat._h0(Lit(x#0))); 
            !Lit(_module.Nat.Zero_q(Lit(y#0)))
               ==> (var b#3 := Lit(_module.Nat._h0(Lit(y#0))); 
                _module.__default.leq#canCall(a#3, b#3))))
         && _module.__default.leq($LS($ly), Lit(x#0), Lit(y#0))
           == (if _module.Nat.Zero_q(Lit(x#0))
             then #_module.Bool.True()
             else (var a#2 := Lit(_module.Nat._h0(Lit(x#0))); 
              (if _module.Nat.Zero_q(Lit(y#0))
                 then #_module.Bool.False()
                 else (var b#2 := Lit(_module.Nat._h0(Lit(y#0))); 
                  Lit(_module.__default.leq($LS($ly), a#2, b#2)))))));

procedure CheckWellformed$$_module.__default.leq(x#0: DatatypeType where $Is(x#0, Tclass._module.Nat()), 
    y#0: DatatypeType where $Is(y#0, Tclass._module.Nat()));
  free requires 11 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.leq(x#0: DatatypeType, y#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: DatatypeType;
  var a#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var _mcc#1#0: DatatypeType;
  var b#Z#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var ##x#0: DatatypeType;
  var ##y#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function leq
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(61,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.leq($LS($LZ), x#0, y#0), Tclass._module.Bool());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (x#0 == #_module.Nat.Zero())
        {
            assume _module.__default.leq($LS($LZ), x#0, y#0) == Lit(#_module.Bool.True());
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.leq($LS($LZ), x#0, y#0), Tclass._module.Bool());
        }
        else if (x#0 == #_module.Nat.Suc(_mcc#0#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.Nat());
            havoc a#Z#0;
            assume $Is(a#Z#0, Tclass._module.Nat());
            assume let#0#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.Nat());
            assume a#Z#0 == let#0#0#0;
            if (y#0 == #_module.Nat.Zero())
            {
                assume _module.__default.leq($LS($LZ), x#0, y#0) == Lit(#_module.Bool.False());
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.leq($LS($LZ), x#0, y#0), Tclass._module.Bool());
            }
            else if (y#0 == #_module.Nat.Suc(_mcc#1#0))
            {
                assume $Is(_mcc#1#0, Tclass._module.Nat());
                havoc b#Z#0;
                assume $Is(b#Z#0, Tclass._module.Nat());
                assume let#1#0#0 == _mcc#1#0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(let#1#0#0, Tclass._module.Nat());
                assume b#Z#0 == let#1#0#0;
                ##x#0 := a#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##x#0, Tclass._module.Nat(), $Heap);
                ##y#0 := b#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##y#0, Tclass._module.Nat(), $Heap);
                b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assert DtRank(##x#0) < DtRank(x#0)
                   || (DtRank(##x#0) == DtRank(x#0) && DtRank(##y#0) < DtRank(y#0));
                assume _module.__default.leq#canCall(a#Z#0, b#Z#0);
                assume _module.__default.leq($LS($LZ), x#0, y#0)
                   == _module.__default.leq($LS($LZ), a#Z#0, b#Z#0);
                assume _module.__default.leq#canCall(a#Z#0, b#Z#0);
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.leq($LS($LZ), x#0, y#0), Tclass._module.Bool());
            }
            else
            {
                assume false;
            }
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
    }
}



// function declaration for _module._default.less
function _module.__default.less($ly: LayerType, x#0: DatatypeType, y#0: DatatypeType) : DatatypeType;

function _module.__default.less#canCall(x#0: DatatypeType, y#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, x#0: DatatypeType, y#0: DatatypeType :: 
  { _module.__default.less($LS($ly), x#0, y#0) } 
  _module.__default.less($LS($ly), x#0, y#0)
     == _module.__default.less($ly, x#0, y#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, x#0: DatatypeType, y#0: DatatypeType :: 
  { _module.__default.less(AsFuelBottom($ly), x#0, y#0) } 
  _module.__default.less($ly, x#0, y#0) == _module.__default.less($LZ, x#0, y#0));

// consequence axiom for _module.__default.less
axiom 12 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, x#0: DatatypeType, y#0: DatatypeType :: 
    { _module.__default.less($ly, x#0, y#0) } 
    _module.__default.less#canCall(x#0, y#0)
         || (12 != $FunctionContextHeight
           && 
          $Is(x#0, Tclass._module.Nat())
           && $Is(y#0, Tclass._module.Nat()))
       ==> $Is(_module.__default.less($ly, x#0, y#0), Tclass._module.Bool()));

function _module.__default.less#requires(LayerType, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.less
axiom (forall $ly: LayerType, x#0: DatatypeType, y#0: DatatypeType :: 
  { _module.__default.less#requires($ly, x#0, y#0) } 
  $Is(x#0, Tclass._module.Nat()) && $Is(y#0, Tclass._module.Nat())
     ==> _module.__default.less#requires($ly, x#0, y#0) == true);

// definition axiom for _module.__default.less (revealed)
axiom 12 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, x#0: DatatypeType, y#0: DatatypeType :: 
    { _module.__default.less($LS($ly), x#0, y#0) } 
    _module.__default.less#canCall(x#0, y#0)
         || (12 != $FunctionContextHeight
           && 
          $Is(x#0, Tclass._module.Nat())
           && $Is(y#0, Tclass._module.Nat()))
       ==> (!_module.Nat.Zero_q(y#0)
           ==> (var b#1 := _module.Nat._h0(y#0); 
            !_module.Nat.Zero_q(x#0)
               ==> (var a#1 := _module.Nat._h0(x#0); _module.__default.less#canCall(a#1, b#1))))
         && _module.__default.less($LS($ly), x#0, y#0)
           == (if _module.Nat.Zero_q(y#0)
             then #_module.Bool.False()
             else (var b#0 := _module.Nat._h0(y#0); 
              (if _module.Nat.Zero_q(x#0)
                 then #_module.Bool.True()
                 else (var a#0 := _module.Nat._h0(x#0); _module.__default.less($ly, a#0, b#0))))));

// definition axiom for _module.__default.less for all literals (revealed)
axiom 12 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, x#0: DatatypeType, y#0: DatatypeType :: 
    {:weight 3} { _module.__default.less($LS($ly), Lit(x#0), Lit(y#0)) } 
    _module.__default.less#canCall(Lit(x#0), Lit(y#0))
         || (12 != $FunctionContextHeight
           && 
          $Is(x#0, Tclass._module.Nat())
           && $Is(y#0, Tclass._module.Nat()))
       ==> (!Lit(_module.Nat.Zero_q(Lit(y#0)))
           ==> (var b#3 := Lit(_module.Nat._h0(Lit(y#0))); 
            !Lit(_module.Nat.Zero_q(Lit(x#0)))
               ==> (var a#3 := Lit(_module.Nat._h0(Lit(x#0))); 
                _module.__default.less#canCall(a#3, b#3))))
         && _module.__default.less($LS($ly), Lit(x#0), Lit(y#0))
           == (if _module.Nat.Zero_q(Lit(y#0))
             then #_module.Bool.False()
             else (var b#2 := Lit(_module.Nat._h0(Lit(y#0))); 
              (if _module.Nat.Zero_q(Lit(x#0))
                 then #_module.Bool.True()
                 else (var a#2 := Lit(_module.Nat._h0(Lit(x#0))); 
                  Lit(_module.__default.less($LS($ly), a#2, b#2)))))));

procedure CheckWellformed$$_module.__default.less(x#0: DatatypeType where $Is(x#0, Tclass._module.Nat()), 
    y#0: DatatypeType where $Is(y#0, Tclass._module.Nat()));
  free requires 12 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.less(x#0: DatatypeType, y#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: DatatypeType;
  var b#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var _mcc#1#0: DatatypeType;
  var a#Z#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var ##x#0: DatatypeType;
  var ##y#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function less
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(70,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.less($LS($LZ), x#0, y#0), Tclass._module.Bool());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (y#0 == #_module.Nat.Zero())
        {
            assume _module.__default.less($LS($LZ), x#0, y#0) == Lit(#_module.Bool.False());
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.less($LS($LZ), x#0, y#0), Tclass._module.Bool());
        }
        else if (y#0 == #_module.Nat.Suc(_mcc#0#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.Nat());
            havoc b#Z#0;
            assume $Is(b#Z#0, Tclass._module.Nat());
            assume let#0#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.Nat());
            assume b#Z#0 == let#0#0#0;
            if (x#0 == #_module.Nat.Zero())
            {
                assume _module.__default.less($LS($LZ), x#0, y#0) == Lit(#_module.Bool.True());
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.less($LS($LZ), x#0, y#0), Tclass._module.Bool());
            }
            else if (x#0 == #_module.Nat.Suc(_mcc#1#0))
            {
                assume $Is(_mcc#1#0, Tclass._module.Nat());
                havoc a#Z#0;
                assume $Is(a#Z#0, Tclass._module.Nat());
                assume let#1#0#0 == _mcc#1#0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(let#1#0#0, Tclass._module.Nat());
                assume a#Z#0 == let#1#0#0;
                ##x#0 := a#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##x#0, Tclass._module.Nat(), $Heap);
                ##y#0 := b#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##y#0, Tclass._module.Nat(), $Heap);
                b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assert DtRank(##x#0) < DtRank(x#0)
                   || (DtRank(##x#0) == DtRank(x#0) && DtRank(##y#0) < DtRank(y#0));
                assume _module.__default.less#canCall(a#Z#0, b#Z#0);
                assume _module.__default.less($LS($LZ), x#0, y#0)
                   == _module.__default.less($LS($LZ), a#Z#0, b#Z#0);
                assume _module.__default.less#canCall(a#Z#0, b#Z#0);
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.less($LS($LZ), x#0, y#0), Tclass._module.Bool());
            }
            else
            {
                assume false;
            }
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
    }
}



// function declaration for _module._default.min
function _module.__default.min($ly: LayerType, x#0: DatatypeType, y#0: DatatypeType) : DatatypeType;

function _module.__default.min#canCall(x#0: DatatypeType, y#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, x#0: DatatypeType, y#0: DatatypeType :: 
  { _module.__default.min($LS($ly), x#0, y#0) } 
  _module.__default.min($LS($ly), x#0, y#0)
     == _module.__default.min($ly, x#0, y#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, x#0: DatatypeType, y#0: DatatypeType :: 
  { _module.__default.min(AsFuelBottom($ly), x#0, y#0) } 
  _module.__default.min($ly, x#0, y#0) == _module.__default.min($LZ, x#0, y#0));

// consequence axiom for _module.__default.min
axiom 13 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, x#0: DatatypeType, y#0: DatatypeType :: 
    { _module.__default.min($ly, x#0, y#0) } 
    _module.__default.min#canCall(x#0, y#0)
         || (13 != $FunctionContextHeight
           && 
          $Is(x#0, Tclass._module.Nat())
           && $Is(y#0, Tclass._module.Nat()))
       ==> $Is(_module.__default.min($ly, x#0, y#0), Tclass._module.Nat()));

function _module.__default.min#requires(LayerType, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.min
axiom (forall $ly: LayerType, x#0: DatatypeType, y#0: DatatypeType :: 
  { _module.__default.min#requires($ly, x#0, y#0) } 
  $Is(x#0, Tclass._module.Nat()) && $Is(y#0, Tclass._module.Nat())
     ==> _module.__default.min#requires($ly, x#0, y#0) == true);

// definition axiom for _module.__default.min (revealed)
axiom 13 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, x#0: DatatypeType, y#0: DatatypeType :: 
    { _module.__default.min($LS($ly), x#0, y#0) } 
    _module.__default.min#canCall(x#0, y#0)
         || (13 != $FunctionContextHeight
           && 
          $Is(x#0, Tclass._module.Nat())
           && $Is(y#0, Tclass._module.Nat()))
       ==> (!_module.Nat.Zero_q(x#0)
           ==> (var a#1 := _module.Nat._h0(x#0); 
            !_module.Nat.Zero_q(y#0)
               ==> (var b#1 := _module.Nat._h0(y#0); _module.__default.min#canCall(a#1, b#1))))
         && _module.__default.min($LS($ly), x#0, y#0)
           == (if _module.Nat.Zero_q(x#0)
             then #_module.Nat.Zero()
             else (var a#0 := _module.Nat._h0(x#0); 
              (if _module.Nat.Zero_q(y#0)
                 then #_module.Nat.Zero()
                 else (var b#0 := _module.Nat._h0(y#0); 
                  #_module.Nat.Suc(_module.__default.min($ly, a#0, b#0)))))));

// definition axiom for _module.__default.min for all literals (revealed)
axiom 13 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, x#0: DatatypeType, y#0: DatatypeType :: 
    {:weight 3} { _module.__default.min($LS($ly), Lit(x#0), Lit(y#0)) } 
    _module.__default.min#canCall(Lit(x#0), Lit(y#0))
         || (13 != $FunctionContextHeight
           && 
          $Is(x#0, Tclass._module.Nat())
           && $Is(y#0, Tclass._module.Nat()))
       ==> (!Lit(_module.Nat.Zero_q(Lit(x#0)))
           ==> (var a#3 := Lit(_module.Nat._h0(Lit(x#0))); 
            !Lit(_module.Nat.Zero_q(Lit(y#0)))
               ==> (var b#3 := Lit(_module.Nat._h0(Lit(y#0))); 
                _module.__default.min#canCall(a#3, b#3))))
         && _module.__default.min($LS($ly), Lit(x#0), Lit(y#0))
           == (if _module.Nat.Zero_q(Lit(x#0))
             then #_module.Nat.Zero()
             else (var a#2 := Lit(_module.Nat._h0(Lit(x#0))); 
              (if _module.Nat.Zero_q(Lit(y#0))
                 then #_module.Nat.Zero()
                 else (var b#2 := Lit(_module.Nat._h0(Lit(y#0))); 
                  Lit(#_module.Nat.Suc(Lit(_module.__default.min($LS($ly), a#2, b#2)))))))));

procedure CheckWellformed$$_module.__default.min(x#0: DatatypeType where $Is(x#0, Tclass._module.Nat()), 
    y#0: DatatypeType where $Is(y#0, Tclass._module.Nat()));
  free requires 13 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.min(x#0: DatatypeType, y#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: DatatypeType;
  var a#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var _mcc#1#0: DatatypeType;
  var b#Z#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var ##x#0: DatatypeType;
  var ##y#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function min
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(79,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.min($LS($LZ), x#0, y#0), Tclass._module.Nat());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (x#0 == #_module.Nat.Zero())
        {
            assume _module.__default.min($LS($LZ), x#0, y#0) == Lit(#_module.Nat.Zero());
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.min($LS($LZ), x#0, y#0), Tclass._module.Nat());
        }
        else if (x#0 == #_module.Nat.Suc(_mcc#0#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.Nat());
            havoc a#Z#0;
            assume $Is(a#Z#0, Tclass._module.Nat());
            assume let#0#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.Nat());
            assume a#Z#0 == let#0#0#0;
            if (y#0 == #_module.Nat.Zero())
            {
                assume _module.__default.min($LS($LZ), x#0, y#0) == Lit(#_module.Nat.Zero());
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.min($LS($LZ), x#0, y#0), Tclass._module.Nat());
            }
            else if (y#0 == #_module.Nat.Suc(_mcc#1#0))
            {
                assume $Is(_mcc#1#0, Tclass._module.Nat());
                havoc b#Z#0;
                assume $Is(b#Z#0, Tclass._module.Nat());
                assume let#1#0#0 == _mcc#1#0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(let#1#0#0, Tclass._module.Nat());
                assume b#Z#0 == let#1#0#0;
                ##x#0 := a#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##x#0, Tclass._module.Nat(), $Heap);
                ##y#0 := b#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##y#0, Tclass._module.Nat(), $Heap);
                b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assert DtRank(##x#0) < DtRank(x#0)
                   || (DtRank(##x#0) == DtRank(x#0) && DtRank(##y#0) < DtRank(y#0));
                assume _module.__default.min#canCall(a#Z#0, b#Z#0);
                assume _module.__default.min($LS($LZ), x#0, y#0)
                   == #_module.Nat.Suc(_module.__default.min($LS($LZ), a#Z#0, b#Z#0));
                assume _module.__default.min#canCall(a#Z#0, b#Z#0);
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.min($LS($LZ), x#0, y#0), Tclass._module.Nat());
            }
            else
            {
                assume false;
            }
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
    }
}



// function declaration for _module._default.max
function _module.__default.max($ly: LayerType, x#0: DatatypeType, y#0: DatatypeType) : DatatypeType;

function _module.__default.max#canCall(x#0: DatatypeType, y#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, x#0: DatatypeType, y#0: DatatypeType :: 
  { _module.__default.max($LS($ly), x#0, y#0) } 
  _module.__default.max($LS($ly), x#0, y#0)
     == _module.__default.max($ly, x#0, y#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, x#0: DatatypeType, y#0: DatatypeType :: 
  { _module.__default.max(AsFuelBottom($ly), x#0, y#0) } 
  _module.__default.max($ly, x#0, y#0) == _module.__default.max($LZ, x#0, y#0));

// consequence axiom for _module.__default.max
axiom 14 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, x#0: DatatypeType, y#0: DatatypeType :: 
    { _module.__default.max($ly, x#0, y#0) } 
    _module.__default.max#canCall(x#0, y#0)
         || (14 != $FunctionContextHeight
           && 
          $Is(x#0, Tclass._module.Nat())
           && $Is(y#0, Tclass._module.Nat()))
       ==> $Is(_module.__default.max($ly, x#0, y#0), Tclass._module.Nat()));

function _module.__default.max#requires(LayerType, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.max
axiom (forall $ly: LayerType, x#0: DatatypeType, y#0: DatatypeType :: 
  { _module.__default.max#requires($ly, x#0, y#0) } 
  $Is(x#0, Tclass._module.Nat()) && $Is(y#0, Tclass._module.Nat())
     ==> _module.__default.max#requires($ly, x#0, y#0) == true);

// definition axiom for _module.__default.max (revealed)
axiom 14 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, x#0: DatatypeType, y#0: DatatypeType :: 
    { _module.__default.max($LS($ly), x#0, y#0) } 
    _module.__default.max#canCall(x#0, y#0)
         || (14 != $FunctionContextHeight
           && 
          $Is(x#0, Tclass._module.Nat())
           && $Is(y#0, Tclass._module.Nat()))
       ==> (!_module.Nat.Zero_q(x#0)
           ==> (var a#1 := _module.Nat._h0(x#0); 
            !_module.Nat.Zero_q(y#0)
               ==> (var b#1 := _module.Nat._h0(y#0); _module.__default.max#canCall(a#1, b#1))))
         && _module.__default.max($LS($ly), x#0, y#0)
           == (if _module.Nat.Zero_q(x#0)
             then y#0
             else (var a#0 := _module.Nat._h0(x#0); 
              (if _module.Nat.Zero_q(y#0)
                 then x#0
                 else (var b#0 := _module.Nat._h0(y#0); 
                  #_module.Nat.Suc(_module.__default.max($ly, a#0, b#0)))))));

// definition axiom for _module.__default.max for all literals (revealed)
axiom 14 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, x#0: DatatypeType, y#0: DatatypeType :: 
    {:weight 3} { _module.__default.max($LS($ly), Lit(x#0), Lit(y#0)) } 
    _module.__default.max#canCall(Lit(x#0), Lit(y#0))
         || (14 != $FunctionContextHeight
           && 
          $Is(x#0, Tclass._module.Nat())
           && $Is(y#0, Tclass._module.Nat()))
       ==> (!Lit(_module.Nat.Zero_q(Lit(x#0)))
           ==> (var a#3 := Lit(_module.Nat._h0(Lit(x#0))); 
            !Lit(_module.Nat.Zero_q(Lit(y#0)))
               ==> (var b#3 := Lit(_module.Nat._h0(Lit(y#0))); 
                _module.__default.max#canCall(a#3, b#3))))
         && _module.__default.max($LS($ly), Lit(x#0), Lit(y#0))
           == (if _module.Nat.Zero_q(Lit(x#0))
             then y#0
             else (var a#2 := Lit(_module.Nat._h0(Lit(x#0))); 
              (if _module.Nat.Zero_q(Lit(y#0))
                 then x#0
                 else (var b#2 := Lit(_module.Nat._h0(Lit(y#0))); 
                  Lit(#_module.Nat.Suc(Lit(_module.__default.max($LS($ly), a#2, b#2)))))))));

procedure CheckWellformed$$_module.__default.max(x#0: DatatypeType where $Is(x#0, Tclass._module.Nat()), 
    y#0: DatatypeType where $Is(y#0, Tclass._module.Nat()));
  free requires 14 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.max(x#0: DatatypeType, y#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: DatatypeType;
  var a#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var _mcc#1#0: DatatypeType;
  var b#Z#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var ##x#0: DatatypeType;
  var ##y#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function max
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(88,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.max($LS($LZ), x#0, y#0), Tclass._module.Nat());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (x#0 == #_module.Nat.Zero())
        {
            assume _module.__default.max($LS($LZ), x#0, y#0) == y#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.max($LS($LZ), x#0, y#0), Tclass._module.Nat());
        }
        else if (x#0 == #_module.Nat.Suc(_mcc#0#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.Nat());
            havoc a#Z#0;
            assume $Is(a#Z#0, Tclass._module.Nat());
            assume let#0#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.Nat());
            assume a#Z#0 == let#0#0#0;
            if (y#0 == #_module.Nat.Zero())
            {
                assume _module.__default.max($LS($LZ), x#0, y#0) == x#0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.max($LS($LZ), x#0, y#0), Tclass._module.Nat());
            }
            else if (y#0 == #_module.Nat.Suc(_mcc#1#0))
            {
                assume $Is(_mcc#1#0, Tclass._module.Nat());
                havoc b#Z#0;
                assume $Is(b#Z#0, Tclass._module.Nat());
                assume let#1#0#0 == _mcc#1#0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(let#1#0#0, Tclass._module.Nat());
                assume b#Z#0 == let#1#0#0;
                ##x#0 := a#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##x#0, Tclass._module.Nat(), $Heap);
                ##y#0 := b#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##y#0, Tclass._module.Nat(), $Heap);
                b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assert DtRank(##x#0) < DtRank(x#0)
                   || (DtRank(##x#0) == DtRank(x#0) && DtRank(##y#0) < DtRank(y#0));
                assume _module.__default.max#canCall(a#Z#0, b#Z#0);
                assume _module.__default.max($LS($LZ), x#0, y#0)
                   == #_module.Nat.Suc(_module.__default.max($LS($LZ), a#Z#0, b#Z#0));
                assume _module.__default.max#canCall(a#Z#0, b#Z#0);
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.max($LS($LZ), x#0, y#0), Tclass._module.Nat());
            }
            else
            {
                assume false;
            }
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
    }
}



// function declaration for _module._default.concat
function _module.__default.concat($ly: LayerType, xs#0: DatatypeType, ys#0: DatatypeType) : DatatypeType;

function _module.__default.concat#canCall(xs#0: DatatypeType, ys#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, xs#0: DatatypeType, ys#0: DatatypeType :: 
  { _module.__default.concat($LS($ly), xs#0, ys#0) } 
  _module.__default.concat($LS($ly), xs#0, ys#0)
     == _module.__default.concat($ly, xs#0, ys#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, xs#0: DatatypeType, ys#0: DatatypeType :: 
  { _module.__default.concat(AsFuelBottom($ly), xs#0, ys#0) } 
  _module.__default.concat($ly, xs#0, ys#0)
     == _module.__default.concat($LZ, xs#0, ys#0));

// consequence axiom for _module.__default.concat
axiom 15 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, xs#0: DatatypeType, ys#0: DatatypeType :: 
    { _module.__default.concat($ly, xs#0, ys#0) } 
    _module.__default.concat#canCall(xs#0, ys#0)
         || (15 != $FunctionContextHeight
           && 
          $Is(xs#0, Tclass._module.List())
           && $Is(ys#0, Tclass._module.List()))
       ==> $Is(_module.__default.concat($ly, xs#0, ys#0), Tclass._module.List()));

function _module.__default.concat#requires(LayerType, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.concat
axiom (forall $ly: LayerType, xs#0: DatatypeType, ys#0: DatatypeType :: 
  { _module.__default.concat#requires($ly, xs#0, ys#0) } 
  $Is(xs#0, Tclass._module.List()) && $Is(ys#0, Tclass._module.List())
     ==> _module.__default.concat#requires($ly, xs#0, ys#0) == true);

// definition axiom for _module.__default.concat (revealed)
axiom 15 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, xs#0: DatatypeType, ys#0: DatatypeType :: 
    { _module.__default.concat($LS($ly), xs#0, ys#0) } 
    _module.__default.concat#canCall(xs#0, ys#0)
         || (15 != $FunctionContextHeight
           && 
          $Is(xs#0, Tclass._module.List())
           && $Is(ys#0, Tclass._module.List()))
       ==> (!_module.List.Nil_q(xs#0)
           ==> (var tail#1 := _module.List._h2(xs#0); 
            _module.__default.concat#canCall(tail#1, ys#0)))
         && _module.__default.concat($LS($ly), xs#0, ys#0)
           == (if _module.List.Nil_q(xs#0)
             then ys#0
             else (var tail#0 := _module.List._h2(xs#0); 
              (var x#0 := _module.List._h1(xs#0); 
                #_module.List.Cons(x#0, _module.__default.concat($ly, tail#0, ys#0))))));

// definition axiom for _module.__default.concat for all literals (revealed)
axiom 15 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, xs#0: DatatypeType, ys#0: DatatypeType :: 
    {:weight 3} { _module.__default.concat($LS($ly), Lit(xs#0), Lit(ys#0)) } 
    _module.__default.concat#canCall(Lit(xs#0), Lit(ys#0))
         || (15 != $FunctionContextHeight
           && 
          $Is(xs#0, Tclass._module.List())
           && $Is(ys#0, Tclass._module.List()))
       ==> (!Lit(_module.List.Nil_q(Lit(xs#0)))
           ==> (var tail#3 := Lit(_module.List._h2(Lit(xs#0))); 
            _module.__default.concat#canCall(tail#3, Lit(ys#0))))
         && _module.__default.concat($LS($ly), Lit(xs#0), Lit(ys#0))
           == (if _module.List.Nil_q(Lit(xs#0))
             then ys#0
             else (var tail#2 := Lit(_module.List._h2(Lit(xs#0))); 
              (var x#2 := Lit(_module.List._h1(Lit(xs#0))); 
                Lit(#_module.List.Cons(x#2, Lit(_module.__default.concat($LS($ly), tail#2, Lit(ys#0)))))))));

procedure CheckWellformed$$_module.__default.concat(xs#0: DatatypeType where $Is(xs#0, Tclass._module.List()), 
    ys#0: DatatypeType where $Is(ys#0, Tclass._module.List()));
  free requires 15 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.concat(xs#0: DatatypeType, ys#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: DatatypeType;
  var _mcc#1#0: DatatypeType;
  var tail#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var x#Z#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var ##xs#0: DatatypeType;
  var ##ys#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function concat
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(99,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.concat($LS($LZ), xs#0, ys#0), Tclass._module.List());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (xs#0 == #_module.List.Nil())
        {
            assume _module.__default.concat($LS($LZ), xs#0, ys#0) == ys#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.concat($LS($LZ), xs#0, ys#0), Tclass._module.List());
        }
        else if (xs#0 == #_module.List.Cons(_mcc#0#0, _mcc#1#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.Nat());
            assume $Is(_mcc#1#0, Tclass._module.List());
            havoc tail#Z#0;
            assume $Is(tail#Z#0, Tclass._module.List());
            assume let#0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.List());
            assume tail#Z#0 == let#0#0#0;
            havoc x#Z#0;
            assume $Is(x#Z#0, Tclass._module.Nat());
            assume let#1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#1#0#0, Tclass._module.Nat());
            assume x#Z#0 == let#1#0#0;
            ##xs#0 := tail#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##xs#0, Tclass._module.List(), $Heap);
            ##ys#0 := ys#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##ys#0, Tclass._module.List(), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(##xs#0) < DtRank(xs#0)
               || (DtRank(##xs#0) == DtRank(xs#0) && DtRank(##ys#0) < DtRank(ys#0));
            assume _module.__default.concat#canCall(tail#Z#0, ys#0);
            assume _module.__default.concat($LS($LZ), xs#0, ys#0)
               == #_module.List.Cons(x#Z#0, _module.__default.concat($LS($LZ), tail#Z#0, ys#0));
            assume _module.__default.concat#canCall(tail#Z#0, ys#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.concat($LS($LZ), xs#0, ys#0), Tclass._module.List());
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
    }
}



// function declaration for _module._default.mem
function _module.__default.mem($ly: LayerType, x#0: DatatypeType, xs#0: DatatypeType) : DatatypeType;

function _module.__default.mem#canCall(x#0: DatatypeType, xs#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, x#0: DatatypeType, xs#0: DatatypeType :: 
  { _module.__default.mem($LS($ly), x#0, xs#0) } 
  _module.__default.mem($LS($ly), x#0, xs#0)
     == _module.__default.mem($ly, x#0, xs#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, x#0: DatatypeType, xs#0: DatatypeType :: 
  { _module.__default.mem(AsFuelBottom($ly), x#0, xs#0) } 
  _module.__default.mem($ly, x#0, xs#0) == _module.__default.mem($LZ, x#0, xs#0));

// consequence axiom for _module.__default.mem
axiom 16 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, x#0: DatatypeType, xs#0: DatatypeType :: 
    { _module.__default.mem($ly, x#0, xs#0) } 
    _module.__default.mem#canCall(x#0, xs#0)
         || (16 != $FunctionContextHeight
           && 
          $Is(x#0, Tclass._module.Nat())
           && $Is(xs#0, Tclass._module.List()))
       ==> $Is(_module.__default.mem($ly, x#0, xs#0), Tclass._module.Bool()));

function _module.__default.mem#requires(LayerType, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.mem
axiom (forall $ly: LayerType, x#0: DatatypeType, xs#0: DatatypeType :: 
  { _module.__default.mem#requires($ly, x#0, xs#0) } 
  $Is(x#0, Tclass._module.Nat()) && $Is(xs#0, Tclass._module.List())
     ==> _module.__default.mem#requires($ly, x#0, xs#0) == true);

// definition axiom for _module.__default.mem (revealed)
axiom 16 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, x#0: DatatypeType, xs#0: DatatypeType :: 
    { _module.__default.mem($LS($ly), x#0, xs#0) } 
    _module.__default.mem#canCall(x#0, xs#0)
         || (16 != $FunctionContextHeight
           && 
          $Is(x#0, Tclass._module.Nat())
           && $Is(xs#0, Tclass._module.List()))
       ==> (!_module.List.Nil_q(xs#0)
           ==> (var ys#1 := _module.List._h2(xs#0); 
            (var y#1 := _module.List._h1(xs#0); 
              $IsA#_module.Nat(x#0)
                 && $IsA#_module.Nat(y#1)
                 && (!_module.Nat#Equal(x#0, y#1) ==> _module.__default.mem#canCall(x#0, ys#1)))))
         && _module.__default.mem($LS($ly), x#0, xs#0)
           == (if _module.List.Nil_q(xs#0)
             then #_module.Bool.False()
             else (var ys#0 := _module.List._h2(xs#0); 
              (var y#0 := _module.List._h1(xs#0); 
                (if _module.Nat#Equal(x#0, y#0)
                   then #_module.Bool.True()
                   else _module.__default.mem($ly, x#0, ys#0))))));

// definition axiom for _module.__default.mem for all literals (revealed)
axiom 16 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, x#0: DatatypeType, xs#0: DatatypeType :: 
    {:weight 3} { _module.__default.mem($LS($ly), Lit(x#0), Lit(xs#0)) } 
    _module.__default.mem#canCall(Lit(x#0), Lit(xs#0))
         || (16 != $FunctionContextHeight
           && 
          $Is(x#0, Tclass._module.Nat())
           && $Is(xs#0, Tclass._module.List()))
       ==> (!Lit(_module.List.Nil_q(Lit(xs#0)))
           ==> (var ys#3 := Lit(_module.List._h2(Lit(xs#0))); 
            (var y#3 := Lit(_module.List._h1(Lit(xs#0))); 
              $IsA#_module.Nat(Lit(x#0))
                 && $IsA#_module.Nat(y#3)
                 && (!_module.Nat#Equal(x#0, y#3) ==> _module.__default.mem#canCall(Lit(x#0), ys#3)))))
         && _module.__default.mem($LS($ly), Lit(x#0), Lit(xs#0))
           == (if _module.List.Nil_q(Lit(xs#0))
             then #_module.Bool.False()
             else (var ys#2 := Lit(_module.List._h2(Lit(xs#0))); 
              (var y#2 := Lit(_module.List._h1(Lit(xs#0))); 
                (if _module.Nat#Equal(x#0, y#2)
                   then #_module.Bool.True()
                   else _module.__default.mem($LS($ly), Lit(x#0), ys#2))))));

procedure CheckWellformed$$_module.__default.mem(x#0: DatatypeType where $Is(x#0, Tclass._module.Nat()), 
    xs#0: DatatypeType where $Is(xs#0, Tclass._module.List()));
  free requires 16 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.mem(x#0: DatatypeType, xs#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: DatatypeType;
  var _mcc#1#0: DatatypeType;
  var ys#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var y#Z#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var ##x#0: DatatypeType;
  var ##xs#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function mem
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(106,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.mem($LS($LZ), x#0, xs#0), Tclass._module.Bool());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (xs#0 == #_module.List.Nil())
        {
            assume _module.__default.mem($LS($LZ), x#0, xs#0) == Lit(#_module.Bool.False());
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.mem($LS($LZ), x#0, xs#0), Tclass._module.Bool());
        }
        else if (xs#0 == #_module.List.Cons(_mcc#0#0, _mcc#1#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.Nat());
            assume $Is(_mcc#1#0, Tclass._module.List());
            havoc ys#Z#0;
            assume $Is(ys#Z#0, Tclass._module.List());
            assume let#0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.List());
            assume ys#Z#0 == let#0#0#0;
            havoc y#Z#0;
            assume $Is(y#Z#0, Tclass._module.Nat());
            assume let#1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#1#0#0, Tclass._module.Nat());
            assume y#Z#0 == let#1#0#0;
            if (_module.Nat#Equal(x#0, y#Z#0))
            {
                assume _module.__default.mem($LS($LZ), x#0, xs#0) == Lit(#_module.Bool.True());
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.mem($LS($LZ), x#0, xs#0), Tclass._module.Bool());
            }
            else
            {
                ##x#0 := x#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##x#0, Tclass._module.Nat(), $Heap);
                ##xs#0 := ys#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##xs#0, Tclass._module.List(), $Heap);
                b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assert DtRank(##x#0) < DtRank(x#0)
                   || (DtRank(##x#0) == DtRank(x#0) && DtRank(##xs#0) < DtRank(xs#0));
                assume _module.__default.mem#canCall(x#0, ys#Z#0);
                assume _module.__default.mem($LS($LZ), x#0, xs#0)
                   == _module.__default.mem($LS($LZ), x#0, ys#Z#0);
                assume _module.__default.mem#canCall(x#0, ys#Z#0);
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.mem($LS($LZ), x#0, xs#0), Tclass._module.Bool());
            }
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
    }
}



// function declaration for _module._default.delete
function _module.__default.delete($ly: LayerType, n#0: DatatypeType, xs#0: DatatypeType) : DatatypeType;

function _module.__default.delete#canCall(n#0: DatatypeType, xs#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, n#0: DatatypeType, xs#0: DatatypeType :: 
  { _module.__default.delete($LS($ly), n#0, xs#0) } 
  _module.__default.delete($LS($ly), n#0, xs#0)
     == _module.__default.delete($ly, n#0, xs#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, n#0: DatatypeType, xs#0: DatatypeType :: 
  { _module.__default.delete(AsFuelBottom($ly), n#0, xs#0) } 
  _module.__default.delete($ly, n#0, xs#0)
     == _module.__default.delete($LZ, n#0, xs#0));

// consequence axiom for _module.__default.delete
axiom 17 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: DatatypeType, xs#0: DatatypeType :: 
    { _module.__default.delete($ly, n#0, xs#0) } 
    _module.__default.delete#canCall(n#0, xs#0)
         || (17 != $FunctionContextHeight
           && 
          $Is(n#0, Tclass._module.Nat())
           && $Is(xs#0, Tclass._module.List()))
       ==> $Is(_module.__default.delete($ly, n#0, xs#0), Tclass._module.List()));

function _module.__default.delete#requires(LayerType, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.delete
axiom (forall $ly: LayerType, n#0: DatatypeType, xs#0: DatatypeType :: 
  { _module.__default.delete#requires($ly, n#0, xs#0) } 
  $Is(n#0, Tclass._module.Nat()) && $Is(xs#0, Tclass._module.List())
     ==> _module.__default.delete#requires($ly, n#0, xs#0) == true);

// definition axiom for _module.__default.delete (revealed)
axiom 17 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: DatatypeType, xs#0: DatatypeType :: 
    { _module.__default.delete($LS($ly), n#0, xs#0) } 
    _module.__default.delete#canCall(n#0, xs#0)
         || (17 != $FunctionContextHeight
           && 
          $Is(n#0, Tclass._module.Nat())
           && $Is(xs#0, Tclass._module.List()))
       ==> (!_module.List.Nil_q(xs#0)
           ==> (var ys#1 := _module.List._h2(xs#0); 
            (var y#1 := _module.List._h1(xs#0); 
              $IsA#_module.Nat(y#1)
                 && $IsA#_module.Nat(n#0)
                 && (_module.Nat#Equal(y#1, n#0) ==> _module.__default.delete#canCall(n#0, ys#1))
                 && (!_module.Nat#Equal(y#1, n#0) ==> _module.__default.delete#canCall(n#0, ys#1)))))
         && _module.__default.delete($LS($ly), n#0, xs#0)
           == (if _module.List.Nil_q(xs#0)
             then #_module.List.Nil()
             else (var ys#0 := _module.List._h2(xs#0); 
              (var y#0 := _module.List._h1(xs#0); 
                (if _module.Nat#Equal(y#0, n#0)
                   then _module.__default.delete($ly, n#0, ys#0)
                   else #_module.List.Cons(y#0, _module.__default.delete($ly, n#0, ys#0)))))));

// definition axiom for _module.__default.delete for all literals (revealed)
axiom 17 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: DatatypeType, xs#0: DatatypeType :: 
    {:weight 3} { _module.__default.delete($LS($ly), Lit(n#0), Lit(xs#0)) } 
    _module.__default.delete#canCall(Lit(n#0), Lit(xs#0))
         || (17 != $FunctionContextHeight
           && 
          $Is(n#0, Tclass._module.Nat())
           && $Is(xs#0, Tclass._module.List()))
       ==> (!Lit(_module.List.Nil_q(Lit(xs#0)))
           ==> (var ys#3 := Lit(_module.List._h2(Lit(xs#0))); 
            (var y#3 := Lit(_module.List._h1(Lit(xs#0))); 
              $IsA#_module.Nat(y#3)
                 && $IsA#_module.Nat(Lit(n#0))
                 && (_module.Nat#Equal(y#3, n#0)
                   ==> _module.__default.delete#canCall(Lit(n#0), ys#3))
                 && (!_module.Nat#Equal(y#3, n#0)
                   ==> _module.__default.delete#canCall(Lit(n#0), ys#3)))))
         && _module.__default.delete($LS($ly), Lit(n#0), Lit(xs#0))
           == (if _module.List.Nil_q(Lit(xs#0))
             then #_module.List.Nil()
             else (var ys#2 := Lit(_module.List._h2(Lit(xs#0))); 
              (var y#2 := Lit(_module.List._h1(Lit(xs#0))); 
                (if _module.Nat#Equal(y#2, n#0)
                   then _module.__default.delete($LS($ly), Lit(n#0), ys#2)
                   else #_module.List.Cons(y#2, Lit(_module.__default.delete($LS($ly), Lit(n#0), ys#2))))))));

procedure CheckWellformed$$_module.__default.delete(n#0: DatatypeType where $Is(n#0, Tclass._module.Nat()), 
    xs#0: DatatypeType where $Is(xs#0, Tclass._module.List()));
  free requires 17 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.delete(n#0: DatatypeType, xs#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: DatatypeType;
  var _mcc#1#0: DatatypeType;
  var ys#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var y#Z#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var ##n#0: DatatypeType;
  var ##xs#0: DatatypeType;
  var ##n#1: DatatypeType;
  var ##xs#1: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function delete
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(113,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.delete($LS($LZ), n#0, xs#0), Tclass._module.List());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (xs#0 == #_module.List.Nil())
        {
            assume _module.__default.delete($LS($LZ), n#0, xs#0) == Lit(#_module.List.Nil());
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.delete($LS($LZ), n#0, xs#0), Tclass._module.List());
        }
        else if (xs#0 == #_module.List.Cons(_mcc#0#0, _mcc#1#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.Nat());
            assume $Is(_mcc#1#0, Tclass._module.List());
            havoc ys#Z#0;
            assume $Is(ys#Z#0, Tclass._module.List());
            assume let#0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.List());
            assume ys#Z#0 == let#0#0#0;
            havoc y#Z#0;
            assume $Is(y#Z#0, Tclass._module.Nat());
            assume let#1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#1#0#0, Tclass._module.Nat());
            assume y#Z#0 == let#1#0#0;
            if (_module.Nat#Equal(y#Z#0, n#0))
            {
                ##n#0 := n#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#0, Tclass._module.Nat(), $Heap);
                ##xs#0 := ys#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##xs#0, Tclass._module.List(), $Heap);
                b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assert DtRank(##n#0) < DtRank(n#0)
                   || (DtRank(##n#0) == DtRank(n#0) && DtRank(##xs#0) < DtRank(xs#0));
                assume _module.__default.delete#canCall(n#0, ys#Z#0);
                assume _module.__default.delete($LS($LZ), n#0, xs#0)
                   == _module.__default.delete($LS($LZ), n#0, ys#Z#0);
                assume _module.__default.delete#canCall(n#0, ys#Z#0);
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.delete($LS($LZ), n#0, xs#0), Tclass._module.List());
            }
            else
            {
                ##n#1 := n#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#1, Tclass._module.Nat(), $Heap);
                ##xs#1 := ys#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##xs#1, Tclass._module.List(), $Heap);
                b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assert DtRank(##n#1) < DtRank(n#0)
                   || (DtRank(##n#1) == DtRank(n#0) && DtRank(##xs#1) < DtRank(xs#0));
                assume _module.__default.delete#canCall(n#0, ys#Z#0);
                assume _module.__default.delete($LS($LZ), n#0, xs#0)
                   == #_module.List.Cons(y#Z#0, _module.__default.delete($LS($LZ), n#0, ys#Z#0));
                assume _module.__default.delete#canCall(n#0, ys#Z#0);
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.delete($LS($LZ), n#0, xs#0), Tclass._module.List());
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



// function declaration for _module._default.drop
function _module.__default.drop($ly: LayerType, n#0: DatatypeType, xs#0: DatatypeType) : DatatypeType;

function _module.__default.drop#canCall(n#0: DatatypeType, xs#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, n#0: DatatypeType, xs#0: DatatypeType :: 
  { _module.__default.drop($LS($ly), n#0, xs#0) } 
  _module.__default.drop($LS($ly), n#0, xs#0)
     == _module.__default.drop($ly, n#0, xs#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, n#0: DatatypeType, xs#0: DatatypeType :: 
  { _module.__default.drop(AsFuelBottom($ly), n#0, xs#0) } 
  _module.__default.drop($ly, n#0, xs#0) == _module.__default.drop($LZ, n#0, xs#0));

// consequence axiom for _module.__default.drop
axiom 18 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: DatatypeType, xs#0: DatatypeType :: 
    { _module.__default.drop($ly, n#0, xs#0) } 
    _module.__default.drop#canCall(n#0, xs#0)
         || (18 != $FunctionContextHeight
           && 
          $Is(n#0, Tclass._module.Nat())
           && $Is(xs#0, Tclass._module.List()))
       ==> $Is(_module.__default.drop($ly, n#0, xs#0), Tclass._module.List()));

function _module.__default.drop#requires(LayerType, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.drop
axiom (forall $ly: LayerType, n#0: DatatypeType, xs#0: DatatypeType :: 
  { _module.__default.drop#requires($ly, n#0, xs#0) } 
  $Is(n#0, Tclass._module.Nat()) && $Is(xs#0, Tclass._module.List())
     ==> _module.__default.drop#requires($ly, n#0, xs#0) == true);

// definition axiom for _module.__default.drop (revealed)
axiom 18 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: DatatypeType, xs#0: DatatypeType :: 
    { _module.__default.drop($LS($ly), n#0, xs#0) } 
    _module.__default.drop#canCall(n#0, xs#0)
         || (18 != $FunctionContextHeight
           && 
          $Is(n#0, Tclass._module.Nat())
           && $Is(xs#0, Tclass._module.List()))
       ==> (!_module.Nat.Zero_q(n#0)
           ==> (var m#1 := _module.Nat._h0(n#0); 
            !_module.List.Nil_q(xs#0)
               ==> (var tail#1 := _module.List._h2(xs#0); 
                _module.__default.drop#canCall(m#1, tail#1))))
         && _module.__default.drop($LS($ly), n#0, xs#0)
           == (if _module.Nat.Zero_q(n#0)
             then xs#0
             else (var m#0 := _module.Nat._h0(n#0); 
              (if _module.List.Nil_q(xs#0)
                 then #_module.List.Nil()
                 else (var tail#0 := _module.List._h2(xs#0); 
                  (var x#0 := _module.List._h1(xs#0); _module.__default.drop($ly, m#0, tail#0)))))));

// definition axiom for _module.__default.drop for all literals (revealed)
axiom 18 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: DatatypeType, xs#0: DatatypeType :: 
    {:weight 3} { _module.__default.drop($LS($ly), Lit(n#0), Lit(xs#0)) } 
    _module.__default.drop#canCall(Lit(n#0), Lit(xs#0))
         || (18 != $FunctionContextHeight
           && 
          $Is(n#0, Tclass._module.Nat())
           && $Is(xs#0, Tclass._module.List()))
       ==> (!Lit(_module.Nat.Zero_q(Lit(n#0)))
           ==> (var m#3 := Lit(_module.Nat._h0(Lit(n#0))); 
            !Lit(_module.List.Nil_q(Lit(xs#0)))
               ==> (var tail#3 := Lit(_module.List._h2(Lit(xs#0))); 
                _module.__default.drop#canCall(m#3, tail#3))))
         && _module.__default.drop($LS($ly), Lit(n#0), Lit(xs#0))
           == (if _module.Nat.Zero_q(Lit(n#0))
             then xs#0
             else (var m#2 := Lit(_module.Nat._h0(Lit(n#0))); 
              (if _module.List.Nil_q(Lit(xs#0))
                 then #_module.List.Nil()
                 else (var tail#2 := Lit(_module.List._h2(Lit(xs#0))); 
                  (var x#2 := Lit(_module.List._h1(Lit(xs#0))); 
                    Lit(_module.__default.drop($LS($ly), m#2, tail#2))))))));

procedure CheckWellformed$$_module.__default.drop(n#0: DatatypeType where $Is(n#0, Tclass._module.Nat()), 
    xs#0: DatatypeType where $Is(xs#0, Tclass._module.List()));
  free requires 18 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.drop(n#0: DatatypeType, xs#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: DatatypeType;
  var m#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var _mcc#1#0: DatatypeType;
  var _mcc#2#0: DatatypeType;
  var tail#Z#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var x#Z#0: DatatypeType;
  var let#2#0#0: DatatypeType;
  var ##n#0: DatatypeType;
  var ##xs#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function drop
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(121,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.drop($LS($LZ), n#0, xs#0), Tclass._module.List());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (n#0 == #_module.Nat.Zero())
        {
            assume _module.__default.drop($LS($LZ), n#0, xs#0) == xs#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.drop($LS($LZ), n#0, xs#0), Tclass._module.List());
        }
        else if (n#0 == #_module.Nat.Suc(_mcc#0#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.Nat());
            havoc m#Z#0;
            assume $Is(m#Z#0, Tclass._module.Nat());
            assume let#0#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.Nat());
            assume m#Z#0 == let#0#0#0;
            if (xs#0 == #_module.List.Nil())
            {
                assume _module.__default.drop($LS($LZ), n#0, xs#0) == Lit(#_module.List.Nil());
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.drop($LS($LZ), n#0, xs#0), Tclass._module.List());
            }
            else if (xs#0 == #_module.List.Cons(_mcc#1#0, _mcc#2#0))
            {
                assume $Is(_mcc#1#0, Tclass._module.Nat());
                assume $Is(_mcc#2#0, Tclass._module.List());
                havoc tail#Z#0;
                assume $Is(tail#Z#0, Tclass._module.List());
                assume let#1#0#0 == _mcc#2#0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(let#1#0#0, Tclass._module.List());
                assume tail#Z#0 == let#1#0#0;
                havoc x#Z#0;
                assume $Is(x#Z#0, Tclass._module.Nat());
                assume let#2#0#0 == _mcc#1#0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(let#2#0#0, Tclass._module.Nat());
                assume x#Z#0 == let#2#0#0;
                ##n#0 := m#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#0, Tclass._module.Nat(), $Heap);
                ##xs#0 := tail#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##xs#0, Tclass._module.List(), $Heap);
                b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assert DtRank(##n#0) < DtRank(n#0)
                   || (DtRank(##n#0) == DtRank(n#0) && DtRank(##xs#0) < DtRank(xs#0));
                assume _module.__default.drop#canCall(m#Z#0, tail#Z#0);
                assume _module.__default.drop($LS($LZ), n#0, xs#0)
                   == _module.__default.drop($LS($LZ), m#Z#0, tail#Z#0);
                assume _module.__default.drop#canCall(m#Z#0, tail#Z#0);
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.drop($LS($LZ), n#0, xs#0), Tclass._module.List());
            }
            else
            {
                assume false;
            }
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
    }
}



// function declaration for _module._default.take
function _module.__default.take($ly: LayerType, n#0: DatatypeType, xs#0: DatatypeType) : DatatypeType;

function _module.__default.take#canCall(n#0: DatatypeType, xs#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, n#0: DatatypeType, xs#0: DatatypeType :: 
  { _module.__default.take($LS($ly), n#0, xs#0) } 
  _module.__default.take($LS($ly), n#0, xs#0)
     == _module.__default.take($ly, n#0, xs#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, n#0: DatatypeType, xs#0: DatatypeType :: 
  { _module.__default.take(AsFuelBottom($ly), n#0, xs#0) } 
  _module.__default.take($ly, n#0, xs#0) == _module.__default.take($LZ, n#0, xs#0));

// consequence axiom for _module.__default.take
axiom 19 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: DatatypeType, xs#0: DatatypeType :: 
    { _module.__default.take($ly, n#0, xs#0) } 
    _module.__default.take#canCall(n#0, xs#0)
         || (19 != $FunctionContextHeight
           && 
          $Is(n#0, Tclass._module.Nat())
           && $Is(xs#0, Tclass._module.List()))
       ==> $Is(_module.__default.take($ly, n#0, xs#0), Tclass._module.List()));

function _module.__default.take#requires(LayerType, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.take
axiom (forall $ly: LayerType, n#0: DatatypeType, xs#0: DatatypeType :: 
  { _module.__default.take#requires($ly, n#0, xs#0) } 
  $Is(n#0, Tclass._module.Nat()) && $Is(xs#0, Tclass._module.List())
     ==> _module.__default.take#requires($ly, n#0, xs#0) == true);

// definition axiom for _module.__default.take (revealed)
axiom 19 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: DatatypeType, xs#0: DatatypeType :: 
    { _module.__default.take($LS($ly), n#0, xs#0) } 
    _module.__default.take#canCall(n#0, xs#0)
         || (19 != $FunctionContextHeight
           && 
          $Is(n#0, Tclass._module.Nat())
           && $Is(xs#0, Tclass._module.List()))
       ==> (!_module.Nat.Zero_q(n#0)
           ==> (var m#1 := _module.Nat._h0(n#0); 
            !_module.List.Nil_q(xs#0)
               ==> (var tail#1 := _module.List._h2(xs#0); 
                _module.__default.take#canCall(m#1, tail#1))))
         && _module.__default.take($LS($ly), n#0, xs#0)
           == (if _module.Nat.Zero_q(n#0)
             then #_module.List.Nil()
             else (var m#0 := _module.Nat._h0(n#0); 
              (if _module.List.Nil_q(xs#0)
                 then #_module.List.Nil()
                 else (var tail#0 := _module.List._h2(xs#0); 
                  (var x#0 := _module.List._h1(xs#0); 
                    #_module.List.Cons(x#0, _module.__default.take($ly, m#0, tail#0))))))));

// definition axiom for _module.__default.take for all literals (revealed)
axiom 19 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: DatatypeType, xs#0: DatatypeType :: 
    {:weight 3} { _module.__default.take($LS($ly), Lit(n#0), Lit(xs#0)) } 
    _module.__default.take#canCall(Lit(n#0), Lit(xs#0))
         || (19 != $FunctionContextHeight
           && 
          $Is(n#0, Tclass._module.Nat())
           && $Is(xs#0, Tclass._module.List()))
       ==> (!Lit(_module.Nat.Zero_q(Lit(n#0)))
           ==> (var m#3 := Lit(_module.Nat._h0(Lit(n#0))); 
            !Lit(_module.List.Nil_q(Lit(xs#0)))
               ==> (var tail#3 := Lit(_module.List._h2(Lit(xs#0))); 
                _module.__default.take#canCall(m#3, tail#3))))
         && _module.__default.take($LS($ly), Lit(n#0), Lit(xs#0))
           == (if _module.Nat.Zero_q(Lit(n#0))
             then #_module.List.Nil()
             else (var m#2 := Lit(_module.Nat._h0(Lit(n#0))); 
              (if _module.List.Nil_q(Lit(xs#0))
                 then #_module.List.Nil()
                 else (var tail#2 := Lit(_module.List._h2(Lit(xs#0))); 
                  (var x#2 := Lit(_module.List._h1(Lit(xs#0))); 
                    Lit(#_module.List.Cons(x#2, Lit(_module.__default.take($LS($ly), m#2, tail#2))))))))));

procedure CheckWellformed$$_module.__default.take(n#0: DatatypeType where $Is(n#0, Tclass._module.Nat()), 
    xs#0: DatatypeType where $Is(xs#0, Tclass._module.List()));
  free requires 19 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.take(n#0: DatatypeType, xs#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: DatatypeType;
  var m#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var _mcc#1#0: DatatypeType;
  var _mcc#2#0: DatatypeType;
  var tail#Z#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var x#Z#0: DatatypeType;
  var let#2#0#0: DatatypeType;
  var ##n#0: DatatypeType;
  var ##xs#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function take
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(130,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.take($LS($LZ), n#0, xs#0), Tclass._module.List());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (n#0 == #_module.Nat.Zero())
        {
            assume _module.__default.take($LS($LZ), n#0, xs#0) == Lit(#_module.List.Nil());
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.take($LS($LZ), n#0, xs#0), Tclass._module.List());
        }
        else if (n#0 == #_module.Nat.Suc(_mcc#0#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.Nat());
            havoc m#Z#0;
            assume $Is(m#Z#0, Tclass._module.Nat());
            assume let#0#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.Nat());
            assume m#Z#0 == let#0#0#0;
            if (xs#0 == #_module.List.Nil())
            {
                assume _module.__default.take($LS($LZ), n#0, xs#0) == Lit(#_module.List.Nil());
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.take($LS($LZ), n#0, xs#0), Tclass._module.List());
            }
            else if (xs#0 == #_module.List.Cons(_mcc#1#0, _mcc#2#0))
            {
                assume $Is(_mcc#1#0, Tclass._module.Nat());
                assume $Is(_mcc#2#0, Tclass._module.List());
                havoc tail#Z#0;
                assume $Is(tail#Z#0, Tclass._module.List());
                assume let#1#0#0 == _mcc#2#0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(let#1#0#0, Tclass._module.List());
                assume tail#Z#0 == let#1#0#0;
                havoc x#Z#0;
                assume $Is(x#Z#0, Tclass._module.Nat());
                assume let#2#0#0 == _mcc#1#0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(let#2#0#0, Tclass._module.Nat());
                assume x#Z#0 == let#2#0#0;
                ##n#0 := m#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#0, Tclass._module.Nat(), $Heap);
                ##xs#0 := tail#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##xs#0, Tclass._module.List(), $Heap);
                b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assert DtRank(##n#0) < DtRank(n#0)
                   || (DtRank(##n#0) == DtRank(n#0) && DtRank(##xs#0) < DtRank(xs#0));
                assume _module.__default.take#canCall(m#Z#0, tail#Z#0);
                assume _module.__default.take($LS($LZ), n#0, xs#0)
                   == #_module.List.Cons(x#Z#0, _module.__default.take($LS($LZ), m#Z#0, tail#Z#0));
                assume _module.__default.take#canCall(m#Z#0, tail#Z#0);
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.take($LS($LZ), n#0, xs#0), Tclass._module.List());
            }
            else
            {
                assume false;
            }
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
    }
}



// function declaration for _module._default.len
function _module.__default.len($ly: LayerType, xs#0: DatatypeType) : DatatypeType;

function _module.__default.len#canCall(xs#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, xs#0: DatatypeType :: 
  { _module.__default.len($LS($ly), xs#0) } 
  _module.__default.len($LS($ly), xs#0) == _module.__default.len($ly, xs#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, xs#0: DatatypeType :: 
  { _module.__default.len(AsFuelBottom($ly), xs#0) } 
  _module.__default.len($ly, xs#0) == _module.__default.len($LZ, xs#0));

// consequence axiom for _module.__default.len
axiom 20 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, xs#0: DatatypeType :: 
    { _module.__default.len($ly, xs#0) } 
    _module.__default.len#canCall(xs#0)
         || (20 != $FunctionContextHeight && $Is(xs#0, Tclass._module.List()))
       ==> $Is(_module.__default.len($ly, xs#0), Tclass._module.Nat()));

function _module.__default.len#requires(LayerType, DatatypeType) : bool;

// #requires axiom for _module.__default.len
axiom (forall $ly: LayerType, xs#0: DatatypeType :: 
  { _module.__default.len#requires($ly, xs#0) } 
  $Is(xs#0, Tclass._module.List())
     ==> _module.__default.len#requires($ly, xs#0) == true);

// definition axiom for _module.__default.len (revealed)
axiom 20 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, xs#0: DatatypeType :: 
    { _module.__default.len($LS($ly), xs#0) } 
    _module.__default.len#canCall(xs#0)
         || (20 != $FunctionContextHeight && $Is(xs#0, Tclass._module.List()))
       ==> (!_module.List.Nil_q(xs#0)
           ==> (var ys#1 := _module.List._h2(xs#0); _module.__default.len#canCall(ys#1)))
         && _module.__default.len($LS($ly), xs#0)
           == (if _module.List.Nil_q(xs#0)
             then #_module.Nat.Zero()
             else (var ys#0 := _module.List._h2(xs#0); 
              (var y#0 := _module.List._h1(xs#0); 
                #_module.Nat.Suc(_module.__default.len($ly, ys#0))))));

// definition axiom for _module.__default.len for all literals (revealed)
axiom 20 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, xs#0: DatatypeType :: 
    {:weight 3} { _module.__default.len($LS($ly), Lit(xs#0)) } 
    _module.__default.len#canCall(Lit(xs#0))
         || (20 != $FunctionContextHeight && $Is(xs#0, Tclass._module.List()))
       ==> (!Lit(_module.List.Nil_q(Lit(xs#0)))
           ==> (var ys#3 := Lit(_module.List._h2(Lit(xs#0))); 
            _module.__default.len#canCall(ys#3)))
         && _module.__default.len($LS($ly), Lit(xs#0))
           == (if _module.List.Nil_q(Lit(xs#0))
             then #_module.Nat.Zero()
             else (var ys#2 := Lit(_module.List._h2(Lit(xs#0))); 
              (var y#2 := Lit(_module.List._h1(Lit(xs#0))); 
                Lit(#_module.Nat.Suc(Lit(_module.__default.len($LS($ly), ys#2))))))));

procedure CheckWellformed$$_module.__default.len(xs#0: DatatypeType where $Is(xs#0, Tclass._module.List()));
  free requires 20 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.len(xs#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: DatatypeType;
  var _mcc#1#0: DatatypeType;
  var ys#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var y#Z#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var ##xs#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function len
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(139,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.len($LS($LZ), xs#0), Tclass._module.Nat());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (xs#0 == #_module.List.Nil())
        {
            assume _module.__default.len($LS($LZ), xs#0) == Lit(#_module.Nat.Zero());
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.len($LS($LZ), xs#0), Tclass._module.Nat());
        }
        else if (xs#0 == #_module.List.Cons(_mcc#0#0, _mcc#1#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.Nat());
            assume $Is(_mcc#1#0, Tclass._module.List());
            havoc ys#Z#0;
            assume $Is(ys#Z#0, Tclass._module.List());
            assume let#0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.List());
            assume ys#Z#0 == let#0#0#0;
            havoc y#Z#0;
            assume $Is(y#Z#0, Tclass._module.Nat());
            assume let#1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#1#0#0, Tclass._module.Nat());
            assume y#Z#0 == let#1#0#0;
            ##xs#0 := ys#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##xs#0, Tclass._module.List(), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(##xs#0) < DtRank(xs#0);
            assume _module.__default.len#canCall(ys#Z#0);
            assume _module.__default.len($LS($LZ), xs#0)
               == #_module.Nat.Suc(_module.__default.len($LS($LZ), ys#Z#0));
            assume _module.__default.len#canCall(ys#Z#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.len($LS($LZ), xs#0), Tclass._module.Nat());
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
    }
}



// function declaration for _module._default.count
function _module.__default.count($ly: LayerType, x#0: DatatypeType, xs#0: DatatypeType) : DatatypeType;

function _module.__default.count#canCall(x#0: DatatypeType, xs#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, x#0: DatatypeType, xs#0: DatatypeType :: 
  { _module.__default.count($LS($ly), x#0, xs#0) } 
  _module.__default.count($LS($ly), x#0, xs#0)
     == _module.__default.count($ly, x#0, xs#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, x#0: DatatypeType, xs#0: DatatypeType :: 
  { _module.__default.count(AsFuelBottom($ly), x#0, xs#0) } 
  _module.__default.count($ly, x#0, xs#0)
     == _module.__default.count($LZ, x#0, xs#0));

// consequence axiom for _module.__default.count
axiom 21 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, x#0: DatatypeType, xs#0: DatatypeType :: 
    { _module.__default.count($ly, x#0, xs#0) } 
    _module.__default.count#canCall(x#0, xs#0)
         || (21 != $FunctionContextHeight
           && 
          $Is(x#0, Tclass._module.Nat())
           && $Is(xs#0, Tclass._module.List()))
       ==> $Is(_module.__default.count($ly, x#0, xs#0), Tclass._module.Nat()));

function _module.__default.count#requires(LayerType, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.count
axiom (forall $ly: LayerType, x#0: DatatypeType, xs#0: DatatypeType :: 
  { _module.__default.count#requires($ly, x#0, xs#0) } 
  $Is(x#0, Tclass._module.Nat()) && $Is(xs#0, Tclass._module.List())
     ==> _module.__default.count#requires($ly, x#0, xs#0) == true);

// definition axiom for _module.__default.count (revealed)
axiom 21 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, x#0: DatatypeType, xs#0: DatatypeType :: 
    { _module.__default.count($LS($ly), x#0, xs#0) } 
    _module.__default.count#canCall(x#0, xs#0)
         || (21 != $FunctionContextHeight
           && 
          $Is(x#0, Tclass._module.Nat())
           && $Is(xs#0, Tclass._module.List()))
       ==> (!_module.List.Nil_q(xs#0)
           ==> (var ys#1 := _module.List._h2(xs#0); 
            (var y#1 := _module.List._h1(xs#0); 
              $IsA#_module.Nat(x#0)
                 && $IsA#_module.Nat(y#1)
                 && (_module.Nat#Equal(x#0, y#1) ==> _module.__default.count#canCall(x#0, ys#1))
                 && (!_module.Nat#Equal(x#0, y#1) ==> _module.__default.count#canCall(x#0, ys#1)))))
         && _module.__default.count($LS($ly), x#0, xs#0)
           == (if _module.List.Nil_q(xs#0)
             then #_module.Nat.Zero()
             else (var ys#0 := _module.List._h2(xs#0); 
              (var y#0 := _module.List._h1(xs#0); 
                (if _module.Nat#Equal(x#0, y#0)
                   then #_module.Nat.Suc(_module.__default.count($ly, x#0, ys#0))
                   else _module.__default.count($ly, x#0, ys#0))))));

// definition axiom for _module.__default.count for all literals (revealed)
axiom 21 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, x#0: DatatypeType, xs#0: DatatypeType :: 
    {:weight 3} { _module.__default.count($LS($ly), Lit(x#0), Lit(xs#0)) } 
    _module.__default.count#canCall(Lit(x#0), Lit(xs#0))
         || (21 != $FunctionContextHeight
           && 
          $Is(x#0, Tclass._module.Nat())
           && $Is(xs#0, Tclass._module.List()))
       ==> (!Lit(_module.List.Nil_q(Lit(xs#0)))
           ==> (var ys#3 := Lit(_module.List._h2(Lit(xs#0))); 
            (var y#3 := Lit(_module.List._h1(Lit(xs#0))); 
              $IsA#_module.Nat(Lit(x#0))
                 && $IsA#_module.Nat(y#3)
                 && (_module.Nat#Equal(x#0, y#3)
                   ==> _module.__default.count#canCall(Lit(x#0), ys#3))
                 && (!_module.Nat#Equal(x#0, y#3)
                   ==> _module.__default.count#canCall(Lit(x#0), ys#3)))))
         && _module.__default.count($LS($ly), Lit(x#0), Lit(xs#0))
           == (if _module.List.Nil_q(Lit(xs#0))
             then #_module.Nat.Zero()
             else (var ys#2 := Lit(_module.List._h2(Lit(xs#0))); 
              (var y#2 := Lit(_module.List._h1(Lit(xs#0))); 
                (if _module.Nat#Equal(x#0, y#2)
                   then #_module.Nat.Suc(Lit(_module.__default.count($LS($ly), Lit(x#0), ys#2)))
                   else _module.__default.count($LS($ly), Lit(x#0), ys#2))))));

procedure CheckWellformed$$_module.__default.count(x#0: DatatypeType where $Is(x#0, Tclass._module.Nat()), 
    xs#0: DatatypeType where $Is(xs#0, Tclass._module.List()));
  free requires 21 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.count(x#0: DatatypeType, xs#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: DatatypeType;
  var _mcc#1#0: DatatypeType;
  var ys#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var y#Z#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var ##x#0: DatatypeType;
  var ##xs#0: DatatypeType;
  var ##x#1: DatatypeType;
  var ##xs#1: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function count
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(146,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.count($LS($LZ), x#0, xs#0), Tclass._module.Nat());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (xs#0 == #_module.List.Nil())
        {
            assume _module.__default.count($LS($LZ), x#0, xs#0) == Lit(#_module.Nat.Zero());
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.count($LS($LZ), x#0, xs#0), Tclass._module.Nat());
        }
        else if (xs#0 == #_module.List.Cons(_mcc#0#0, _mcc#1#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.Nat());
            assume $Is(_mcc#1#0, Tclass._module.List());
            havoc ys#Z#0;
            assume $Is(ys#Z#0, Tclass._module.List());
            assume let#0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.List());
            assume ys#Z#0 == let#0#0#0;
            havoc y#Z#0;
            assume $Is(y#Z#0, Tclass._module.Nat());
            assume let#1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#1#0#0, Tclass._module.Nat());
            assume y#Z#0 == let#1#0#0;
            if (_module.Nat#Equal(x#0, y#Z#0))
            {
                ##x#0 := x#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##x#0, Tclass._module.Nat(), $Heap);
                ##xs#0 := ys#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##xs#0, Tclass._module.List(), $Heap);
                b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assert DtRank(##x#0) < DtRank(x#0)
                   || (DtRank(##x#0) == DtRank(x#0) && DtRank(##xs#0) < DtRank(xs#0));
                assume _module.__default.count#canCall(x#0, ys#Z#0);
                assume _module.__default.count($LS($LZ), x#0, xs#0)
                   == #_module.Nat.Suc(_module.__default.count($LS($LZ), x#0, ys#Z#0));
                assume _module.__default.count#canCall(x#0, ys#Z#0);
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.count($LS($LZ), x#0, xs#0), Tclass._module.Nat());
            }
            else
            {
                ##x#1 := x#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##x#1, Tclass._module.Nat(), $Heap);
                ##xs#1 := ys#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##xs#1, Tclass._module.List(), $Heap);
                b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assert DtRank(##x#1) < DtRank(x#0)
                   || (DtRank(##x#1) == DtRank(x#0) && DtRank(##xs#1) < DtRank(xs#0));
                assume _module.__default.count#canCall(x#0, ys#Z#0);
                assume _module.__default.count($LS($LZ), x#0, xs#0)
                   == _module.__default.count($LS($LZ), x#0, ys#Z#0);
                assume _module.__default.count#canCall(x#0, ys#Z#0);
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.count($LS($LZ), x#0, xs#0), Tclass._module.Nat());
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



// function declaration for _module._default.last
function _module.__default.last($ly: LayerType, xs#0: DatatypeType) : DatatypeType;

function _module.__default.last#canCall(xs#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, xs#0: DatatypeType :: 
  { _module.__default.last($LS($ly), xs#0) } 
  _module.__default.last($LS($ly), xs#0) == _module.__default.last($ly, xs#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, xs#0: DatatypeType :: 
  { _module.__default.last(AsFuelBottom($ly), xs#0) } 
  _module.__default.last($ly, xs#0) == _module.__default.last($LZ, xs#0));

// consequence axiom for _module.__default.last
axiom 22 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, xs#0: DatatypeType :: 
    { _module.__default.last($ly, xs#0) } 
    _module.__default.last#canCall(xs#0)
         || (22 != $FunctionContextHeight && $Is(xs#0, Tclass._module.List()))
       ==> $Is(_module.__default.last($ly, xs#0), Tclass._module.Nat()));

function _module.__default.last#requires(LayerType, DatatypeType) : bool;

// #requires axiom for _module.__default.last
axiom (forall $ly: LayerType, xs#0: DatatypeType :: 
  { _module.__default.last#requires($ly, xs#0) } 
  $Is(xs#0, Tclass._module.List())
     ==> _module.__default.last#requires($ly, xs#0) == true);

// definition axiom for _module.__default.last (revealed)
axiom 22 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, xs#0: DatatypeType :: 
    { _module.__default.last($LS($ly), xs#0) } 
    _module.__default.last#canCall(xs#0)
         || (22 != $FunctionContextHeight && $Is(xs#0, Tclass._module.List()))
       ==> (!_module.List.Nil_q(xs#0)
           ==> (var ys#1 := _module.List._h2(xs#0); 
            !_module.List.Nil_q(ys#1) ==> _module.__default.last#canCall(ys#1)))
         && _module.__default.last($LS($ly), xs#0)
           == (if _module.List.Nil_q(xs#0)
             then #_module.Nat.Zero()
             else (var ys#0 := _module.List._h2(xs#0); 
              (var y#0 := _module.List._h1(xs#0); 
                (if _module.List.Nil_q(ys#0)
                   then y#0
                   else (var zs#0 := _module.List._h2(ys#0); 
                    (var z#0 := _module.List._h1(ys#0); _module.__default.last($ly, ys#0))))))));

// definition axiom for _module.__default.last for all literals (revealed)
axiom 22 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, xs#0: DatatypeType :: 
    {:weight 3} { _module.__default.last($LS($ly), Lit(xs#0)) } 
    _module.__default.last#canCall(Lit(xs#0))
         || (22 != $FunctionContextHeight && $Is(xs#0, Tclass._module.List()))
       ==> (!Lit(_module.List.Nil_q(Lit(xs#0)))
           ==> (var ys#3 := Lit(_module.List._h2(Lit(xs#0))); 
            !_module.List.Nil_q(ys#3) ==> _module.__default.last#canCall(ys#3)))
         && _module.__default.last($LS($ly), Lit(xs#0))
           == (if _module.List.Nil_q(Lit(xs#0))
             then #_module.Nat.Zero()
             else (var ys#2 := Lit(_module.List._h2(Lit(xs#0))); 
              (var y#2 := Lit(_module.List._h1(Lit(xs#0))); 
                (if _module.List.Nil_q(ys#2)
                   then y#2
                   else (var zs#2 := Lit(_module.List._h2(ys#2)); 
                    (var z#2 := Lit(_module.List._h1(ys#2)); 
                      Lit(_module.__default.last($LS($ly), ys#2)))))))));

procedure CheckWellformed$$_module.__default.last(xs#0: DatatypeType where $Is(xs#0, Tclass._module.List()));
  free requires 22 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.last(xs#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: DatatypeType;
  var _mcc#1#0: DatatypeType;
  var ys#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var y#Z#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var _mcc#2#0: DatatypeType;
  var _mcc#3#0: DatatypeType;
  var zs#Z#0: DatatypeType;
  var let#2#0#0: DatatypeType;
  var z#Z#0: DatatypeType;
  var let#3#0#0: DatatypeType;
  var ##xs#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function last
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(154,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.last($LS($LZ), xs#0), Tclass._module.Nat());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (xs#0 == #_module.List.Nil())
        {
            assume _module.__default.last($LS($LZ), xs#0) == Lit(#_module.Nat.Zero());
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.last($LS($LZ), xs#0), Tclass._module.Nat());
        }
        else if (xs#0 == #_module.List.Cons(_mcc#0#0, _mcc#1#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.Nat());
            assume $Is(_mcc#1#0, Tclass._module.List());
            havoc ys#Z#0;
            assume $Is(ys#Z#0, Tclass._module.List());
            assume let#0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.List());
            assume ys#Z#0 == let#0#0#0;
            havoc y#Z#0;
            assume $Is(y#Z#0, Tclass._module.Nat());
            assume let#1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#1#0#0, Tclass._module.Nat());
            assume y#Z#0 == let#1#0#0;
            if (ys#Z#0 == #_module.List.Nil())
            {
                assume _module.__default.last($LS($LZ), xs#0) == y#Z#0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.last($LS($LZ), xs#0), Tclass._module.Nat());
            }
            else if (ys#Z#0 == #_module.List.Cons(_mcc#2#0, _mcc#3#0))
            {
                assume $Is(_mcc#2#0, Tclass._module.Nat());
                assume $Is(_mcc#3#0, Tclass._module.List());
                havoc zs#Z#0;
                assume $Is(zs#Z#0, Tclass._module.List());
                assume let#2#0#0 == _mcc#3#0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(let#2#0#0, Tclass._module.List());
                assume zs#Z#0 == let#2#0#0;
                havoc z#Z#0;
                assume $Is(z#Z#0, Tclass._module.Nat());
                assume let#3#0#0 == _mcc#2#0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(let#3#0#0, Tclass._module.Nat());
                assume z#Z#0 == let#3#0#0;
                ##xs#0 := ys#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##xs#0, Tclass._module.List(), $Heap);
                b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assert DtRank(##xs#0) < DtRank(xs#0);
                assume _module.__default.last#canCall(ys#Z#0);
                assume _module.__default.last($LS($LZ), xs#0)
                   == _module.__default.last($LS($LZ), ys#Z#0);
                assume _module.__default.last#canCall(ys#Z#0);
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.last($LS($LZ), xs#0), Tclass._module.Nat());
            }
            else
            {
                assume false;
            }
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
    }
}



// function declaration for _module._default.apply
function _module.__default.apply($ly: LayerType, f#0: HandleType, xs#0: DatatypeType) : DatatypeType;

function _module.__default.apply#canCall(f#0: HandleType, xs#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, f#0: HandleType, xs#0: DatatypeType :: 
  { _module.__default.apply($LS($ly), f#0, xs#0) } 
  _module.__default.apply($LS($ly), f#0, xs#0)
     == _module.__default.apply($ly, f#0, xs#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, f#0: HandleType, xs#0: DatatypeType :: 
  { _module.__default.apply(AsFuelBottom($ly), f#0, xs#0) } 
  _module.__default.apply($ly, f#0, xs#0)
     == _module.__default.apply($LZ, f#0, xs#0));

// consequence axiom for _module.__default.apply
axiom 24 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, f#0: HandleType, xs#0: DatatypeType :: 
    { _module.__default.apply($ly, f#0, xs#0) } 
    _module.__default.apply#canCall(f#0, xs#0)
         || (24 != $FunctionContextHeight
           && 
          $Is(f#0, Tclass._System.___hTotalFunc1(Tclass._module.Nat(), Tclass._module.Nat()))
           && $Is(xs#0, Tclass._module.List()))
       ==> $Is(_module.__default.apply($ly, f#0, xs#0), Tclass._module.List()));

function _module.__default.apply#requires(LayerType, HandleType, DatatypeType) : bool;

// #requires axiom for _module.__default.apply
axiom (forall $ly: LayerType, $Heap: Heap, f#0: HandleType, xs#0: DatatypeType :: 
  { _module.__default.apply#requires($ly, f#0, xs#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && $Is(f#0, Tclass._System.___hTotalFunc1(Tclass._module.Nat(), Tclass._module.Nat()))
       && $Is(xs#0, Tclass._module.List())
     ==> _module.__default.apply#requires($ly, f#0, xs#0) == true);

// definition axiom for _module.__default.apply (revealed)
axiom 24 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, f#0: HandleType, xs#0: DatatypeType :: 
    { _module.__default.apply($LS($ly), f#0, xs#0), $IsGoodHeap($Heap) } 
    _module.__default.apply#canCall(f#0, xs#0)
         || (24 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(f#0, Tclass._System.___hTotalFunc1(Tclass._module.Nat(), Tclass._module.Nat()))
           && $Is(xs#0, Tclass._module.List()))
       ==> (!_module.List.Nil_q(xs#0)
           ==> (var ys#1 := _module.List._h2(xs#0); _module.__default.apply#canCall(f#0, ys#1)))
         && _module.__default.apply($LS($ly), f#0, xs#0)
           == (if _module.List.Nil_q(xs#0)
             then #_module.List.Nil()
             else (var ys#0 := _module.List._h2(xs#0); 
              (var y#0 := _module.List._h1(xs#0); 
                #_module.List.Cons($Unbox(Apply1(Tclass._module.Nat(), Tclass._module.Nat(), $Heap, f#0, $Box(y#0))): DatatypeType, 
                  _module.__default.apply($ly, f#0, ys#0))))));

// definition axiom for _module.__default.apply for decreasing-related literals (revealed)
axiom 24 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, f#0: HandleType, xs#0: DatatypeType :: 
    {:weight 3} { _module.__default.apply($LS($ly), f#0, Lit(xs#0)), $IsGoodHeap($Heap) } 
    _module.__default.apply#canCall(f#0, Lit(xs#0))
         || (24 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(f#0, Tclass._System.___hTotalFunc1(Tclass._module.Nat(), Tclass._module.Nat()))
           && $Is(xs#0, Tclass._module.List()))
       ==> (!Lit(_module.List.Nil_q(Lit(xs#0)))
           ==> (var ys#3 := Lit(_module.List._h2(Lit(xs#0))); 
            _module.__default.apply#canCall(f#0, ys#3)))
         && _module.__default.apply($LS($ly), f#0, Lit(xs#0))
           == (if _module.List.Nil_q(Lit(xs#0))
             then #_module.List.Nil()
             else (var ys#2 := Lit(_module.List._h2(Lit(xs#0))); 
              (var y#2 := Lit(_module.List._h1(Lit(xs#0))); 
                #_module.List.Cons($Unbox(Apply1(Tclass._module.Nat(), Tclass._module.Nat(), $Heap, f#0, $Box(y#2))): DatatypeType, 
                  _module.__default.apply($LS($ly), f#0, ys#2))))));

// definition axiom for _module.__default.apply for all literals (revealed)
axiom 24 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, f#0: HandleType, xs#0: DatatypeType :: 
    {:weight 3} { _module.__default.apply($LS($ly), Lit(f#0), Lit(xs#0)), $IsGoodHeap($Heap) } 
    _module.__default.apply#canCall(Lit(f#0), Lit(xs#0))
         || (24 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(f#0, Tclass._System.___hTotalFunc1(Tclass._module.Nat(), Tclass._module.Nat()))
           && $Is(xs#0, Tclass._module.List()))
       ==> (!Lit(_module.List.Nil_q(Lit(xs#0)))
           ==> (var ys#5 := Lit(_module.List._h2(Lit(xs#0))); 
            _module.__default.apply#canCall(Lit(f#0), ys#5)))
         && _module.__default.apply($LS($ly), Lit(f#0), Lit(xs#0))
           == (if _module.List.Nil_q(Lit(xs#0))
             then #_module.List.Nil()
             else (var ys#4 := Lit(_module.List._h2(Lit(xs#0))); 
              (var y#4 := Lit(_module.List._h1(Lit(xs#0))); 
                #_module.List.Cons($Unbox(Apply1(Tclass._module.Nat(), Tclass._module.Nat(), $Heap, Lit(f#0), $Box(y#4))): DatatypeType, 
                  Lit(_module.__default.apply($LS($ly), Lit(f#0), ys#4)))))));

procedure CheckWellformed$$_module.__default.apply(f#0: HandleType
       where $Is(f#0, Tclass._System.___hTotalFunc1(Tclass._module.Nat(), Tclass._module.Nat())), 
    xs#0: DatatypeType where $Is(xs#0, Tclass._module.List()));
  free requires 24 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.apply(f#0: HandleType, xs#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: DatatypeType;
  var _mcc#1#0: DatatypeType;
  var ys#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var y#Z#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var ##f#0: HandleType;
  var ##xs#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function apply
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(163,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.apply($LS($LZ), f#0, xs#0), Tclass._module.List());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (xs#0 == #_module.List.Nil())
        {
            assume _module.__default.apply($LS($LZ), f#0, xs#0) == Lit(#_module.List.Nil());
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.apply($LS($LZ), f#0, xs#0), Tclass._module.List());
        }
        else if (xs#0 == #_module.List.Cons(_mcc#0#0, _mcc#1#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.Nat());
            assume $Is(_mcc#1#0, Tclass._module.List());
            havoc ys#Z#0;
            assume $Is(ys#Z#0, Tclass._module.List());
            assume let#0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.List());
            assume ys#Z#0 == let#0#0#0;
            havoc y#Z#0;
            assume $Is(y#Z#0, Tclass._module.Nat());
            assume let#1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#1#0#0, Tclass._module.Nat());
            assume y#Z#0 == let#1#0#0;
            ##f#0 := f#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##f#0, 
              Tclass._System.___hTotalFunc1(Tclass._module.Nat(), Tclass._module.Nat()), 
              $Heap);
            ##xs#0 := ys#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##xs#0, Tclass._module.List(), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(##xs#0) < DtRank(xs#0);
            assume _module.__default.apply#canCall(f#0, ys#Z#0);
            assume _module.__default.apply($LS($LZ), f#0, xs#0)
               == #_module.List.Cons($Unbox(Apply1(Tclass._module.Nat(), Tclass._module.Nat(), $Heap, f#0, $Box(y#Z#0))): DatatypeType, 
                _module.__default.apply($LS($LZ), f#0, ys#Z#0));
            assume _module.__default.apply#canCall(f#0, ys#Z#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.apply($LS($LZ), f#0, xs#0), Tclass._module.List());
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
    }
}



// function declaration for _module._default.takeWhileAlways
function _module.__default.takeWhileAlways($ly: LayerType, p#0: HandleType, xs#0: DatatypeType) : DatatypeType;

function _module.__default.takeWhileAlways#canCall(p#0: HandleType, xs#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, p#0: HandleType, xs#0: DatatypeType :: 
  { _module.__default.takeWhileAlways($LS($ly), p#0, xs#0) } 
  _module.__default.takeWhileAlways($LS($ly), p#0, xs#0)
     == _module.__default.takeWhileAlways($ly, p#0, xs#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, p#0: HandleType, xs#0: DatatypeType :: 
  { _module.__default.takeWhileAlways(AsFuelBottom($ly), p#0, xs#0) } 
  _module.__default.takeWhileAlways($ly, p#0, xs#0)
     == _module.__default.takeWhileAlways($LZ, p#0, xs#0));

// consequence axiom for _module.__default.takeWhileAlways
axiom 25 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, p#0: HandleType, xs#0: DatatypeType :: 
    { _module.__default.takeWhileAlways($ly, p#0, xs#0) } 
    _module.__default.takeWhileAlways#canCall(p#0, xs#0)
         || (25 != $FunctionContextHeight
           && 
          $Is(p#0, Tclass._System.___hTotalFunc1(Tclass._module.Nat(), Tclass._module.Nat()))
           && $Is(xs#0, Tclass._module.List()))
       ==> $Is(_module.__default.takeWhileAlways($ly, p#0, xs#0), Tclass._module.List()));

function _module.__default.takeWhileAlways#requires(LayerType, HandleType, DatatypeType) : bool;

// #requires axiom for _module.__default.takeWhileAlways
axiom (forall $ly: LayerType, $Heap: Heap, p#0: HandleType, xs#0: DatatypeType :: 
  { _module.__default.takeWhileAlways#requires($ly, p#0, xs#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && $Is(p#0, Tclass._System.___hTotalFunc1(Tclass._module.Nat(), Tclass._module.Nat()))
       && $Is(xs#0, Tclass._module.List())
     ==> _module.__default.takeWhileAlways#requires($ly, p#0, xs#0) == true);

// definition axiom for _module.__default.takeWhileAlways (revealed)
axiom 25 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, p#0: HandleType, xs#0: DatatypeType :: 
    { _module.__default.takeWhileAlways($LS($ly), p#0, xs#0), $IsGoodHeap($Heap) } 
    _module.__default.takeWhileAlways#canCall(p#0, xs#0)
         || (25 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(p#0, Tclass._System.___hTotalFunc1(Tclass._module.Nat(), Tclass._module.Nat()))
           && $Is(xs#0, Tclass._module.List()))
       ==> (!_module.List.Nil_q(xs#0)
           ==> (var ys#1 := _module.List._h2(xs#0); 
            (var y#1 := _module.List._h1(xs#0); 
              $IsA#_module.Nat($Unbox(Apply1(Tclass._module.Nat(), Tclass._module.Nat(), $Heap, p#0, $Box(y#1))): DatatypeType)
                 && (!_module.Nat#Equal($Unbox(Apply1(Tclass._module.Nat(), Tclass._module.Nat(), $Heap, p#0, $Box(y#1))): DatatypeType, 
                    #_module.Nat.Zero())
                   ==> _module.__default.takeWhileAlways#canCall(p#0, ys#1)))))
         && _module.__default.takeWhileAlways($LS($ly), p#0, xs#0)
           == (if _module.List.Nil_q(xs#0)
             then #_module.List.Nil()
             else (var ys#0 := _module.List._h2(xs#0); 
              (var y#0 := _module.List._h1(xs#0); 
                (if !_module.Nat#Equal($Unbox(Apply1(Tclass._module.Nat(), Tclass._module.Nat(), $Heap, p#0, $Box(y#0))): DatatypeType, 
                    #_module.Nat.Zero())
                   then #_module.List.Cons(y#0, _module.__default.takeWhileAlways($ly, p#0, ys#0))
                   else #_module.List.Nil())))));

// definition axiom for _module.__default.takeWhileAlways for decreasing-related literals (revealed)
axiom 25 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, p#0: HandleType, xs#0: DatatypeType :: 
    {:weight 3} { _module.__default.takeWhileAlways($LS($ly), p#0, Lit(xs#0)), $IsGoodHeap($Heap) } 
    _module.__default.takeWhileAlways#canCall(p#0, Lit(xs#0))
         || (25 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(p#0, Tclass._System.___hTotalFunc1(Tclass._module.Nat(), Tclass._module.Nat()))
           && $Is(xs#0, Tclass._module.List()))
       ==> (!Lit(_module.List.Nil_q(Lit(xs#0)))
           ==> (var ys#3 := Lit(_module.List._h2(Lit(xs#0))); 
            (var y#3 := Lit(_module.List._h1(Lit(xs#0))); 
              $IsA#_module.Nat($Unbox(Apply1(Tclass._module.Nat(), Tclass._module.Nat(), $Heap, p#0, $Box(y#3))): DatatypeType)
                 && (!_module.Nat#Equal($Unbox(Apply1(Tclass._module.Nat(), Tclass._module.Nat(), $Heap, p#0, $Box(y#3))): DatatypeType, 
                    #_module.Nat.Zero())
                   ==> _module.__default.takeWhileAlways#canCall(p#0, ys#3)))))
         && _module.__default.takeWhileAlways($LS($ly), p#0, Lit(xs#0))
           == (if _module.List.Nil_q(Lit(xs#0))
             then #_module.List.Nil()
             else (var ys#2 := Lit(_module.List._h2(Lit(xs#0))); 
              (var y#2 := Lit(_module.List._h1(Lit(xs#0))); 
                (if !_module.Nat#Equal($Unbox(Apply1(Tclass._module.Nat(), Tclass._module.Nat(), $Heap, p#0, $Box(y#2))): DatatypeType, 
                    #_module.Nat.Zero())
                   then #_module.List.Cons(y#2, _module.__default.takeWhileAlways($LS($ly), p#0, ys#2))
                   else #_module.List.Nil())))));

// definition axiom for _module.__default.takeWhileAlways for all literals (revealed)
axiom 25 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, p#0: HandleType, xs#0: DatatypeType :: 
    {:weight 3} { _module.__default.takeWhileAlways($LS($ly), Lit(p#0), Lit(xs#0)), $IsGoodHeap($Heap) } 
    _module.__default.takeWhileAlways#canCall(Lit(p#0), Lit(xs#0))
         || (25 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(p#0, Tclass._System.___hTotalFunc1(Tclass._module.Nat(), Tclass._module.Nat()))
           && $Is(xs#0, Tclass._module.List()))
       ==> (!Lit(_module.List.Nil_q(Lit(xs#0)))
           ==> (var ys#5 := Lit(_module.List._h2(Lit(xs#0))); 
            (var y#5 := Lit(_module.List._h1(Lit(xs#0))); 
              $IsA#_module.Nat($Unbox(Apply1(Tclass._module.Nat(), Tclass._module.Nat(), $Heap, Lit(p#0), $Box(y#5))): DatatypeType)
                 && (!_module.Nat#Equal($Unbox(Apply1(Tclass._module.Nat(), Tclass._module.Nat(), $Heap, Lit(p#0), $Box(y#5))): DatatypeType, 
                    #_module.Nat.Zero())
                   ==> _module.__default.takeWhileAlways#canCall(Lit(p#0), ys#5)))))
         && _module.__default.takeWhileAlways($LS($ly), Lit(p#0), Lit(xs#0))
           == (if _module.List.Nil_q(Lit(xs#0))
             then #_module.List.Nil()
             else (var ys#4 := Lit(_module.List._h2(Lit(xs#0))); 
              (var y#4 := Lit(_module.List._h1(Lit(xs#0))); 
                (if !_module.Nat#Equal($Unbox(Apply1(Tclass._module.Nat(), Tclass._module.Nat(), $Heap, Lit(p#0), $Box(y#4))): DatatypeType, 
                    #_module.Nat.Zero())
                   then #_module.List.Cons(y#4, Lit(_module.__default.takeWhileAlways($LS($ly), Lit(p#0), ys#4)))
                   else #_module.List.Nil())))));

procedure CheckWellformed$$_module.__default.takeWhileAlways(p#0: HandleType
       where $Is(p#0, Tclass._System.___hTotalFunc1(Tclass._module.Nat(), Tclass._module.Nat())), 
    xs#0: DatatypeType where $Is(xs#0, Tclass._module.List()));
  free requires 25 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.takeWhileAlways(p#0: HandleType, xs#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: DatatypeType;
  var _mcc#1#0: DatatypeType;
  var ys#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var y#Z#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var ##p#0: HandleType;
  var ##xs#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function takeWhileAlways
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(173,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.takeWhileAlways($LS($LZ), p#0, xs#0), Tclass._module.List());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (xs#0 == #_module.List.Nil())
        {
            assume _module.__default.takeWhileAlways($LS($LZ), p#0, xs#0)
               == Lit(#_module.List.Nil());
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.takeWhileAlways($LS($LZ), p#0, xs#0), Tclass._module.List());
        }
        else if (xs#0 == #_module.List.Cons(_mcc#0#0, _mcc#1#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.Nat());
            assume $Is(_mcc#1#0, Tclass._module.List());
            havoc ys#Z#0;
            assume $Is(ys#Z#0, Tclass._module.List());
            assume let#0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.List());
            assume ys#Z#0 == let#0#0#0;
            havoc y#Z#0;
            assume $Is(y#Z#0, Tclass._module.Nat());
            assume let#1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#1#0#0, Tclass._module.Nat());
            assume y#Z#0 == let#1#0#0;
            if (!_module.Nat#Equal($Unbox(Apply1(Tclass._module.Nat(), Tclass._module.Nat(), $Heap, p#0, $Box(y#Z#0))): DatatypeType, 
              #_module.Nat.Zero()))
            {
                ##p#0 := p#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##p#0, 
                  Tclass._System.___hTotalFunc1(Tclass._module.Nat(), Tclass._module.Nat()), 
                  $Heap);
                ##xs#0 := ys#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##xs#0, Tclass._module.List(), $Heap);
                b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assert DtRank(##xs#0) < DtRank(xs#0);
                assume _module.__default.takeWhileAlways#canCall(p#0, ys#Z#0);
                assume _module.__default.takeWhileAlways($LS($LZ), p#0, xs#0)
                   == #_module.List.Cons(y#Z#0, _module.__default.takeWhileAlways($LS($LZ), p#0, ys#Z#0));
                assume _module.__default.takeWhileAlways#canCall(p#0, ys#Z#0);
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.takeWhileAlways($LS($LZ), p#0, xs#0), Tclass._module.List());
            }
            else
            {
                assume _module.__default.takeWhileAlways($LS($LZ), p#0, xs#0)
                   == Lit(#_module.List.Nil());
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.takeWhileAlways($LS($LZ), p#0, xs#0), Tclass._module.List());
            }
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
    }
}



// function declaration for _module._default.dropWhileAlways
function _module.__default.dropWhileAlways($ly: LayerType, p#0: HandleType, xs#0: DatatypeType) : DatatypeType;

function _module.__default.dropWhileAlways#canCall(p#0: HandleType, xs#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, p#0: HandleType, xs#0: DatatypeType :: 
  { _module.__default.dropWhileAlways($LS($ly), p#0, xs#0) } 
  _module.__default.dropWhileAlways($LS($ly), p#0, xs#0)
     == _module.__default.dropWhileAlways($ly, p#0, xs#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, p#0: HandleType, xs#0: DatatypeType :: 
  { _module.__default.dropWhileAlways(AsFuelBottom($ly), p#0, xs#0) } 
  _module.__default.dropWhileAlways($ly, p#0, xs#0)
     == _module.__default.dropWhileAlways($LZ, p#0, xs#0));

// consequence axiom for _module.__default.dropWhileAlways
axiom 26 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, p#0: HandleType, xs#0: DatatypeType :: 
    { _module.__default.dropWhileAlways($ly, p#0, xs#0) } 
    _module.__default.dropWhileAlways#canCall(p#0, xs#0)
         || (26 != $FunctionContextHeight
           && 
          $Is(p#0, Tclass._System.___hTotalFunc1(Tclass._module.Nat(), Tclass._module.Nat()))
           && $Is(xs#0, Tclass._module.List()))
       ==> $Is(_module.__default.dropWhileAlways($ly, p#0, xs#0), Tclass._module.List()));

function _module.__default.dropWhileAlways#requires(LayerType, HandleType, DatatypeType) : bool;

// #requires axiom for _module.__default.dropWhileAlways
axiom (forall $ly: LayerType, $Heap: Heap, p#0: HandleType, xs#0: DatatypeType :: 
  { _module.__default.dropWhileAlways#requires($ly, p#0, xs#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && $Is(p#0, Tclass._System.___hTotalFunc1(Tclass._module.Nat(), Tclass._module.Nat()))
       && $Is(xs#0, Tclass._module.List())
     ==> _module.__default.dropWhileAlways#requires($ly, p#0, xs#0) == true);

// definition axiom for _module.__default.dropWhileAlways (revealed)
axiom 26 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, p#0: HandleType, xs#0: DatatypeType :: 
    { _module.__default.dropWhileAlways($LS($ly), p#0, xs#0), $IsGoodHeap($Heap) } 
    _module.__default.dropWhileAlways#canCall(p#0, xs#0)
         || (26 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(p#0, Tclass._System.___hTotalFunc1(Tclass._module.Nat(), Tclass._module.Nat()))
           && $Is(xs#0, Tclass._module.List()))
       ==> (!_module.List.Nil_q(xs#0)
           ==> (var ys#1 := _module.List._h2(xs#0); 
            (var y#1 := _module.List._h1(xs#0); 
              $IsA#_module.Nat($Unbox(Apply1(Tclass._module.Nat(), Tclass._module.Nat(), $Heap, p#0, $Box(y#1))): DatatypeType)
                 && (!_module.Nat#Equal($Unbox(Apply1(Tclass._module.Nat(), Tclass._module.Nat(), $Heap, p#0, $Box(y#1))): DatatypeType, 
                    #_module.Nat.Zero())
                   ==> _module.__default.dropWhileAlways#canCall(p#0, ys#1)))))
         && _module.__default.dropWhileAlways($LS($ly), p#0, xs#0)
           == (if _module.List.Nil_q(xs#0)
             then #_module.List.Nil()
             else (var ys#0 := _module.List._h2(xs#0); 
              (var y#0 := _module.List._h1(xs#0); 
                (if !_module.Nat#Equal($Unbox(Apply1(Tclass._module.Nat(), Tclass._module.Nat(), $Heap, p#0, $Box(y#0))): DatatypeType, 
                    #_module.Nat.Zero())
                   then _module.__default.dropWhileAlways($ly, p#0, ys#0)
                   else #_module.List.Cons(y#0, ys#0))))));

// definition axiom for _module.__default.dropWhileAlways for decreasing-related literals (revealed)
axiom 26 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, p#0: HandleType, xs#0: DatatypeType :: 
    {:weight 3} { _module.__default.dropWhileAlways($LS($ly), p#0, Lit(xs#0)), $IsGoodHeap($Heap) } 
    _module.__default.dropWhileAlways#canCall(p#0, Lit(xs#0))
         || (26 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(p#0, Tclass._System.___hTotalFunc1(Tclass._module.Nat(), Tclass._module.Nat()))
           && $Is(xs#0, Tclass._module.List()))
       ==> (!Lit(_module.List.Nil_q(Lit(xs#0)))
           ==> (var ys#3 := Lit(_module.List._h2(Lit(xs#0))); 
            (var y#3 := Lit(_module.List._h1(Lit(xs#0))); 
              $IsA#_module.Nat($Unbox(Apply1(Tclass._module.Nat(), Tclass._module.Nat(), $Heap, p#0, $Box(y#3))): DatatypeType)
                 && (!_module.Nat#Equal($Unbox(Apply1(Tclass._module.Nat(), Tclass._module.Nat(), $Heap, p#0, $Box(y#3))): DatatypeType, 
                    #_module.Nat.Zero())
                   ==> _module.__default.dropWhileAlways#canCall(p#0, ys#3)))))
         && _module.__default.dropWhileAlways($LS($ly), p#0, Lit(xs#0))
           == (if _module.List.Nil_q(Lit(xs#0))
             then #_module.List.Nil()
             else (var ys#2 := Lit(_module.List._h2(Lit(xs#0))); 
              (var y#2 := Lit(_module.List._h1(Lit(xs#0))); 
                (if !_module.Nat#Equal($Unbox(Apply1(Tclass._module.Nat(), Tclass._module.Nat(), $Heap, p#0, $Box(y#2))): DatatypeType, 
                    #_module.Nat.Zero())
                   then _module.__default.dropWhileAlways($LS($ly), p#0, ys#2)
                   else #_module.List.Cons(y#2, ys#2))))));

// definition axiom for _module.__default.dropWhileAlways for all literals (revealed)
axiom 26 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, p#0: HandleType, xs#0: DatatypeType :: 
    {:weight 3} { _module.__default.dropWhileAlways($LS($ly), Lit(p#0), Lit(xs#0)), $IsGoodHeap($Heap) } 
    _module.__default.dropWhileAlways#canCall(Lit(p#0), Lit(xs#0))
         || (26 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(p#0, Tclass._System.___hTotalFunc1(Tclass._module.Nat(), Tclass._module.Nat()))
           && $Is(xs#0, Tclass._module.List()))
       ==> (!Lit(_module.List.Nil_q(Lit(xs#0)))
           ==> (var ys#5 := Lit(_module.List._h2(Lit(xs#0))); 
            (var y#5 := Lit(_module.List._h1(Lit(xs#0))); 
              $IsA#_module.Nat($Unbox(Apply1(Tclass._module.Nat(), Tclass._module.Nat(), $Heap, Lit(p#0), $Box(y#5))): DatatypeType)
                 && (!_module.Nat#Equal($Unbox(Apply1(Tclass._module.Nat(), Tclass._module.Nat(), $Heap, Lit(p#0), $Box(y#5))): DatatypeType, 
                    #_module.Nat.Zero())
                   ==> _module.__default.dropWhileAlways#canCall(Lit(p#0), ys#5)))))
         && _module.__default.dropWhileAlways($LS($ly), Lit(p#0), Lit(xs#0))
           == (if _module.List.Nil_q(Lit(xs#0))
             then #_module.List.Nil()
             else (var ys#4 := Lit(_module.List._h2(Lit(xs#0))); 
              (var y#4 := Lit(_module.List._h1(Lit(xs#0))); 
                (if !_module.Nat#Equal($Unbox(Apply1(Tclass._module.Nat(), Tclass._module.Nat(), $Heap, Lit(p#0), $Box(y#4))): DatatypeType, 
                    #_module.Nat.Zero())
                   then _module.__default.dropWhileAlways($LS($ly), Lit(p#0), ys#4)
                   else #_module.List.Cons(y#4, ys#4))))));

procedure CheckWellformed$$_module.__default.dropWhileAlways(p#0: HandleType
       where $Is(p#0, Tclass._System.___hTotalFunc1(Tclass._module.Nat(), Tclass._module.Nat())), 
    xs#0: DatatypeType where $Is(xs#0, Tclass._module.List()));
  free requires 26 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.dropWhileAlways(p#0: HandleType, xs#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: DatatypeType;
  var _mcc#1#0: DatatypeType;
  var ys#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var y#Z#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var ##p#0: HandleType;
  var ##xs#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function dropWhileAlways
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(183,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.dropWhileAlways($LS($LZ), p#0, xs#0), Tclass._module.List());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (xs#0 == #_module.List.Nil())
        {
            assume _module.__default.dropWhileAlways($LS($LZ), p#0, xs#0)
               == Lit(#_module.List.Nil());
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.dropWhileAlways($LS($LZ), p#0, xs#0), Tclass._module.List());
        }
        else if (xs#0 == #_module.List.Cons(_mcc#0#0, _mcc#1#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.Nat());
            assume $Is(_mcc#1#0, Tclass._module.List());
            havoc ys#Z#0;
            assume $Is(ys#Z#0, Tclass._module.List());
            assume let#0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.List());
            assume ys#Z#0 == let#0#0#0;
            havoc y#Z#0;
            assume $Is(y#Z#0, Tclass._module.Nat());
            assume let#1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#1#0#0, Tclass._module.Nat());
            assume y#Z#0 == let#1#0#0;
            if (!_module.Nat#Equal($Unbox(Apply1(Tclass._module.Nat(), Tclass._module.Nat(), $Heap, p#0, $Box(y#Z#0))): DatatypeType, 
              #_module.Nat.Zero()))
            {
                ##p#0 := p#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##p#0, 
                  Tclass._System.___hTotalFunc1(Tclass._module.Nat(), Tclass._module.Nat()), 
                  $Heap);
                ##xs#0 := ys#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##xs#0, Tclass._module.List(), $Heap);
                b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assert DtRank(##xs#0) < DtRank(xs#0);
                assume _module.__default.dropWhileAlways#canCall(p#0, ys#Z#0);
                assume _module.__default.dropWhileAlways($LS($LZ), p#0, xs#0)
                   == _module.__default.dropWhileAlways($LS($LZ), p#0, ys#Z#0);
                assume _module.__default.dropWhileAlways#canCall(p#0, ys#Z#0);
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.dropWhileAlways($LS($LZ), p#0, xs#0), Tclass._module.List());
            }
            else
            {
                assume _module.__default.dropWhileAlways($LS($LZ), p#0, xs#0)
                   == #_module.List.Cons(y#Z#0, ys#Z#0);
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.dropWhileAlways($LS($LZ), p#0, xs#0), Tclass._module.List());
            }
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
    }
}



// function declaration for _module._default.filter
function _module.__default.filter($ly: LayerType, p#0: HandleType, xs#0: DatatypeType) : DatatypeType;

function _module.__default.filter#canCall(p#0: HandleType, xs#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, p#0: HandleType, xs#0: DatatypeType :: 
  { _module.__default.filter($LS($ly), p#0, xs#0) } 
  _module.__default.filter($LS($ly), p#0, xs#0)
     == _module.__default.filter($ly, p#0, xs#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, p#0: HandleType, xs#0: DatatypeType :: 
  { _module.__default.filter(AsFuelBottom($ly), p#0, xs#0) } 
  _module.__default.filter($ly, p#0, xs#0)
     == _module.__default.filter($LZ, p#0, xs#0));

// consequence axiom for _module.__default.filter
axiom 27 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, p#0: HandleType, xs#0: DatatypeType :: 
    { _module.__default.filter($ly, p#0, xs#0) } 
    _module.__default.filter#canCall(p#0, xs#0)
         || (27 != $FunctionContextHeight
           && 
          $Is(p#0, Tclass._System.___hTotalFunc1(Tclass._module.Nat(), Tclass._module.Nat()))
           && $Is(xs#0, Tclass._module.List()))
       ==> $Is(_module.__default.filter($ly, p#0, xs#0), Tclass._module.List()));

function _module.__default.filter#requires(LayerType, HandleType, DatatypeType) : bool;

// #requires axiom for _module.__default.filter
axiom (forall $ly: LayerType, $Heap: Heap, p#0: HandleType, xs#0: DatatypeType :: 
  { _module.__default.filter#requires($ly, p#0, xs#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && $Is(p#0, Tclass._System.___hTotalFunc1(Tclass._module.Nat(), Tclass._module.Nat()))
       && $Is(xs#0, Tclass._module.List())
     ==> _module.__default.filter#requires($ly, p#0, xs#0) == true);

// definition axiom for _module.__default.filter (revealed)
axiom 27 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, p#0: HandleType, xs#0: DatatypeType :: 
    { _module.__default.filter($LS($ly), p#0, xs#0), $IsGoodHeap($Heap) } 
    _module.__default.filter#canCall(p#0, xs#0)
         || (27 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(p#0, Tclass._System.___hTotalFunc1(Tclass._module.Nat(), Tclass._module.Nat()))
           && $Is(xs#0, Tclass._module.List()))
       ==> (!_module.List.Nil_q(xs#0)
           ==> (var ys#1 := _module.List._h2(xs#0); 
            (var y#1 := _module.List._h1(xs#0); 
              $IsA#_module.Nat($Unbox(Apply1(Tclass._module.Nat(), Tclass._module.Nat(), $Heap, p#0, $Box(y#1))): DatatypeType)
                 && (!_module.Nat#Equal($Unbox(Apply1(Tclass._module.Nat(), Tclass._module.Nat(), $Heap, p#0, $Box(y#1))): DatatypeType, 
                    #_module.Nat.Zero())
                   ==> _module.__default.filter#canCall(p#0, ys#1))
                 && (_module.Nat#Equal($Unbox(Apply1(Tclass._module.Nat(), Tclass._module.Nat(), $Heap, p#0, $Box(y#1))): DatatypeType, 
                    #_module.Nat.Zero())
                   ==> _module.__default.filter#canCall(p#0, ys#1)))))
         && _module.__default.filter($LS($ly), p#0, xs#0)
           == (if _module.List.Nil_q(xs#0)
             then #_module.List.Nil()
             else (var ys#0 := _module.List._h2(xs#0); 
              (var y#0 := _module.List._h1(xs#0); 
                (if !_module.Nat#Equal($Unbox(Apply1(Tclass._module.Nat(), Tclass._module.Nat(), $Heap, p#0, $Box(y#0))): DatatypeType, 
                    #_module.Nat.Zero())
                   then #_module.List.Cons(y#0, _module.__default.filter($ly, p#0, ys#0))
                   else _module.__default.filter($ly, p#0, ys#0))))));

// definition axiom for _module.__default.filter for decreasing-related literals (revealed)
axiom 27 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, p#0: HandleType, xs#0: DatatypeType :: 
    {:weight 3} { _module.__default.filter($LS($ly), p#0, Lit(xs#0)), $IsGoodHeap($Heap) } 
    _module.__default.filter#canCall(p#0, Lit(xs#0))
         || (27 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(p#0, Tclass._System.___hTotalFunc1(Tclass._module.Nat(), Tclass._module.Nat()))
           && $Is(xs#0, Tclass._module.List()))
       ==> (!Lit(_module.List.Nil_q(Lit(xs#0)))
           ==> (var ys#3 := Lit(_module.List._h2(Lit(xs#0))); 
            (var y#3 := Lit(_module.List._h1(Lit(xs#0))); 
              $IsA#_module.Nat($Unbox(Apply1(Tclass._module.Nat(), Tclass._module.Nat(), $Heap, p#0, $Box(y#3))): DatatypeType)
                 && (!_module.Nat#Equal($Unbox(Apply1(Tclass._module.Nat(), Tclass._module.Nat(), $Heap, p#0, $Box(y#3))): DatatypeType, 
                    #_module.Nat.Zero())
                   ==> _module.__default.filter#canCall(p#0, ys#3))
                 && (_module.Nat#Equal($Unbox(Apply1(Tclass._module.Nat(), Tclass._module.Nat(), $Heap, p#0, $Box(y#3))): DatatypeType, 
                    #_module.Nat.Zero())
                   ==> _module.__default.filter#canCall(p#0, ys#3)))))
         && _module.__default.filter($LS($ly), p#0, Lit(xs#0))
           == (if _module.List.Nil_q(Lit(xs#0))
             then #_module.List.Nil()
             else (var ys#2 := Lit(_module.List._h2(Lit(xs#0))); 
              (var y#2 := Lit(_module.List._h1(Lit(xs#0))); 
                (if !_module.Nat#Equal($Unbox(Apply1(Tclass._module.Nat(), Tclass._module.Nat(), $Heap, p#0, $Box(y#2))): DatatypeType, 
                    #_module.Nat.Zero())
                   then #_module.List.Cons(y#2, _module.__default.filter($LS($ly), p#0, ys#2))
                   else _module.__default.filter($LS($ly), p#0, ys#2))))));

// definition axiom for _module.__default.filter for all literals (revealed)
axiom 27 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, p#0: HandleType, xs#0: DatatypeType :: 
    {:weight 3} { _module.__default.filter($LS($ly), Lit(p#0), Lit(xs#0)), $IsGoodHeap($Heap) } 
    _module.__default.filter#canCall(Lit(p#0), Lit(xs#0))
         || (27 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(p#0, Tclass._System.___hTotalFunc1(Tclass._module.Nat(), Tclass._module.Nat()))
           && $Is(xs#0, Tclass._module.List()))
       ==> (!Lit(_module.List.Nil_q(Lit(xs#0)))
           ==> (var ys#5 := Lit(_module.List._h2(Lit(xs#0))); 
            (var y#5 := Lit(_module.List._h1(Lit(xs#0))); 
              $IsA#_module.Nat($Unbox(Apply1(Tclass._module.Nat(), Tclass._module.Nat(), $Heap, Lit(p#0), $Box(y#5))): DatatypeType)
                 && (!_module.Nat#Equal($Unbox(Apply1(Tclass._module.Nat(), Tclass._module.Nat(), $Heap, Lit(p#0), $Box(y#5))): DatatypeType, 
                    #_module.Nat.Zero())
                   ==> _module.__default.filter#canCall(Lit(p#0), ys#5))
                 && (_module.Nat#Equal($Unbox(Apply1(Tclass._module.Nat(), Tclass._module.Nat(), $Heap, Lit(p#0), $Box(y#5))): DatatypeType, 
                    #_module.Nat.Zero())
                   ==> _module.__default.filter#canCall(Lit(p#0), ys#5)))))
         && _module.__default.filter($LS($ly), Lit(p#0), Lit(xs#0))
           == (if _module.List.Nil_q(Lit(xs#0))
             then #_module.List.Nil()
             else (var ys#4 := Lit(_module.List._h2(Lit(xs#0))); 
              (var y#4 := Lit(_module.List._h1(Lit(xs#0))); 
                (if !_module.Nat#Equal($Unbox(Apply1(Tclass._module.Nat(), Tclass._module.Nat(), $Heap, Lit(p#0), $Box(y#4))): DatatypeType, 
                    #_module.Nat.Zero())
                   then #_module.List.Cons(y#4, Lit(_module.__default.filter($LS($ly), Lit(p#0), ys#4)))
                   else _module.__default.filter($LS($ly), Lit(p#0), ys#4))))));

procedure CheckWellformed$$_module.__default.filter(p#0: HandleType
       where $Is(p#0, Tclass._System.___hTotalFunc1(Tclass._module.Nat(), Tclass._module.Nat())), 
    xs#0: DatatypeType where $Is(xs#0, Tclass._module.List()));
  free requires 27 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.filter(p#0: HandleType, xs#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: DatatypeType;
  var _mcc#1#0: DatatypeType;
  var ys#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var y#Z#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var ##p#0: HandleType;
  var ##xs#0: DatatypeType;
  var ##p#1: HandleType;
  var ##xs#1: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function filter
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(193,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.filter($LS($LZ), p#0, xs#0), Tclass._module.List());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (xs#0 == #_module.List.Nil())
        {
            assume _module.__default.filter($LS($LZ), p#0, xs#0) == Lit(#_module.List.Nil());
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.filter($LS($LZ), p#0, xs#0), Tclass._module.List());
        }
        else if (xs#0 == #_module.List.Cons(_mcc#0#0, _mcc#1#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.Nat());
            assume $Is(_mcc#1#0, Tclass._module.List());
            havoc ys#Z#0;
            assume $Is(ys#Z#0, Tclass._module.List());
            assume let#0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.List());
            assume ys#Z#0 == let#0#0#0;
            havoc y#Z#0;
            assume $Is(y#Z#0, Tclass._module.Nat());
            assume let#1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#1#0#0, Tclass._module.Nat());
            assume y#Z#0 == let#1#0#0;
            if (!_module.Nat#Equal($Unbox(Apply1(Tclass._module.Nat(), Tclass._module.Nat(), $Heap, p#0, $Box(y#Z#0))): DatatypeType, 
              #_module.Nat.Zero()))
            {
                ##p#0 := p#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##p#0, 
                  Tclass._System.___hTotalFunc1(Tclass._module.Nat(), Tclass._module.Nat()), 
                  $Heap);
                ##xs#0 := ys#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##xs#0, Tclass._module.List(), $Heap);
                b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assert DtRank(##xs#0) < DtRank(xs#0);
                assume _module.__default.filter#canCall(p#0, ys#Z#0);
                assume _module.__default.filter($LS($LZ), p#0, xs#0)
                   == #_module.List.Cons(y#Z#0, _module.__default.filter($LS($LZ), p#0, ys#Z#0));
                assume _module.__default.filter#canCall(p#0, ys#Z#0);
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.filter($LS($LZ), p#0, xs#0), Tclass._module.List());
            }
            else
            {
                ##p#1 := p#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##p#1, 
                  Tclass._System.___hTotalFunc1(Tclass._module.Nat(), Tclass._module.Nat()), 
                  $Heap);
                ##xs#1 := ys#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##xs#1, Tclass._module.List(), $Heap);
                b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assert DtRank(##xs#1) < DtRank(xs#0);
                assume _module.__default.filter#canCall(p#0, ys#Z#0);
                assume _module.__default.filter($LS($LZ), p#0, xs#0)
                   == _module.__default.filter($LS($LZ), p#0, ys#Z#0);
                assume _module.__default.filter#canCall(p#0, ys#Z#0);
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.filter($LS($LZ), p#0, xs#0), Tclass._module.List());
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



// function declaration for _module._default.insort
function _module.__default.insort($ly: LayerType, n#0: DatatypeType, xs#0: DatatypeType) : DatatypeType;

function _module.__default.insort#canCall(n#0: DatatypeType, xs#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, n#0: DatatypeType, xs#0: DatatypeType :: 
  { _module.__default.insort($LS($ly), n#0, xs#0) } 
  _module.__default.insort($LS($ly), n#0, xs#0)
     == _module.__default.insort($ly, n#0, xs#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, n#0: DatatypeType, xs#0: DatatypeType :: 
  { _module.__default.insort(AsFuelBottom($ly), n#0, xs#0) } 
  _module.__default.insort($ly, n#0, xs#0)
     == _module.__default.insort($LZ, n#0, xs#0));

// consequence axiom for _module.__default.insort
axiom 28 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: DatatypeType, xs#0: DatatypeType :: 
    { _module.__default.insort($ly, n#0, xs#0) } 
    _module.__default.insort#canCall(n#0, xs#0)
         || (28 != $FunctionContextHeight
           && 
          $Is(n#0, Tclass._module.Nat())
           && $Is(xs#0, Tclass._module.List()))
       ==> $Is(_module.__default.insort($ly, n#0, xs#0), Tclass._module.List()));

function _module.__default.insort#requires(LayerType, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.insort
axiom (forall $ly: LayerType, n#0: DatatypeType, xs#0: DatatypeType :: 
  { _module.__default.insort#requires($ly, n#0, xs#0) } 
  $Is(n#0, Tclass._module.Nat()) && $Is(xs#0, Tclass._module.List())
     ==> _module.__default.insort#requires($ly, n#0, xs#0) == true);

// definition axiom for _module.__default.insort (revealed)
axiom 28 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: DatatypeType, xs#0: DatatypeType :: 
    { _module.__default.insort($LS($ly), n#0, xs#0) } 
    _module.__default.insort#canCall(n#0, xs#0)
         || (28 != $FunctionContextHeight
           && 
          $Is(n#0, Tclass._module.Nat())
           && $Is(xs#0, Tclass._module.List()))
       ==> (!_module.List.Nil_q(xs#0)
           ==> (var ys#1 := _module.List._h2(xs#0); 
            (var y#1 := _module.List._h1(xs#0); 
              $IsA#_module.Bool(_module.__default.leq($LS($LZ), n#0, y#1))
                 && _module.__default.leq#canCall(n#0, y#1)
                 && (!_module.Bool#Equal(_module.__default.leq($LS($LZ), n#0, y#1), #_module.Bool.True())
                   ==> _module.__default.insort#canCall(n#0, ys#1)))))
         && _module.__default.insort($LS($ly), n#0, xs#0)
           == (if _module.List.Nil_q(xs#0)
             then #_module.List.Cons(n#0, Lit(#_module.List.Nil()))
             else (var ys#0 := _module.List._h2(xs#0); 
              (var y#0 := _module.List._h1(xs#0); 
                (if _module.Bool#Equal(_module.__default.leq($LS($LZ), n#0, y#0), #_module.Bool.True())
                   then #_module.List.Cons(n#0, #_module.List.Cons(y#0, ys#0))
                   else #_module.List.Cons(y#0, _module.__default.insort($ly, n#0, ys#0)))))));

// definition axiom for _module.__default.insort for all literals (revealed)
axiom 28 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: DatatypeType, xs#0: DatatypeType :: 
    {:weight 3} { _module.__default.insort($LS($ly), Lit(n#0), Lit(xs#0)) } 
    _module.__default.insort#canCall(Lit(n#0), Lit(xs#0))
         || (28 != $FunctionContextHeight
           && 
          $Is(n#0, Tclass._module.Nat())
           && $Is(xs#0, Tclass._module.List()))
       ==> (!Lit(_module.List.Nil_q(Lit(xs#0)))
           ==> (var ys#3 := Lit(_module.List._h2(Lit(xs#0))); 
            (var y#3 := Lit(_module.List._h1(Lit(xs#0))); 
              $IsA#_module.Bool(_module.__default.leq($LS($LZ), Lit(n#0), y#3))
                 && _module.__default.leq#canCall(Lit(n#0), y#3)
                 && (!_module.Bool#Equal(_module.__default.leq($LS($LZ), Lit(n#0), y#3), #_module.Bool.True())
                   ==> _module.__default.insort#canCall(Lit(n#0), ys#3)))))
         && _module.__default.insort($LS($ly), Lit(n#0), Lit(xs#0))
           == (if _module.List.Nil_q(Lit(xs#0))
             then #_module.List.Cons(Lit(n#0), Lit(#_module.List.Nil()))
             else (var ys#2 := Lit(_module.List._h2(Lit(xs#0))); 
              (var y#2 := Lit(_module.List._h1(Lit(xs#0))); 
                (if _module.Bool#Equal(_module.__default.leq($LS($LZ), Lit(n#0), y#2), #_module.Bool.True())
                   then #_module.List.Cons(Lit(n#0), Lit(#_module.List.Cons(y#2, ys#2)))
                   else #_module.List.Cons(y#2, Lit(_module.__default.insort($LS($ly), Lit(n#0), ys#2))))))));

procedure CheckWellformed$$_module.__default.insort(n#0: DatatypeType where $Is(n#0, Tclass._module.Nat()), 
    xs#0: DatatypeType where $Is(xs#0, Tclass._module.List()));
  free requires 28 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.insort(n#0: DatatypeType, xs#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: DatatypeType;
  var _mcc#1#0: DatatypeType;
  var ys#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var y#Z#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var ##x#0: DatatypeType;
  var ##y#0: DatatypeType;
  var ##n#0: DatatypeType;
  var ##xs#0: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function insort
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(203,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.insort($LS($LZ), n#0, xs#0), Tclass._module.List());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (xs#0 == #_module.List.Nil())
        {
            assume _module.__default.insort($LS($LZ), n#0, xs#0)
               == #_module.List.Cons(n#0, Lit(#_module.List.Nil()));
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.insort($LS($LZ), n#0, xs#0), Tclass._module.List());
        }
        else if (xs#0 == #_module.List.Cons(_mcc#0#0, _mcc#1#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.Nat());
            assume $Is(_mcc#1#0, Tclass._module.List());
            havoc ys#Z#0;
            assume $Is(ys#Z#0, Tclass._module.List());
            assume let#0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.List());
            assume ys#Z#0 == let#0#0#0;
            havoc y#Z#0;
            assume $Is(y#Z#0, Tclass._module.Nat());
            assume let#1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#1#0#0, Tclass._module.Nat());
            assume y#Z#0 == let#1#0#0;
            ##x#0 := n#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##x#0, Tclass._module.Nat(), $Heap);
            ##y#0 := y#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##y#0, Tclass._module.Nat(), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.leq#canCall(n#0, y#Z#0);
            if (_module.Bool#Equal(_module.__default.leq($LS($LZ), n#0, y#Z#0), #_module.Bool.True()))
            {
                assume _module.__default.insort($LS($LZ), n#0, xs#0)
                   == #_module.List.Cons(n#0, #_module.List.Cons(y#Z#0, ys#Z#0));
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.insort($LS($LZ), n#0, xs#0), Tclass._module.List());
            }
            else
            {
                ##n#0 := n#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#0, Tclass._module.Nat(), $Heap);
                ##xs#0 := ys#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##xs#0, Tclass._module.List(), $Heap);
                b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assert DtRank(##n#0) < DtRank(n#0)
                   || (DtRank(##n#0) == DtRank(n#0) && DtRank(##xs#0) < DtRank(xs#0));
                assume _module.__default.insort#canCall(n#0, ys#Z#0);
                assume _module.__default.insort($LS($LZ), n#0, xs#0)
                   == #_module.List.Cons(y#Z#0, _module.__default.insort($LS($LZ), n#0, ys#Z#0));
                assume _module.__default.insort#canCall(n#0, ys#Z#0);
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.insort($LS($LZ), n#0, xs#0), Tclass._module.List());
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



// function declaration for _module._default.ins
function _module.__default.ins($ly: LayerType, n#0: DatatypeType, xs#0: DatatypeType) : DatatypeType;

function _module.__default.ins#canCall(n#0: DatatypeType, xs#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, n#0: DatatypeType, xs#0: DatatypeType :: 
  { _module.__default.ins($LS($ly), n#0, xs#0) } 
  _module.__default.ins($LS($ly), n#0, xs#0)
     == _module.__default.ins($ly, n#0, xs#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, n#0: DatatypeType, xs#0: DatatypeType :: 
  { _module.__default.ins(AsFuelBottom($ly), n#0, xs#0) } 
  _module.__default.ins($ly, n#0, xs#0) == _module.__default.ins($LZ, n#0, xs#0));

// consequence axiom for _module.__default.ins
axiom 29 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: DatatypeType, xs#0: DatatypeType :: 
    { _module.__default.ins($ly, n#0, xs#0) } 
    _module.__default.ins#canCall(n#0, xs#0)
         || (29 != $FunctionContextHeight
           && 
          $Is(n#0, Tclass._module.Nat())
           && $Is(xs#0, Tclass._module.List()))
       ==> $Is(_module.__default.ins($ly, n#0, xs#0), Tclass._module.List()));

function _module.__default.ins#requires(LayerType, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.ins
axiom (forall $ly: LayerType, n#0: DatatypeType, xs#0: DatatypeType :: 
  { _module.__default.ins#requires($ly, n#0, xs#0) } 
  $Is(n#0, Tclass._module.Nat()) && $Is(xs#0, Tclass._module.List())
     ==> _module.__default.ins#requires($ly, n#0, xs#0) == true);

// definition axiom for _module.__default.ins (revealed)
axiom 29 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: DatatypeType, xs#0: DatatypeType :: 
    { _module.__default.ins($LS($ly), n#0, xs#0) } 
    _module.__default.ins#canCall(n#0, xs#0)
         || (29 != $FunctionContextHeight
           && 
          $Is(n#0, Tclass._module.Nat())
           && $Is(xs#0, Tclass._module.List()))
       ==> (!_module.List.Nil_q(xs#0)
           ==> (var ys#1 := _module.List._h2(xs#0); 
            (var y#1 := _module.List._h1(xs#0); 
              $IsA#_module.Bool(_module.__default.less($LS($LZ), n#0, y#1))
                 && _module.__default.less#canCall(n#0, y#1)
                 && (!_module.Bool#Equal(_module.__default.less($LS($LZ), n#0, y#1), #_module.Bool.True())
                   ==> _module.__default.ins#canCall(n#0, ys#1)))))
         && _module.__default.ins($LS($ly), n#0, xs#0)
           == (if _module.List.Nil_q(xs#0)
             then #_module.List.Cons(n#0, Lit(#_module.List.Nil()))
             else (var ys#0 := _module.List._h2(xs#0); 
              (var y#0 := _module.List._h1(xs#0); 
                (if _module.Bool#Equal(_module.__default.less($LS($LZ), n#0, y#0), #_module.Bool.True())
                   then #_module.List.Cons(n#0, #_module.List.Cons(y#0, ys#0))
                   else #_module.List.Cons(y#0, _module.__default.ins($ly, n#0, ys#0)))))));

// definition axiom for _module.__default.ins for all literals (revealed)
axiom 29 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: DatatypeType, xs#0: DatatypeType :: 
    {:weight 3} { _module.__default.ins($LS($ly), Lit(n#0), Lit(xs#0)) } 
    _module.__default.ins#canCall(Lit(n#0), Lit(xs#0))
         || (29 != $FunctionContextHeight
           && 
          $Is(n#0, Tclass._module.Nat())
           && $Is(xs#0, Tclass._module.List()))
       ==> (!Lit(_module.List.Nil_q(Lit(xs#0)))
           ==> (var ys#3 := Lit(_module.List._h2(Lit(xs#0))); 
            (var y#3 := Lit(_module.List._h1(Lit(xs#0))); 
              $IsA#_module.Bool(_module.__default.less($LS($LZ), Lit(n#0), y#3))
                 && _module.__default.less#canCall(Lit(n#0), y#3)
                 && (!_module.Bool#Equal(_module.__default.less($LS($LZ), Lit(n#0), y#3), #_module.Bool.True())
                   ==> _module.__default.ins#canCall(Lit(n#0), ys#3)))))
         && _module.__default.ins($LS($ly), Lit(n#0), Lit(xs#0))
           == (if _module.List.Nil_q(Lit(xs#0))
             then #_module.List.Cons(Lit(n#0), Lit(#_module.List.Nil()))
             else (var ys#2 := Lit(_module.List._h2(Lit(xs#0))); 
              (var y#2 := Lit(_module.List._h1(Lit(xs#0))); 
                (if _module.Bool#Equal(_module.__default.less($LS($LZ), Lit(n#0), y#2), #_module.Bool.True())
                   then #_module.List.Cons(Lit(n#0), Lit(#_module.List.Cons(y#2, ys#2)))
                   else #_module.List.Cons(y#2, Lit(_module.__default.ins($LS($ly), Lit(n#0), ys#2))))))));

procedure CheckWellformed$$_module.__default.ins(n#0: DatatypeType where $Is(n#0, Tclass._module.Nat()), 
    xs#0: DatatypeType where $Is(xs#0, Tclass._module.List()));
  free requires 29 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.ins(n#0: DatatypeType, xs#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: DatatypeType;
  var _mcc#1#0: DatatypeType;
  var ys#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var y#Z#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var ##x#0: DatatypeType;
  var ##y#0: DatatypeType;
  var ##n#0: DatatypeType;
  var ##xs#0: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function ins
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(213,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.ins($LS($LZ), n#0, xs#0), Tclass._module.List());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (xs#0 == #_module.List.Nil())
        {
            assume _module.__default.ins($LS($LZ), n#0, xs#0)
               == #_module.List.Cons(n#0, Lit(#_module.List.Nil()));
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.ins($LS($LZ), n#0, xs#0), Tclass._module.List());
        }
        else if (xs#0 == #_module.List.Cons(_mcc#0#0, _mcc#1#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.Nat());
            assume $Is(_mcc#1#0, Tclass._module.List());
            havoc ys#Z#0;
            assume $Is(ys#Z#0, Tclass._module.List());
            assume let#0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.List());
            assume ys#Z#0 == let#0#0#0;
            havoc y#Z#0;
            assume $Is(y#Z#0, Tclass._module.Nat());
            assume let#1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#1#0#0, Tclass._module.Nat());
            assume y#Z#0 == let#1#0#0;
            ##x#0 := n#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##x#0, Tclass._module.Nat(), $Heap);
            ##y#0 := y#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##y#0, Tclass._module.Nat(), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.less#canCall(n#0, y#Z#0);
            if (_module.Bool#Equal(_module.__default.less($LS($LZ), n#0, y#Z#0), #_module.Bool.True()))
            {
                assume _module.__default.ins($LS($LZ), n#0, xs#0)
                   == #_module.List.Cons(n#0, #_module.List.Cons(y#Z#0, ys#Z#0));
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.ins($LS($LZ), n#0, xs#0), Tclass._module.List());
            }
            else
            {
                ##n#0 := n#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#0, Tclass._module.Nat(), $Heap);
                ##xs#0 := ys#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##xs#0, Tclass._module.List(), $Heap);
                b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assert DtRank(##n#0) < DtRank(n#0)
                   || (DtRank(##n#0) == DtRank(n#0) && DtRank(##xs#0) < DtRank(xs#0));
                assume _module.__default.ins#canCall(n#0, ys#Z#0);
                assume _module.__default.ins($LS($LZ), n#0, xs#0)
                   == #_module.List.Cons(y#Z#0, _module.__default.ins($LS($LZ), n#0, ys#Z#0));
                assume _module.__default.ins#canCall(n#0, ys#Z#0);
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.ins($LS($LZ), n#0, xs#0), Tclass._module.List());
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



// function declaration for _module._default.ins1
function _module.__default.ins1($ly: LayerType, n#0: DatatypeType, xs#0: DatatypeType) : DatatypeType;

function _module.__default.ins1#canCall(n#0: DatatypeType, xs#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, n#0: DatatypeType, xs#0: DatatypeType :: 
  { _module.__default.ins1($LS($ly), n#0, xs#0) } 
  _module.__default.ins1($LS($ly), n#0, xs#0)
     == _module.__default.ins1($ly, n#0, xs#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, n#0: DatatypeType, xs#0: DatatypeType :: 
  { _module.__default.ins1(AsFuelBottom($ly), n#0, xs#0) } 
  _module.__default.ins1($ly, n#0, xs#0) == _module.__default.ins1($LZ, n#0, xs#0));

// consequence axiom for _module.__default.ins1
axiom 30 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: DatatypeType, xs#0: DatatypeType :: 
    { _module.__default.ins1($ly, n#0, xs#0) } 
    _module.__default.ins1#canCall(n#0, xs#0)
         || (30 != $FunctionContextHeight
           && 
          $Is(n#0, Tclass._module.Nat())
           && $Is(xs#0, Tclass._module.List()))
       ==> $Is(_module.__default.ins1($ly, n#0, xs#0), Tclass._module.List()));

function _module.__default.ins1#requires(LayerType, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.ins1
axiom (forall $ly: LayerType, n#0: DatatypeType, xs#0: DatatypeType :: 
  { _module.__default.ins1#requires($ly, n#0, xs#0) } 
  $Is(n#0, Tclass._module.Nat()) && $Is(xs#0, Tclass._module.List())
     ==> _module.__default.ins1#requires($ly, n#0, xs#0) == true);

// definition axiom for _module.__default.ins1 (revealed)
axiom 30 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: DatatypeType, xs#0: DatatypeType :: 
    { _module.__default.ins1($LS($ly), n#0, xs#0) } 
    _module.__default.ins1#canCall(n#0, xs#0)
         || (30 != $FunctionContextHeight
           && 
          $Is(n#0, Tclass._module.Nat())
           && $Is(xs#0, Tclass._module.List()))
       ==> (!_module.List.Nil_q(xs#0)
           ==> (var ys#1 := _module.List._h2(xs#0); 
            (var y#1 := _module.List._h1(xs#0); 
              $IsA#_module.Nat(n#0)
                 && $IsA#_module.Nat(y#1)
                 && (!_module.Nat#Equal(n#0, y#1) ==> _module.__default.ins1#canCall(n#0, ys#1)))))
         && _module.__default.ins1($LS($ly), n#0, xs#0)
           == (if _module.List.Nil_q(xs#0)
             then #_module.List.Cons(n#0, Lit(#_module.List.Nil()))
             else (var ys#0 := _module.List._h2(xs#0); 
              (var y#0 := _module.List._h1(xs#0); 
                (if _module.Nat#Equal(n#0, y#0)
                   then #_module.List.Cons(y#0, ys#0)
                   else #_module.List.Cons(y#0, _module.__default.ins1($ly, n#0, ys#0)))))));

// definition axiom for _module.__default.ins1 for all literals (revealed)
axiom 30 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: DatatypeType, xs#0: DatatypeType :: 
    {:weight 3} { _module.__default.ins1($LS($ly), Lit(n#0), Lit(xs#0)) } 
    _module.__default.ins1#canCall(Lit(n#0), Lit(xs#0))
         || (30 != $FunctionContextHeight
           && 
          $Is(n#0, Tclass._module.Nat())
           && $Is(xs#0, Tclass._module.List()))
       ==> (!Lit(_module.List.Nil_q(Lit(xs#0)))
           ==> (var ys#3 := Lit(_module.List._h2(Lit(xs#0))); 
            (var y#3 := Lit(_module.List._h1(Lit(xs#0))); 
              $IsA#_module.Nat(Lit(n#0))
                 && $IsA#_module.Nat(y#3)
                 && (!_module.Nat#Equal(n#0, y#3)
                   ==> _module.__default.ins1#canCall(Lit(n#0), ys#3)))))
         && _module.__default.ins1($LS($ly), Lit(n#0), Lit(xs#0))
           == (if _module.List.Nil_q(Lit(xs#0))
             then #_module.List.Cons(Lit(n#0), Lit(#_module.List.Nil()))
             else (var ys#2 := Lit(_module.List._h2(Lit(xs#0))); 
              (var y#2 := Lit(_module.List._h1(Lit(xs#0))); 
                (if _module.Nat#Equal(n#0, y#2)
                   then #_module.List.Cons(y#2, ys#2)
                   else #_module.List.Cons(y#2, Lit(_module.__default.ins1($LS($ly), Lit(n#0), ys#2))))))));

procedure CheckWellformed$$_module.__default.ins1(n#0: DatatypeType where $Is(n#0, Tclass._module.Nat()), 
    xs#0: DatatypeType where $Is(xs#0, Tclass._module.List()));
  free requires 30 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.ins1(n#0: DatatypeType, xs#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: DatatypeType;
  var _mcc#1#0: DatatypeType;
  var ys#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var y#Z#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var ##n#0: DatatypeType;
  var ##xs#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function ins1
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(223,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.ins1($LS($LZ), n#0, xs#0), Tclass._module.List());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (xs#0 == #_module.List.Nil())
        {
            assume _module.__default.ins1($LS($LZ), n#0, xs#0)
               == #_module.List.Cons(n#0, Lit(#_module.List.Nil()));
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.ins1($LS($LZ), n#0, xs#0), Tclass._module.List());
        }
        else if (xs#0 == #_module.List.Cons(_mcc#0#0, _mcc#1#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.Nat());
            assume $Is(_mcc#1#0, Tclass._module.List());
            havoc ys#Z#0;
            assume $Is(ys#Z#0, Tclass._module.List());
            assume let#0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.List());
            assume ys#Z#0 == let#0#0#0;
            havoc y#Z#0;
            assume $Is(y#Z#0, Tclass._module.Nat());
            assume let#1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#1#0#0, Tclass._module.Nat());
            assume y#Z#0 == let#1#0#0;
            if (_module.Nat#Equal(n#0, y#Z#0))
            {
                assume _module.__default.ins1($LS($LZ), n#0, xs#0) == #_module.List.Cons(y#Z#0, ys#Z#0);
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.ins1($LS($LZ), n#0, xs#0), Tclass._module.List());
            }
            else
            {
                ##n#0 := n#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#0, Tclass._module.Nat(), $Heap);
                ##xs#0 := ys#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##xs#0, Tclass._module.List(), $Heap);
                b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assert DtRank(##n#0) < DtRank(n#0)
                   || (DtRank(##n#0) == DtRank(n#0) && DtRank(##xs#0) < DtRank(xs#0));
                assume _module.__default.ins1#canCall(n#0, ys#Z#0);
                assume _module.__default.ins1($LS($LZ), n#0, xs#0)
                   == #_module.List.Cons(y#Z#0, _module.__default.ins1($LS($LZ), n#0, ys#Z#0));
                assume _module.__default.ins1#canCall(n#0, ys#Z#0);
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.ins1($LS($LZ), n#0, xs#0), Tclass._module.List());
            }
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
    }
}



// function declaration for _module._default.sort
function _module.__default.sort($ly: LayerType, xs#0: DatatypeType) : DatatypeType;

function _module.__default.sort#canCall(xs#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, xs#0: DatatypeType :: 
  { _module.__default.sort($LS($ly), xs#0) } 
  _module.__default.sort($LS($ly), xs#0) == _module.__default.sort($ly, xs#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, xs#0: DatatypeType :: 
  { _module.__default.sort(AsFuelBottom($ly), xs#0) } 
  _module.__default.sort($ly, xs#0) == _module.__default.sort($LZ, xs#0));

// consequence axiom for _module.__default.sort
axiom 31 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, xs#0: DatatypeType :: 
    { _module.__default.sort($ly, xs#0) } 
    _module.__default.sort#canCall(xs#0)
         || (31 != $FunctionContextHeight && $Is(xs#0, Tclass._module.List()))
       ==> $Is(_module.__default.sort($ly, xs#0), Tclass._module.List()));

function _module.__default.sort#requires(LayerType, DatatypeType) : bool;

// #requires axiom for _module.__default.sort
axiom (forall $ly: LayerType, xs#0: DatatypeType :: 
  { _module.__default.sort#requires($ly, xs#0) } 
  $Is(xs#0, Tclass._module.List())
     ==> _module.__default.sort#requires($ly, xs#0) == true);

// definition axiom for _module.__default.sort (revealed)
axiom 31 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, xs#0: DatatypeType :: 
    { _module.__default.sort($LS($ly), xs#0) } 
    _module.__default.sort#canCall(xs#0)
         || (31 != $FunctionContextHeight && $Is(xs#0, Tclass._module.List()))
       ==> (!_module.List.Nil_q(xs#0)
           ==> (var ys#1 := _module.List._h2(xs#0); 
            (var y#1 := _module.List._h1(xs#0); 
              _module.__default.sort#canCall(ys#1)
                 && _module.__default.insort#canCall(y#1, _module.__default.sort($ly, ys#1)))))
         && _module.__default.sort($LS($ly), xs#0)
           == (if _module.List.Nil_q(xs#0)
             then #_module.List.Nil()
             else (var ys#0 := _module.List._h2(xs#0); 
              (var y#0 := _module.List._h1(xs#0); 
                _module.__default.insort($LS($LZ), y#0, _module.__default.sort($ly, ys#0))))));

// definition axiom for _module.__default.sort for all literals (revealed)
axiom 31 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, xs#0: DatatypeType :: 
    {:weight 3} { _module.__default.sort($LS($ly), Lit(xs#0)) } 
    _module.__default.sort#canCall(Lit(xs#0))
         || (31 != $FunctionContextHeight && $Is(xs#0, Tclass._module.List()))
       ==> (!Lit(_module.List.Nil_q(Lit(xs#0)))
           ==> (var ys#3 := Lit(_module.List._h2(Lit(xs#0))); 
            (var y#3 := Lit(_module.List._h1(Lit(xs#0))); 
              _module.__default.sort#canCall(ys#3)
                 && _module.__default.insort#canCall(y#3, _module.__default.sort($LS($ly), ys#3)))))
         && _module.__default.sort($LS($ly), Lit(xs#0))
           == (if _module.List.Nil_q(Lit(xs#0))
             then #_module.List.Nil()
             else (var ys#2 := Lit(_module.List._h2(Lit(xs#0))); 
              (var y#2 := Lit(_module.List._h1(Lit(xs#0))); 
                Lit(_module.__default.insort($LS($LZ), y#2, Lit(_module.__default.sort($LS($ly), ys#2))))))));

procedure CheckWellformed$$_module.__default.sort(xs#0: DatatypeType where $Is(xs#0, Tclass._module.List()));
  free requires 31 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.sort(xs#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: DatatypeType;
  var _mcc#1#0: DatatypeType;
  var ys#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var y#Z#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var ##xs#0: DatatypeType;
  var ##n#0: DatatypeType;
  var ##xs#1: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function sort
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(233,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.sort($LS($LZ), xs#0), Tclass._module.List());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (xs#0 == #_module.List.Nil())
        {
            assume _module.__default.sort($LS($LZ), xs#0) == Lit(#_module.List.Nil());
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.sort($LS($LZ), xs#0), Tclass._module.List());
        }
        else if (xs#0 == #_module.List.Cons(_mcc#0#0, _mcc#1#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.Nat());
            assume $Is(_mcc#1#0, Tclass._module.List());
            havoc ys#Z#0;
            assume $Is(ys#Z#0, Tclass._module.List());
            assume let#0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.List());
            assume ys#Z#0 == let#0#0#0;
            havoc y#Z#0;
            assume $Is(y#Z#0, Tclass._module.Nat());
            assume let#1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#1#0#0, Tclass._module.Nat());
            assume y#Z#0 == let#1#0#0;
            ##xs#0 := ys#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##xs#0, Tclass._module.List(), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(##xs#0) < DtRank(xs#0);
            assume _module.__default.sort#canCall(ys#Z#0);
            ##n#0 := y#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0, Tclass._module.Nat(), $Heap);
            ##xs#1 := _module.__default.sort($LS($LZ), ys#Z#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##xs#1, Tclass._module.List(), $Heap);
            b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.insort#canCall(y#Z#0, _module.__default.sort($LS($LZ), ys#Z#0));
            assume _module.__default.sort($LS($LZ), xs#0)
               == _module.__default.insort($LS($LZ), y#Z#0, _module.__default.sort($LS($LZ), ys#Z#0));
            assume _module.__default.sort#canCall(ys#Z#0)
               && _module.__default.insort#canCall(y#Z#0, _module.__default.sort($LS($LZ), ys#Z#0));
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.sort($LS($LZ), xs#0), Tclass._module.List());
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



// function declaration for _module._default.reverse
function _module.__default.reverse($ly: LayerType, xs#0: DatatypeType) : DatatypeType;

function _module.__default.reverse#canCall(xs#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, xs#0: DatatypeType :: 
  { _module.__default.reverse($LS($ly), xs#0) } 
  _module.__default.reverse($LS($ly), xs#0)
     == _module.__default.reverse($ly, xs#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, xs#0: DatatypeType :: 
  { _module.__default.reverse(AsFuelBottom($ly), xs#0) } 
  _module.__default.reverse($ly, xs#0) == _module.__default.reverse($LZ, xs#0));

// consequence axiom for _module.__default.reverse
axiom 32 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, xs#0: DatatypeType :: 
    { _module.__default.reverse($ly, xs#0) } 
    _module.__default.reverse#canCall(xs#0)
         || (32 != $FunctionContextHeight && $Is(xs#0, Tclass._module.List()))
       ==> $Is(_module.__default.reverse($ly, xs#0), Tclass._module.List()));

function _module.__default.reverse#requires(LayerType, DatatypeType) : bool;

// #requires axiom for _module.__default.reverse
axiom (forall $ly: LayerType, xs#0: DatatypeType :: 
  { _module.__default.reverse#requires($ly, xs#0) } 
  $Is(xs#0, Tclass._module.List())
     ==> _module.__default.reverse#requires($ly, xs#0) == true);

// definition axiom for _module.__default.reverse (revealed)
axiom 32 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, xs#0: DatatypeType :: 
    { _module.__default.reverse($LS($ly), xs#0) } 
    _module.__default.reverse#canCall(xs#0)
         || (32 != $FunctionContextHeight && $Is(xs#0, Tclass._module.List()))
       ==> (!_module.List.Nil_q(xs#0)
           ==> (var rest#1 := _module.List._h2(xs#0); 
            (var t#1 := _module.List._h1(xs#0); 
              _module.__default.reverse#canCall(rest#1)
                 && _module.__default.concat#canCall(_module.__default.reverse($ly, rest#1), 
                  #_module.List.Cons(t#1, Lit(#_module.List.Nil()))))))
         && _module.__default.reverse($LS($ly), xs#0)
           == (if _module.List.Nil_q(xs#0)
             then #_module.List.Nil()
             else (var rest#0 := _module.List._h2(xs#0); 
              (var t#0 := _module.List._h1(xs#0); 
                _module.__default.concat($LS($LZ), 
                  _module.__default.reverse($ly, rest#0), 
                  #_module.List.Cons(t#0, Lit(#_module.List.Nil())))))));

// definition axiom for _module.__default.reverse for all literals (revealed)
axiom 32 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, xs#0: DatatypeType :: 
    {:weight 3} { _module.__default.reverse($LS($ly), Lit(xs#0)) } 
    _module.__default.reverse#canCall(Lit(xs#0))
         || (32 != $FunctionContextHeight && $Is(xs#0, Tclass._module.List()))
       ==> (!Lit(_module.List.Nil_q(Lit(xs#0)))
           ==> (var rest#3 := Lit(_module.List._h2(Lit(xs#0))); 
            (var t#3 := Lit(_module.List._h1(Lit(xs#0))); 
              _module.__default.reverse#canCall(rest#3)
                 && _module.__default.concat#canCall(_module.__default.reverse($LS($ly), rest#3), 
                  #_module.List.Cons(t#3, Lit(#_module.List.Nil()))))))
         && _module.__default.reverse($LS($ly), Lit(xs#0))
           == (if _module.List.Nil_q(Lit(xs#0))
             then #_module.List.Nil()
             else (var rest#2 := Lit(_module.List._h2(Lit(xs#0))); 
              (var t#2 := Lit(_module.List._h1(Lit(xs#0))); 
                Lit(_module.__default.concat($LS($LZ), 
                    Lit(_module.__default.reverse($LS($ly), rest#2)), 
                    Lit(#_module.List.Cons(t#2, Lit(#_module.List.Nil())))))))));

procedure CheckWellformed$$_module.__default.reverse(xs#0: DatatypeType where $Is(xs#0, Tclass._module.List()));
  free requires 32 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.reverse(xs#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: DatatypeType;
  var _mcc#1#0: DatatypeType;
  var rest#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var t#Z#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var ##xs#0: DatatypeType;
  var ##xs#1: DatatypeType;
  var ##ys#0: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function reverse
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(240,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.reverse($LS($LZ), xs#0), Tclass._module.List());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (xs#0 == #_module.List.Nil())
        {
            assume _module.__default.reverse($LS($LZ), xs#0) == Lit(#_module.List.Nil());
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.reverse($LS($LZ), xs#0), Tclass._module.List());
        }
        else if (xs#0 == #_module.List.Cons(_mcc#0#0, _mcc#1#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.Nat());
            assume $Is(_mcc#1#0, Tclass._module.List());
            havoc rest#Z#0;
            assume $Is(rest#Z#0, Tclass._module.List());
            assume let#0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.List());
            assume rest#Z#0 == let#0#0#0;
            havoc t#Z#0;
            assume $Is(t#Z#0, Tclass._module.Nat());
            assume let#1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#1#0#0, Tclass._module.Nat());
            assume t#Z#0 == let#1#0#0;
            ##xs#0 := rest#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##xs#0, Tclass._module.List(), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(##xs#0) < DtRank(xs#0);
            assume _module.__default.reverse#canCall(rest#Z#0);
            ##xs#1 := _module.__default.reverse($LS($LZ), rest#Z#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##xs#1, Tclass._module.List(), $Heap);
            ##ys#0 := #_module.List.Cons(t#Z#0, Lit(#_module.List.Nil()));
            // assume allocatedness for argument to function
            assume $IsAlloc(##ys#0, Tclass._module.List(), $Heap);
            b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.concat#canCall(_module.__default.reverse($LS($LZ), rest#Z#0), 
              #_module.List.Cons(t#Z#0, Lit(#_module.List.Nil())));
            assume _module.__default.reverse($LS($LZ), xs#0)
               == _module.__default.concat($LS($LZ), 
                _module.__default.reverse($LS($LZ), rest#Z#0), 
                #_module.List.Cons(t#Z#0, Lit(#_module.List.Nil())));
            assume _module.__default.reverse#canCall(rest#Z#0)
               && _module.__default.concat#canCall(_module.__default.reverse($LS($LZ), rest#Z#0), 
                #_module.List.Cons(t#Z#0, Lit(#_module.List.Nil())));
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.reverse($LS($LZ), xs#0), Tclass._module.List());
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



// function declaration for _module._default.zip
function _module.__default.zip($ly: LayerType, a#0: DatatypeType, b#0: DatatypeType) : DatatypeType;

function _module.__default.zip#canCall(a#0: DatatypeType, b#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, a#0: DatatypeType, b#0: DatatypeType :: 
  { _module.__default.zip($LS($ly), a#0, b#0) } 
  _module.__default.zip($LS($ly), a#0, b#0)
     == _module.__default.zip($ly, a#0, b#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, a#0: DatatypeType, b#0: DatatypeType :: 
  { _module.__default.zip(AsFuelBottom($ly), a#0, b#0) } 
  _module.__default.zip($ly, a#0, b#0) == _module.__default.zip($LZ, a#0, b#0));

// consequence axiom for _module.__default.zip
axiom 33 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, a#0: DatatypeType, b#0: DatatypeType :: 
    { _module.__default.zip($ly, a#0, b#0) } 
    _module.__default.zip#canCall(a#0, b#0)
         || (33 != $FunctionContextHeight
           && 
          $Is(a#0, Tclass._module.List())
           && $Is(b#0, Tclass._module.List()))
       ==> $Is(_module.__default.zip($ly, a#0, b#0), Tclass._module.PList()));

function _module.__default.zip#requires(LayerType, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.zip
axiom (forall $ly: LayerType, a#0: DatatypeType, b#0: DatatypeType :: 
  { _module.__default.zip#requires($ly, a#0, b#0) } 
  $Is(a#0, Tclass._module.List()) && $Is(b#0, Tclass._module.List())
     ==> _module.__default.zip#requires($ly, a#0, b#0) == true);

// definition axiom for _module.__default.zip (revealed)
axiom 33 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, a#0: DatatypeType, b#0: DatatypeType :: 
    { _module.__default.zip($LS($ly), a#0, b#0) } 
    _module.__default.zip#canCall(a#0, b#0)
         || (33 != $FunctionContextHeight
           && 
          $Is(a#0, Tclass._module.List())
           && $Is(b#0, Tclass._module.List()))
       ==> (!_module.List.Nil_q(a#0)
           ==> (var xs#1 := _module.List._h2(a#0); 
            !_module.List.Nil_q(b#0)
               ==> (var ys#1 := _module.List._h2(b#0); _module.__default.zip#canCall(xs#1, ys#1))))
         && _module.__default.zip($LS($ly), a#0, b#0)
           == (if _module.List.Nil_q(a#0)
             then #_module.PList.PNil()
             else (var xs#0 := _module.List._h2(a#0); 
              (var x#0 := _module.List._h1(a#0); 
                (if _module.List.Nil_q(b#0)
                   then #_module.PList.PNil()
                   else (var ys#0 := _module.List._h2(b#0); 
                    (var y#0 := _module.List._h1(b#0); 
                      #_module.PList.PCons(#_module.Pair.Pair(x#0, y#0), _module.__default.zip($ly, xs#0, ys#0)))))))));

// definition axiom for _module.__default.zip for all literals (revealed)
axiom 33 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, a#0: DatatypeType, b#0: DatatypeType :: 
    {:weight 3} { _module.__default.zip($LS($ly), Lit(a#0), Lit(b#0)) } 
    _module.__default.zip#canCall(Lit(a#0), Lit(b#0))
         || (33 != $FunctionContextHeight
           && 
          $Is(a#0, Tclass._module.List())
           && $Is(b#0, Tclass._module.List()))
       ==> (!Lit(_module.List.Nil_q(Lit(a#0)))
           ==> (var xs#3 := Lit(_module.List._h2(Lit(a#0))); 
            !Lit(_module.List.Nil_q(Lit(b#0)))
               ==> (var ys#3 := Lit(_module.List._h2(Lit(b#0))); 
                _module.__default.zip#canCall(xs#3, ys#3))))
         && _module.__default.zip($LS($ly), Lit(a#0), Lit(b#0))
           == (if _module.List.Nil_q(Lit(a#0))
             then #_module.PList.PNil()
             else (var xs#2 := Lit(_module.List._h2(Lit(a#0))); 
              (var x#2 := Lit(_module.List._h1(Lit(a#0))); 
                (if _module.List.Nil_q(Lit(b#0))
                   then #_module.PList.PNil()
                   else (var ys#2 := Lit(_module.List._h2(Lit(b#0))); 
                    (var y#2 := Lit(_module.List._h1(Lit(b#0))); 
                      Lit(#_module.PList.PCons(Lit(#_module.Pair.Pair(x#2, y#2)), 
                          Lit(_module.__default.zip($LS($ly), xs#2, ys#2)))))))))));

procedure CheckWellformed$$_module.__default.zip(a#0: DatatypeType where $Is(a#0, Tclass._module.List()), 
    b#0: DatatypeType where $Is(b#0, Tclass._module.List()));
  free requires 33 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.zip(a#0: DatatypeType, b#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: DatatypeType;
  var _mcc#1#0: DatatypeType;
  var xs#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var x#Z#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var _mcc#2#0: DatatypeType;
  var _mcc#3#0: DatatypeType;
  var ys#Z#0: DatatypeType;
  var let#2#0#0: DatatypeType;
  var y#Z#0: DatatypeType;
  var let#3#0#0: DatatypeType;
  var ##a#0: DatatypeType;
  var ##b#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function zip
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(249,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.zip($LS($LZ), a#0, b#0), Tclass._module.PList());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (a#0 == #_module.List.Nil())
        {
            assume _module.__default.zip($LS($LZ), a#0, b#0) == Lit(#_module.PList.PNil());
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.zip($LS($LZ), a#0, b#0), Tclass._module.PList());
        }
        else if (a#0 == #_module.List.Cons(_mcc#0#0, _mcc#1#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.Nat());
            assume $Is(_mcc#1#0, Tclass._module.List());
            havoc xs#Z#0;
            assume $Is(xs#Z#0, Tclass._module.List());
            assume let#0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.List());
            assume xs#Z#0 == let#0#0#0;
            havoc x#Z#0;
            assume $Is(x#Z#0, Tclass._module.Nat());
            assume let#1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#1#0#0, Tclass._module.Nat());
            assume x#Z#0 == let#1#0#0;
            if (b#0 == #_module.List.Nil())
            {
                assume _module.__default.zip($LS($LZ), a#0, b#0) == Lit(#_module.PList.PNil());
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.zip($LS($LZ), a#0, b#0), Tclass._module.PList());
            }
            else if (b#0 == #_module.List.Cons(_mcc#2#0, _mcc#3#0))
            {
                assume $Is(_mcc#2#0, Tclass._module.Nat());
                assume $Is(_mcc#3#0, Tclass._module.List());
                havoc ys#Z#0;
                assume $Is(ys#Z#0, Tclass._module.List());
                assume let#2#0#0 == _mcc#3#0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(let#2#0#0, Tclass._module.List());
                assume ys#Z#0 == let#2#0#0;
                havoc y#Z#0;
                assume $Is(y#Z#0, Tclass._module.Nat());
                assume let#3#0#0 == _mcc#2#0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(let#3#0#0, Tclass._module.Nat());
                assume y#Z#0 == let#3#0#0;
                ##a#0 := xs#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##a#0, Tclass._module.List(), $Heap);
                ##b#0 := ys#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##b#0, Tclass._module.List(), $Heap);
                b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assert DtRank(##a#0) < DtRank(a#0)
                   || (DtRank(##a#0) == DtRank(a#0) && DtRank(##b#0) < DtRank(b#0));
                assume _module.__default.zip#canCall(xs#Z#0, ys#Z#0);
                assume _module.__default.zip($LS($LZ), a#0, b#0)
                   == #_module.PList.PCons(#_module.Pair.Pair(x#Z#0, y#Z#0), 
                    _module.__default.zip($LS($LZ), xs#Z#0, ys#Z#0));
                assume _module.__default.zip#canCall(xs#Z#0, ys#Z#0);
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.zip($LS($LZ), a#0, b#0), Tclass._module.PList());
            }
            else
            {
                assume false;
            }
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
    }
}



// function declaration for _module._default.zipConcat
function _module.__default.zipConcat(x#0: DatatypeType, xs#0: DatatypeType, more#0: DatatypeType) : DatatypeType;

function _module.__default.zipConcat#canCall(x#0: DatatypeType, xs#0: DatatypeType, more#0: DatatypeType) : bool;

// consequence axiom for _module.__default.zipConcat
axiom 34 <= $FunctionContextHeight
   ==> (forall x#0: DatatypeType, xs#0: DatatypeType, more#0: DatatypeType :: 
    { _module.__default.zipConcat(x#0, xs#0, more#0) } 
    _module.__default.zipConcat#canCall(x#0, xs#0, more#0)
         || (34 != $FunctionContextHeight
           && 
          $Is(x#0, Tclass._module.Nat())
           && $Is(xs#0, Tclass._module.List())
           && $Is(more#0, Tclass._module.List()))
       ==> $Is(_module.__default.zipConcat(x#0, xs#0, more#0), Tclass._module.PList()));

function _module.__default.zipConcat#requires(DatatypeType, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.zipConcat
axiom (forall x#0: DatatypeType, xs#0: DatatypeType, more#0: DatatypeType :: 
  { _module.__default.zipConcat#requires(x#0, xs#0, more#0) } 
  $Is(x#0, Tclass._module.Nat())
       && $Is(xs#0, Tclass._module.List())
       && $Is(more#0, Tclass._module.List())
     ==> _module.__default.zipConcat#requires(x#0, xs#0, more#0) == true);

// definition axiom for _module.__default.zipConcat (revealed)
axiom 34 <= $FunctionContextHeight
   ==> (forall x#0: DatatypeType, xs#0: DatatypeType, more#0: DatatypeType :: 
    { _module.__default.zipConcat(x#0, xs#0, more#0) } 
    _module.__default.zipConcat#canCall(x#0, xs#0, more#0)
         || (34 != $FunctionContextHeight
           && 
          $Is(x#0, Tclass._module.Nat())
           && $Is(xs#0, Tclass._module.List())
           && $Is(more#0, Tclass._module.List()))
       ==> (!_module.List.Nil_q(more#0)
           ==> (var ys#1 := _module.List._h2(more#0); 
            _module.__default.zip#canCall(xs#0, ys#1)))
         && _module.__default.zipConcat(x#0, xs#0, more#0)
           == (if _module.List.Nil_q(more#0)
             then #_module.PList.PNil()
             else (var ys#0 := _module.List._h2(more#0); 
              (var y#0 := _module.List._h1(more#0); 
                #_module.PList.PCons(#_module.Pair.Pair(x#0, y#0), _module.__default.zip($LS($LZ), xs#0, ys#0))))));

// definition axiom for _module.__default.zipConcat for all literals (revealed)
axiom 34 <= $FunctionContextHeight
   ==> (forall x#0: DatatypeType, xs#0: DatatypeType, more#0: DatatypeType :: 
    {:weight 3} { _module.__default.zipConcat(Lit(x#0), Lit(xs#0), Lit(more#0)) } 
    _module.__default.zipConcat#canCall(Lit(x#0), Lit(xs#0), Lit(more#0))
         || (34 != $FunctionContextHeight
           && 
          $Is(x#0, Tclass._module.Nat())
           && $Is(xs#0, Tclass._module.List())
           && $Is(more#0, Tclass._module.List()))
       ==> (!Lit(_module.List.Nil_q(Lit(more#0)))
           ==> (var ys#3 := Lit(_module.List._h2(Lit(more#0))); 
            _module.__default.zip#canCall(Lit(xs#0), ys#3)))
         && _module.__default.zipConcat(Lit(x#0), Lit(xs#0), Lit(more#0))
           == (if _module.List.Nil_q(Lit(more#0))
             then #_module.PList.PNil()
             else (var ys#2 := Lit(_module.List._h2(Lit(more#0))); 
              (var y#2 := Lit(_module.List._h1(Lit(more#0))); 
                Lit(#_module.PList.PCons(Lit(#_module.Pair.Pair(Lit(x#0), y#2)), 
                    Lit(_module.__default.zip($LS($LZ), Lit(xs#0), ys#2))))))));

procedure CheckWellformed$$_module.__default.zipConcat(x#0: DatatypeType where $Is(x#0, Tclass._module.Nat()), 
    xs#0: DatatypeType where $Is(xs#0, Tclass._module.List()), 
    more#0: DatatypeType where $Is(more#0, Tclass._module.List()));
  free requires 34 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.zipConcat(x#0: DatatypeType, xs#0: DatatypeType, more#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: DatatypeType;
  var _mcc#1#0: DatatypeType;
  var ys#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var y#Z#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var ##a#0: DatatypeType;
  var ##b#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function zipConcat
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(258,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.zipConcat(x#0, xs#0, more#0), Tclass._module.PList());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (more#0 == #_module.List.Nil())
        {
            assume _module.__default.zipConcat(x#0, xs#0, more#0) == Lit(#_module.PList.PNil());
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.zipConcat(x#0, xs#0, more#0), Tclass._module.PList());
        }
        else if (more#0 == #_module.List.Cons(_mcc#0#0, _mcc#1#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.Nat());
            assume $Is(_mcc#1#0, Tclass._module.List());
            havoc ys#Z#0;
            assume $Is(ys#Z#0, Tclass._module.List());
            assume let#0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.List());
            assume ys#Z#0 == let#0#0#0;
            havoc y#Z#0;
            assume $Is(y#Z#0, Tclass._module.Nat());
            assume let#1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#1#0#0, Tclass._module.Nat());
            assume y#Z#0 == let#1#0#0;
            ##a#0 := xs#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##a#0, Tclass._module.List(), $Heap);
            ##b#0 := ys#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#0, Tclass._module.List(), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.zip#canCall(xs#0, ys#Z#0);
            assume _module.__default.zipConcat(x#0, xs#0, more#0)
               == #_module.PList.PCons(#_module.Pair.Pair(x#0, y#Z#0), _module.__default.zip($LS($LZ), xs#0, ys#Z#0));
            assume _module.__default.zip#canCall(xs#0, ys#Z#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.zipConcat(x#0, xs#0, more#0), Tclass._module.PList());
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
    }
}



// function declaration for _module._default.height
function _module.__default.height($ly: LayerType, t#0: DatatypeType) : DatatypeType;

function _module.__default.height#canCall(t#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, t#0: DatatypeType :: 
  { _module.__default.height($LS($ly), t#0) } 
  _module.__default.height($LS($ly), t#0) == _module.__default.height($ly, t#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, t#0: DatatypeType :: 
  { _module.__default.height(AsFuelBottom($ly), t#0) } 
  _module.__default.height($ly, t#0) == _module.__default.height($LZ, t#0));

// consequence axiom for _module.__default.height
axiom 35 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, t#0: DatatypeType :: 
    { _module.__default.height($ly, t#0) } 
    _module.__default.height#canCall(t#0)
         || (35 != $FunctionContextHeight && $Is(t#0, Tclass._module.Tree()))
       ==> $Is(_module.__default.height($ly, t#0), Tclass._module.Nat()));

function _module.__default.height#requires(LayerType, DatatypeType) : bool;

// #requires axiom for _module.__default.height
axiom (forall $ly: LayerType, t#0: DatatypeType :: 
  { _module.__default.height#requires($ly, t#0) } 
  $Is(t#0, Tclass._module.Tree())
     ==> _module.__default.height#requires($ly, t#0) == true);

// definition axiom for _module.__default.height (revealed)
axiom 35 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, t#0: DatatypeType :: 
    { _module.__default.height($LS($ly), t#0) } 
    _module.__default.height#canCall(t#0)
         || (35 != $FunctionContextHeight && $Is(t#0, Tclass._module.Tree()))
       ==> (!_module.Tree.Leaf_q(t#0)
           ==> (var r#1 := _module.Tree._h9(t#0); 
            (var l#1 := _module.Tree._h7(t#0); 
              _module.__default.height#canCall(l#1)
                 && _module.__default.height#canCall(r#1)
                 && _module.__default.max#canCall(_module.__default.height($ly, l#1), _module.__default.height($ly, r#1)))))
         && _module.__default.height($LS($ly), t#0)
           == (if _module.Tree.Leaf_q(t#0)
             then #_module.Nat.Zero()
             else (var r#0 := _module.Tree._h9(t#0); 
              (var x#0 := _module.Tree._h8(t#0); 
                (var l#0 := _module.Tree._h7(t#0); 
                  #_module.Nat.Suc(_module.__default.max($LS($LZ), _module.__default.height($ly, l#0), _module.__default.height($ly, r#0))))))));

// definition axiom for _module.__default.height for all literals (revealed)
axiom 35 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, t#0: DatatypeType :: 
    {:weight 3} { _module.__default.height($LS($ly), Lit(t#0)) } 
    _module.__default.height#canCall(Lit(t#0))
         || (35 != $FunctionContextHeight && $Is(t#0, Tclass._module.Tree()))
       ==> (!Lit(_module.Tree.Leaf_q(Lit(t#0)))
           ==> (var r#3 := Lit(_module.Tree._h9(Lit(t#0))); 
            (var l#3 := Lit(_module.Tree._h7(Lit(t#0))); 
              _module.__default.height#canCall(l#3)
                 && _module.__default.height#canCall(r#3)
                 && _module.__default.max#canCall(_module.__default.height($LS($ly), l#3), _module.__default.height($LS($ly), r#3)))))
         && _module.__default.height($LS($ly), Lit(t#0))
           == (if _module.Tree.Leaf_q(Lit(t#0))
             then #_module.Nat.Zero()
             else (var r#2 := Lit(_module.Tree._h9(Lit(t#0))); 
              (var x#2 := Lit(_module.Tree._h8(Lit(t#0))); 
                (var l#2 := Lit(_module.Tree._h7(Lit(t#0))); 
                  Lit(#_module.Nat.Suc(Lit(_module.__default.max($LS($LZ), 
                          Lit(_module.__default.height($LS($ly), l#2)), 
                          Lit(_module.__default.height($LS($ly), r#2)))))))))));

procedure CheckWellformed$$_module.__default.height(t#0: DatatypeType where $Is(t#0, Tclass._module.Tree()));
  free requires 35 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.height(t#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: DatatypeType;
  var _mcc#1#0: DatatypeType;
  var _mcc#2#0: DatatypeType;
  var r#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var x#Z#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var l#Z#0: DatatypeType;
  var let#2#0#0: DatatypeType;
  var ##t#0: DatatypeType;
  var ##t#1: DatatypeType;
  var ##x#0: DatatypeType;
  var ##y#0: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;
  var b$reqreads#2: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;

    // AddWellformednessCheck for function height
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(267,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.height($LS($LZ), t#0), Tclass._module.Nat());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (t#0 == #_module.Tree.Leaf())
        {
            assume _module.__default.height($LS($LZ), t#0) == Lit(#_module.Nat.Zero());
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.height($LS($LZ), t#0), Tclass._module.Nat());
        }
        else if (t#0 == #_module.Tree.Node(_mcc#0#0, _mcc#1#0, _mcc#2#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.Tree());
            assume $Is(_mcc#1#0, Tclass._module.Nat());
            assume $Is(_mcc#2#0, Tclass._module.Tree());
            havoc r#Z#0;
            assume $Is(r#Z#0, Tclass._module.Tree());
            assume let#0#0#0 == _mcc#2#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.Tree());
            assume r#Z#0 == let#0#0#0;
            havoc x#Z#0;
            assume $Is(x#Z#0, Tclass._module.Nat());
            assume let#1#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#1#0#0, Tclass._module.Nat());
            assume x#Z#0 == let#1#0#0;
            havoc l#Z#0;
            assume $Is(l#Z#0, Tclass._module.Tree());
            assume let#2#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#2#0#0, Tclass._module.Tree());
            assume l#Z#0 == let#2#0#0;
            ##t#0 := l#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#0, Tclass._module.Tree(), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(##t#0) < DtRank(t#0);
            assume _module.__default.height#canCall(l#Z#0);
            ##t#1 := r#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#1, Tclass._module.Tree(), $Heap);
            b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(##t#1) < DtRank(t#0);
            assume _module.__default.height#canCall(r#Z#0);
            ##x#0 := _module.__default.height($LS($LZ), l#Z#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##x#0, Tclass._module.Nat(), $Heap);
            ##y#0 := _module.__default.height($LS($LZ), r#Z#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##y#0, Tclass._module.Nat(), $Heap);
            b$reqreads#2 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.max#canCall(_module.__default.height($LS($LZ), l#Z#0), 
              _module.__default.height($LS($LZ), r#Z#0));
            assume _module.__default.height($LS($LZ), t#0)
               == #_module.Nat.Suc(_module.__default.max($LS($LZ), 
                  _module.__default.height($LS($LZ), l#Z#0), 
                  _module.__default.height($LS($LZ), r#Z#0)));
            assume _module.__default.height#canCall(l#Z#0)
               && _module.__default.height#canCall(r#Z#0)
               && _module.__default.max#canCall(_module.__default.height($LS($LZ), l#Z#0), 
                _module.__default.height($LS($LZ), r#Z#0));
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.height($LS($LZ), t#0), Tclass._module.Nat());
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
        assert b$reqreads#1;
        assert b$reqreads#2;
    }
}



// function declaration for _module._default.mirror
function _module.__default.mirror($ly: LayerType, t#0: DatatypeType) : DatatypeType;

function _module.__default.mirror#canCall(t#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, t#0: DatatypeType :: 
  { _module.__default.mirror($LS($ly), t#0) } 
  _module.__default.mirror($LS($ly), t#0) == _module.__default.mirror($ly, t#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, t#0: DatatypeType :: 
  { _module.__default.mirror(AsFuelBottom($ly), t#0) } 
  _module.__default.mirror($ly, t#0) == _module.__default.mirror($LZ, t#0));

// consequence axiom for _module.__default.mirror
axiom 36 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, t#0: DatatypeType :: 
    { _module.__default.mirror($ly, t#0) } 
    _module.__default.mirror#canCall(t#0)
         || (36 != $FunctionContextHeight && $Is(t#0, Tclass._module.Tree()))
       ==> $Is(_module.__default.mirror($ly, t#0), Tclass._module.Tree()));

function _module.__default.mirror#requires(LayerType, DatatypeType) : bool;

// #requires axiom for _module.__default.mirror
axiom (forall $ly: LayerType, t#0: DatatypeType :: 
  { _module.__default.mirror#requires($ly, t#0) } 
  $Is(t#0, Tclass._module.Tree())
     ==> _module.__default.mirror#requires($ly, t#0) == true);

// definition axiom for _module.__default.mirror (revealed)
axiom 36 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, t#0: DatatypeType :: 
    { _module.__default.mirror($LS($ly), t#0) } 
    _module.__default.mirror#canCall(t#0)
         || (36 != $FunctionContextHeight && $Is(t#0, Tclass._module.Tree()))
       ==> (!_module.Tree.Leaf_q(t#0)
           ==> (var r#1 := _module.Tree._h9(t#0); 
            (var l#1 := _module.Tree._h7(t#0); 
              _module.__default.mirror#canCall(r#1) && _module.__default.mirror#canCall(l#1))))
         && _module.__default.mirror($LS($ly), t#0)
           == (if _module.Tree.Leaf_q(t#0)
             then #_module.Tree.Leaf()
             else (var r#0 := _module.Tree._h9(t#0); 
              (var x#0 := _module.Tree._h8(t#0); 
                (var l#0 := _module.Tree._h7(t#0); 
                  #_module.Tree.Node(_module.__default.mirror($ly, r#0), x#0, _module.__default.mirror($ly, l#0)))))));

// definition axiom for _module.__default.mirror for all literals (revealed)
axiom 36 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, t#0: DatatypeType :: 
    {:weight 3} { _module.__default.mirror($LS($ly), Lit(t#0)) } 
    _module.__default.mirror#canCall(Lit(t#0))
         || (36 != $FunctionContextHeight && $Is(t#0, Tclass._module.Tree()))
       ==> (!Lit(_module.Tree.Leaf_q(Lit(t#0)))
           ==> (var r#3 := Lit(_module.Tree._h9(Lit(t#0))); 
            (var l#3 := Lit(_module.Tree._h7(Lit(t#0))); 
              _module.__default.mirror#canCall(r#3) && _module.__default.mirror#canCall(l#3))))
         && _module.__default.mirror($LS($ly), Lit(t#0))
           == (if _module.Tree.Leaf_q(Lit(t#0))
             then #_module.Tree.Leaf()
             else (var r#2 := Lit(_module.Tree._h9(Lit(t#0))); 
              (var x#2 := Lit(_module.Tree._h8(Lit(t#0))); 
                (var l#2 := Lit(_module.Tree._h7(Lit(t#0))); 
                  Lit(#_module.Tree.Node(Lit(_module.__default.mirror($LS($ly), r#2)), 
                      x#2, 
                      Lit(_module.__default.mirror($LS($ly), l#2)))))))));

procedure CheckWellformed$$_module.__default.mirror(t#0: DatatypeType where $Is(t#0, Tclass._module.Tree()));
  free requires 36 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.mirror(t#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: DatatypeType;
  var _mcc#1#0: DatatypeType;
  var _mcc#2#0: DatatypeType;
  var r#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var x#Z#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var l#Z#0: DatatypeType;
  var let#2#0#0: DatatypeType;
  var ##t#0: DatatypeType;
  var ##t#1: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function mirror
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(274,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.mirror($LS($LZ), t#0), Tclass._module.Tree());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (t#0 == #_module.Tree.Leaf())
        {
            assume _module.__default.mirror($LS($LZ), t#0) == Lit(#_module.Tree.Leaf());
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.mirror($LS($LZ), t#0), Tclass._module.Tree());
        }
        else if (t#0 == #_module.Tree.Node(_mcc#0#0, _mcc#1#0, _mcc#2#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.Tree());
            assume $Is(_mcc#1#0, Tclass._module.Nat());
            assume $Is(_mcc#2#0, Tclass._module.Tree());
            havoc r#Z#0;
            assume $Is(r#Z#0, Tclass._module.Tree());
            assume let#0#0#0 == _mcc#2#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.Tree());
            assume r#Z#0 == let#0#0#0;
            havoc x#Z#0;
            assume $Is(x#Z#0, Tclass._module.Nat());
            assume let#1#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#1#0#0, Tclass._module.Nat());
            assume x#Z#0 == let#1#0#0;
            havoc l#Z#0;
            assume $Is(l#Z#0, Tclass._module.Tree());
            assume let#2#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#2#0#0, Tclass._module.Tree());
            assume l#Z#0 == let#2#0#0;
            ##t#0 := r#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#0, Tclass._module.Tree(), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(##t#0) < DtRank(t#0);
            assume _module.__default.mirror#canCall(r#Z#0);
            ##t#1 := l#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#1, Tclass._module.Tree(), $Heap);
            b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(##t#1) < DtRank(t#0);
            assume _module.__default.mirror#canCall(l#Z#0);
            assume _module.__default.mirror($LS($LZ), t#0)
               == #_module.Tree.Node(_module.__default.mirror($LS($LZ), r#Z#0), 
                x#Z#0, 
                _module.__default.mirror($LS($LZ), l#Z#0));
            assume _module.__default.mirror#canCall(r#Z#0)
               && _module.__default.mirror#canCall(l#Z#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.mirror($LS($LZ), t#0), Tclass._module.Tree());
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



// function declaration for _module._default.AlwaysFalseFunction
function _module.__default.AlwaysFalseFunction() : HandleType;

function _module.__default.AlwaysFalseFunction#canCall() : bool;

// consequence axiom for _module.__default.AlwaysFalseFunction
axiom 37 <= $FunctionContextHeight
   ==> 
  _module.__default.AlwaysFalseFunction#canCall() || 37 != $FunctionContextHeight
   ==> $Is(_module.__default.AlwaysFalseFunction(), 
    Tclass._System.___hTotalFunc1(Tclass._module.Nat(), Tclass._module.Nat()));

function _module.__default.AlwaysFalseFunction#requires() : bool;

// #requires axiom for _module.__default.AlwaysFalseFunction
axiom _module.__default.AlwaysFalseFunction#requires() == true;

// definition axiom for _module.__default.AlwaysFalseFunction (revealed)
axiom 37 <= $FunctionContextHeight
   ==> 
  _module.__default.AlwaysFalseFunction#canCall() || 37 != $FunctionContextHeight
   ==> _module.__default.AlwaysFalseFunction()
     == Lit(AtLayer((lambda $l#0#ly#0: LayerType :: 
          Handle1((lambda $l#0#heap#0: Heap, $l#0#n#0: Box :: $Box(Lit(#_module.Nat.Zero()))), 
            (lambda $l#0#heap#0: Heap, $l#0#n#0: Box :: 
              $IsBox($l#0#n#0, Tclass._module.Nat())), 
            (lambda $l#0#heap#0: Heap, $l#0#n#0: Box :: 
              SetRef_to_SetBox((lambda $l#0#o#0: ref :: false))))), 
        $LS($LZ)));

// definition axiom for _module.__default.AlwaysFalseFunction for all literals (revealed)
axiom 37 <= $FunctionContextHeight
   ==> 
  _module.__default.AlwaysFalseFunction#canCall() || 37 != $FunctionContextHeight
   ==> _module.__default.AlwaysFalseFunction()
     == Lit(AtLayer((lambda $l#2#ly#0: LayerType :: 
          Handle1((lambda $l#2#heap#0: Heap, $l#2#n#0: Box :: $Box(Lit(#_module.Nat.Zero()))), 
            (lambda $l#2#heap#0: Heap, $l#2#n#0: Box :: 
              $IsBox($l#2#n#0, Tclass._module.Nat())), 
            (lambda $l#2#heap#0: Heap, $l#2#n#0: Box :: 
              SetRef_to_SetBox((lambda $l#2#o#0: ref :: false))))), 
        $LS($LZ)));

procedure CheckWellformed$$_module.__default.AlwaysFalseFunction();
  free requires 37 == $FunctionContextHeight;
  modifies $Heap, $Tick;



// function declaration for _module._default.AlwaysTrueFunction
function _module.__default.AlwaysTrueFunction() : HandleType;

function _module.__default.AlwaysTrueFunction#canCall() : bool;

// consequence axiom for _module.__default.AlwaysTrueFunction
axiom 38 <= $FunctionContextHeight
   ==> 
  _module.__default.AlwaysTrueFunction#canCall() || 38 != $FunctionContextHeight
   ==> $Is(_module.__default.AlwaysTrueFunction(), 
    Tclass._System.___hTotalFunc1(Tclass._module.Nat(), Tclass._module.Nat()));

function _module.__default.AlwaysTrueFunction#requires() : bool;

// #requires axiom for _module.__default.AlwaysTrueFunction
axiom _module.__default.AlwaysTrueFunction#requires() == true;

// definition axiom for _module.__default.AlwaysTrueFunction (revealed)
axiom 38 <= $FunctionContextHeight
   ==> 
  _module.__default.AlwaysTrueFunction#canCall() || 38 != $FunctionContextHeight
   ==> _module.__default.AlwaysTrueFunction()
     == Lit(AtLayer((lambda $l#0#ly#0: LayerType :: 
          Handle1((lambda $l#0#heap#0: Heap, $l#0#n#0: Box :: 
              $Box(Lit(#_module.Nat.Suc(Lit(#_module.Nat.Zero()))))), 
            (lambda $l#0#heap#0: Heap, $l#0#n#0: Box :: 
              $IsBox($l#0#n#0, Tclass._module.Nat())), 
            (lambda $l#0#heap#0: Heap, $l#0#n#0: Box :: 
              SetRef_to_SetBox((lambda $l#0#o#0: ref :: false))))), 
        $LS($LZ)));

// definition axiom for _module.__default.AlwaysTrueFunction for all literals (revealed)
axiom 38 <= $FunctionContextHeight
   ==> 
  _module.__default.AlwaysTrueFunction#canCall() || 38 != $FunctionContextHeight
   ==> _module.__default.AlwaysTrueFunction()
     == Lit(AtLayer((lambda $l#2#ly#0: LayerType :: 
          Handle1((lambda $l#2#heap#0: Heap, $l#2#n#0: Box :: 
              $Box(Lit(#_module.Nat.Suc(Lit(#_module.Nat.Zero()))))), 
            (lambda $l#2#heap#0: Heap, $l#2#n#0: Box :: 
              $IsBox($l#2#n#0, Tclass._module.Nat())), 
            (lambda $l#2#heap#0: Heap, $l#2#n#0: Box :: 
              SetRef_to_SetBox((lambda $l#2#o#0: ref :: false))))), 
        $LS($LZ)));

procedure CheckWellformed$$_module.__default.AlwaysTrueFunction();
  free requires 38 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure CheckWellformed$$_module.__default.AboutAlwaysFalseFunction();
  free requires 44 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.AboutAlwaysFalseFunction();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall n#1: DatatypeType :: 
    { $Unbox(Apply1(Tclass._module.Nat(), 
          Tclass._module.Nat(), 
          $Heap, 
          _module.__default.AlwaysFalseFunction(), 
          $Box(n#1))): DatatypeType } 
    $Is(n#1, Tclass._module.Nat())
       ==> $IsA#_module.Nat($Unbox(Apply1(Tclass._module.Nat(), 
              Tclass._module.Nat(), 
              $Heap, 
              Lit(_module.__default.AlwaysFalseFunction()), 
              $Box(n#1))): DatatypeType)
         && _module.__default.AlwaysFalseFunction#canCall());
  ensures (forall n#1: DatatypeType :: 
    { $Unbox(Apply1(Tclass._module.Nat(), 
          Tclass._module.Nat(), 
          $Heap, 
          _module.__default.AlwaysFalseFunction(), 
          $Box(n#1))): DatatypeType } 
    $Is(n#1, Tclass._module.Nat())
       ==> _module.Nat#Equal($Unbox(Apply1(Tclass._module.Nat(), 
            Tclass._module.Nat(), 
            $Heap, 
            Lit(_module.__default.AlwaysFalseFunction()), 
            $Box(n#1))): DatatypeType, 
        #_module.Nat.Zero()));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.AboutAlwaysFalseFunction() returns ($_reverifyPost: bool);
  free requires 44 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall n#1: DatatypeType :: 
    { $Unbox(Apply1(Tclass._module.Nat(), 
          Tclass._module.Nat(), 
          $Heap, 
          _module.__default.AlwaysFalseFunction(), 
          $Box(n#1))): DatatypeType } 
    $Is(n#1, Tclass._module.Nat())
       ==> $IsA#_module.Nat($Unbox(Apply1(Tclass._module.Nat(), 
              Tclass._module.Nat(), 
              $Heap, 
              Lit(_module.__default.AlwaysFalseFunction()), 
              $Box(n#1))): DatatypeType)
         && _module.__default.AlwaysFalseFunction#canCall());
  ensures (forall n#1: DatatypeType :: 
    { $Unbox(Apply1(Tclass._module.Nat(), 
          Tclass._module.Nat(), 
          $Heap, 
          _module.__default.AlwaysFalseFunction(), 
          $Box(n#1))): DatatypeType } 
    $Is(n#1, Tclass._module.Nat())
       ==> _module.Nat#Equal($Unbox(Apply1(Tclass._module.Nat(), 
            Tclass._module.Nat(), 
            $Heap, 
            Lit(_module.__default.AlwaysFalseFunction()), 
            $Box(n#1))): DatatypeType, 
        #_module.Nat.Zero()));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.AboutAlwaysFalseFunction() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: AboutAlwaysFalseFunction, Impl$$_module.__default.AboutAlwaysFalseFunction
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(291,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.AboutAlwaysTrueFunction();
  free requires 45 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.AboutAlwaysTrueFunction();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall n#1: DatatypeType :: 
    { $Unbox(Apply1(Tclass._module.Nat(), 
          Tclass._module.Nat(), 
          $Heap, 
          _module.__default.AlwaysTrueFunction(), 
          $Box(n#1))): DatatypeType } 
    $Is(n#1, Tclass._module.Nat())
       ==> $IsA#_module.Nat($Unbox(Apply1(Tclass._module.Nat(), 
              Tclass._module.Nat(), 
              $Heap, 
              Lit(_module.__default.AlwaysTrueFunction()), 
              $Box(n#1))): DatatypeType)
         && _module.__default.AlwaysTrueFunction#canCall());
  ensures (forall n#1: DatatypeType :: 
    { $Unbox(Apply1(Tclass._module.Nat(), 
          Tclass._module.Nat(), 
          $Heap, 
          _module.__default.AlwaysTrueFunction(), 
          $Box(n#1))): DatatypeType } 
    $Is(n#1, Tclass._module.Nat())
       ==> !_module.Nat#Equal($Unbox(Apply1(Tclass._module.Nat(), 
            Tclass._module.Nat(), 
            $Heap, 
            Lit(_module.__default.AlwaysTrueFunction()), 
            $Box(n#1))): DatatypeType, 
        #_module.Nat.Zero()));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.AboutAlwaysTrueFunction() returns ($_reverifyPost: bool);
  free requires 45 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall n#1: DatatypeType :: 
    { $Unbox(Apply1(Tclass._module.Nat(), 
          Tclass._module.Nat(), 
          $Heap, 
          _module.__default.AlwaysTrueFunction(), 
          $Box(n#1))): DatatypeType } 
    $Is(n#1, Tclass._module.Nat())
       ==> $IsA#_module.Nat($Unbox(Apply1(Tclass._module.Nat(), 
              Tclass._module.Nat(), 
              $Heap, 
              Lit(_module.__default.AlwaysTrueFunction()), 
              $Box(n#1))): DatatypeType)
         && _module.__default.AlwaysTrueFunction#canCall());
  ensures (forall n#1: DatatypeType :: 
    { $Unbox(Apply1(Tclass._module.Nat(), 
          Tclass._module.Nat(), 
          $Heap, 
          _module.__default.AlwaysTrueFunction(), 
          $Box(n#1))): DatatypeType } 
    $Is(n#1, Tclass._module.Nat())
       ==> !_module.Nat#Equal($Unbox(Apply1(Tclass._module.Nat(), 
            Tclass._module.Nat(), 
            $Heap, 
            Lit(_module.__default.AlwaysTrueFunction()), 
            $Box(n#1))): DatatypeType, 
        #_module.Nat.Zero()));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.AboutAlwaysTrueFunction() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: AboutAlwaysTrueFunction, Impl$$_module.__default.AboutAlwaysTrueFunction
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(295,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.P1();
  free requires 46 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.P1();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall n#1: DatatypeType, xs#1: DatatypeType :: 
    { _module.__default.drop($LS($LZ), n#1, xs#1) } 
      { _module.__default.take($LS($LZ), n#1, xs#1) } 
    $Is(n#1, Tclass._module.Nat()) && $Is(xs#1, Tclass._module.List())
       ==> $IsA#_module.List(_module.__default.concat($LS($LZ), 
            _module.__default.take($LS($LZ), n#1, xs#1), 
            _module.__default.drop($LS($LZ), n#1, xs#1)))
         && $IsA#_module.List(xs#1)
         && 
        _module.__default.take#canCall(n#1, xs#1)
         && _module.__default.drop#canCall(n#1, xs#1)
         && _module.__default.concat#canCall(_module.__default.take($LS($LZ), n#1, xs#1), 
          _module.__default.drop($LS($LZ), n#1, xs#1)));
  free ensures (forall n#1: DatatypeType, xs#1: DatatypeType :: 
    { _module.__default.drop($LS($LZ), n#1, xs#1) } 
      { _module.__default.take($LS($LZ), n#1, xs#1) } 
    $Is(n#1, Tclass._module.Nat()) && $Is(xs#1, Tclass._module.List())
       ==> _module.List#Equal(_module.__default.concat($LS($LZ), 
          _module.__default.take($LS($LZ), n#1, xs#1), 
          _module.__default.drop($LS($LZ), n#1, xs#1)), 
        xs#1));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.P1() returns ($_reverifyPost: bool);
  free requires 46 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall n#1: DatatypeType, xs#1: DatatypeType :: 
    { _module.__default.drop($LS($LZ), n#1, xs#1) } 
      { _module.__default.take($LS($LZ), n#1, xs#1) } 
    $Is(n#1, Tclass._module.Nat()) && $Is(xs#1, Tclass._module.List())
       ==> $IsA#_module.List(_module.__default.concat($LS($LZ), 
            _module.__default.take($LS($LZ), n#1, xs#1), 
            _module.__default.drop($LS($LZ), n#1, xs#1)))
         && $IsA#_module.List(xs#1)
         && 
        _module.__default.take#canCall(n#1, xs#1)
         && _module.__default.drop#canCall(n#1, xs#1)
         && _module.__default.concat#canCall(_module.__default.take($LS($LZ), n#1, xs#1), 
          _module.__default.drop($LS($LZ), n#1, xs#1)));
  ensures (forall n#1: DatatypeType, xs#1: DatatypeType :: 
    { _module.__default.drop($LS($LS($LZ)), n#1, xs#1) } 
      { _module.__default.take($LS($LS($LZ)), n#1, xs#1) } 
    $Is(n#1, Tclass._module.Nat()) && $Is(xs#1, Tclass._module.List())
       ==> _module.List#Equal(_module.__default.concat($LS($LS($LZ)), 
          _module.__default.take($LS($LS($LZ)), n#1, xs#1), 
          _module.__default.drop($LS($LS($LZ)), n#1, xs#1)), 
        xs#1));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.P1() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: P1, Impl$$_module.__default.P1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(304,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.P2();
  free requires 47 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.P2();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall n#1: DatatypeType, xs#1: DatatypeType, ys#1: DatatypeType :: 
    { _module.__default.count($LS($LZ), n#1, _module.__default.concat($LS($LZ), xs#1, ys#1)) } 
      { _module.__default.add($LS($LZ), 
        _module.__default.count($LS($LZ), n#1, xs#1), 
        _module.__default.count($LS($LZ), n#1, ys#1)) } 
    $Is(n#1, Tclass._module.Nat())
         && $Is(xs#1, Tclass._module.List())
         && $Is(ys#1, Tclass._module.List())
       ==> $IsA#_module.Nat(_module.__default.add($LS($LZ), 
            _module.__default.count($LS($LZ), n#1, xs#1), 
            _module.__default.count($LS($LZ), n#1, ys#1)))
         && $IsA#_module.Nat(_module.__default.count($LS($LZ), n#1, _module.__default.concat($LS($LZ), xs#1, ys#1)))
         && 
        _module.__default.count#canCall(n#1, xs#1)
         && _module.__default.count#canCall(n#1, ys#1)
         && _module.__default.add#canCall(_module.__default.count($LS($LZ), n#1, xs#1), 
          _module.__default.count($LS($LZ), n#1, ys#1))
         && 
        _module.__default.concat#canCall(xs#1, ys#1)
         && _module.__default.count#canCall(n#1, _module.__default.concat($LS($LZ), xs#1, ys#1)));
  free ensures (forall n#1: DatatypeType, xs#1: DatatypeType, ys#1: DatatypeType :: 
    { _module.__default.count($LS($LZ), n#1, _module.__default.concat($LS($LZ), xs#1, ys#1)) } 
      { _module.__default.add($LS($LZ), 
        _module.__default.count($LS($LZ), n#1, xs#1), 
        _module.__default.count($LS($LZ), n#1, ys#1)) } 
    $Is(n#1, Tclass._module.Nat())
         && $Is(xs#1, Tclass._module.List())
         && $Is(ys#1, Tclass._module.List())
       ==> _module.Nat#Equal(_module.__default.add($LS($LZ), 
          _module.__default.count($LS($LZ), n#1, xs#1), 
          _module.__default.count($LS($LZ), n#1, ys#1)), 
        _module.__default.count($LS($LZ), n#1, _module.__default.concat($LS($LZ), xs#1, ys#1))));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.P2() returns ($_reverifyPost: bool);
  free requires 47 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall n#1: DatatypeType, xs#1: DatatypeType, ys#1: DatatypeType :: 
    { _module.__default.count($LS($LZ), n#1, _module.__default.concat($LS($LZ), xs#1, ys#1)) } 
      { _module.__default.add($LS($LZ), 
        _module.__default.count($LS($LZ), n#1, xs#1), 
        _module.__default.count($LS($LZ), n#1, ys#1)) } 
    $Is(n#1, Tclass._module.Nat())
         && $Is(xs#1, Tclass._module.List())
         && $Is(ys#1, Tclass._module.List())
       ==> $IsA#_module.Nat(_module.__default.add($LS($LZ), 
            _module.__default.count($LS($LZ), n#1, xs#1), 
            _module.__default.count($LS($LZ), n#1, ys#1)))
         && $IsA#_module.Nat(_module.__default.count($LS($LZ), n#1, _module.__default.concat($LS($LZ), xs#1, ys#1)))
         && 
        _module.__default.count#canCall(n#1, xs#1)
         && _module.__default.count#canCall(n#1, ys#1)
         && _module.__default.add#canCall(_module.__default.count($LS($LZ), n#1, xs#1), 
          _module.__default.count($LS($LZ), n#1, ys#1))
         && 
        _module.__default.concat#canCall(xs#1, ys#1)
         && _module.__default.count#canCall(n#1, _module.__default.concat($LS($LZ), xs#1, ys#1)));
  ensures (forall n#1: DatatypeType, xs#1: DatatypeType, ys#1: DatatypeType :: 
    { _module.__default.count($LS($LS($LZ)), n#1, _module.__default.concat($LS($LS($LZ)), xs#1, ys#1)) } 
      { _module.__default.add($LS($LS($LZ)), 
        _module.__default.count($LS($LS($LZ)), n#1, xs#1), 
        _module.__default.count($LS($LS($LZ)), n#1, ys#1)) } 
    $Is(n#1, Tclass._module.Nat())
         && $Is(xs#1, Tclass._module.List())
         && $Is(ys#1, Tclass._module.List())
       ==> _module.Nat#Equal(_module.__default.add($LS($LS($LZ)), 
          _module.__default.count($LS($LS($LZ)), n#1, xs#1), 
          _module.__default.count($LS($LS($LZ)), n#1, ys#1)), 
        _module.__default.count($LS($LS($LZ)), n#1, _module.__default.concat($LS($LS($LZ)), xs#1, ys#1))));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.P2() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: P2, Impl$$_module.__default.P2
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(309,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.P3();
  free requires 48 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.P3();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall n#1: DatatypeType, xs#1: DatatypeType, ys#1: DatatypeType :: 
    { _module.__default.count($LS($LZ), n#1, _module.__default.concat($LS($LZ), xs#1, ys#1)) } 
    $Is(n#1, Tclass._module.Nat())
         && $Is(xs#1, Tclass._module.List())
         && $Is(ys#1, Tclass._module.List())
       ==> $IsA#_module.Bool(_module.__default.leq($LS($LZ), 
            _module.__default.count($LS($LZ), n#1, xs#1), 
            _module.__default.count($LS($LZ), n#1, _module.__default.concat($LS($LZ), xs#1, ys#1))))
         && 
        _module.__default.count#canCall(n#1, xs#1)
         && 
        _module.__default.concat#canCall(xs#1, ys#1)
         && _module.__default.count#canCall(n#1, _module.__default.concat($LS($LZ), xs#1, ys#1))
         && _module.__default.leq#canCall(_module.__default.count($LS($LZ), n#1, xs#1), 
          _module.__default.count($LS($LZ), n#1, _module.__default.concat($LS($LZ), xs#1, ys#1))));
  free ensures (forall n#1: DatatypeType, xs#1: DatatypeType, ys#1: DatatypeType :: 
    { _module.__default.count($LS($LZ), n#1, _module.__default.concat($LS($LZ), xs#1, ys#1)) } 
    $Is(n#1, Tclass._module.Nat())
         && $Is(xs#1, Tclass._module.List())
         && $Is(ys#1, Tclass._module.List())
       ==> _module.Bool#Equal(_module.__default.leq($LS($LZ), 
          _module.__default.count($LS($LZ), n#1, xs#1), 
          _module.__default.count($LS($LZ), n#1, _module.__default.concat($LS($LZ), xs#1, ys#1))), 
        #_module.Bool.True()));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.P3() returns ($_reverifyPost: bool);
  free requires 48 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall n#1: DatatypeType, xs#1: DatatypeType, ys#1: DatatypeType :: 
    { _module.__default.count($LS($LZ), n#1, _module.__default.concat($LS($LZ), xs#1, ys#1)) } 
    $Is(n#1, Tclass._module.Nat())
         && $Is(xs#1, Tclass._module.List())
         && $Is(ys#1, Tclass._module.List())
       ==> $IsA#_module.Bool(_module.__default.leq($LS($LZ), 
            _module.__default.count($LS($LZ), n#1, xs#1), 
            _module.__default.count($LS($LZ), n#1, _module.__default.concat($LS($LZ), xs#1, ys#1))))
         && 
        _module.__default.count#canCall(n#1, xs#1)
         && 
        _module.__default.concat#canCall(xs#1, ys#1)
         && _module.__default.count#canCall(n#1, _module.__default.concat($LS($LZ), xs#1, ys#1))
         && _module.__default.leq#canCall(_module.__default.count($LS($LZ), n#1, xs#1), 
          _module.__default.count($LS($LZ), n#1, _module.__default.concat($LS($LZ), xs#1, ys#1))));
  ensures (forall n#1: DatatypeType, xs#1: DatatypeType, ys#1: DatatypeType :: 
    { _module.__default.count($LS($LS($LZ)), n#1, _module.__default.concat($LS($LS($LZ)), xs#1, ys#1)) } 
    $Is(n#1, Tclass._module.Nat())
         && $Is(xs#1, Tclass._module.List())
         && $Is(ys#1, Tclass._module.List())
       ==> _module.Bool#Equal(_module.__default.leq($LS($LS($LZ)), 
          _module.__default.count($LS($LS($LZ)), n#1, xs#1), 
          _module.__default.count($LS($LS($LZ)), n#1, _module.__default.concat($LS($LS($LZ)), xs#1, ys#1))), 
        #_module.Bool.True()));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.P3() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: P3, Impl$$_module.__default.P3
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(314,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.P4();
  free requires 49 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.P4();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall n#1: DatatypeType, xs#1: DatatypeType :: 
    { #_module.List.Cons(n#1, xs#1) } 
      { _module.__default.add($LS($LZ), 
        #_module.Nat.Suc(#_module.Nat.Zero()), 
        _module.__default.count($LS($LZ), n#1, xs#1)) } 
    $Is(n#1, Tclass._module.Nat()) && $Is(xs#1, Tclass._module.List())
       ==> $IsA#_module.Nat(_module.__default.add($LS($LZ), 
            Lit(#_module.Nat.Suc(Lit(#_module.Nat.Zero()))), 
            _module.__default.count($LS($LZ), n#1, xs#1)))
         && $IsA#_module.Nat(_module.__default.count($LS($LZ), n#1, #_module.List.Cons(n#1, xs#1)))
         && 
        _module.__default.count#canCall(n#1, xs#1)
         && _module.__default.add#canCall(Lit(#_module.Nat.Suc(Lit(#_module.Nat.Zero()))), 
          _module.__default.count($LS($LZ), n#1, xs#1))
         && _module.__default.count#canCall(n#1, #_module.List.Cons(n#1, xs#1)));
  free ensures (forall n#1: DatatypeType, xs#1: DatatypeType :: 
    { #_module.List.Cons(n#1, xs#1) } 
      { _module.__default.add($LS($LZ), 
        #_module.Nat.Suc(#_module.Nat.Zero()), 
        _module.__default.count($LS($LZ), n#1, xs#1)) } 
    $Is(n#1, Tclass._module.Nat()) && $Is(xs#1, Tclass._module.List())
       ==> _module.Nat#Equal(_module.__default.add($LS($LZ), 
          Lit(#_module.Nat.Suc(Lit(#_module.Nat.Zero()))), 
          _module.__default.count($LS($LZ), n#1, xs#1)), 
        _module.__default.count($LS($LZ), n#1, #_module.List.Cons(n#1, xs#1))));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.P4() returns ($_reverifyPost: bool);
  free requires 49 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall n#1: DatatypeType, xs#1: DatatypeType :: 
    { #_module.List.Cons(n#1, xs#1) } 
      { _module.__default.add($LS($LZ), 
        #_module.Nat.Suc(#_module.Nat.Zero()), 
        _module.__default.count($LS($LZ), n#1, xs#1)) } 
    $Is(n#1, Tclass._module.Nat()) && $Is(xs#1, Tclass._module.List())
       ==> $IsA#_module.Nat(_module.__default.add($LS($LZ), 
            Lit(#_module.Nat.Suc(Lit(#_module.Nat.Zero()))), 
            _module.__default.count($LS($LZ), n#1, xs#1)))
         && $IsA#_module.Nat(_module.__default.count($LS($LZ), n#1, #_module.List.Cons(n#1, xs#1)))
         && 
        _module.__default.count#canCall(n#1, xs#1)
         && _module.__default.add#canCall(Lit(#_module.Nat.Suc(Lit(#_module.Nat.Zero()))), 
          _module.__default.count($LS($LZ), n#1, xs#1))
         && _module.__default.count#canCall(n#1, #_module.List.Cons(n#1, xs#1)));
  ensures (forall n#1: DatatypeType, xs#1: DatatypeType :: 
    { #_module.List.Cons(n#1, xs#1) } 
      { _module.__default.add($LS($LS($LZ)), 
        #_module.Nat.Suc(#_module.Nat.Zero()), 
        _module.__default.count($LS($LS($LZ)), n#1, xs#1)) } 
    $Is(n#1, Tclass._module.Nat()) && $Is(xs#1, Tclass._module.List())
       ==> _module.Nat#Equal(_module.__default.add($LS($LS($LZ)), 
          Lit(#_module.Nat.Suc(Lit(#_module.Nat.Zero()))), 
          _module.__default.count($LS($LS($LZ)), n#1, xs#1)), 
        _module.__default.count($LS($LS($LZ)), n#1, #_module.List.Cons(n#1, xs#1))));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.P4() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: P4, Impl$$_module.__default.P4
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(319,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.P5();
  free requires 50 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.P5();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall n#1: DatatypeType, xs#1: DatatypeType, x#1: DatatypeType :: 
    { #_module.List.Cons(x#1, xs#1), _module.__default.add($LS($LZ), 
        #_module.Nat.Suc(#_module.Nat.Zero()), 
        _module.__default.count($LS($LZ), n#1, xs#1)) } 
    $Is(n#1, Tclass._module.Nat())
         && $Is(xs#1, Tclass._module.List())
         && $Is(x#1, Tclass._module.Nat())
       ==> $IsA#_module.Nat(_module.__default.add($LS($LZ), 
            Lit(#_module.Nat.Suc(Lit(#_module.Nat.Zero()))), 
            _module.__default.count($LS($LZ), n#1, xs#1)))
         && $IsA#_module.Nat(_module.__default.count($LS($LZ), n#1, #_module.List.Cons(x#1, xs#1)))
         && 
        _module.__default.count#canCall(n#1, xs#1)
         && _module.__default.add#canCall(Lit(#_module.Nat.Suc(Lit(#_module.Nat.Zero()))), 
          _module.__default.count($LS($LZ), n#1, xs#1))
         && _module.__default.count#canCall(n#1, #_module.List.Cons(x#1, xs#1))
         && (_module.Nat#Equal(_module.__default.add($LS($LZ), 
              Lit(#_module.Nat.Suc(Lit(#_module.Nat.Zero()))), 
              _module.__default.count($LS($LZ), n#1, xs#1)), 
            _module.__default.count($LS($LZ), n#1, #_module.List.Cons(x#1, xs#1)))
           ==> $IsA#_module.Nat(n#1) && $IsA#_module.Nat(x#1)));
  free ensures (forall n#1: DatatypeType, xs#1: DatatypeType, x#1: DatatypeType :: 
    { #_module.List.Cons(x#1, xs#1), _module.__default.add($LS($LZ), 
        #_module.Nat.Suc(#_module.Nat.Zero()), 
        _module.__default.count($LS($LZ), n#1, xs#1)) } 
    $Is(n#1, Tclass._module.Nat())
         && $Is(xs#1, Tclass._module.List())
         && $Is(x#1, Tclass._module.Nat())
       ==> 
      _module.Nat#Equal(_module.__default.add($LS($LZ), 
          Lit(#_module.Nat.Suc(Lit(#_module.Nat.Zero()))), 
          _module.__default.count($LS($LZ), n#1, xs#1)), 
        _module.__default.count($LS($LZ), n#1, #_module.List.Cons(x#1, xs#1)))
       ==> _module.Nat#Equal(n#1, x#1));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.P5() returns ($_reverifyPost: bool);
  free requires 50 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall n#1: DatatypeType, xs#1: DatatypeType, x#1: DatatypeType :: 
    { #_module.List.Cons(x#1, xs#1), _module.__default.add($LS($LZ), 
        #_module.Nat.Suc(#_module.Nat.Zero()), 
        _module.__default.count($LS($LZ), n#1, xs#1)) } 
    $Is(n#1, Tclass._module.Nat())
         && $Is(xs#1, Tclass._module.List())
         && $Is(x#1, Tclass._module.Nat())
       ==> $IsA#_module.Nat(_module.__default.add($LS($LZ), 
            Lit(#_module.Nat.Suc(Lit(#_module.Nat.Zero()))), 
            _module.__default.count($LS($LZ), n#1, xs#1)))
         && $IsA#_module.Nat(_module.__default.count($LS($LZ), n#1, #_module.List.Cons(x#1, xs#1)))
         && 
        _module.__default.count#canCall(n#1, xs#1)
         && _module.__default.add#canCall(Lit(#_module.Nat.Suc(Lit(#_module.Nat.Zero()))), 
          _module.__default.count($LS($LZ), n#1, xs#1))
         && _module.__default.count#canCall(n#1, #_module.List.Cons(x#1, xs#1))
         && (_module.Nat#Equal(_module.__default.add($LS($LZ), 
              Lit(#_module.Nat.Suc(Lit(#_module.Nat.Zero()))), 
              _module.__default.count($LS($LZ), n#1, xs#1)), 
            _module.__default.count($LS($LZ), n#1, #_module.List.Cons(x#1, xs#1)))
           ==> $IsA#_module.Nat(n#1) && $IsA#_module.Nat(x#1)));
  ensures (forall n#1: DatatypeType, xs#1: DatatypeType, x#1: DatatypeType :: 
    { #_module.List.Cons(x#1, xs#1), _module.__default.add($LS($LS($LZ)), 
        #_module.Nat.Suc(#_module.Nat.Zero()), 
        _module.__default.count($LS($LS($LZ)), n#1, xs#1)) } 
    $Is(n#1, Tclass._module.Nat())
         && $Is(xs#1, Tclass._module.List())
         && $Is(x#1, Tclass._module.Nat())
       ==> 
      _module.Nat#Equal(_module.__default.add($LS($LS($LZ)), 
          Lit(#_module.Nat.Suc(Lit(#_module.Nat.Zero()))), 
          _module.__default.count($LS($LS($LZ)), n#1, xs#1)), 
        _module.__default.count($LS($LS($LZ)), n#1, #_module.List.Cons(x#1, xs#1)))
       ==> _module.Nat#Equal(n#1, x#1));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.P5() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: P5, Impl$$_module.__default.P5
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(326,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.P6();
  free requires 51 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.P6();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall m#1: DatatypeType, n#1: DatatypeType :: 
    { _module.__default.add($LS($LZ), n#1, m#1) } 
    $Is(m#1, Tclass._module.Nat()) && $Is(n#1, Tclass._module.Nat())
       ==> $IsA#_module.Nat(_module.__default.minus($LS($LZ), n#1, _module.__default.add($LS($LZ), n#1, m#1)))
         && 
        _module.__default.add#canCall(n#1, m#1)
         && _module.__default.minus#canCall(n#1, _module.__default.add($LS($LZ), n#1, m#1)));
  free ensures (forall m#1: DatatypeType, n#1: DatatypeType :: 
    { _module.__default.add($LS($LZ), n#1, m#1) } 
    $Is(m#1, Tclass._module.Nat()) && $Is(n#1, Tclass._module.Nat())
       ==> _module.Nat#Equal(_module.__default.minus($LS($LZ), n#1, _module.__default.add($LS($LZ), n#1, m#1)), 
        #_module.Nat.Zero()));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.P6() returns ($_reverifyPost: bool);
  free requires 51 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall m#1: DatatypeType, n#1: DatatypeType :: 
    { _module.__default.add($LS($LZ), n#1, m#1) } 
    $Is(m#1, Tclass._module.Nat()) && $Is(n#1, Tclass._module.Nat())
       ==> $IsA#_module.Nat(_module.__default.minus($LS($LZ), n#1, _module.__default.add($LS($LZ), n#1, m#1)))
         && 
        _module.__default.add#canCall(n#1, m#1)
         && _module.__default.minus#canCall(n#1, _module.__default.add($LS($LZ), n#1, m#1)));
  ensures (forall m#1: DatatypeType, n#1: DatatypeType :: 
    { _module.__default.add($LS($LS($LZ)), n#1, m#1) } 
    $Is(m#1, Tclass._module.Nat()) && $Is(n#1, Tclass._module.Nat())
       ==> _module.Nat#Equal(_module.__default.minus($LS($LS($LZ)), n#1, _module.__default.add($LS($LS($LZ)), n#1, m#1)), 
        #_module.Nat.Zero()));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.P6() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: P6, Impl$$_module.__default.P6
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(331,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.P7();
  free requires 52 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.P7();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall m#1: DatatypeType, n#1: DatatypeType :: 
    { _module.__default.add($LS($LZ), n#1, m#1) } 
    $Is(m#1, Tclass._module.Nat()) && $Is(n#1, Tclass._module.Nat())
       ==> $IsA#_module.Nat(_module.__default.minus($LS($LZ), _module.__default.add($LS($LZ), n#1, m#1), n#1))
         && $IsA#_module.Nat(m#1)
         && 
        _module.__default.add#canCall(n#1, m#1)
         && _module.__default.minus#canCall(_module.__default.add($LS($LZ), n#1, m#1), n#1));
  free ensures (forall m#1: DatatypeType, n#1: DatatypeType :: 
    { _module.__default.add($LS($LZ), n#1, m#1) } 
    $Is(m#1, Tclass._module.Nat()) && $Is(n#1, Tclass._module.Nat())
       ==> _module.Nat#Equal(_module.__default.minus($LS($LZ), _module.__default.add($LS($LZ), n#1, m#1), n#1), 
        m#1));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.P7() returns ($_reverifyPost: bool);
  free requires 52 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall m#1: DatatypeType, n#1: DatatypeType :: 
    { _module.__default.add($LS($LZ), n#1, m#1) } 
    $Is(m#1, Tclass._module.Nat()) && $Is(n#1, Tclass._module.Nat())
       ==> $IsA#_module.Nat(_module.__default.minus($LS($LZ), _module.__default.add($LS($LZ), n#1, m#1), n#1))
         && $IsA#_module.Nat(m#1)
         && 
        _module.__default.add#canCall(n#1, m#1)
         && _module.__default.minus#canCall(_module.__default.add($LS($LZ), n#1, m#1), n#1));
  ensures (forall m#1: DatatypeType, n#1: DatatypeType :: 
    { _module.__default.add($LS($LS($LZ)), n#1, m#1) } 
    $Is(m#1, Tclass._module.Nat()) && $Is(n#1, Tclass._module.Nat())
       ==> _module.Nat#Equal(_module.__default.minus($LS($LS($LZ)), _module.__default.add($LS($LS($LZ)), n#1, m#1), n#1), 
        m#1));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.P7() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: P7, Impl$$_module.__default.P7
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(336,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.P8();
  free requires 53 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.P8();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall k#1: DatatypeType, m#1: DatatypeType, n#1: DatatypeType :: 
    { _module.__default.add($LS($LZ), k#1, n#1), _module.__default.add($LS($LZ), k#1, m#1) } 
    $Is(k#1, Tclass._module.Nat())
         && $Is(m#1, Tclass._module.Nat())
         && $Is(n#1, Tclass._module.Nat())
       ==> $IsA#_module.Nat(_module.__default.minus($LS($LZ), 
            _module.__default.add($LS($LZ), k#1, m#1), 
            _module.__default.add($LS($LZ), k#1, n#1)))
         && $IsA#_module.Nat(_module.__default.minus($LS($LZ), m#1, n#1))
         && 
        _module.__default.add#canCall(k#1, m#1)
         && _module.__default.add#canCall(k#1, n#1)
         && _module.__default.minus#canCall(_module.__default.add($LS($LZ), k#1, m#1), 
          _module.__default.add($LS($LZ), k#1, n#1))
         && _module.__default.minus#canCall(m#1, n#1));
  free ensures (forall k#1: DatatypeType, m#1: DatatypeType, n#1: DatatypeType :: 
    { _module.__default.add($LS($LZ), k#1, n#1), _module.__default.add($LS($LZ), k#1, m#1) } 
    $Is(k#1, Tclass._module.Nat())
         && $Is(m#1, Tclass._module.Nat())
         && $Is(n#1, Tclass._module.Nat())
       ==> _module.Nat#Equal(_module.__default.minus($LS($LZ), 
          _module.__default.add($LS($LZ), k#1, m#1), 
          _module.__default.add($LS($LZ), k#1, n#1)), 
        _module.__default.minus($LS($LZ), m#1, n#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.P8() returns ($_reverifyPost: bool);
  free requires 53 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall k#1: DatatypeType, m#1: DatatypeType, n#1: DatatypeType :: 
    { _module.__default.add($LS($LZ), k#1, n#1), _module.__default.add($LS($LZ), k#1, m#1) } 
    $Is(k#1, Tclass._module.Nat())
         && $Is(m#1, Tclass._module.Nat())
         && $Is(n#1, Tclass._module.Nat())
       ==> $IsA#_module.Nat(_module.__default.minus($LS($LZ), 
            _module.__default.add($LS($LZ), k#1, m#1), 
            _module.__default.add($LS($LZ), k#1, n#1)))
         && $IsA#_module.Nat(_module.__default.minus($LS($LZ), m#1, n#1))
         && 
        _module.__default.add#canCall(k#1, m#1)
         && _module.__default.add#canCall(k#1, n#1)
         && _module.__default.minus#canCall(_module.__default.add($LS($LZ), k#1, m#1), 
          _module.__default.add($LS($LZ), k#1, n#1))
         && _module.__default.minus#canCall(m#1, n#1));
  ensures (forall k#1: DatatypeType, m#1: DatatypeType, n#1: DatatypeType :: 
    { _module.__default.add($LS($LS($LZ)), k#1, n#1), _module.__default.add($LS($LS($LZ)), k#1, m#1) } 
    $Is(k#1, Tclass._module.Nat())
         && $Is(m#1, Tclass._module.Nat())
         && $Is(n#1, Tclass._module.Nat())
       ==> _module.Nat#Equal(_module.__default.minus($LS($LS($LZ)), 
          _module.__default.add($LS($LS($LZ)), k#1, m#1), 
          _module.__default.add($LS($LS($LZ)), k#1, n#1)), 
        _module.__default.minus($LS($LS($LZ)), m#1, n#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.P8() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: P8, Impl$$_module.__default.P8
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(341,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.P9();
  free requires 54 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.P9();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall i#1: DatatypeType, j#1: DatatypeType, k#1: DatatypeType :: 
    { _module.__default.minus($LS($LZ), i#1, _module.__default.add($LS($LZ), j#1, k#1)) } 
      { _module.__default.minus($LS($LZ), _module.__default.minus($LS($LZ), i#1, j#1), k#1) } 
    $Is(i#1, Tclass._module.Nat())
         && $Is(j#1, Tclass._module.Nat())
         && $Is(k#1, Tclass._module.Nat())
       ==> $IsA#_module.Nat(_module.__default.minus($LS($LZ), _module.__default.minus($LS($LZ), i#1, j#1), k#1))
         && $IsA#_module.Nat(_module.__default.minus($LS($LZ), i#1, _module.__default.add($LS($LZ), j#1, k#1)))
         && 
        _module.__default.minus#canCall(i#1, j#1)
         && _module.__default.minus#canCall(_module.__default.minus($LS($LZ), i#1, j#1), k#1)
         && 
        _module.__default.add#canCall(j#1, k#1)
         && _module.__default.minus#canCall(i#1, _module.__default.add($LS($LZ), j#1, k#1)));
  free ensures (forall i#1: DatatypeType, j#1: DatatypeType, k#1: DatatypeType :: 
    { _module.__default.minus($LS($LZ), i#1, _module.__default.add($LS($LZ), j#1, k#1)) } 
      { _module.__default.minus($LS($LZ), _module.__default.minus($LS($LZ), i#1, j#1), k#1) } 
    $Is(i#1, Tclass._module.Nat())
         && $Is(j#1, Tclass._module.Nat())
         && $Is(k#1, Tclass._module.Nat())
       ==> _module.Nat#Equal(_module.__default.minus($LS($LZ), _module.__default.minus($LS($LZ), i#1, j#1), k#1), 
        _module.__default.minus($LS($LZ), i#1, _module.__default.add($LS($LZ), j#1, k#1))));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.P9() returns ($_reverifyPost: bool);
  free requires 54 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall i#1: DatatypeType, j#1: DatatypeType, k#1: DatatypeType :: 
    { _module.__default.minus($LS($LZ), i#1, _module.__default.add($LS($LZ), j#1, k#1)) } 
      { _module.__default.minus($LS($LZ), _module.__default.minus($LS($LZ), i#1, j#1), k#1) } 
    $Is(i#1, Tclass._module.Nat())
         && $Is(j#1, Tclass._module.Nat())
         && $Is(k#1, Tclass._module.Nat())
       ==> $IsA#_module.Nat(_module.__default.minus($LS($LZ), _module.__default.minus($LS($LZ), i#1, j#1), k#1))
         && $IsA#_module.Nat(_module.__default.minus($LS($LZ), i#1, _module.__default.add($LS($LZ), j#1, k#1)))
         && 
        _module.__default.minus#canCall(i#1, j#1)
         && _module.__default.minus#canCall(_module.__default.minus($LS($LZ), i#1, j#1), k#1)
         && 
        _module.__default.add#canCall(j#1, k#1)
         && _module.__default.minus#canCall(i#1, _module.__default.add($LS($LZ), j#1, k#1)));
  ensures (forall i#1: DatatypeType, j#1: DatatypeType, k#1: DatatypeType :: 
    { _module.__default.minus($LS($LS($LZ)), i#1, _module.__default.add($LS($LS($LZ)), j#1, k#1)) } 
      { _module.__default.minus($LS($LS($LZ)), _module.__default.minus($LS($LS($LZ)), i#1, j#1), k#1) } 
    $Is(i#1, Tclass._module.Nat())
         && $Is(j#1, Tclass._module.Nat())
         && $Is(k#1, Tclass._module.Nat())
       ==> _module.Nat#Equal(_module.__default.minus($LS($LS($LZ)), _module.__default.minus($LS($LS($LZ)), i#1, j#1), k#1), 
        _module.__default.minus($LS($LS($LZ)), i#1, _module.__default.add($LS($LS($LZ)), j#1, k#1))));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.P9() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: P9, Impl$$_module.__default.P9
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(346,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.P10();
  free requires 55 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.P10();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall m#1: DatatypeType :: 
    { _module.__default.minus($LS($LZ), m#1, m#1) } 
    $Is(m#1, Tclass._module.Nat())
       ==> $IsA#_module.Nat(_module.__default.minus($LS($LZ), m#1, m#1))
         && _module.__default.minus#canCall(m#1, m#1));
  free ensures (forall m#1: DatatypeType :: 
    { _module.__default.minus($LS($LZ), m#1, m#1) } 
    $Is(m#1, Tclass._module.Nat())
       ==> _module.Nat#Equal(_module.__default.minus($LS($LZ), m#1, m#1), #_module.Nat.Zero()));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.P10() returns ($_reverifyPost: bool);
  free requires 55 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall m#1: DatatypeType :: 
    { _module.__default.minus($LS($LZ), m#1, m#1) } 
    $Is(m#1, Tclass._module.Nat())
       ==> $IsA#_module.Nat(_module.__default.minus($LS($LZ), m#1, m#1))
         && _module.__default.minus#canCall(m#1, m#1));
  ensures (forall m#1: DatatypeType :: 
    { _module.__default.minus($LS($LS($LZ)), m#1, m#1) } 
    $Is(m#1, Tclass._module.Nat())
       ==> _module.Nat#Equal(_module.__default.minus($LS($LS($LZ)), m#1, m#1), #_module.Nat.Zero()));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.P10() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: P10, Impl$$_module.__default.P10
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(351,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.P11();
  free requires 56 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.P11();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall xs#1: DatatypeType :: 
    { _module.__default.drop($LS($LZ), #_module.Nat.Zero(), xs#1) } 
    $Is(xs#1, Tclass._module.List())
       ==> $IsA#_module.List(_module.__default.drop($LS($LZ), Lit(#_module.Nat.Zero()), xs#1))
         && $IsA#_module.List(xs#1)
         && _module.__default.drop#canCall(Lit(#_module.Nat.Zero()), xs#1));
  free ensures (forall xs#1: DatatypeType :: 
    { _module.__default.drop($LS($LZ), #_module.Nat.Zero(), xs#1) } 
    $Is(xs#1, Tclass._module.List())
       ==> _module.List#Equal(_module.__default.drop($LS($LZ), Lit(#_module.Nat.Zero()), xs#1), xs#1));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.P11() returns ($_reverifyPost: bool);
  free requires 56 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall xs#1: DatatypeType :: 
    { _module.__default.drop($LS($LZ), #_module.Nat.Zero(), xs#1) } 
    $Is(xs#1, Tclass._module.List())
       ==> $IsA#_module.List(_module.__default.drop($LS($LZ), Lit(#_module.Nat.Zero()), xs#1))
         && $IsA#_module.List(xs#1)
         && _module.__default.drop#canCall(Lit(#_module.Nat.Zero()), xs#1));
  ensures (forall xs#1: DatatypeType :: 
    { _module.__default.drop($LS($LS($LZ)), #_module.Nat.Zero(), xs#1) } 
    $Is(xs#1, Tclass._module.List())
       ==> _module.List#Equal(_module.__default.drop($LS($LS($LZ)), Lit(#_module.Nat.Zero()), xs#1), xs#1));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.P11() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: P11, Impl$$_module.__default.P11
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(356,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.P12();
  free requires 57 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.P12();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall n#1: DatatypeType, xs#1: DatatypeType, f#1: HandleType :: 
    { _module.__default.apply($LS($LZ), f#1, _module.__default.drop($LS($LZ), n#1, xs#1)) } 
      { _module.__default.drop($LS($LZ), n#1, _module.__default.apply($LS($LZ), f#1, xs#1)) } 
    $Is(n#1, Tclass._module.Nat())
         && $Is(xs#1, Tclass._module.List())
         && $Is(f#1, Tclass._System.___hTotalFunc1(Tclass._module.Nat(), Tclass._module.Nat()))
       ==> $IsA#_module.List(_module.__default.drop($LS($LZ), n#1, _module.__default.apply($LS($LZ), f#1, xs#1)))
         && $IsA#_module.List(_module.__default.apply($LS($LZ), f#1, _module.__default.drop($LS($LZ), n#1, xs#1)))
         && 
        _module.__default.apply#canCall(f#1, xs#1)
         && _module.__default.drop#canCall(n#1, _module.__default.apply($LS($LZ), f#1, xs#1))
         && 
        _module.__default.drop#canCall(n#1, xs#1)
         && _module.__default.apply#canCall(f#1, _module.__default.drop($LS($LZ), n#1, xs#1)));
  free ensures (forall n#1: DatatypeType, xs#1: DatatypeType, f#1: HandleType :: 
    { _module.__default.apply($LS($LZ), f#1, _module.__default.drop($LS($LZ), n#1, xs#1)) } 
      { _module.__default.drop($LS($LZ), n#1, _module.__default.apply($LS($LZ), f#1, xs#1)) } 
    $Is(n#1, Tclass._module.Nat())
         && $Is(xs#1, Tclass._module.List())
         && $Is(f#1, Tclass._System.___hTotalFunc1(Tclass._module.Nat(), Tclass._module.Nat()))
       ==> _module.List#Equal(_module.__default.drop($LS($LZ), n#1, _module.__default.apply($LS($LZ), f#1, xs#1)), 
        _module.__default.apply($LS($LZ), f#1, _module.__default.drop($LS($LZ), n#1, xs#1))));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.P12() returns ($_reverifyPost: bool);
  free requires 57 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall n#1: DatatypeType, xs#1: DatatypeType, f#1: HandleType :: 
    { _module.__default.apply($LS($LZ), f#1, _module.__default.drop($LS($LZ), n#1, xs#1)) } 
      { _module.__default.drop($LS($LZ), n#1, _module.__default.apply($LS($LZ), f#1, xs#1)) } 
    $Is(n#1, Tclass._module.Nat())
         && $Is(xs#1, Tclass._module.List())
         && $Is(f#1, Tclass._System.___hTotalFunc1(Tclass._module.Nat(), Tclass._module.Nat()))
       ==> $IsA#_module.List(_module.__default.drop($LS($LZ), n#1, _module.__default.apply($LS($LZ), f#1, xs#1)))
         && $IsA#_module.List(_module.__default.apply($LS($LZ), f#1, _module.__default.drop($LS($LZ), n#1, xs#1)))
         && 
        _module.__default.apply#canCall(f#1, xs#1)
         && _module.__default.drop#canCall(n#1, _module.__default.apply($LS($LZ), f#1, xs#1))
         && 
        _module.__default.drop#canCall(n#1, xs#1)
         && _module.__default.apply#canCall(f#1, _module.__default.drop($LS($LZ), n#1, xs#1)));
  ensures (forall n#1: DatatypeType, xs#1: DatatypeType, f#1: HandleType :: 
    { _module.__default.apply($LS($LS($LZ)), f#1, _module.__default.drop($LS($LS($LZ)), n#1, xs#1)) } 
      { _module.__default.drop($LS($LS($LZ)), n#1, _module.__default.apply($LS($LS($LZ)), f#1, xs#1)) } 
    $Is(n#1, Tclass._module.Nat())
         && $Is(xs#1, Tclass._module.List())
         && $Is(f#1, Tclass._System.___hTotalFunc1(Tclass._module.Nat(), Tclass._module.Nat()))
       ==> _module.List#Equal(_module.__default.drop($LS($LS($LZ)), n#1, _module.__default.apply($LS($LS($LZ)), f#1, xs#1)), 
        _module.__default.apply($LS($LS($LZ)), f#1, _module.__default.drop($LS($LS($LZ)), n#1, xs#1))));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.P12() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: P12, Impl$$_module.__default.P12
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(361,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.P13();
  free requires 58 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.P13();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall n#1: DatatypeType, x#1: DatatypeType, xs#1: DatatypeType :: 
    { #_module.List.Cons(x#1, xs#1), #_module.Nat.Suc(n#1) } 
    $Is(n#1, Tclass._module.Nat())
         && $Is(x#1, Tclass._module.Nat())
         && $Is(xs#1, Tclass._module.List())
       ==> $IsA#_module.List(_module.__default.drop($LS($LZ), #_module.Nat.Suc(n#1), #_module.List.Cons(x#1, xs#1)))
         && $IsA#_module.List(_module.__default.drop($LS($LZ), n#1, xs#1))
         && 
        _module.__default.drop#canCall(#_module.Nat.Suc(n#1), #_module.List.Cons(x#1, xs#1))
         && _module.__default.drop#canCall(n#1, xs#1));
  free ensures (forall n#1: DatatypeType, x#1: DatatypeType, xs#1: DatatypeType :: 
    { #_module.List.Cons(x#1, xs#1), #_module.Nat.Suc(n#1) } 
    $Is(n#1, Tclass._module.Nat())
         && $Is(x#1, Tclass._module.Nat())
         && $Is(xs#1, Tclass._module.List())
       ==> _module.List#Equal(_module.__default.drop($LS($LZ), #_module.Nat.Suc(n#1), #_module.List.Cons(x#1, xs#1)), 
        _module.__default.drop($LS($LZ), n#1, xs#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.P13() returns ($_reverifyPost: bool);
  free requires 58 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall n#1: DatatypeType, x#1: DatatypeType, xs#1: DatatypeType :: 
    { #_module.List.Cons(x#1, xs#1), #_module.Nat.Suc(n#1) } 
    $Is(n#1, Tclass._module.Nat())
         && $Is(x#1, Tclass._module.Nat())
         && $Is(xs#1, Tclass._module.List())
       ==> $IsA#_module.List(_module.__default.drop($LS($LZ), #_module.Nat.Suc(n#1), #_module.List.Cons(x#1, xs#1)))
         && $IsA#_module.List(_module.__default.drop($LS($LZ), n#1, xs#1))
         && 
        _module.__default.drop#canCall(#_module.Nat.Suc(n#1), #_module.List.Cons(x#1, xs#1))
         && _module.__default.drop#canCall(n#1, xs#1));
  ensures (forall n#1: DatatypeType, x#1: DatatypeType, xs#1: DatatypeType :: 
    { #_module.List.Cons(x#1, xs#1), #_module.Nat.Suc(n#1) } 
    $Is(n#1, Tclass._module.Nat())
         && $Is(x#1, Tclass._module.Nat())
         && $Is(xs#1, Tclass._module.List())
       ==> _module.List#Equal(_module.__default.drop($LS($LS($LZ)), #_module.Nat.Suc(n#1), #_module.List.Cons(x#1, xs#1)), 
        _module.__default.drop($LS($LS($LZ)), n#1, xs#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.P13() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: P13, Impl$$_module.__default.P13
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(366,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.P14();
  free requires 59 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.P14();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall xs#1: DatatypeType, ys#1: DatatypeType, p#1: HandleType :: 
    { _module.__default.concat($LS($LZ), 
        _module.__default.filter($LS($LZ), p#1, xs#1), 
        _module.__default.filter($LS($LZ), p#1, ys#1)) } 
      { _module.__default.filter($LS($LZ), p#1, _module.__default.concat($LS($LZ), xs#1, ys#1)) } 
    $Is(xs#1, Tclass._module.List())
         && $Is(ys#1, Tclass._module.List())
         && $Is(p#1, Tclass._System.___hTotalFunc1(Tclass._module.Nat(), Tclass._module.Nat()))
       ==> $IsA#_module.List(_module.__default.filter($LS($LZ), p#1, _module.__default.concat($LS($LZ), xs#1, ys#1)))
         && $IsA#_module.List(_module.__default.concat($LS($LZ), 
            _module.__default.filter($LS($LZ), p#1, xs#1), 
            _module.__default.filter($LS($LZ), p#1, ys#1)))
         && 
        _module.__default.concat#canCall(xs#1, ys#1)
         && _module.__default.filter#canCall(p#1, _module.__default.concat($LS($LZ), xs#1, ys#1))
         && 
        _module.__default.filter#canCall(p#1, xs#1)
         && _module.__default.filter#canCall(p#1, ys#1)
         && _module.__default.concat#canCall(_module.__default.filter($LS($LZ), p#1, xs#1), 
          _module.__default.filter($LS($LZ), p#1, ys#1)));
  free ensures (forall xs#1: DatatypeType, ys#1: DatatypeType, p#1: HandleType :: 
    { _module.__default.concat($LS($LZ), 
        _module.__default.filter($LS($LZ), p#1, xs#1), 
        _module.__default.filter($LS($LZ), p#1, ys#1)) } 
      { _module.__default.filter($LS($LZ), p#1, _module.__default.concat($LS($LZ), xs#1, ys#1)) } 
    $Is(xs#1, Tclass._module.List())
         && $Is(ys#1, Tclass._module.List())
         && $Is(p#1, Tclass._System.___hTotalFunc1(Tclass._module.Nat(), Tclass._module.Nat()))
       ==> _module.List#Equal(_module.__default.filter($LS($LZ), p#1, _module.__default.concat($LS($LZ), xs#1, ys#1)), 
        _module.__default.concat($LS($LZ), 
          _module.__default.filter($LS($LZ), p#1, xs#1), 
          _module.__default.filter($LS($LZ), p#1, ys#1))));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.P14() returns ($_reverifyPost: bool);
  free requires 59 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall xs#1: DatatypeType, ys#1: DatatypeType, p#1: HandleType :: 
    { _module.__default.concat($LS($LZ), 
        _module.__default.filter($LS($LZ), p#1, xs#1), 
        _module.__default.filter($LS($LZ), p#1, ys#1)) } 
      { _module.__default.filter($LS($LZ), p#1, _module.__default.concat($LS($LZ), xs#1, ys#1)) } 
    $Is(xs#1, Tclass._module.List())
         && $Is(ys#1, Tclass._module.List())
         && $Is(p#1, Tclass._System.___hTotalFunc1(Tclass._module.Nat(), Tclass._module.Nat()))
       ==> $IsA#_module.List(_module.__default.filter($LS($LZ), p#1, _module.__default.concat($LS($LZ), xs#1, ys#1)))
         && $IsA#_module.List(_module.__default.concat($LS($LZ), 
            _module.__default.filter($LS($LZ), p#1, xs#1), 
            _module.__default.filter($LS($LZ), p#1, ys#1)))
         && 
        _module.__default.concat#canCall(xs#1, ys#1)
         && _module.__default.filter#canCall(p#1, _module.__default.concat($LS($LZ), xs#1, ys#1))
         && 
        _module.__default.filter#canCall(p#1, xs#1)
         && _module.__default.filter#canCall(p#1, ys#1)
         && _module.__default.concat#canCall(_module.__default.filter($LS($LZ), p#1, xs#1), 
          _module.__default.filter($LS($LZ), p#1, ys#1)));
  ensures (forall xs#1: DatatypeType, ys#1: DatatypeType, p#1: HandleType :: 
    { _module.__default.concat($LS($LS($LZ)), 
        _module.__default.filter($LS($LS($LZ)), p#1, xs#1), 
        _module.__default.filter($LS($LS($LZ)), p#1, ys#1)) } 
      { _module.__default.filter($LS($LS($LZ)), p#1, _module.__default.concat($LS($LS($LZ)), xs#1, ys#1)) } 
    $Is(xs#1, Tclass._module.List())
         && $Is(ys#1, Tclass._module.List())
         && $Is(p#1, Tclass._System.___hTotalFunc1(Tclass._module.Nat(), Tclass._module.Nat()))
       ==> _module.List#Equal(_module.__default.filter($LS($LS($LZ)), p#1, _module.__default.concat($LS($LS($LZ)), xs#1, ys#1)), 
        _module.__default.concat($LS($LS($LZ)), 
          _module.__default.filter($LS($LS($LZ)), p#1, xs#1), 
          _module.__default.filter($LS($LS($LZ)), p#1, ys#1))));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.P14() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: P14, Impl$$_module.__default.P14
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(371,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.P15();
  free requires 60 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.P15();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall x#1: DatatypeType, xs#1: DatatypeType :: 
    { _module.__default.ins($LS($LZ), x#1, xs#1) } 
    $Is(x#1, Tclass._module.Nat()) && $Is(xs#1, Tclass._module.List())
       ==> $IsA#_module.Nat(_module.__default.len($LS($LZ), _module.__default.ins($LS($LZ), x#1, xs#1)))
         && 
        _module.__default.ins#canCall(x#1, xs#1)
         && _module.__default.len#canCall(_module.__default.ins($LS($LZ), x#1, xs#1))
         && _module.__default.len#canCall(xs#1));
  free ensures (forall x#1: DatatypeType, xs#1: DatatypeType :: 
    { _module.__default.ins($LS($LZ), x#1, xs#1) } 
    $Is(x#1, Tclass._module.Nat()) && $Is(xs#1, Tclass._module.List())
       ==> _module.Nat#Equal(_module.__default.len($LS($LZ), _module.__default.ins($LS($LZ), x#1, xs#1)), 
        #_module.Nat.Suc(_module.__default.len($LS($LZ), xs#1))));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.P15() returns ($_reverifyPost: bool);
  free requires 60 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall x#1: DatatypeType, xs#1: DatatypeType :: 
    { _module.__default.ins($LS($LZ), x#1, xs#1) } 
    $Is(x#1, Tclass._module.Nat()) && $Is(xs#1, Tclass._module.List())
       ==> $IsA#_module.Nat(_module.__default.len($LS($LZ), _module.__default.ins($LS($LZ), x#1, xs#1)))
         && 
        _module.__default.ins#canCall(x#1, xs#1)
         && _module.__default.len#canCall(_module.__default.ins($LS($LZ), x#1, xs#1))
         && _module.__default.len#canCall(xs#1));
  ensures (forall x#1: DatatypeType, xs#1: DatatypeType :: 
    { _module.__default.ins($LS($LS($LZ)), x#1, xs#1) } 
    $Is(x#1, Tclass._module.Nat()) && $Is(xs#1, Tclass._module.List())
       ==> _module.Nat#Equal(_module.__default.len($LS($LS($LZ)), _module.__default.ins($LS($LS($LZ)), x#1, xs#1)), 
        #_module.Nat.Suc(_module.__default.len($LS($LS($LZ)), xs#1))));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.P15() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: P15, Impl$$_module.__default.P15
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(376,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.P16();
  free requires 61 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.P16();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall x#1: DatatypeType, xs#1: DatatypeType :: 
    { #_module.List.Cons(x#1, xs#1) } 
    $Is(x#1, Tclass._module.Nat()) && $Is(xs#1, Tclass._module.List())
       ==> $IsA#_module.List(xs#1)
         && (_module.List#Equal(xs#1, #_module.List.Nil())
           ==> $IsA#_module.Nat(_module.__default.last($LS($LZ), #_module.List.Cons(x#1, xs#1)))
             && $IsA#_module.Nat(x#1)
             && _module.__default.last#canCall(#_module.List.Cons(x#1, xs#1))));
  free ensures (forall x#1: DatatypeType, xs#1: DatatypeType :: 
    { #_module.List.Cons(x#1, xs#1) } 
    $Is(x#1, Tclass._module.Nat()) && $Is(xs#1, Tclass._module.List())
       ==> 
      _module.List#Equal(xs#1, #_module.List.Nil())
       ==> _module.Nat#Equal(_module.__default.last($LS($LZ), #_module.List.Cons(x#1, xs#1)), x#1));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.P16() returns ($_reverifyPost: bool);
  free requires 61 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall x#1: DatatypeType, xs#1: DatatypeType :: 
    { #_module.List.Cons(x#1, xs#1) } 
    $Is(x#1, Tclass._module.Nat()) && $Is(xs#1, Tclass._module.List())
       ==> $IsA#_module.List(xs#1)
         && (_module.List#Equal(xs#1, #_module.List.Nil())
           ==> $IsA#_module.Nat(_module.__default.last($LS($LZ), #_module.List.Cons(x#1, xs#1)))
             && $IsA#_module.Nat(x#1)
             && _module.__default.last#canCall(#_module.List.Cons(x#1, xs#1))));
  ensures (forall x#1: DatatypeType, xs#1: DatatypeType :: 
    { #_module.List.Cons(x#1, xs#1) } 
    $Is(x#1, Tclass._module.Nat()) && $Is(xs#1, Tclass._module.List())
       ==> 
      _module.List#Equal(xs#1, #_module.List.Nil())
       ==> _module.Nat#Equal(_module.__default.last($LS($LS($LZ)), #_module.List.Cons(x#1, xs#1)), x#1));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.P16() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: P16, Impl$$_module.__default.P16
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(381,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.P17();
  free requires 62 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.P17();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall n#1: DatatypeType :: 
    { _module.__default.leq($LS($LZ), n#1, #_module.Nat.Zero()) } 
    $Is(n#1, Tclass._module.Nat())
       ==> $IsA#_module.Bool(_module.__default.leq($LS($LZ), n#1, Lit(#_module.Nat.Zero())))
         && _module.__default.leq#canCall(n#1, Lit(#_module.Nat.Zero()))
         && $IsA#_module.Nat(n#1));
  free ensures (forall n#1: DatatypeType :: 
    { _module.__default.leq($LS($LZ), n#1, #_module.Nat.Zero()) } 
    $Is(n#1, Tclass._module.Nat())
       ==> (_module.Bool#Equal(_module.__default.leq($LS($LZ), n#1, Lit(#_module.Nat.Zero())), 
          #_module.Bool.True())
         <==> _module.Nat#Equal(n#1, #_module.Nat.Zero())));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.P17() returns ($_reverifyPost: bool);
  free requires 62 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall n#1: DatatypeType :: 
    { _module.__default.leq($LS($LZ), n#1, #_module.Nat.Zero()) } 
    $Is(n#1, Tclass._module.Nat())
       ==> $IsA#_module.Bool(_module.__default.leq($LS($LZ), n#1, Lit(#_module.Nat.Zero())))
         && _module.__default.leq#canCall(n#1, Lit(#_module.Nat.Zero()))
         && $IsA#_module.Nat(n#1));
  ensures (forall n#1: DatatypeType :: 
    { _module.__default.leq($LS($LS($LZ)), n#1, #_module.Nat.Zero()) } 
    $Is(n#1, Tclass._module.Nat())
       ==> (_module.Bool#Equal(_module.__default.leq($LS($LS($LZ)), n#1, Lit(#_module.Nat.Zero())), 
          #_module.Bool.True())
         <==> _module.Nat#Equal(n#1, #_module.Nat.Zero())));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.P17() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: P17, Impl$$_module.__default.P17
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(386,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.P18();
  free requires 63 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.P18();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall i#1: DatatypeType, m#1: DatatypeType :: 
    { _module.__default.add($LS($LZ), i#1, m#1) } 
    $Is(i#1, Tclass._module.Nat()) && $Is(m#1, Tclass._module.Nat())
       ==> $IsA#_module.Bool(_module.__default.less($LS($LZ), i#1, #_module.Nat.Suc(_module.__default.add($LS($LZ), i#1, m#1))))
         && 
        _module.__default.add#canCall(i#1, m#1)
         && _module.__default.less#canCall(i#1, #_module.Nat.Suc(_module.__default.add($LS($LZ), i#1, m#1))));
  free ensures (forall i#1: DatatypeType, m#1: DatatypeType :: 
    { _module.__default.add($LS($LZ), i#1, m#1) } 
    $Is(i#1, Tclass._module.Nat()) && $Is(m#1, Tclass._module.Nat())
       ==> _module.Bool#Equal(_module.__default.less($LS($LZ), i#1, #_module.Nat.Suc(_module.__default.add($LS($LZ), i#1, m#1))), 
        #_module.Bool.True()));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.P18() returns ($_reverifyPost: bool);
  free requires 63 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall i#1: DatatypeType, m#1: DatatypeType :: 
    { _module.__default.add($LS($LZ), i#1, m#1) } 
    $Is(i#1, Tclass._module.Nat()) && $Is(m#1, Tclass._module.Nat())
       ==> $IsA#_module.Bool(_module.__default.less($LS($LZ), i#1, #_module.Nat.Suc(_module.__default.add($LS($LZ), i#1, m#1))))
         && 
        _module.__default.add#canCall(i#1, m#1)
         && _module.__default.less#canCall(i#1, #_module.Nat.Suc(_module.__default.add($LS($LZ), i#1, m#1))));
  ensures (forall i#1: DatatypeType, m#1: DatatypeType :: 
    { _module.__default.add($LS($LS($LZ)), i#1, m#1) } 
    $Is(i#1, Tclass._module.Nat()) && $Is(m#1, Tclass._module.Nat())
       ==> _module.Bool#Equal(_module.__default.less($LS($LS($LZ)), 
          i#1, 
          #_module.Nat.Suc(_module.__default.add($LS($LS($LZ)), i#1, m#1))), 
        #_module.Bool.True()));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.P18() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: P18, Impl$$_module.__default.P18
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(391,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.P19();
  free requires 64 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.P19();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall n#1: DatatypeType, xs#1: DatatypeType :: 
    { _module.__default.minus($LS($LZ), _module.__default.len($LS($LZ), xs#1), n#1) } 
      { _module.__default.drop($LS($LZ), n#1, xs#1) } 
    $Is(n#1, Tclass._module.Nat()) && $Is(xs#1, Tclass._module.List())
       ==> $IsA#_module.Nat(_module.__default.len($LS($LZ), _module.__default.drop($LS($LZ), n#1, xs#1)))
         && $IsA#_module.Nat(_module.__default.minus($LS($LZ), _module.__default.len($LS($LZ), xs#1), n#1))
         && 
        _module.__default.drop#canCall(n#1, xs#1)
         && _module.__default.len#canCall(_module.__default.drop($LS($LZ), n#1, xs#1))
         && 
        _module.__default.len#canCall(xs#1)
         && _module.__default.minus#canCall(_module.__default.len($LS($LZ), xs#1), n#1));
  free ensures (forall n#1: DatatypeType, xs#1: DatatypeType :: 
    { _module.__default.minus($LS($LZ), _module.__default.len($LS($LZ), xs#1), n#1) } 
      { _module.__default.drop($LS($LZ), n#1, xs#1) } 
    $Is(n#1, Tclass._module.Nat()) && $Is(xs#1, Tclass._module.List())
       ==> _module.Nat#Equal(_module.__default.len($LS($LZ), _module.__default.drop($LS($LZ), n#1, xs#1)), 
        _module.__default.minus($LS($LZ), _module.__default.len($LS($LZ), xs#1), n#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.P19() returns ($_reverifyPost: bool);
  free requires 64 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall n#1: DatatypeType, xs#1: DatatypeType :: 
    { _module.__default.minus($LS($LZ), _module.__default.len($LS($LZ), xs#1), n#1) } 
      { _module.__default.drop($LS($LZ), n#1, xs#1) } 
    $Is(n#1, Tclass._module.Nat()) && $Is(xs#1, Tclass._module.List())
       ==> $IsA#_module.Nat(_module.__default.len($LS($LZ), _module.__default.drop($LS($LZ), n#1, xs#1)))
         && $IsA#_module.Nat(_module.__default.minus($LS($LZ), _module.__default.len($LS($LZ), xs#1), n#1))
         && 
        _module.__default.drop#canCall(n#1, xs#1)
         && _module.__default.len#canCall(_module.__default.drop($LS($LZ), n#1, xs#1))
         && 
        _module.__default.len#canCall(xs#1)
         && _module.__default.minus#canCall(_module.__default.len($LS($LZ), xs#1), n#1));
  ensures (forall n#1: DatatypeType, xs#1: DatatypeType :: 
    { _module.__default.minus($LS($LS($LZ)), _module.__default.len($LS($LS($LZ)), xs#1), n#1) } 
      { _module.__default.drop($LS($LS($LZ)), n#1, xs#1) } 
    $Is(n#1, Tclass._module.Nat()) && $Is(xs#1, Tclass._module.List())
       ==> _module.Nat#Equal(_module.__default.len($LS($LS($LZ)), _module.__default.drop($LS($LS($LZ)), n#1, xs#1)), 
        _module.__default.minus($LS($LS($LZ)), _module.__default.len($LS($LS($LZ)), xs#1), n#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.P19() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: P19, Impl$$_module.__default.P19
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(396,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.P20();
  free requires 65 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.P20();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall xs#1: DatatypeType :: 
    { _module.__default.sort($LS($LZ), xs#1) } 
    $Is(xs#1, Tclass._module.List())
       ==> $IsA#_module.Nat(_module.__default.len($LS($LZ), _module.__default.sort($LS($LZ), xs#1)))
         && $IsA#_module.Nat(_module.__default.len($LS($LZ), xs#1))
         && 
        _module.__default.sort#canCall(xs#1)
         && _module.__default.len#canCall(_module.__default.sort($LS($LZ), xs#1))
         && _module.__default.len#canCall(xs#1));
  free ensures (forall xs#1: DatatypeType :: 
    { _module.__default.sort($LS($LZ), xs#1) } 
    $Is(xs#1, Tclass._module.List())
       ==> _module.Nat#Equal(_module.__default.len($LS($LZ), _module.__default.sort($LS($LZ), xs#1)), 
        _module.__default.len($LS($LZ), xs#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.P20() returns ($_reverifyPost: bool);
  free requires 65 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall xs#1: DatatypeType :: 
    { _module.__default.sort($LS($LZ), xs#1) } 
    $Is(xs#1, Tclass._module.List())
       ==> $IsA#_module.Nat(_module.__default.len($LS($LZ), _module.__default.sort($LS($LZ), xs#1)))
         && $IsA#_module.Nat(_module.__default.len($LS($LZ), xs#1))
         && 
        _module.__default.sort#canCall(xs#1)
         && _module.__default.len#canCall(_module.__default.sort($LS($LZ), xs#1))
         && _module.__default.len#canCall(xs#1));
  ensures (forall xs#1: DatatypeType :: 
    { _module.__default.sort($LS($LS($LZ)), xs#1) } 
    $Is(xs#1, Tclass._module.List())
       ==> _module.Nat#Equal(_module.__default.len($LS($LS($LZ)), _module.__default.sort($LS($LS($LZ)), xs#1)), 
        _module.__default.len($LS($LS($LZ)), xs#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.P20() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var x#0: DatatypeType;
  var xs#2: DatatypeType;
  var ##n#0: DatatypeType;
  var ##xs#3: DatatypeType;
  var ##xs#4: DatatypeType;
  var ##xs#5: DatatypeType;

    // AddMethodImpl: P20, Impl$$_module.__default.P20
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(401,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(403,3)
    // Begin Comprehension WF check
    havoc x#0;
    havoc xs#2;
    if ($Is(x#0, Tclass._module.Nat()) && $Is(xs#2, Tclass._module.List()))
    {
        ##n#0 := x#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#0, Tclass._module.Nat(), $Heap);
        ##xs#3 := xs#2;
        // assume allocatedness for argument to function
        assume $IsAlloc(##xs#3, Tclass._module.List(), $Heap);
        assume _module.__default.insort#canCall(x#0, xs#2);
        ##xs#4 := _module.__default.insort($LS($LZ), x#0, xs#2);
        // assume allocatedness for argument to function
        assume $IsAlloc(##xs#4, Tclass._module.List(), $Heap);
        assume _module.__default.len#canCall(_module.__default.insort($LS($LZ), x#0, xs#2));
        ##xs#5 := xs#2;
        // assume allocatedness for argument to function
        assume $IsAlloc(##xs#5, Tclass._module.List(), $Heap);
        assume _module.__default.len#canCall(xs#2);
    }

    // End Comprehension WF check
    assume (forall x#1: DatatypeType, xs#3: DatatypeType :: 
      { _module.__default.insort($LS($LZ), x#1, xs#3) } 
      $Is(x#1, Tclass._module.Nat()) && $Is(xs#3, Tclass._module.List())
         ==> $IsA#_module.Nat(_module.__default.len($LS($LZ), _module.__default.insort($LS($LZ), x#1, xs#3)))
           && 
          _module.__default.insort#canCall(x#1, xs#3)
           && _module.__default.len#canCall(_module.__default.insort($LS($LZ), x#1, xs#3))
           && _module.__default.len#canCall(xs#3));
    assert {:subsumption 0} (forall x#1: DatatypeType, xs#3: DatatypeType :: 
      { _module.__default.insort($LS($LS($LZ)), x#1, xs#3) } 
      $Is(x#1, Tclass._module.Nat()) && $Is(xs#3, Tclass._module.List())
         ==> _module.Nat#Equal(_module.__default.len($LS($LS($LZ)), _module.__default.insort($LS($LS($LZ)), x#1, xs#3)), 
          #_module.Nat.Suc(_module.__default.len($LS($LS($LZ)), xs#3))));
    assume (forall x#1: DatatypeType, xs#3: DatatypeType :: 
      { _module.__default.insort($LS($LZ), x#1, xs#3) } 
      $Is(x#1, Tclass._module.Nat()) && $Is(xs#3, Tclass._module.List())
         ==> _module.Nat#Equal(_module.__default.len($LS($LZ), _module.__default.insort($LS($LZ), x#1, xs#3)), 
          #_module.Nat.Suc(_module.__default.len($LS($LZ), xs#3))));
}



procedure CheckWellformed$$_module.__default.P21();
  free requires 66 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.P21();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall n#1: DatatypeType, m#1: DatatypeType :: 
    { _module.__default.add($LS($LZ), n#1, m#1) } 
    $Is(n#1, Tclass._module.Nat()) && $Is(m#1, Tclass._module.Nat())
       ==> $IsA#_module.Bool(_module.__default.leq($LS($LZ), n#1, _module.__default.add($LS($LZ), n#1, m#1)))
         && 
        _module.__default.add#canCall(n#1, m#1)
         && _module.__default.leq#canCall(n#1, _module.__default.add($LS($LZ), n#1, m#1)));
  free ensures (forall n#1: DatatypeType, m#1: DatatypeType :: 
    { _module.__default.add($LS($LZ), n#1, m#1) } 
    $Is(n#1, Tclass._module.Nat()) && $Is(m#1, Tclass._module.Nat())
       ==> _module.Bool#Equal(_module.__default.leq($LS($LZ), n#1, _module.__default.add($LS($LZ), n#1, m#1)), 
        #_module.Bool.True()));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.P21() returns ($_reverifyPost: bool);
  free requires 66 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall n#1: DatatypeType, m#1: DatatypeType :: 
    { _module.__default.add($LS($LZ), n#1, m#1) } 
    $Is(n#1, Tclass._module.Nat()) && $Is(m#1, Tclass._module.Nat())
       ==> $IsA#_module.Bool(_module.__default.leq($LS($LZ), n#1, _module.__default.add($LS($LZ), n#1, m#1)))
         && 
        _module.__default.add#canCall(n#1, m#1)
         && _module.__default.leq#canCall(n#1, _module.__default.add($LS($LZ), n#1, m#1)));
  ensures (forall n#1: DatatypeType, m#1: DatatypeType :: 
    { _module.__default.add($LS($LS($LZ)), n#1, m#1) } 
    $Is(n#1, Tclass._module.Nat()) && $Is(m#1, Tclass._module.Nat())
       ==> _module.Bool#Equal(_module.__default.leq($LS($LS($LZ)), n#1, _module.__default.add($LS($LS($LZ)), n#1, m#1)), 
        #_module.Bool.True()));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.P21() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: P21, Impl$$_module.__default.P21
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(408,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.P22();
  free requires 67 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.P22();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall a#1: DatatypeType, b#1: DatatypeType, c#1: DatatypeType :: 
    { _module.__default.max($LS($LZ), a#1, _module.__default.max($LS($LZ), b#1, c#1)) } 
      { _module.__default.max($LS($LZ), _module.__default.max($LS($LZ), a#1, b#1), c#1) } 
    $Is(a#1, Tclass._module.Nat())
         && $Is(b#1, Tclass._module.Nat())
         && $Is(c#1, Tclass._module.Nat())
       ==> $IsA#_module.Nat(_module.__default.max($LS($LZ), _module.__default.max($LS($LZ), a#1, b#1), c#1))
         && $IsA#_module.Nat(_module.__default.max($LS($LZ), a#1, _module.__default.max($LS($LZ), b#1, c#1)))
         && 
        _module.__default.max#canCall(a#1, b#1)
         && _module.__default.max#canCall(_module.__default.max($LS($LZ), a#1, b#1), c#1)
         && 
        _module.__default.max#canCall(b#1, c#1)
         && _module.__default.max#canCall(a#1, _module.__default.max($LS($LZ), b#1, c#1)));
  free ensures (forall a#1: DatatypeType, b#1: DatatypeType, c#1: DatatypeType :: 
    { _module.__default.max($LS($LZ), a#1, _module.__default.max($LS($LZ), b#1, c#1)) } 
      { _module.__default.max($LS($LZ), _module.__default.max($LS($LZ), a#1, b#1), c#1) } 
    $Is(a#1, Tclass._module.Nat())
         && $Is(b#1, Tclass._module.Nat())
         && $Is(c#1, Tclass._module.Nat())
       ==> _module.Nat#Equal(_module.__default.max($LS($LZ), _module.__default.max($LS($LZ), a#1, b#1), c#1), 
        _module.__default.max($LS($LZ), a#1, _module.__default.max($LS($LZ), b#1, c#1))));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.P22() returns ($_reverifyPost: bool);
  free requires 67 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall a#1: DatatypeType, b#1: DatatypeType, c#1: DatatypeType :: 
    { _module.__default.max($LS($LZ), a#1, _module.__default.max($LS($LZ), b#1, c#1)) } 
      { _module.__default.max($LS($LZ), _module.__default.max($LS($LZ), a#1, b#1), c#1) } 
    $Is(a#1, Tclass._module.Nat())
         && $Is(b#1, Tclass._module.Nat())
         && $Is(c#1, Tclass._module.Nat())
       ==> $IsA#_module.Nat(_module.__default.max($LS($LZ), _module.__default.max($LS($LZ), a#1, b#1), c#1))
         && $IsA#_module.Nat(_module.__default.max($LS($LZ), a#1, _module.__default.max($LS($LZ), b#1, c#1)))
         && 
        _module.__default.max#canCall(a#1, b#1)
         && _module.__default.max#canCall(_module.__default.max($LS($LZ), a#1, b#1), c#1)
         && 
        _module.__default.max#canCall(b#1, c#1)
         && _module.__default.max#canCall(a#1, _module.__default.max($LS($LZ), b#1, c#1)));
  ensures (forall a#1: DatatypeType, b#1: DatatypeType, c#1: DatatypeType :: 
    { _module.__default.max($LS($LS($LZ)), a#1, _module.__default.max($LS($LS($LZ)), b#1, c#1)) } 
      { _module.__default.max($LS($LS($LZ)), _module.__default.max($LS($LS($LZ)), a#1, b#1), c#1) } 
    $Is(a#1, Tclass._module.Nat())
         && $Is(b#1, Tclass._module.Nat())
         && $Is(c#1, Tclass._module.Nat())
       ==> _module.Nat#Equal(_module.__default.max($LS($LS($LZ)), _module.__default.max($LS($LS($LZ)), a#1, b#1), c#1), 
        _module.__default.max($LS($LS($LZ)), a#1, _module.__default.max($LS($LS($LZ)), b#1, c#1))));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.P22() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: P22, Impl$$_module.__default.P22
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(413,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.P23();
  free requires 68 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.P23();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall a#1: DatatypeType, b#1: DatatypeType :: 
    { _module.__default.max($LS($LZ), b#1, a#1) } 
      { _module.__default.max($LS($LZ), a#1, b#1) } 
    $Is(a#1, Tclass._module.Nat()) && $Is(b#1, Tclass._module.Nat())
       ==> $IsA#_module.Nat(_module.__default.max($LS($LZ), a#1, b#1))
         && $IsA#_module.Nat(_module.__default.max($LS($LZ), b#1, a#1))
         && 
        _module.__default.max#canCall(a#1, b#1)
         && _module.__default.max#canCall(b#1, a#1));
  free ensures (forall a#1: DatatypeType, b#1: DatatypeType :: 
    { _module.__default.max($LS($LZ), b#1, a#1) } 
      { _module.__default.max($LS($LZ), a#1, b#1) } 
    $Is(a#1, Tclass._module.Nat()) && $Is(b#1, Tclass._module.Nat())
       ==> _module.Nat#Equal(_module.__default.max($LS($LZ), a#1, b#1), 
        _module.__default.max($LS($LZ), b#1, a#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.P23() returns ($_reverifyPost: bool);
  free requires 68 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall a#1: DatatypeType, b#1: DatatypeType :: 
    { _module.__default.max($LS($LZ), b#1, a#1) } 
      { _module.__default.max($LS($LZ), a#1, b#1) } 
    $Is(a#1, Tclass._module.Nat()) && $Is(b#1, Tclass._module.Nat())
       ==> $IsA#_module.Nat(_module.__default.max($LS($LZ), a#1, b#1))
         && $IsA#_module.Nat(_module.__default.max($LS($LZ), b#1, a#1))
         && 
        _module.__default.max#canCall(a#1, b#1)
         && _module.__default.max#canCall(b#1, a#1));
  ensures (forall a#1: DatatypeType, b#1: DatatypeType :: 
    { _module.__default.max($LS($LS($LZ)), b#1, a#1) } 
      { _module.__default.max($LS($LS($LZ)), a#1, b#1) } 
    $Is(a#1, Tclass._module.Nat()) && $Is(b#1, Tclass._module.Nat())
       ==> _module.Nat#Equal(_module.__default.max($LS($LS($LZ)), a#1, b#1), 
        _module.__default.max($LS($LS($LZ)), b#1, a#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.P23() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: P23, Impl$$_module.__default.P23
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(418,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.P24();
  free requires 69 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.P24();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall a#1: DatatypeType, b#1: DatatypeType :: 
    { _module.__default.leq($LS($LZ), b#1, a#1) } 
      { _module.__default.max($LS($LZ), a#1, b#1) } 
    $Is(a#1, Tclass._module.Nat()) && $Is(b#1, Tclass._module.Nat())
       ==> $IsA#_module.Nat(_module.__default.max($LS($LZ), a#1, b#1))
         && $IsA#_module.Nat(a#1)
         && _module.__default.max#canCall(a#1, b#1)
         && 
        $IsA#_module.Bool(_module.__default.leq($LS($LZ), b#1, a#1))
         && _module.__default.leq#canCall(b#1, a#1));
  free ensures (forall a#1: DatatypeType, b#1: DatatypeType :: 
    { _module.__default.leq($LS($LZ), b#1, a#1) } 
      { _module.__default.max($LS($LZ), a#1, b#1) } 
    $Is(a#1, Tclass._module.Nat()) && $Is(b#1, Tclass._module.Nat())
       ==> (_module.Nat#Equal(_module.__default.max($LS($LZ), a#1, b#1), a#1)
         <==> _module.Bool#Equal(_module.__default.leq($LS($LZ), b#1, a#1), #_module.Bool.True())));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.P24() returns ($_reverifyPost: bool);
  free requires 69 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall a#1: DatatypeType, b#1: DatatypeType :: 
    { _module.__default.leq($LS($LZ), b#1, a#1) } 
      { _module.__default.max($LS($LZ), a#1, b#1) } 
    $Is(a#1, Tclass._module.Nat()) && $Is(b#1, Tclass._module.Nat())
       ==> $IsA#_module.Nat(_module.__default.max($LS($LZ), a#1, b#1))
         && $IsA#_module.Nat(a#1)
         && _module.__default.max#canCall(a#1, b#1)
         && 
        $IsA#_module.Bool(_module.__default.leq($LS($LZ), b#1, a#1))
         && _module.__default.leq#canCall(b#1, a#1));
  ensures (forall a#1: DatatypeType, b#1: DatatypeType :: 
    { _module.__default.leq($LS($LS($LZ)), b#1, a#1) } 
      { _module.__default.max($LS($LS($LZ)), a#1, b#1) } 
    $Is(a#1, Tclass._module.Nat()) && $Is(b#1, Tclass._module.Nat())
       ==> (_module.Nat#Equal(_module.__default.max($LS($LS($LZ)), a#1, b#1), a#1)
         <==> _module.Bool#Equal(_module.__default.leq($LS($LS($LZ)), b#1, a#1), #_module.Bool.True())));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.P24() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: P24, Impl$$_module.__default.P24
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(423,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.P25();
  free requires 70 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.P25();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall a#1: DatatypeType, b#1: DatatypeType :: 
    { _module.__default.leq($LS($LZ), a#1, b#1) } 
      { _module.__default.max($LS($LZ), a#1, b#1) } 
    $Is(a#1, Tclass._module.Nat()) && $Is(b#1, Tclass._module.Nat())
       ==> $IsA#_module.Nat(_module.__default.max($LS($LZ), a#1, b#1))
         && $IsA#_module.Nat(b#1)
         && _module.__default.max#canCall(a#1, b#1)
         && 
        $IsA#_module.Bool(_module.__default.leq($LS($LZ), a#1, b#1))
         && _module.__default.leq#canCall(a#1, b#1));
  free ensures (forall a#1: DatatypeType, b#1: DatatypeType :: 
    { _module.__default.leq($LS($LZ), a#1, b#1) } 
      { _module.__default.max($LS($LZ), a#1, b#1) } 
    $Is(a#1, Tclass._module.Nat()) && $Is(b#1, Tclass._module.Nat())
       ==> (_module.Nat#Equal(_module.__default.max($LS($LZ), a#1, b#1), b#1)
         <==> _module.Bool#Equal(_module.__default.leq($LS($LZ), a#1, b#1), #_module.Bool.True())));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.P25() returns ($_reverifyPost: bool);
  free requires 70 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall a#1: DatatypeType, b#1: DatatypeType :: 
    { _module.__default.leq($LS($LZ), a#1, b#1) } 
      { _module.__default.max($LS($LZ), a#1, b#1) } 
    $Is(a#1, Tclass._module.Nat()) && $Is(b#1, Tclass._module.Nat())
       ==> $IsA#_module.Nat(_module.__default.max($LS($LZ), a#1, b#1))
         && $IsA#_module.Nat(b#1)
         && _module.__default.max#canCall(a#1, b#1)
         && 
        $IsA#_module.Bool(_module.__default.leq($LS($LZ), a#1, b#1))
         && _module.__default.leq#canCall(a#1, b#1));
  ensures (forall a#1: DatatypeType, b#1: DatatypeType :: 
    { _module.__default.leq($LS($LS($LZ)), a#1, b#1) } 
      { _module.__default.max($LS($LS($LZ)), a#1, b#1) } 
    $Is(a#1, Tclass._module.Nat()) && $Is(b#1, Tclass._module.Nat())
       ==> (_module.Nat#Equal(_module.__default.max($LS($LS($LZ)), a#1, b#1), b#1)
         <==> _module.Bool#Equal(_module.__default.leq($LS($LS($LZ)), a#1, b#1), #_module.Bool.True())));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.P25() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: P25, Impl$$_module.__default.P25
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(428,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.P26();
  free requires 71 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.P26();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall x#1: DatatypeType, xs#1: DatatypeType, ys#1: DatatypeType :: 
    { _module.__default.mem($LS($LZ), x#1, _module.__default.concat($LS($LZ), xs#1, ys#1)) } 
    $Is(x#1, Tclass._module.Nat())
         && $Is(xs#1, Tclass._module.List())
         && $Is(ys#1, Tclass._module.List())
       ==> $IsA#_module.Bool(_module.__default.mem($LS($LZ), x#1, xs#1))
         && _module.__default.mem#canCall(x#1, xs#1)
         && (_module.Bool#Equal(_module.__default.mem($LS($LZ), x#1, xs#1), #_module.Bool.True())
           ==> $IsA#_module.Bool(_module.__default.mem($LS($LZ), x#1, _module.__default.concat($LS($LZ), xs#1, ys#1)))
             && 
            _module.__default.concat#canCall(xs#1, ys#1)
             && _module.__default.mem#canCall(x#1, _module.__default.concat($LS($LZ), xs#1, ys#1))));
  free ensures (forall x#1: DatatypeType, xs#1: DatatypeType, ys#1: DatatypeType :: 
    { _module.__default.mem($LS($LZ), x#1, _module.__default.concat($LS($LZ), xs#1, ys#1)) } 
    $Is(x#1, Tclass._module.Nat())
         && $Is(xs#1, Tclass._module.List())
         && $Is(ys#1, Tclass._module.List())
       ==> 
      _module.Bool#Equal(_module.__default.mem($LS($LZ), x#1, xs#1), #_module.Bool.True())
       ==> _module.Bool#Equal(_module.__default.mem($LS($LZ), x#1, _module.__default.concat($LS($LZ), xs#1, ys#1)), 
        #_module.Bool.True()));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.P26() returns ($_reverifyPost: bool);
  free requires 71 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall x#1: DatatypeType, xs#1: DatatypeType, ys#1: DatatypeType :: 
    { _module.__default.mem($LS($LZ), x#1, _module.__default.concat($LS($LZ), xs#1, ys#1)) } 
    $Is(x#1, Tclass._module.Nat())
         && $Is(xs#1, Tclass._module.List())
         && $Is(ys#1, Tclass._module.List())
       ==> $IsA#_module.Bool(_module.__default.mem($LS($LZ), x#1, xs#1))
         && _module.__default.mem#canCall(x#1, xs#1)
         && (_module.Bool#Equal(_module.__default.mem($LS($LZ), x#1, xs#1), #_module.Bool.True())
           ==> $IsA#_module.Bool(_module.__default.mem($LS($LZ), x#1, _module.__default.concat($LS($LZ), xs#1, ys#1)))
             && 
            _module.__default.concat#canCall(xs#1, ys#1)
             && _module.__default.mem#canCall(x#1, _module.__default.concat($LS($LZ), xs#1, ys#1))));
  ensures (forall x#1: DatatypeType, xs#1: DatatypeType, ys#1: DatatypeType :: 
    { _module.__default.mem($LS($LS($LZ)), x#1, _module.__default.concat($LS($LS($LZ)), xs#1, ys#1)) } 
    $Is(x#1, Tclass._module.Nat())
         && $Is(xs#1, Tclass._module.List())
         && $Is(ys#1, Tclass._module.List())
       ==> 
      _module.Bool#Equal(_module.__default.mem($LS($LS($LZ)), x#1, xs#1), #_module.Bool.True())
       ==> _module.Bool#Equal(_module.__default.mem($LS($LS($LZ)), x#1, _module.__default.concat($LS($LS($LZ)), xs#1, ys#1)), 
        #_module.Bool.True()));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.P26() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: P26, Impl$$_module.__default.P26
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(433,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.P27();
  free requires 72 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.P27();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall x#1: DatatypeType, xs#1: DatatypeType, ys#1: DatatypeType :: 
    { _module.__default.mem($LS($LZ), x#1, _module.__default.concat($LS($LZ), xs#1, ys#1)) } 
    $Is(x#1, Tclass._module.Nat())
         && $Is(xs#1, Tclass._module.List())
         && $Is(ys#1, Tclass._module.List())
       ==> $IsA#_module.Bool(_module.__default.mem($LS($LZ), x#1, ys#1))
         && _module.__default.mem#canCall(x#1, ys#1)
         && (_module.Bool#Equal(_module.__default.mem($LS($LZ), x#1, ys#1), #_module.Bool.True())
           ==> $IsA#_module.Bool(_module.__default.mem($LS($LZ), x#1, _module.__default.concat($LS($LZ), xs#1, ys#1)))
             && 
            _module.__default.concat#canCall(xs#1, ys#1)
             && _module.__default.mem#canCall(x#1, _module.__default.concat($LS($LZ), xs#1, ys#1))));
  free ensures (forall x#1: DatatypeType, xs#1: DatatypeType, ys#1: DatatypeType :: 
    { _module.__default.mem($LS($LZ), x#1, _module.__default.concat($LS($LZ), xs#1, ys#1)) } 
    $Is(x#1, Tclass._module.Nat())
         && $Is(xs#1, Tclass._module.List())
         && $Is(ys#1, Tclass._module.List())
       ==> 
      _module.Bool#Equal(_module.__default.mem($LS($LZ), x#1, ys#1), #_module.Bool.True())
       ==> _module.Bool#Equal(_module.__default.mem($LS($LZ), x#1, _module.__default.concat($LS($LZ), xs#1, ys#1)), 
        #_module.Bool.True()));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.P27() returns ($_reverifyPost: bool);
  free requires 72 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall x#1: DatatypeType, xs#1: DatatypeType, ys#1: DatatypeType :: 
    { _module.__default.mem($LS($LZ), x#1, _module.__default.concat($LS($LZ), xs#1, ys#1)) } 
    $Is(x#1, Tclass._module.Nat())
         && $Is(xs#1, Tclass._module.List())
         && $Is(ys#1, Tclass._module.List())
       ==> $IsA#_module.Bool(_module.__default.mem($LS($LZ), x#1, ys#1))
         && _module.__default.mem#canCall(x#1, ys#1)
         && (_module.Bool#Equal(_module.__default.mem($LS($LZ), x#1, ys#1), #_module.Bool.True())
           ==> $IsA#_module.Bool(_module.__default.mem($LS($LZ), x#1, _module.__default.concat($LS($LZ), xs#1, ys#1)))
             && 
            _module.__default.concat#canCall(xs#1, ys#1)
             && _module.__default.mem#canCall(x#1, _module.__default.concat($LS($LZ), xs#1, ys#1))));
  ensures (forall x#1: DatatypeType, xs#1: DatatypeType, ys#1: DatatypeType :: 
    { _module.__default.mem($LS($LS($LZ)), x#1, _module.__default.concat($LS($LS($LZ)), xs#1, ys#1)) } 
    $Is(x#1, Tclass._module.Nat())
         && $Is(xs#1, Tclass._module.List())
         && $Is(ys#1, Tclass._module.List())
       ==> 
      _module.Bool#Equal(_module.__default.mem($LS($LS($LZ)), x#1, ys#1), #_module.Bool.True())
       ==> _module.Bool#Equal(_module.__default.mem($LS($LS($LZ)), x#1, _module.__default.concat($LS($LS($LZ)), xs#1, ys#1)), 
        #_module.Bool.True()));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.P27() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: P27, Impl$$_module.__default.P27
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(438,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.P28();
  free requires 73 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.P28();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall x#1: DatatypeType, xs#1: DatatypeType :: 
    { _module.__default.concat($LS($LZ), xs#1, #_module.List.Cons(x#1, #_module.List.Nil())) } 
    $Is(x#1, Tclass._module.Nat()) && $Is(xs#1, Tclass._module.List())
       ==> $IsA#_module.Bool(_module.__default.mem($LS($LZ), 
            x#1, 
            _module.__default.concat($LS($LZ), xs#1, #_module.List.Cons(x#1, Lit(#_module.List.Nil())))))
         && 
        _module.__default.concat#canCall(xs#1, #_module.List.Cons(x#1, Lit(#_module.List.Nil())))
         && _module.__default.mem#canCall(x#1, 
          _module.__default.concat($LS($LZ), xs#1, #_module.List.Cons(x#1, Lit(#_module.List.Nil())))));
  free ensures (forall x#1: DatatypeType, xs#1: DatatypeType :: 
    { _module.__default.concat($LS($LZ), xs#1, #_module.List.Cons(x#1, #_module.List.Nil())) } 
    $Is(x#1, Tclass._module.Nat()) && $Is(xs#1, Tclass._module.List())
       ==> _module.Bool#Equal(_module.__default.mem($LS($LZ), 
          x#1, 
          _module.__default.concat($LS($LZ), xs#1, #_module.List.Cons(x#1, Lit(#_module.List.Nil())))), 
        #_module.Bool.True()));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.P28() returns ($_reverifyPost: bool);
  free requires 73 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall x#1: DatatypeType, xs#1: DatatypeType :: 
    { _module.__default.concat($LS($LZ), xs#1, #_module.List.Cons(x#1, #_module.List.Nil())) } 
    $Is(x#1, Tclass._module.Nat()) && $Is(xs#1, Tclass._module.List())
       ==> $IsA#_module.Bool(_module.__default.mem($LS($LZ), 
            x#1, 
            _module.__default.concat($LS($LZ), xs#1, #_module.List.Cons(x#1, Lit(#_module.List.Nil())))))
         && 
        _module.__default.concat#canCall(xs#1, #_module.List.Cons(x#1, Lit(#_module.List.Nil())))
         && _module.__default.mem#canCall(x#1, 
          _module.__default.concat($LS($LZ), xs#1, #_module.List.Cons(x#1, Lit(#_module.List.Nil())))));
  ensures (forall x#1: DatatypeType, xs#1: DatatypeType :: 
    { _module.__default.concat($LS($LS($LZ)), xs#1, #_module.List.Cons(x#1, #_module.List.Nil())) } 
    $Is(x#1, Tclass._module.Nat()) && $Is(xs#1, Tclass._module.List())
       ==> _module.Bool#Equal(_module.__default.mem($LS($LS($LZ)), 
          x#1, 
          _module.__default.concat($LS($LS($LZ)), xs#1, #_module.List.Cons(x#1, Lit(#_module.List.Nil())))), 
        #_module.Bool.True()));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.P28() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: P28, Impl$$_module.__default.P28
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(443,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.P29();
  free requires 74 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.P29();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall x#1: DatatypeType, xs#1: DatatypeType :: 
    { _module.__default.ins1($LS($LZ), x#1, xs#1) } 
    $Is(x#1, Tclass._module.Nat()) && $Is(xs#1, Tclass._module.List())
       ==> $IsA#_module.Bool(_module.__default.mem($LS($LZ), x#1, _module.__default.ins1($LS($LZ), x#1, xs#1)))
         && 
        _module.__default.ins1#canCall(x#1, xs#1)
         && _module.__default.mem#canCall(x#1, _module.__default.ins1($LS($LZ), x#1, xs#1)));
  free ensures (forall x#1: DatatypeType, xs#1: DatatypeType :: 
    { _module.__default.ins1($LS($LZ), x#1, xs#1) } 
    $Is(x#1, Tclass._module.Nat()) && $Is(xs#1, Tclass._module.List())
       ==> _module.Bool#Equal(_module.__default.mem($LS($LZ), x#1, _module.__default.ins1($LS($LZ), x#1, xs#1)), 
        #_module.Bool.True()));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.P29() returns ($_reverifyPost: bool);
  free requires 74 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall x#1: DatatypeType, xs#1: DatatypeType :: 
    { _module.__default.ins1($LS($LZ), x#1, xs#1) } 
    $Is(x#1, Tclass._module.Nat()) && $Is(xs#1, Tclass._module.List())
       ==> $IsA#_module.Bool(_module.__default.mem($LS($LZ), x#1, _module.__default.ins1($LS($LZ), x#1, xs#1)))
         && 
        _module.__default.ins1#canCall(x#1, xs#1)
         && _module.__default.mem#canCall(x#1, _module.__default.ins1($LS($LZ), x#1, xs#1)));
  ensures (forall x#1: DatatypeType, xs#1: DatatypeType :: 
    { _module.__default.ins1($LS($LS($LZ)), x#1, xs#1) } 
    $Is(x#1, Tclass._module.Nat()) && $Is(xs#1, Tclass._module.List())
       ==> _module.Bool#Equal(_module.__default.mem($LS($LS($LZ)), x#1, _module.__default.ins1($LS($LS($LZ)), x#1, xs#1)), 
        #_module.Bool.True()));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.P29() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: P29, Impl$$_module.__default.P29
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(448,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.P30();
  free requires 75 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.P30();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall x#1: DatatypeType, xs#1: DatatypeType :: 
    { _module.__default.ins($LS($LZ), x#1, xs#1) } 
    $Is(x#1, Tclass._module.Nat()) && $Is(xs#1, Tclass._module.List())
       ==> $IsA#_module.Bool(_module.__default.mem($LS($LZ), x#1, _module.__default.ins($LS($LZ), x#1, xs#1)))
         && 
        _module.__default.ins#canCall(x#1, xs#1)
         && _module.__default.mem#canCall(x#1, _module.__default.ins($LS($LZ), x#1, xs#1)));
  free ensures (forall x#1: DatatypeType, xs#1: DatatypeType :: 
    { _module.__default.ins($LS($LZ), x#1, xs#1) } 
    $Is(x#1, Tclass._module.Nat()) && $Is(xs#1, Tclass._module.List())
       ==> _module.Bool#Equal(_module.__default.mem($LS($LZ), x#1, _module.__default.ins($LS($LZ), x#1, xs#1)), 
        #_module.Bool.True()));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.P30() returns ($_reverifyPost: bool);
  free requires 75 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall x#1: DatatypeType, xs#1: DatatypeType :: 
    { _module.__default.ins($LS($LZ), x#1, xs#1) } 
    $Is(x#1, Tclass._module.Nat()) && $Is(xs#1, Tclass._module.List())
       ==> $IsA#_module.Bool(_module.__default.mem($LS($LZ), x#1, _module.__default.ins($LS($LZ), x#1, xs#1)))
         && 
        _module.__default.ins#canCall(x#1, xs#1)
         && _module.__default.mem#canCall(x#1, _module.__default.ins($LS($LZ), x#1, xs#1)));
  ensures (forall x#1: DatatypeType, xs#1: DatatypeType :: 
    { _module.__default.ins($LS($LS($LZ)), x#1, xs#1) } 
    $Is(x#1, Tclass._module.Nat()) && $Is(xs#1, Tclass._module.List())
       ==> _module.Bool#Equal(_module.__default.mem($LS($LS($LZ)), x#1, _module.__default.ins($LS($LS($LZ)), x#1, xs#1)), 
        #_module.Bool.True()));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.P30() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: P30, Impl$$_module.__default.P30
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(453,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.P31();
  free requires 76 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.P31();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall a#1: DatatypeType, b#1: DatatypeType, c#1: DatatypeType :: 
    { _module.__default.min($LS($LZ), a#1, _module.__default.min($LS($LZ), b#1, c#1)) } 
      { _module.__default.min($LS($LZ), _module.__default.min($LS($LZ), a#1, b#1), c#1) } 
    $Is(a#1, Tclass._module.Nat())
         && $Is(b#1, Tclass._module.Nat())
         && $Is(c#1, Tclass._module.Nat())
       ==> $IsA#_module.Nat(_module.__default.min($LS($LZ), _module.__default.min($LS($LZ), a#1, b#1), c#1))
         && $IsA#_module.Nat(_module.__default.min($LS($LZ), a#1, _module.__default.min($LS($LZ), b#1, c#1)))
         && 
        _module.__default.min#canCall(a#1, b#1)
         && _module.__default.min#canCall(_module.__default.min($LS($LZ), a#1, b#1), c#1)
         && 
        _module.__default.min#canCall(b#1, c#1)
         && _module.__default.min#canCall(a#1, _module.__default.min($LS($LZ), b#1, c#1)));
  free ensures (forall a#1: DatatypeType, b#1: DatatypeType, c#1: DatatypeType :: 
    { _module.__default.min($LS($LZ), a#1, _module.__default.min($LS($LZ), b#1, c#1)) } 
      { _module.__default.min($LS($LZ), _module.__default.min($LS($LZ), a#1, b#1), c#1) } 
    $Is(a#1, Tclass._module.Nat())
         && $Is(b#1, Tclass._module.Nat())
         && $Is(c#1, Tclass._module.Nat())
       ==> _module.Nat#Equal(_module.__default.min($LS($LZ), _module.__default.min($LS($LZ), a#1, b#1), c#1), 
        _module.__default.min($LS($LZ), a#1, _module.__default.min($LS($LZ), b#1, c#1))));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.P31() returns ($_reverifyPost: bool);
  free requires 76 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall a#1: DatatypeType, b#1: DatatypeType, c#1: DatatypeType :: 
    { _module.__default.min($LS($LZ), a#1, _module.__default.min($LS($LZ), b#1, c#1)) } 
      { _module.__default.min($LS($LZ), _module.__default.min($LS($LZ), a#1, b#1), c#1) } 
    $Is(a#1, Tclass._module.Nat())
         && $Is(b#1, Tclass._module.Nat())
         && $Is(c#1, Tclass._module.Nat())
       ==> $IsA#_module.Nat(_module.__default.min($LS($LZ), _module.__default.min($LS($LZ), a#1, b#1), c#1))
         && $IsA#_module.Nat(_module.__default.min($LS($LZ), a#1, _module.__default.min($LS($LZ), b#1, c#1)))
         && 
        _module.__default.min#canCall(a#1, b#1)
         && _module.__default.min#canCall(_module.__default.min($LS($LZ), a#1, b#1), c#1)
         && 
        _module.__default.min#canCall(b#1, c#1)
         && _module.__default.min#canCall(a#1, _module.__default.min($LS($LZ), b#1, c#1)));
  ensures (forall a#1: DatatypeType, b#1: DatatypeType, c#1: DatatypeType :: 
    { _module.__default.min($LS($LS($LZ)), a#1, _module.__default.min($LS($LS($LZ)), b#1, c#1)) } 
      { _module.__default.min($LS($LS($LZ)), _module.__default.min($LS($LS($LZ)), a#1, b#1), c#1) } 
    $Is(a#1, Tclass._module.Nat())
         && $Is(b#1, Tclass._module.Nat())
         && $Is(c#1, Tclass._module.Nat())
       ==> _module.Nat#Equal(_module.__default.min($LS($LS($LZ)), _module.__default.min($LS($LS($LZ)), a#1, b#1), c#1), 
        _module.__default.min($LS($LS($LZ)), a#1, _module.__default.min($LS($LS($LZ)), b#1, c#1))));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.P31() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: P31, Impl$$_module.__default.P31
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(458,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.P32();
  free requires 77 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.P32();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall a#1: DatatypeType, b#1: DatatypeType :: 
    { _module.__default.min($LS($LZ), b#1, a#1) } 
      { _module.__default.min($LS($LZ), a#1, b#1) } 
    $Is(a#1, Tclass._module.Nat()) && $Is(b#1, Tclass._module.Nat())
       ==> $IsA#_module.Nat(_module.__default.min($LS($LZ), a#1, b#1))
         && $IsA#_module.Nat(_module.__default.min($LS($LZ), b#1, a#1))
         && 
        _module.__default.min#canCall(a#1, b#1)
         && _module.__default.min#canCall(b#1, a#1));
  free ensures (forall a#1: DatatypeType, b#1: DatatypeType :: 
    { _module.__default.min($LS($LZ), b#1, a#1) } 
      { _module.__default.min($LS($LZ), a#1, b#1) } 
    $Is(a#1, Tclass._module.Nat()) && $Is(b#1, Tclass._module.Nat())
       ==> _module.Nat#Equal(_module.__default.min($LS($LZ), a#1, b#1), 
        _module.__default.min($LS($LZ), b#1, a#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.P32() returns ($_reverifyPost: bool);
  free requires 77 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall a#1: DatatypeType, b#1: DatatypeType :: 
    { _module.__default.min($LS($LZ), b#1, a#1) } 
      { _module.__default.min($LS($LZ), a#1, b#1) } 
    $Is(a#1, Tclass._module.Nat()) && $Is(b#1, Tclass._module.Nat())
       ==> $IsA#_module.Nat(_module.__default.min($LS($LZ), a#1, b#1))
         && $IsA#_module.Nat(_module.__default.min($LS($LZ), b#1, a#1))
         && 
        _module.__default.min#canCall(a#1, b#1)
         && _module.__default.min#canCall(b#1, a#1));
  ensures (forall a#1: DatatypeType, b#1: DatatypeType :: 
    { _module.__default.min($LS($LS($LZ)), b#1, a#1) } 
      { _module.__default.min($LS($LS($LZ)), a#1, b#1) } 
    $Is(a#1, Tclass._module.Nat()) && $Is(b#1, Tclass._module.Nat())
       ==> _module.Nat#Equal(_module.__default.min($LS($LS($LZ)), a#1, b#1), 
        _module.__default.min($LS($LS($LZ)), b#1, a#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.P32() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: P32, Impl$$_module.__default.P32
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(463,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.P33();
  free requires 78 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.P33();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall a#1: DatatypeType, b#1: DatatypeType :: 
    { _module.__default.leq($LS($LZ), a#1, b#1) } 
      { _module.__default.min($LS($LZ), a#1, b#1) } 
    $Is(a#1, Tclass._module.Nat()) && $Is(b#1, Tclass._module.Nat())
       ==> $IsA#_module.Nat(_module.__default.min($LS($LZ), a#1, b#1))
         && $IsA#_module.Nat(a#1)
         && _module.__default.min#canCall(a#1, b#1)
         && 
        $IsA#_module.Bool(_module.__default.leq($LS($LZ), a#1, b#1))
         && _module.__default.leq#canCall(a#1, b#1));
  free ensures (forall a#1: DatatypeType, b#1: DatatypeType :: 
    { _module.__default.leq($LS($LZ), a#1, b#1) } 
      { _module.__default.min($LS($LZ), a#1, b#1) } 
    $Is(a#1, Tclass._module.Nat()) && $Is(b#1, Tclass._module.Nat())
       ==> (_module.Nat#Equal(_module.__default.min($LS($LZ), a#1, b#1), a#1)
         <==> _module.Bool#Equal(_module.__default.leq($LS($LZ), a#1, b#1), #_module.Bool.True())));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.P33() returns ($_reverifyPost: bool);
  free requires 78 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall a#1: DatatypeType, b#1: DatatypeType :: 
    { _module.__default.leq($LS($LZ), a#1, b#1) } 
      { _module.__default.min($LS($LZ), a#1, b#1) } 
    $Is(a#1, Tclass._module.Nat()) && $Is(b#1, Tclass._module.Nat())
       ==> $IsA#_module.Nat(_module.__default.min($LS($LZ), a#1, b#1))
         && $IsA#_module.Nat(a#1)
         && _module.__default.min#canCall(a#1, b#1)
         && 
        $IsA#_module.Bool(_module.__default.leq($LS($LZ), a#1, b#1))
         && _module.__default.leq#canCall(a#1, b#1));
  ensures (forall a#1: DatatypeType, b#1: DatatypeType :: 
    { _module.__default.leq($LS($LS($LZ)), a#1, b#1) } 
      { _module.__default.min($LS($LS($LZ)), a#1, b#1) } 
    $Is(a#1, Tclass._module.Nat()) && $Is(b#1, Tclass._module.Nat())
       ==> (_module.Nat#Equal(_module.__default.min($LS($LS($LZ)), a#1, b#1), a#1)
         <==> _module.Bool#Equal(_module.__default.leq($LS($LS($LZ)), a#1, b#1), #_module.Bool.True())));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.P33() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: P33, Impl$$_module.__default.P33
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(468,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.P34();
  free requires 79 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.P34();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall a#1: DatatypeType, b#1: DatatypeType :: 
    { _module.__default.leq($LS($LZ), b#1, a#1) } 
      { _module.__default.min($LS($LZ), a#1, b#1) } 
    $Is(a#1, Tclass._module.Nat()) && $Is(b#1, Tclass._module.Nat())
       ==> $IsA#_module.Nat(_module.__default.min($LS($LZ), a#1, b#1))
         && $IsA#_module.Nat(b#1)
         && _module.__default.min#canCall(a#1, b#1)
         && 
        $IsA#_module.Bool(_module.__default.leq($LS($LZ), b#1, a#1))
         && _module.__default.leq#canCall(b#1, a#1));
  free ensures (forall a#1: DatatypeType, b#1: DatatypeType :: 
    { _module.__default.leq($LS($LZ), b#1, a#1) } 
      { _module.__default.min($LS($LZ), a#1, b#1) } 
    $Is(a#1, Tclass._module.Nat()) && $Is(b#1, Tclass._module.Nat())
       ==> (_module.Nat#Equal(_module.__default.min($LS($LZ), a#1, b#1), b#1)
         <==> _module.Bool#Equal(_module.__default.leq($LS($LZ), b#1, a#1), #_module.Bool.True())));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.P34() returns ($_reverifyPost: bool);
  free requires 79 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall a#1: DatatypeType, b#1: DatatypeType :: 
    { _module.__default.leq($LS($LZ), b#1, a#1) } 
      { _module.__default.min($LS($LZ), a#1, b#1) } 
    $Is(a#1, Tclass._module.Nat()) && $Is(b#1, Tclass._module.Nat())
       ==> $IsA#_module.Nat(_module.__default.min($LS($LZ), a#1, b#1))
         && $IsA#_module.Nat(b#1)
         && _module.__default.min#canCall(a#1, b#1)
         && 
        $IsA#_module.Bool(_module.__default.leq($LS($LZ), b#1, a#1))
         && _module.__default.leq#canCall(b#1, a#1));
  ensures (forall a#1: DatatypeType, b#1: DatatypeType :: 
    { _module.__default.leq($LS($LS($LZ)), b#1, a#1) } 
      { _module.__default.min($LS($LS($LZ)), a#1, b#1) } 
    $Is(a#1, Tclass._module.Nat()) && $Is(b#1, Tclass._module.Nat())
       ==> (_module.Nat#Equal(_module.__default.min($LS($LS($LZ)), a#1, b#1), b#1)
         <==> _module.Bool#Equal(_module.__default.leq($LS($LS($LZ)), b#1, a#1), #_module.Bool.True())));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.P34() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: P34, Impl$$_module.__default.P34
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(473,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.P35();
  free requires 80 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.P35();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall xs#1: DatatypeType :: 
    { _module.__default.dropWhileAlways($LS($LZ), _module.__default.AlwaysFalseFunction(), xs#1) } 
    $Is(xs#1, Tclass._module.List())
       ==> $IsA#_module.List(_module.__default.dropWhileAlways($LS($LZ), Lit(_module.__default.AlwaysFalseFunction()), xs#1))
         && $IsA#_module.List(xs#1)
         && 
        _module.__default.AlwaysFalseFunction#canCall()
         && _module.__default.dropWhileAlways#canCall(Lit(_module.__default.AlwaysFalseFunction()), xs#1));
  free ensures (forall xs#1: DatatypeType :: 
    { _module.__default.dropWhileAlways($LS($LZ), _module.__default.AlwaysFalseFunction(), xs#1) } 
    $Is(xs#1, Tclass._module.List())
       ==> _module.List#Equal(_module.__default.dropWhileAlways($LS($LZ), Lit(_module.__default.AlwaysFalseFunction()), xs#1), 
        xs#1));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.P35() returns ($_reverifyPost: bool);
  free requires 80 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall xs#1: DatatypeType :: 
    { _module.__default.dropWhileAlways($LS($LZ), _module.__default.AlwaysFalseFunction(), xs#1) } 
    $Is(xs#1, Tclass._module.List())
       ==> $IsA#_module.List(_module.__default.dropWhileAlways($LS($LZ), Lit(_module.__default.AlwaysFalseFunction()), xs#1))
         && $IsA#_module.List(xs#1)
         && 
        _module.__default.AlwaysFalseFunction#canCall()
         && _module.__default.dropWhileAlways#canCall(Lit(_module.__default.AlwaysFalseFunction()), xs#1));
  ensures (forall xs#1: DatatypeType :: 
    { _module.__default.dropWhileAlways($LS($LS($LZ)), _module.__default.AlwaysFalseFunction(), xs#1) } 
    $Is(xs#1, Tclass._module.List())
       ==> _module.List#Equal(_module.__default.dropWhileAlways($LS($LS($LZ)), Lit(_module.__default.AlwaysFalseFunction()), xs#1), 
        xs#1));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.P35() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: P35, Impl$$_module.__default.P35
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(478,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.P36();
  free requires 81 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.P36();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall xs#1: DatatypeType :: 
    { _module.__default.takeWhileAlways($LS($LZ), _module.__default.AlwaysTrueFunction(), xs#1) } 
    $Is(xs#1, Tclass._module.List())
       ==> $IsA#_module.List(_module.__default.takeWhileAlways($LS($LZ), Lit(_module.__default.AlwaysTrueFunction()), xs#1))
         && $IsA#_module.List(xs#1)
         && 
        _module.__default.AlwaysTrueFunction#canCall()
         && _module.__default.takeWhileAlways#canCall(Lit(_module.__default.AlwaysTrueFunction()), xs#1));
  free ensures (forall xs#1: DatatypeType :: 
    { _module.__default.takeWhileAlways($LS($LZ), _module.__default.AlwaysTrueFunction(), xs#1) } 
    $Is(xs#1, Tclass._module.List())
       ==> _module.List#Equal(_module.__default.takeWhileAlways($LS($LZ), Lit(_module.__default.AlwaysTrueFunction()), xs#1), 
        xs#1));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.P36() returns ($_reverifyPost: bool);
  free requires 81 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall xs#1: DatatypeType :: 
    { _module.__default.takeWhileAlways($LS($LZ), _module.__default.AlwaysTrueFunction(), xs#1) } 
    $Is(xs#1, Tclass._module.List())
       ==> $IsA#_module.List(_module.__default.takeWhileAlways($LS($LZ), Lit(_module.__default.AlwaysTrueFunction()), xs#1))
         && $IsA#_module.List(xs#1)
         && 
        _module.__default.AlwaysTrueFunction#canCall()
         && _module.__default.takeWhileAlways#canCall(Lit(_module.__default.AlwaysTrueFunction()), xs#1));
  ensures (forall xs#1: DatatypeType :: 
    { _module.__default.takeWhileAlways($LS($LS($LZ)), _module.__default.AlwaysTrueFunction(), xs#1) } 
    $Is(xs#1, Tclass._module.List())
       ==> _module.List#Equal(_module.__default.takeWhileAlways($LS($LS($LZ)), Lit(_module.__default.AlwaysTrueFunction()), xs#1), 
        xs#1));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.P36() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: P36, Impl$$_module.__default.P36
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(483,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.P37();
  free requires 82 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.P37();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall x#1: DatatypeType, xs#1: DatatypeType :: 
    { _module.__default.delete($LS($LZ), x#1, xs#1) } 
    $Is(x#1, Tclass._module.Nat()) && $Is(xs#1, Tclass._module.List())
       ==> $IsA#_module.Bool(_module.__default.not(_module.__default.mem($LS($LZ), x#1, _module.__default.delete($LS($LZ), x#1, xs#1))))
         && 
        _module.__default.delete#canCall(x#1, xs#1)
         && _module.__default.mem#canCall(x#1, _module.__default.delete($LS($LZ), x#1, xs#1))
         && _module.__default.not#canCall(_module.__default.mem($LS($LZ), x#1, _module.__default.delete($LS($LZ), x#1, xs#1))));
  free ensures (forall x#1: DatatypeType, xs#1: DatatypeType :: 
    { _module.__default.delete($LS($LZ), x#1, xs#1) } 
    $Is(x#1, Tclass._module.Nat()) && $Is(xs#1, Tclass._module.List())
       ==> _module.Bool#Equal(_module.__default.not(_module.__default.mem($LS($LZ), x#1, _module.__default.delete($LS($LZ), x#1, xs#1))), 
        #_module.Bool.True()));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.P37() returns ($_reverifyPost: bool);
  free requires 82 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall x#1: DatatypeType, xs#1: DatatypeType :: 
    { _module.__default.delete($LS($LZ), x#1, xs#1) } 
    $Is(x#1, Tclass._module.Nat()) && $Is(xs#1, Tclass._module.List())
       ==> $IsA#_module.Bool(_module.__default.not(_module.__default.mem($LS($LZ), x#1, _module.__default.delete($LS($LZ), x#1, xs#1))))
         && 
        _module.__default.delete#canCall(x#1, xs#1)
         && _module.__default.mem#canCall(x#1, _module.__default.delete($LS($LZ), x#1, xs#1))
         && _module.__default.not#canCall(_module.__default.mem($LS($LZ), x#1, _module.__default.delete($LS($LZ), x#1, xs#1))));
  ensures (forall x#1: DatatypeType, xs#1: DatatypeType :: 
    { _module.__default.delete($LS($LS($LZ)), x#1, xs#1) } 
    $Is(x#1, Tclass._module.Nat()) && $Is(xs#1, Tclass._module.List())
       ==> _module.Bool#Equal(_module.__default.not(_module.__default.mem($LS($LS($LZ)), x#1, _module.__default.delete($LS($LS($LZ)), x#1, xs#1))), 
        #_module.Bool.True()));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.P37() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: P37, Impl$$_module.__default.P37
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(488,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.P38();
  free requires 83 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.P38();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall n#1: DatatypeType, xs#1: DatatypeType :: 
    { #_module.Nat.Suc(_module.__default.count($LS($LZ), n#1, xs#1)) } 
      { _module.__default.concat($LS($LZ), xs#1, #_module.List.Cons(n#1, #_module.List.Nil())) } 
    $Is(n#1, Tclass._module.Nat()) && $Is(xs#1, Tclass._module.List())
       ==> $IsA#_module.Nat(_module.__default.count($LS($LZ), 
            n#1, 
            _module.__default.concat($LS($LZ), xs#1, #_module.List.Cons(n#1, Lit(#_module.List.Nil())))))
         && 
        _module.__default.concat#canCall(xs#1, #_module.List.Cons(n#1, Lit(#_module.List.Nil())))
         && _module.__default.count#canCall(n#1, 
          _module.__default.concat($LS($LZ), xs#1, #_module.List.Cons(n#1, Lit(#_module.List.Nil()))))
         && _module.__default.count#canCall(n#1, xs#1));
  free ensures (forall n#1: DatatypeType, xs#1: DatatypeType :: 
    { #_module.Nat.Suc(_module.__default.count($LS($LZ), n#1, xs#1)) } 
      { _module.__default.concat($LS($LZ), xs#1, #_module.List.Cons(n#1, #_module.List.Nil())) } 
    $Is(n#1, Tclass._module.Nat()) && $Is(xs#1, Tclass._module.List())
       ==> _module.Nat#Equal(_module.__default.count($LS($LZ), 
          n#1, 
          _module.__default.concat($LS($LZ), xs#1, #_module.List.Cons(n#1, Lit(#_module.List.Nil())))), 
        #_module.Nat.Suc(_module.__default.count($LS($LZ), n#1, xs#1))));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.P38() returns ($_reverifyPost: bool);
  free requires 83 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall n#1: DatatypeType, xs#1: DatatypeType :: 
    { #_module.Nat.Suc(_module.__default.count($LS($LZ), n#1, xs#1)) } 
      { _module.__default.concat($LS($LZ), xs#1, #_module.List.Cons(n#1, #_module.List.Nil())) } 
    $Is(n#1, Tclass._module.Nat()) && $Is(xs#1, Tclass._module.List())
       ==> $IsA#_module.Nat(_module.__default.count($LS($LZ), 
            n#1, 
            _module.__default.concat($LS($LZ), xs#1, #_module.List.Cons(n#1, Lit(#_module.List.Nil())))))
         && 
        _module.__default.concat#canCall(xs#1, #_module.List.Cons(n#1, Lit(#_module.List.Nil())))
         && _module.__default.count#canCall(n#1, 
          _module.__default.concat($LS($LZ), xs#1, #_module.List.Cons(n#1, Lit(#_module.List.Nil()))))
         && _module.__default.count#canCall(n#1, xs#1));
  ensures (forall n#1: DatatypeType, xs#1: DatatypeType :: 
    { #_module.Nat.Suc(_module.__default.count($LS($LS($LZ)), n#1, xs#1)) } 
      { _module.__default.concat($LS($LS($LZ)), xs#1, #_module.List.Cons(n#1, #_module.List.Nil())) } 
    $Is(n#1, Tclass._module.Nat()) && $Is(xs#1, Tclass._module.List())
       ==> _module.Nat#Equal(_module.__default.count($LS($LS($LZ)), 
          n#1, 
          _module.__default.concat($LS($LS($LZ)), xs#1, #_module.List.Cons(n#1, Lit(#_module.List.Nil())))), 
        #_module.Nat.Suc(_module.__default.count($LS($LS($LZ)), n#1, xs#1))));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.P38() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: P38, Impl$$_module.__default.P38
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(493,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.P39();
  free requires 84 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.P39();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall n#1: DatatypeType, x#1: DatatypeType, xs#1: DatatypeType :: 
    { _module.__default.count($LS($LZ), n#1, #_module.List.Cons(x#1, xs#1)) } 
      { _module.__default.add($LS($LZ), 
        _module.__default.count($LS($LZ), n#1, #_module.List.Cons(x#1, #_module.List.Nil())), 
        _module.__default.count($LS($LZ), n#1, xs#1)) } 
    $Is(n#1, Tclass._module.Nat())
         && $Is(x#1, Tclass._module.Nat())
         && $Is(xs#1, Tclass._module.List())
       ==> $IsA#_module.Nat(_module.__default.add($LS($LZ), 
            _module.__default.count($LS($LZ), n#1, #_module.List.Cons(x#1, Lit(#_module.List.Nil()))), 
            _module.__default.count($LS($LZ), n#1, xs#1)))
         && $IsA#_module.Nat(_module.__default.count($LS($LZ), n#1, #_module.List.Cons(x#1, xs#1)))
         && 
        _module.__default.count#canCall(n#1, #_module.List.Cons(x#1, Lit(#_module.List.Nil())))
         && _module.__default.count#canCall(n#1, xs#1)
         && _module.__default.add#canCall(_module.__default.count($LS($LZ), n#1, #_module.List.Cons(x#1, Lit(#_module.List.Nil()))), 
          _module.__default.count($LS($LZ), n#1, xs#1))
         && _module.__default.count#canCall(n#1, #_module.List.Cons(x#1, xs#1)));
  free ensures (forall n#1: DatatypeType, x#1: DatatypeType, xs#1: DatatypeType :: 
    { _module.__default.count($LS($LZ), n#1, #_module.List.Cons(x#1, xs#1)) } 
      { _module.__default.add($LS($LZ), 
        _module.__default.count($LS($LZ), n#1, #_module.List.Cons(x#1, #_module.List.Nil())), 
        _module.__default.count($LS($LZ), n#1, xs#1)) } 
    $Is(n#1, Tclass._module.Nat())
         && $Is(x#1, Tclass._module.Nat())
         && $Is(xs#1, Tclass._module.List())
       ==> _module.Nat#Equal(_module.__default.add($LS($LZ), 
          _module.__default.count($LS($LZ), n#1, #_module.List.Cons(x#1, Lit(#_module.List.Nil()))), 
          _module.__default.count($LS($LZ), n#1, xs#1)), 
        _module.__default.count($LS($LZ), n#1, #_module.List.Cons(x#1, xs#1))));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.P39() returns ($_reverifyPost: bool);
  free requires 84 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall n#1: DatatypeType, x#1: DatatypeType, xs#1: DatatypeType :: 
    { _module.__default.count($LS($LZ), n#1, #_module.List.Cons(x#1, xs#1)) } 
      { _module.__default.add($LS($LZ), 
        _module.__default.count($LS($LZ), n#1, #_module.List.Cons(x#1, #_module.List.Nil())), 
        _module.__default.count($LS($LZ), n#1, xs#1)) } 
    $Is(n#1, Tclass._module.Nat())
         && $Is(x#1, Tclass._module.Nat())
         && $Is(xs#1, Tclass._module.List())
       ==> $IsA#_module.Nat(_module.__default.add($LS($LZ), 
            _module.__default.count($LS($LZ), n#1, #_module.List.Cons(x#1, Lit(#_module.List.Nil()))), 
            _module.__default.count($LS($LZ), n#1, xs#1)))
         && $IsA#_module.Nat(_module.__default.count($LS($LZ), n#1, #_module.List.Cons(x#1, xs#1)))
         && 
        _module.__default.count#canCall(n#1, #_module.List.Cons(x#1, Lit(#_module.List.Nil())))
         && _module.__default.count#canCall(n#1, xs#1)
         && _module.__default.add#canCall(_module.__default.count($LS($LZ), n#1, #_module.List.Cons(x#1, Lit(#_module.List.Nil()))), 
          _module.__default.count($LS($LZ), n#1, xs#1))
         && _module.__default.count#canCall(n#1, #_module.List.Cons(x#1, xs#1)));
  ensures (forall n#1: DatatypeType, x#1: DatatypeType, xs#1: DatatypeType :: 
    { _module.__default.count($LS($LS($LZ)), n#1, #_module.List.Cons(x#1, xs#1)) } 
      { _module.__default.add($LS($LS($LZ)), 
        _module.__default.count($LS($LS($LZ)), n#1, #_module.List.Cons(x#1, #_module.List.Nil())), 
        _module.__default.count($LS($LS($LZ)), n#1, xs#1)) } 
    $Is(n#1, Tclass._module.Nat())
         && $Is(x#1, Tclass._module.Nat())
         && $Is(xs#1, Tclass._module.List())
       ==> _module.Nat#Equal(_module.__default.add($LS($LS($LZ)), 
          _module.__default.count($LS($LS($LZ)), n#1, #_module.List.Cons(x#1, Lit(#_module.List.Nil()))), 
          _module.__default.count($LS($LS($LZ)), n#1, xs#1)), 
        _module.__default.count($LS($LS($LZ)), n#1, #_module.List.Cons(x#1, xs#1))));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.P39() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: P39, Impl$$_module.__default.P39
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(499,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.P40();
  free requires 85 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.P40();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall xs#1: DatatypeType :: 
    { _module.__default.take($LS($LZ), #_module.Nat.Zero(), xs#1) } 
    $Is(xs#1, Tclass._module.List())
       ==> $IsA#_module.List(_module.__default.take($LS($LZ), Lit(#_module.Nat.Zero()), xs#1))
         && _module.__default.take#canCall(Lit(#_module.Nat.Zero()), xs#1));
  free ensures (forall xs#1: DatatypeType :: 
    { _module.__default.take($LS($LZ), #_module.Nat.Zero(), xs#1) } 
    $Is(xs#1, Tclass._module.List())
       ==> _module.List#Equal(_module.__default.take($LS($LZ), Lit(#_module.Nat.Zero()), xs#1), 
        #_module.List.Nil()));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.P40() returns ($_reverifyPost: bool);
  free requires 85 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall xs#1: DatatypeType :: 
    { _module.__default.take($LS($LZ), #_module.Nat.Zero(), xs#1) } 
    $Is(xs#1, Tclass._module.List())
       ==> $IsA#_module.List(_module.__default.take($LS($LZ), Lit(#_module.Nat.Zero()), xs#1))
         && _module.__default.take#canCall(Lit(#_module.Nat.Zero()), xs#1));
  ensures (forall xs#1: DatatypeType :: 
    { _module.__default.take($LS($LS($LZ)), #_module.Nat.Zero(), xs#1) } 
    $Is(xs#1, Tclass._module.List())
       ==> _module.List#Equal(_module.__default.take($LS($LS($LZ)), Lit(#_module.Nat.Zero()), xs#1), 
        #_module.List.Nil()));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.P40() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: P40, Impl$$_module.__default.P40
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(504,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.P41();
  free requires 86 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.P41();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall n#1: DatatypeType, xs#1: DatatypeType, f#1: HandleType :: 
    { _module.__default.apply($LS($LZ), f#1, _module.__default.take($LS($LZ), n#1, xs#1)) } 
      { _module.__default.take($LS($LZ), n#1, _module.__default.apply($LS($LZ), f#1, xs#1)) } 
    $Is(n#1, Tclass._module.Nat())
         && $Is(xs#1, Tclass._module.List())
         && $Is(f#1, Tclass._System.___hTotalFunc1(Tclass._module.Nat(), Tclass._module.Nat()))
       ==> $IsA#_module.List(_module.__default.take($LS($LZ), n#1, _module.__default.apply($LS($LZ), f#1, xs#1)))
         && $IsA#_module.List(_module.__default.apply($LS($LZ), f#1, _module.__default.take($LS($LZ), n#1, xs#1)))
         && 
        _module.__default.apply#canCall(f#1, xs#1)
         && _module.__default.take#canCall(n#1, _module.__default.apply($LS($LZ), f#1, xs#1))
         && 
        _module.__default.take#canCall(n#1, xs#1)
         && _module.__default.apply#canCall(f#1, _module.__default.take($LS($LZ), n#1, xs#1)));
  free ensures (forall n#1: DatatypeType, xs#1: DatatypeType, f#1: HandleType :: 
    { _module.__default.apply($LS($LZ), f#1, _module.__default.take($LS($LZ), n#1, xs#1)) } 
      { _module.__default.take($LS($LZ), n#1, _module.__default.apply($LS($LZ), f#1, xs#1)) } 
    $Is(n#1, Tclass._module.Nat())
         && $Is(xs#1, Tclass._module.List())
         && $Is(f#1, Tclass._System.___hTotalFunc1(Tclass._module.Nat(), Tclass._module.Nat()))
       ==> _module.List#Equal(_module.__default.take($LS($LZ), n#1, _module.__default.apply($LS($LZ), f#1, xs#1)), 
        _module.__default.apply($LS($LZ), f#1, _module.__default.take($LS($LZ), n#1, xs#1))));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.P41() returns ($_reverifyPost: bool);
  free requires 86 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall n#1: DatatypeType, xs#1: DatatypeType, f#1: HandleType :: 
    { _module.__default.apply($LS($LZ), f#1, _module.__default.take($LS($LZ), n#1, xs#1)) } 
      { _module.__default.take($LS($LZ), n#1, _module.__default.apply($LS($LZ), f#1, xs#1)) } 
    $Is(n#1, Tclass._module.Nat())
         && $Is(xs#1, Tclass._module.List())
         && $Is(f#1, Tclass._System.___hTotalFunc1(Tclass._module.Nat(), Tclass._module.Nat()))
       ==> $IsA#_module.List(_module.__default.take($LS($LZ), n#1, _module.__default.apply($LS($LZ), f#1, xs#1)))
         && $IsA#_module.List(_module.__default.apply($LS($LZ), f#1, _module.__default.take($LS($LZ), n#1, xs#1)))
         && 
        _module.__default.apply#canCall(f#1, xs#1)
         && _module.__default.take#canCall(n#1, _module.__default.apply($LS($LZ), f#1, xs#1))
         && 
        _module.__default.take#canCall(n#1, xs#1)
         && _module.__default.apply#canCall(f#1, _module.__default.take($LS($LZ), n#1, xs#1)));
  ensures (forall n#1: DatatypeType, xs#1: DatatypeType, f#1: HandleType :: 
    { _module.__default.apply($LS($LS($LZ)), f#1, _module.__default.take($LS($LS($LZ)), n#1, xs#1)) } 
      { _module.__default.take($LS($LS($LZ)), n#1, _module.__default.apply($LS($LS($LZ)), f#1, xs#1)) } 
    $Is(n#1, Tclass._module.Nat())
         && $Is(xs#1, Tclass._module.List())
         && $Is(f#1, Tclass._System.___hTotalFunc1(Tclass._module.Nat(), Tclass._module.Nat()))
       ==> _module.List#Equal(_module.__default.take($LS($LS($LZ)), n#1, _module.__default.apply($LS($LS($LZ)), f#1, xs#1)), 
        _module.__default.apply($LS($LS($LZ)), f#1, _module.__default.take($LS($LS($LZ)), n#1, xs#1))));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.P41() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: P41, Impl$$_module.__default.P41
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(509,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.P42();
  free requires 87 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.P42();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall n#1: DatatypeType, x#1: DatatypeType, xs#1: DatatypeType :: 
    { #_module.List.Cons(x#1, _module.__default.take($LS($LZ), n#1, xs#1)) } 
      { _module.__default.take($LS($LZ), #_module.Nat.Suc(n#1), #_module.List.Cons(x#1, xs#1)) } 
    $Is(n#1, Tclass._module.Nat())
         && $Is(x#1, Tclass._module.Nat())
         && $Is(xs#1, Tclass._module.List())
       ==> $IsA#_module.List(_module.__default.take($LS($LZ), #_module.Nat.Suc(n#1), #_module.List.Cons(x#1, xs#1)))
         && 
        _module.__default.take#canCall(#_module.Nat.Suc(n#1), #_module.List.Cons(x#1, xs#1))
         && _module.__default.take#canCall(n#1, xs#1));
  free ensures (forall n#1: DatatypeType, x#1: DatatypeType, xs#1: DatatypeType :: 
    { #_module.List.Cons(x#1, _module.__default.take($LS($LZ), n#1, xs#1)) } 
      { _module.__default.take($LS($LZ), #_module.Nat.Suc(n#1), #_module.List.Cons(x#1, xs#1)) } 
    $Is(n#1, Tclass._module.Nat())
         && $Is(x#1, Tclass._module.Nat())
         && $Is(xs#1, Tclass._module.List())
       ==> _module.List#Equal(_module.__default.take($LS($LZ), #_module.Nat.Suc(n#1), #_module.List.Cons(x#1, xs#1)), 
        #_module.List.Cons(x#1, _module.__default.take($LS($LZ), n#1, xs#1))));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.P42() returns ($_reverifyPost: bool);
  free requires 87 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall n#1: DatatypeType, x#1: DatatypeType, xs#1: DatatypeType :: 
    { #_module.List.Cons(x#1, _module.__default.take($LS($LZ), n#1, xs#1)) } 
      { _module.__default.take($LS($LZ), #_module.Nat.Suc(n#1), #_module.List.Cons(x#1, xs#1)) } 
    $Is(n#1, Tclass._module.Nat())
         && $Is(x#1, Tclass._module.Nat())
         && $Is(xs#1, Tclass._module.List())
       ==> $IsA#_module.List(_module.__default.take($LS($LZ), #_module.Nat.Suc(n#1), #_module.List.Cons(x#1, xs#1)))
         && 
        _module.__default.take#canCall(#_module.Nat.Suc(n#1), #_module.List.Cons(x#1, xs#1))
         && _module.__default.take#canCall(n#1, xs#1));
  ensures (forall n#1: DatatypeType, x#1: DatatypeType, xs#1: DatatypeType :: 
    { #_module.List.Cons(x#1, _module.__default.take($LS($LS($LZ)), n#1, xs#1)) } 
      { _module.__default.take($LS($LS($LZ)), #_module.Nat.Suc(n#1), #_module.List.Cons(x#1, xs#1)) } 
    $Is(n#1, Tclass._module.Nat())
         && $Is(x#1, Tclass._module.Nat())
         && $Is(xs#1, Tclass._module.List())
       ==> _module.List#Equal(_module.__default.take($LS($LS($LZ)), #_module.Nat.Suc(n#1), #_module.List.Cons(x#1, xs#1)), 
        #_module.List.Cons(x#1, _module.__default.take($LS($LS($LZ)), n#1, xs#1))));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.P42() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: P42, Impl$$_module.__default.P42
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(514,0): initial state"} true;
    $_reverifyPost := false;
}



procedure {:_induction p#0} CheckWellformed$$_module.__default.P43(p#0: HandleType
       where $Is(p#0, Tclass._System.___hTotalFunc1(Tclass._module.Nat(), Tclass._module.Nat()))
         && $IsAlloc(p#0, 
          Tclass._System.___hTotalFunc1(Tclass._module.Nat(), Tclass._module.Nat()), 
          $Heap));
  free requires 39 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction p#0} Call$$_module.__default.P43(p#0: HandleType
       where $Is(p#0, Tclass._System.___hTotalFunc1(Tclass._module.Nat(), Tclass._module.Nat()))
         && $IsAlloc(p#0, 
          Tclass._System.___hTotalFunc1(Tclass._module.Nat(), Tclass._module.Nat()), 
          $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall xs#1: DatatypeType :: 
    { _module.__default.dropWhileAlways($LS($LZ), p#0, xs#1) } 
      { _module.__default.takeWhileAlways($LS($LZ), p#0, xs#1) } 
    $Is(xs#1, Tclass._module.List())
       ==> $IsA#_module.List(_module.__default.concat($LS($LZ), 
            _module.__default.takeWhileAlways($LS($LZ), p#0, xs#1), 
            _module.__default.dropWhileAlways($LS($LZ), p#0, xs#1)))
         && $IsA#_module.List(xs#1)
         && 
        _module.__default.takeWhileAlways#canCall(p#0, xs#1)
         && _module.__default.dropWhileAlways#canCall(p#0, xs#1)
         && _module.__default.concat#canCall(_module.__default.takeWhileAlways($LS($LZ), p#0, xs#1), 
          _module.__default.dropWhileAlways($LS($LZ), p#0, xs#1)));
  free ensures (forall xs#1: DatatypeType :: 
    { _module.__default.dropWhileAlways($LS($LZ), p#0, xs#1) } 
      { _module.__default.takeWhileAlways($LS($LZ), p#0, xs#1) } 
    $Is(xs#1, Tclass._module.List())
       ==> _module.List#Equal(_module.__default.concat($LS($LZ), 
          _module.__default.takeWhileAlways($LS($LZ), p#0, xs#1), 
          _module.__default.dropWhileAlways($LS($LZ), p#0, xs#1)), 
        xs#1));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction p#0} Impl$$_module.__default.P43(p#0: HandleType
       where $Is(p#0, Tclass._System.___hTotalFunc1(Tclass._module.Nat(), Tclass._module.Nat()))
         && $IsAlloc(p#0, 
          Tclass._System.___hTotalFunc1(Tclass._module.Nat(), Tclass._module.Nat()), 
          $Heap))
   returns ($_reverifyPost: bool);
  free requires 39 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall xs#1: DatatypeType :: 
    { _module.__default.dropWhileAlways($LS($LZ), p#0, xs#1) } 
      { _module.__default.takeWhileAlways($LS($LZ), p#0, xs#1) } 
    $Is(xs#1, Tclass._module.List())
       ==> $IsA#_module.List(_module.__default.concat($LS($LZ), 
            _module.__default.takeWhileAlways($LS($LZ), p#0, xs#1), 
            _module.__default.dropWhileAlways($LS($LZ), p#0, xs#1)))
         && $IsA#_module.List(xs#1)
         && 
        _module.__default.takeWhileAlways#canCall(p#0, xs#1)
         && _module.__default.dropWhileAlways#canCall(p#0, xs#1)
         && _module.__default.concat#canCall(_module.__default.takeWhileAlways($LS($LZ), p#0, xs#1), 
          _module.__default.dropWhileAlways($LS($LZ), p#0, xs#1)));
  ensures (forall xs#1: DatatypeType :: 
    { _module.__default.dropWhileAlways($LS($LS($LZ)), p#0, xs#1) } 
      { _module.__default.takeWhileAlways($LS($LS($LZ)), p#0, xs#1) } 
    $Is(xs#1, Tclass._module.List())
       ==> _module.List#Equal(_module.__default.concat($LS($LS($LZ)), 
          _module.__default.takeWhileAlways($LS($LS($LZ)), p#0, xs#1), 
          _module.__default.dropWhileAlways($LS($LS($LZ)), p#0, xs#1)), 
        xs#1));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction p#0} Impl$$_module.__default.P43(p#0: HandleType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;

    // AddMethodImpl: P43, Impl$$_module.__default.P43
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(519,0): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#p0#0: HandleType :: 
      $Is($ih#p0#0, 
            Tclass._System.___hTotalFunc1(Tclass._module.Nat(), Tclass._module.Nat()))
           && Lit(true)
           && false
         ==> (forall xs#2: DatatypeType :: 
          { _module.__default.dropWhileAlways($LS($LZ), $ih#p0#0, xs#2) } 
            { _module.__default.takeWhileAlways($LS($LZ), $ih#p0#0, xs#2) } 
          $Is(xs#2, Tclass._module.List())
             ==> _module.List#Equal(_module.__default.concat($LS($LZ), 
                _module.__default.takeWhileAlways($LS($LZ), $ih#p0#0, xs#2), 
                _module.__default.dropWhileAlways($LS($LZ), $ih#p0#0, xs#2)), 
              xs#2)));
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.P44();
  free requires 88 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.P44();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall x#1: DatatypeType, xs#1: DatatypeType, ys#1: DatatypeType :: 
    { _module.__default.zipConcat(x#1, xs#1, ys#1) } 
      { _module.__default.zip($LS($LZ), #_module.List.Cons(x#1, xs#1), ys#1) } 
    $Is(x#1, Tclass._module.Nat())
         && $Is(xs#1, Tclass._module.List())
         && $Is(ys#1, Tclass._module.List())
       ==> $IsA#_module.PList(_module.__default.zip($LS($LZ), #_module.List.Cons(x#1, xs#1), ys#1))
         && $IsA#_module.PList(_module.__default.zipConcat(x#1, xs#1, ys#1))
         && 
        _module.__default.zip#canCall(#_module.List.Cons(x#1, xs#1), ys#1)
         && _module.__default.zipConcat#canCall(x#1, xs#1, ys#1));
  free ensures (forall x#1: DatatypeType, xs#1: DatatypeType, ys#1: DatatypeType :: 
    { _module.__default.zipConcat(x#1, xs#1, ys#1) } 
      { _module.__default.zip($LS($LZ), #_module.List.Cons(x#1, xs#1), ys#1) } 
    $Is(x#1, Tclass._module.Nat())
         && $Is(xs#1, Tclass._module.List())
         && $Is(ys#1, Tclass._module.List())
       ==> _module.PList#Equal(_module.__default.zip($LS($LZ), #_module.List.Cons(x#1, xs#1), ys#1), 
        _module.__default.zipConcat(x#1, xs#1, ys#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.P44() returns ($_reverifyPost: bool);
  free requires 88 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall x#1: DatatypeType, xs#1: DatatypeType, ys#1: DatatypeType :: 
    { _module.__default.zipConcat(x#1, xs#1, ys#1) } 
      { _module.__default.zip($LS($LZ), #_module.List.Cons(x#1, xs#1), ys#1) } 
    $Is(x#1, Tclass._module.Nat())
         && $Is(xs#1, Tclass._module.List())
         && $Is(ys#1, Tclass._module.List())
       ==> $IsA#_module.PList(_module.__default.zip($LS($LZ), #_module.List.Cons(x#1, xs#1), ys#1))
         && $IsA#_module.PList(_module.__default.zipConcat(x#1, xs#1, ys#1))
         && 
        _module.__default.zip#canCall(#_module.List.Cons(x#1, xs#1), ys#1)
         && _module.__default.zipConcat#canCall(x#1, xs#1, ys#1));
  ensures (forall x#1: DatatypeType, xs#1: DatatypeType, ys#1: DatatypeType :: 
    { _module.__default.zipConcat(x#1, xs#1, ys#1) } 
      { _module.__default.zip($LS($LS($LZ)), #_module.List.Cons(x#1, xs#1), ys#1) } 
    $Is(x#1, Tclass._module.Nat())
         && $Is(xs#1, Tclass._module.List())
         && $Is(ys#1, Tclass._module.List())
       ==> _module.PList#Equal(_module.__default.zip($LS($LS($LZ)), #_module.List.Cons(x#1, xs#1), ys#1), 
        _module.__default.zipConcat(x#1, xs#1, ys#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.P44() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: P44, Impl$$_module.__default.P44
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(524,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.P45();
  free requires 89 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.P45();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall x#1: DatatypeType, xs#1: DatatypeType, y#1: DatatypeType, ys#1: DatatypeType :: 
    { #_module.PList.PCons(#_module.Pair.Pair(x#1, y#1), _module.__default.zip($LS($LZ), xs#1, ys#1)) } 
      { #_module.List.Cons(y#1, ys#1), #_module.List.Cons(x#1, xs#1) } 
    $Is(x#1, Tclass._module.Nat())
         && $Is(xs#1, Tclass._module.List())
         && $Is(y#1, Tclass._module.Nat())
         && $Is(ys#1, Tclass._module.List())
       ==> $IsA#_module.PList(_module.__default.zip($LS($LZ), #_module.List.Cons(x#1, xs#1), #_module.List.Cons(y#1, ys#1)))
         && 
        _module.__default.zip#canCall(#_module.List.Cons(x#1, xs#1), #_module.List.Cons(y#1, ys#1))
         && _module.__default.zip#canCall(xs#1, ys#1));
  free ensures (forall x#1: DatatypeType, xs#1: DatatypeType, y#1: DatatypeType, ys#1: DatatypeType :: 
    { #_module.PList.PCons(#_module.Pair.Pair(x#1, y#1), _module.__default.zip($LS($LZ), xs#1, ys#1)) } 
      { #_module.List.Cons(y#1, ys#1), #_module.List.Cons(x#1, xs#1) } 
    $Is(x#1, Tclass._module.Nat())
         && $Is(xs#1, Tclass._module.List())
         && $Is(y#1, Tclass._module.Nat())
         && $Is(ys#1, Tclass._module.List())
       ==> _module.PList#Equal(_module.__default.zip($LS($LZ), #_module.List.Cons(x#1, xs#1), #_module.List.Cons(y#1, ys#1)), 
        #_module.PList.PCons(#_module.Pair.Pair(x#1, y#1), _module.__default.zip($LS($LZ), xs#1, ys#1))));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.P45() returns ($_reverifyPost: bool);
  free requires 89 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall x#1: DatatypeType, xs#1: DatatypeType, y#1: DatatypeType, ys#1: DatatypeType :: 
    { #_module.PList.PCons(#_module.Pair.Pair(x#1, y#1), _module.__default.zip($LS($LZ), xs#1, ys#1)) } 
      { #_module.List.Cons(y#1, ys#1), #_module.List.Cons(x#1, xs#1) } 
    $Is(x#1, Tclass._module.Nat())
         && $Is(xs#1, Tclass._module.List())
         && $Is(y#1, Tclass._module.Nat())
         && $Is(ys#1, Tclass._module.List())
       ==> $IsA#_module.PList(_module.__default.zip($LS($LZ), #_module.List.Cons(x#1, xs#1), #_module.List.Cons(y#1, ys#1)))
         && 
        _module.__default.zip#canCall(#_module.List.Cons(x#1, xs#1), #_module.List.Cons(y#1, ys#1))
         && _module.__default.zip#canCall(xs#1, ys#1));
  ensures (forall x#1: DatatypeType, xs#1: DatatypeType, y#1: DatatypeType, ys#1: DatatypeType :: 
    { #_module.PList.PCons(#_module.Pair.Pair(x#1, y#1), _module.__default.zip($LS($LS($LZ)), xs#1, ys#1)) } 
      { #_module.List.Cons(y#1, ys#1), #_module.List.Cons(x#1, xs#1) } 
    $Is(x#1, Tclass._module.Nat())
         && $Is(xs#1, Tclass._module.List())
         && $Is(y#1, Tclass._module.Nat())
         && $Is(ys#1, Tclass._module.List())
       ==> _module.PList#Equal(_module.__default.zip($LS($LS($LZ)), #_module.List.Cons(x#1, xs#1), #_module.List.Cons(y#1, ys#1)), 
        #_module.PList.PCons(#_module.Pair.Pair(x#1, y#1), _module.__default.zip($LS($LS($LZ)), xs#1, ys#1))));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.P45() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: P45, Impl$$_module.__default.P45
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(531,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.P46();
  free requires 90 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.P46();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall ys#1: DatatypeType :: 
    { _module.__default.zip($LS($LZ), #_module.List.Nil(), ys#1) } 
    $Is(ys#1, Tclass._module.List())
       ==> $IsA#_module.PList(_module.__default.zip($LS($LZ), Lit(#_module.List.Nil()), ys#1))
         && _module.__default.zip#canCall(Lit(#_module.List.Nil()), ys#1));
  free ensures (forall ys#1: DatatypeType :: 
    { _module.__default.zip($LS($LZ), #_module.List.Nil(), ys#1) } 
    $Is(ys#1, Tclass._module.List())
       ==> _module.PList#Equal(_module.__default.zip($LS($LZ), Lit(#_module.List.Nil()), ys#1), 
        #_module.PList.PNil()));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.P46() returns ($_reverifyPost: bool);
  free requires 90 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall ys#1: DatatypeType :: 
    { _module.__default.zip($LS($LZ), #_module.List.Nil(), ys#1) } 
    $Is(ys#1, Tclass._module.List())
       ==> $IsA#_module.PList(_module.__default.zip($LS($LZ), Lit(#_module.List.Nil()), ys#1))
         && _module.__default.zip#canCall(Lit(#_module.List.Nil()), ys#1));
  ensures (forall ys#1: DatatypeType :: 
    { _module.__default.zip($LS($LS($LZ)), #_module.List.Nil(), ys#1) } 
    $Is(ys#1, Tclass._module.List())
       ==> _module.PList#Equal(_module.__default.zip($LS($LS($LZ)), Lit(#_module.List.Nil()), ys#1), 
        #_module.PList.PNil()));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.P46() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: P46, Impl$$_module.__default.P46
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(536,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.P47();
  free requires 91 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.P47();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall a#1: DatatypeType :: 
    { _module.__default.mirror($LS($LZ), a#1) } 
    $Is(a#1, Tclass._module.Tree())
       ==> $IsA#_module.Nat(_module.__default.height($LS($LZ), _module.__default.mirror($LS($LZ), a#1)))
         && $IsA#_module.Nat(_module.__default.height($LS($LZ), a#1))
         && 
        _module.__default.mirror#canCall(a#1)
         && _module.__default.height#canCall(_module.__default.mirror($LS($LZ), a#1))
         && _module.__default.height#canCall(a#1));
  free ensures (forall a#1: DatatypeType :: 
    { _module.__default.mirror($LS($LZ), a#1) } 
    $Is(a#1, Tclass._module.Tree())
       ==> _module.Nat#Equal(_module.__default.height($LS($LZ), _module.__default.mirror($LS($LZ), a#1)), 
        _module.__default.height($LS($LZ), a#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.P47() returns ($_reverifyPost: bool);
  free requires 91 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall a#1: DatatypeType :: 
    { _module.__default.mirror($LS($LZ), a#1) } 
    $Is(a#1, Tclass._module.Tree())
       ==> $IsA#_module.Nat(_module.__default.height($LS($LZ), _module.__default.mirror($LS($LZ), a#1)))
         && $IsA#_module.Nat(_module.__default.height($LS($LZ), a#1))
         && 
        _module.__default.mirror#canCall(a#1)
         && _module.__default.height#canCall(_module.__default.mirror($LS($LZ), a#1))
         && _module.__default.height#canCall(a#1));
  ensures (forall a#1: DatatypeType :: 
    { _module.__default.mirror($LS($LS($LZ)), a#1) } 
    $Is(a#1, Tclass._module.Tree())
       ==> _module.Nat#Equal(_module.__default.height($LS($LS($LZ)), _module.__default.mirror($LS($LS($LZ)), a#1)), 
        _module.__default.height($LS($LS($LZ)), a#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.P47() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: P47, Impl$$_module.__default.P47
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(541,0): initial state"} true;
    $_reverifyPost := false;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(543,6)
    // TrCallStmt: Before ProcessCallStmt
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.P23();
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(543,7)"} true;
}



procedure CheckWellformed$$_module.__default.P54();
  free requires 92 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.P54();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall m#1: DatatypeType, n#1: DatatypeType :: 
    { _module.__default.add($LS($LZ), m#1, n#1) } 
    $Is(m#1, Tclass._module.Nat()) && $Is(n#1, Tclass._module.Nat())
       ==> $IsA#_module.Nat(_module.__default.minus($LS($LZ), _module.__default.add($LS($LZ), m#1, n#1), n#1))
         && $IsA#_module.Nat(m#1)
         && 
        _module.__default.add#canCall(m#1, n#1)
         && _module.__default.minus#canCall(_module.__default.add($LS($LZ), m#1, n#1), n#1));
  free ensures (forall m#1: DatatypeType, n#1: DatatypeType :: 
    { _module.__default.add($LS($LZ), m#1, n#1) } 
    $Is(m#1, Tclass._module.Nat()) && $Is(n#1, Tclass._module.Nat())
       ==> _module.Nat#Equal(_module.__default.minus($LS($LZ), _module.__default.add($LS($LZ), m#1, n#1), n#1), 
        m#1));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.P54() returns ($_reverifyPost: bool);
  free requires 92 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall m#1: DatatypeType, n#1: DatatypeType :: 
    { _module.__default.add($LS($LZ), m#1, n#1) } 
    $Is(m#1, Tclass._module.Nat()) && $Is(n#1, Tclass._module.Nat())
       ==> $IsA#_module.Nat(_module.__default.minus($LS($LZ), _module.__default.add($LS($LZ), m#1, n#1), n#1))
         && $IsA#_module.Nat(m#1)
         && 
        _module.__default.add#canCall(m#1, n#1)
         && _module.__default.minus#canCall(_module.__default.add($LS($LZ), m#1, n#1), n#1));
  ensures (forall m#1: DatatypeType, n#1: DatatypeType :: 
    { _module.__default.add($LS($LS($LZ)), m#1, n#1) } 
    $Is(m#1, Tclass._module.Nat()) && $Is(n#1, Tclass._module.Nat())
       ==> _module.Nat#Equal(_module.__default.minus($LS($LS($LZ)), _module.__default.add($LS($LS($LZ)), m#1, n#1), n#1), 
        m#1));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.P54() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var m#2: DatatypeType;
  var n#2: DatatypeType;
  var ##x#2: DatatypeType;
  var ##y#2: DatatypeType;
  var ##x#3: DatatypeType;
  var ##y#3: DatatypeType;
  var m#4: DatatypeType;
  var n#4: DatatypeType;
  var ##x#4: DatatypeType;
  var ##y#4: DatatypeType;
  var ##x#5: DatatypeType;
  var ##y#5: DatatypeType;

    // AddMethodImpl: P54, Impl$$_module.__default.P54
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(550,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(552,3)
    // Begin Comprehension WF check
    havoc m#2;
    havoc n#2;
    if ($Is(m#2, Tclass._module.Nat()) && $Is(n#2, Tclass._module.Nat()))
    {
        ##x#2 := n#2;
        // assume allocatedness for argument to function
        assume $IsAlloc(##x#2, Tclass._module.Nat(), $Heap);
        ##y#2 := m#2;
        // assume allocatedness for argument to function
        assume $IsAlloc(##y#2, Tclass._module.Nat(), $Heap);
        assume _module.__default.add#canCall(n#2, m#2);
        ##x#3 := _module.__default.add($LS($LZ), n#2, m#2);
        // assume allocatedness for argument to function
        assume $IsAlloc(##x#3, Tclass._module.Nat(), $Heap);
        ##y#3 := n#2;
        // assume allocatedness for argument to function
        assume $IsAlloc(##y#3, Tclass._module.Nat(), $Heap);
        assume _module.__default.minus#canCall(_module.__default.add($LS($LZ), n#2, m#2), n#2);
    }

    // End Comprehension WF check
    assume (forall m#3: DatatypeType, n#3: DatatypeType :: 
      $Is(m#3, Tclass._module.Nat()) && $Is(n#3, Tclass._module.Nat())
         ==> $IsA#_module.Nat(_module.__default.minus($LS($LZ), _module.__default.add($LS($LZ), n#3, m#3), n#3))
           && $IsA#_module.Nat(m#3)
           && 
          _module.__default.add#canCall(n#3, m#3)
           && _module.__default.minus#canCall(_module.__default.add($LS($LZ), n#3, m#3), n#3));
    assert {:subsumption 0} (forall m#3: DatatypeType, n#3: DatatypeType :: 
      {:autotriggers false} 
      $Is(m#3, Tclass._module.Nat()) && $Is(n#3, Tclass._module.Nat())
         ==> _module.Nat#Equal(_module.__default.minus($LS($LS($LZ)), _module.__default.add($LS($LS($LZ)), n#3, m#3), n#3), 
          m#3));
    assume (forall m#3: DatatypeType, n#3: DatatypeType :: 
      {:autotriggers false} 
      $Is(m#3, Tclass._module.Nat()) && $Is(n#3, Tclass._module.Nat())
         ==> _module.Nat#Equal(_module.__default.minus($LS($LZ), _module.__default.add($LS($LZ), n#3, m#3), n#3), 
          m#3));
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(553,3)
    // Begin Comprehension WF check
    havoc m#4;
    havoc n#4;
    if ($Is(m#4, Tclass._module.Nat()) && $Is(n#4, Tclass._module.Nat()))
    {
        ##x#4 := m#4;
        // assume allocatedness for argument to function
        assume $IsAlloc(##x#4, Tclass._module.Nat(), $Heap);
        ##y#4 := n#4;
        // assume allocatedness for argument to function
        assume $IsAlloc(##y#4, Tclass._module.Nat(), $Heap);
        assume _module.__default.add#canCall(m#4, n#4);
        ##x#5 := n#4;
        // assume allocatedness for argument to function
        assume $IsAlloc(##x#5, Tclass._module.Nat(), $Heap);
        ##y#5 := m#4;
        // assume allocatedness for argument to function
        assume $IsAlloc(##y#5, Tclass._module.Nat(), $Heap);
        assume _module.__default.add#canCall(n#4, m#4);
    }

    // End Comprehension WF check
    assume (forall m#5: DatatypeType, n#5: DatatypeType :: 
      { _module.__default.add($LS($LZ), n#5, m#5) } 
        { _module.__default.add($LS($LZ), m#5, n#5) } 
      $Is(m#5, Tclass._module.Nat()) && $Is(n#5, Tclass._module.Nat())
         ==> $IsA#_module.Nat(_module.__default.add($LS($LZ), m#5, n#5))
           && $IsA#_module.Nat(_module.__default.add($LS($LZ), n#5, m#5))
           && 
          _module.__default.add#canCall(m#5, n#5)
           && _module.__default.add#canCall(n#5, m#5));
    assert {:subsumption 0} (forall m#5: DatatypeType, n#5: DatatypeType :: 
      { _module.__default.add($LS($LS($LZ)), n#5, m#5) } 
        { _module.__default.add($LS($LS($LZ)), m#5, n#5) } 
      $Is(m#5, Tclass._module.Nat()) && $Is(n#5, Tclass._module.Nat())
         ==> _module.Nat#Equal(_module.__default.add($LS($LS($LZ)), m#5, n#5), 
          _module.__default.add($LS($LS($LZ)), n#5, m#5)));
    assume (forall m#5: DatatypeType, n#5: DatatypeType :: 
      { _module.__default.add($LS($LZ), n#5, m#5) } 
        { _module.__default.add($LS($LZ), m#5, n#5) } 
      $Is(m#5, Tclass._module.Nat()) && $Is(n#5, Tclass._module.Nat())
         ==> _module.Nat#Equal(_module.__default.add($LS($LZ), m#5, n#5), 
          _module.__default.add($LS($LZ), n#5, m#5)));
}



procedure CheckWellformed$$_module.__default.P65();
  free requires 93 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.P65();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall i#1: DatatypeType, m#1: DatatypeType :: 
    { _module.__default.add($LS($LZ), m#1, i#1) } 
    $Is(i#1, Tclass._module.Nat()) && $Is(m#1, Tclass._module.Nat())
       ==> $IsA#_module.Bool(_module.__default.less($LS($LZ), i#1, #_module.Nat.Suc(_module.__default.add($LS($LZ), m#1, i#1))))
         && 
        _module.__default.add#canCall(m#1, i#1)
         && _module.__default.less#canCall(i#1, #_module.Nat.Suc(_module.__default.add($LS($LZ), m#1, i#1))));
  free ensures (forall i#1: DatatypeType, m#1: DatatypeType :: 
    { _module.__default.add($LS($LZ), m#1, i#1) } 
    $Is(i#1, Tclass._module.Nat()) && $Is(m#1, Tclass._module.Nat())
       ==> _module.Bool#Equal(_module.__default.less($LS($LZ), i#1, #_module.Nat.Suc(_module.__default.add($LS($LZ), m#1, i#1))), 
        #_module.Bool.True()));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.P65() returns ($_reverifyPost: bool);
  free requires 93 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall i#1: DatatypeType, m#1: DatatypeType :: 
    { _module.__default.add($LS($LZ), m#1, i#1) } 
    $Is(i#1, Tclass._module.Nat()) && $Is(m#1, Tclass._module.Nat())
       ==> $IsA#_module.Bool(_module.__default.less($LS($LZ), i#1, #_module.Nat.Suc(_module.__default.add($LS($LZ), m#1, i#1))))
         && 
        _module.__default.add#canCall(m#1, i#1)
         && _module.__default.less#canCall(i#1, #_module.Nat.Suc(_module.__default.add($LS($LZ), m#1, i#1))));
  ensures (forall i#1: DatatypeType, m#1: DatatypeType :: 
    { _module.__default.add($LS($LS($LZ)), m#1, i#1) } 
    $Is(i#1, Tclass._module.Nat()) && $Is(m#1, Tclass._module.Nat())
       ==> _module.Bool#Equal(_module.__default.less($LS($LS($LZ)), 
          i#1, 
          #_module.Nat.Suc(_module.__default.add($LS($LS($LZ)), m#1, i#1))), 
        #_module.Bool.True()));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.P65() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var i#0_0: DatatypeType;
  var m#0_0: DatatypeType;
  var ##x#0_0: DatatypeType;
  var ##y#0_0: DatatypeType;
  var ##x#0_1: DatatypeType;
  var ##y#0_1: DatatypeType;
  var m#0_2: DatatypeType;
  var n#0_0: DatatypeType;
  var ##x#0_2: DatatypeType;
  var ##y#0_2: DatatypeType;
  var ##x#0_3: DatatypeType;
  var ##y#0_3: DatatypeType;
  var x#0: DatatypeType;
  var y#0: DatatypeType;
  var ##x#2: DatatypeType;
  var ##y#2: DatatypeType;
  var ##x#3: DatatypeType;
  var ##y#3: DatatypeType;

    // AddMethodImpl: P65, Impl$$_module.__default.P65
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(558,0): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(559,3)
    if (*)
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(561,5)
        // Begin Comprehension WF check
        havoc i#0_0;
        havoc m#0_0;
        if ($Is(i#0_0, Tclass._module.Nat()) && $Is(m#0_0, Tclass._module.Nat()))
        {
            ##x#0_0 := i#0_0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##x#0_0, Tclass._module.Nat(), $Heap);
            ##y#0_0 := m#0_0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##y#0_0, Tclass._module.Nat(), $Heap);
            assume _module.__default.add#canCall(i#0_0, m#0_0);
            ##x#0_1 := i#0_0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##x#0_1, Tclass._module.Nat(), $Heap);
            ##y#0_1 := #_module.Nat.Suc(_module.__default.add($LS($LZ), i#0_0, m#0_0));
            // assume allocatedness for argument to function
            assume $IsAlloc(##y#0_1, Tclass._module.Nat(), $Heap);
            assume _module.__default.less#canCall(i#0_0, #_module.Nat.Suc(_module.__default.add($LS($LZ), i#0_0, m#0_0)));
        }

        // End Comprehension WF check
        assume (forall i#0_1: DatatypeType, m#0_1: DatatypeType :: 
          $Is(i#0_1, Tclass._module.Nat()) && $Is(m#0_1, Tclass._module.Nat())
             ==> $IsA#_module.Bool(_module.__default.less($LS($LZ), i#0_1, #_module.Nat.Suc(_module.__default.add($LS($LZ), i#0_1, m#0_1))))
               && 
              _module.__default.add#canCall(i#0_1, m#0_1)
               && _module.__default.less#canCall(i#0_1, #_module.Nat.Suc(_module.__default.add($LS($LZ), i#0_1, m#0_1))));
        assert {:subsumption 0} (forall i#0_1: DatatypeType, m#0_1: DatatypeType :: 
          {:autotriggers false} 
          $Is(i#0_1, Tclass._module.Nat()) && $Is(m#0_1, Tclass._module.Nat())
             ==> _module.Bool#Equal(_module.__default.less($LS($LS($LZ)), 
                i#0_1, 
                #_module.Nat.Suc(_module.__default.add($LS($LS($LZ)), i#0_1, m#0_1))), 
              #_module.Bool.True()));
        assume (forall i#0_1: DatatypeType, m#0_1: DatatypeType :: 
          {:autotriggers false} 
          $Is(i#0_1, Tclass._module.Nat()) && $Is(m#0_1, Tclass._module.Nat())
             ==> _module.Bool#Equal(_module.__default.less($LS($LZ), i#0_1, #_module.Nat.Suc(_module.__default.add($LS($LZ), i#0_1, m#0_1))), 
              #_module.Bool.True()));
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(562,5)
        // Begin Comprehension WF check
        havoc m#0_2;
        havoc n#0_0;
        if ($Is(m#0_2, Tclass._module.Nat()) && $Is(n#0_0, Tclass._module.Nat()))
        {
            ##x#0_2 := m#0_2;
            // assume allocatedness for argument to function
            assume $IsAlloc(##x#0_2, Tclass._module.Nat(), $Heap);
            ##y#0_2 := n#0_0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##y#0_2, Tclass._module.Nat(), $Heap);
            assume _module.__default.add#canCall(m#0_2, n#0_0);
            ##x#0_3 := n#0_0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##x#0_3, Tclass._module.Nat(), $Heap);
            ##y#0_3 := m#0_2;
            // assume allocatedness for argument to function
            assume $IsAlloc(##y#0_3, Tclass._module.Nat(), $Heap);
            assume _module.__default.add#canCall(n#0_0, m#0_2);
        }

        // End Comprehension WF check
        assume (forall m#0_3: DatatypeType, n#0_1: DatatypeType :: 
          { _module.__default.add($LS($LZ), n#0_1, m#0_3) } 
            { _module.__default.add($LS($LZ), m#0_3, n#0_1) } 
          $Is(m#0_3, Tclass._module.Nat()) && $Is(n#0_1, Tclass._module.Nat())
             ==> $IsA#_module.Nat(_module.__default.add($LS($LZ), m#0_3, n#0_1))
               && $IsA#_module.Nat(_module.__default.add($LS($LZ), n#0_1, m#0_3))
               && 
              _module.__default.add#canCall(m#0_3, n#0_1)
               && _module.__default.add#canCall(n#0_1, m#0_3));
        assert {:subsumption 0} (forall m#0_3: DatatypeType, n#0_1: DatatypeType :: 
          { _module.__default.add($LS($LS($LZ)), n#0_1, m#0_3) } 
            { _module.__default.add($LS($LS($LZ)), m#0_3, n#0_1) } 
          $Is(m#0_3, Tclass._module.Nat()) && $Is(n#0_1, Tclass._module.Nat())
             ==> _module.Nat#Equal(_module.__default.add($LS($LS($LZ)), m#0_3, n#0_1), 
              _module.__default.add($LS($LS($LZ)), n#0_1, m#0_3)));
        assume (forall m#0_3: DatatypeType, n#0_1: DatatypeType :: 
          { _module.__default.add($LS($LZ), n#0_1, m#0_3) } 
            { _module.__default.add($LS($LZ), m#0_3, n#0_1) } 
          $Is(m#0_3, Tclass._module.Nat()) && $Is(n#0_1, Tclass._module.Nat())
             ==> _module.Nat#Equal(_module.__default.add($LS($LZ), m#0_3, n#0_1), 
              _module.__default.add($LS($LZ), n#0_1, m#0_3)));
    }
    else
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(565,5)
        // Begin Comprehension WF check
        havoc x#0;
        havoc y#0;
        if ($Is(x#0, Tclass._module.Nat()) && $Is(y#0, Tclass._module.Nat()))
        {
            ##x#2 := x#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##x#2, Tclass._module.Nat(), $Heap);
            ##y#2 := #_module.Nat.Suc(y#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##y#2, Tclass._module.Nat(), $Heap);
            assume _module.__default.add#canCall(x#0, #_module.Nat.Suc(y#0));
            ##x#3 := x#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##x#3, Tclass._module.Nat(), $Heap);
            ##y#3 := y#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##y#3, Tclass._module.Nat(), $Heap);
            assume _module.__default.add#canCall(x#0, y#0);
        }

        // End Comprehension WF check
        assume (forall x#1: DatatypeType, y#1: DatatypeType :: 
          { #_module.Nat.Suc(_module.__default.add($LS($LZ), x#1, y#1)) } 
            { _module.__default.add($LS($LZ), x#1, #_module.Nat.Suc(y#1)) } 
          $Is(x#1, Tclass._module.Nat()) && $Is(y#1, Tclass._module.Nat())
             ==> $IsA#_module.Nat(_module.__default.add($LS($LZ), x#1, #_module.Nat.Suc(y#1)))
               && 
              _module.__default.add#canCall(x#1, #_module.Nat.Suc(y#1))
               && _module.__default.add#canCall(x#1, y#1));
        assert {:subsumption 0} (forall x#1: DatatypeType, y#1: DatatypeType :: 
          { #_module.Nat.Suc(_module.__default.add($LS($LS($LZ)), x#1, y#1)) } 
            { _module.__default.add($LS($LS($LZ)), x#1, #_module.Nat.Suc(y#1)) } 
          $Is(x#1, Tclass._module.Nat()) && $Is(y#1, Tclass._module.Nat())
             ==> _module.Nat#Equal(_module.__default.add($LS($LS($LZ)), x#1, #_module.Nat.Suc(y#1)), 
              #_module.Nat.Suc(_module.__default.add($LS($LS($LZ)), x#1, y#1))));
        assume (forall x#1: DatatypeType, y#1: DatatypeType :: 
          { #_module.Nat.Suc(_module.__default.add($LS($LZ), x#1, y#1)) } 
            { _module.__default.add($LS($LZ), x#1, #_module.Nat.Suc(y#1)) } 
          $Is(x#1, Tclass._module.Nat()) && $Is(y#1, Tclass._module.Nat())
             ==> _module.Nat#Equal(_module.__default.add($LS($LZ), x#1, #_module.Nat.Suc(y#1)), 
              #_module.Nat.Suc(_module.__default.add($LS($LZ), x#1, y#1))));
    }
}



procedure CheckWellformed$$_module.__default.P67();
  free requires 94 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.P67();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall m#1: DatatypeType, n#1: DatatypeType :: 
    { _module.__default.add($LS($LZ), m#1, n#1) } 
    $Is(m#1, Tclass._module.Nat()) && $Is(n#1, Tclass._module.Nat())
       ==> $IsA#_module.Bool(_module.__default.leq($LS($LZ), n#1, _module.__default.add($LS($LZ), m#1, n#1)))
         && 
        _module.__default.add#canCall(m#1, n#1)
         && _module.__default.leq#canCall(n#1, _module.__default.add($LS($LZ), m#1, n#1)));
  free ensures (forall m#1: DatatypeType, n#1: DatatypeType :: 
    { _module.__default.add($LS($LZ), m#1, n#1) } 
    $Is(m#1, Tclass._module.Nat()) && $Is(n#1, Tclass._module.Nat())
       ==> _module.Bool#Equal(_module.__default.leq($LS($LZ), n#1, _module.__default.add($LS($LZ), m#1, n#1)), 
        #_module.Bool.True()));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.P67() returns ($_reverifyPost: bool);
  free requires 94 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall m#1: DatatypeType, n#1: DatatypeType :: 
    { _module.__default.add($LS($LZ), m#1, n#1) } 
    $Is(m#1, Tclass._module.Nat()) && $Is(n#1, Tclass._module.Nat())
       ==> $IsA#_module.Bool(_module.__default.leq($LS($LZ), n#1, _module.__default.add($LS($LZ), m#1, n#1)))
         && 
        _module.__default.add#canCall(m#1, n#1)
         && _module.__default.leq#canCall(n#1, _module.__default.add($LS($LZ), m#1, n#1)));
  ensures (forall m#1: DatatypeType, n#1: DatatypeType :: 
    { _module.__default.add($LS($LS($LZ)), m#1, n#1) } 
    $Is(m#1, Tclass._module.Nat()) && $Is(n#1, Tclass._module.Nat())
       ==> _module.Bool#Equal(_module.__default.leq($LS($LS($LZ)), n#1, _module.__default.add($LS($LS($LZ)), m#1, n#1)), 
        #_module.Bool.True()));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.P67() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var m#0_0: DatatypeType;
  var n#0_0: DatatypeType;
  var ##x#0_0: DatatypeType;
  var ##y#0_0: DatatypeType;
  var ##x#0_1: DatatypeType;
  var ##y#0_1: DatatypeType;
  var m#0_2: DatatypeType;
  var n#0_2: DatatypeType;
  var ##x#0_2: DatatypeType;
  var ##y#0_2: DatatypeType;
  var ##x#0_3: DatatypeType;
  var ##y#0_3: DatatypeType;
  var x#0: DatatypeType;
  var y#0: DatatypeType;
  var ##x#2: DatatypeType;
  var ##y#2: DatatypeType;
  var ##x#3: DatatypeType;
  var ##y#3: DatatypeType;

    // AddMethodImpl: P67, Impl$$_module.__default.P67
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(571,0): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(572,3)
    if (*)
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(574,5)
        // Begin Comprehension WF check
        havoc m#0_0;
        havoc n#0_0;
        if ($Is(m#0_0, Tclass._module.Nat()) && $Is(n#0_0, Tclass._module.Nat()))
        {
            ##x#0_0 := n#0_0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##x#0_0, Tclass._module.Nat(), $Heap);
            ##y#0_0 := m#0_0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##y#0_0, Tclass._module.Nat(), $Heap);
            assume _module.__default.add#canCall(n#0_0, m#0_0);
            ##x#0_1 := n#0_0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##x#0_1, Tclass._module.Nat(), $Heap);
            ##y#0_1 := _module.__default.add($LS($LZ), n#0_0, m#0_0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##y#0_1, Tclass._module.Nat(), $Heap);
            assume _module.__default.leq#canCall(n#0_0, _module.__default.add($LS($LZ), n#0_0, m#0_0));
        }

        // End Comprehension WF check
        assume (forall m#0_1: DatatypeType, n#0_1: DatatypeType :: 
          $Is(m#0_1, Tclass._module.Nat()) && $Is(n#0_1, Tclass._module.Nat())
             ==> $IsA#_module.Bool(_module.__default.leq($LS($LZ), n#0_1, _module.__default.add($LS($LZ), n#0_1, m#0_1)))
               && 
              _module.__default.add#canCall(n#0_1, m#0_1)
               && _module.__default.leq#canCall(n#0_1, _module.__default.add($LS($LZ), n#0_1, m#0_1)));
        assert {:subsumption 0} (forall m#0_1: DatatypeType, n#0_1: DatatypeType :: 
          {:autotriggers false} 
          $Is(m#0_1, Tclass._module.Nat()) && $Is(n#0_1, Tclass._module.Nat())
             ==> _module.Bool#Equal(_module.__default.leq($LS($LS($LZ)), n#0_1, _module.__default.add($LS($LS($LZ)), n#0_1, m#0_1)), 
              #_module.Bool.True()));
        assume (forall m#0_1: DatatypeType, n#0_1: DatatypeType :: 
          {:autotriggers false} 
          $Is(m#0_1, Tclass._module.Nat()) && $Is(n#0_1, Tclass._module.Nat())
             ==> _module.Bool#Equal(_module.__default.leq($LS($LZ), n#0_1, _module.__default.add($LS($LZ), n#0_1, m#0_1)), 
              #_module.Bool.True()));
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(575,5)
        // Begin Comprehension WF check
        havoc m#0_2;
        havoc n#0_2;
        if ($Is(m#0_2, Tclass._module.Nat()) && $Is(n#0_2, Tclass._module.Nat()))
        {
            ##x#0_2 := m#0_2;
            // assume allocatedness for argument to function
            assume $IsAlloc(##x#0_2, Tclass._module.Nat(), $Heap);
            ##y#0_2 := n#0_2;
            // assume allocatedness for argument to function
            assume $IsAlloc(##y#0_2, Tclass._module.Nat(), $Heap);
            assume _module.__default.add#canCall(m#0_2, n#0_2);
            ##x#0_3 := n#0_2;
            // assume allocatedness for argument to function
            assume $IsAlloc(##x#0_3, Tclass._module.Nat(), $Heap);
            ##y#0_3 := m#0_2;
            // assume allocatedness for argument to function
            assume $IsAlloc(##y#0_3, Tclass._module.Nat(), $Heap);
            assume _module.__default.add#canCall(n#0_2, m#0_2);
        }

        // End Comprehension WF check
        assume (forall m#0_3: DatatypeType, n#0_3: DatatypeType :: 
          { _module.__default.add($LS($LZ), n#0_3, m#0_3) } 
            { _module.__default.add($LS($LZ), m#0_3, n#0_3) } 
          $Is(m#0_3, Tclass._module.Nat()) && $Is(n#0_3, Tclass._module.Nat())
             ==> $IsA#_module.Nat(_module.__default.add($LS($LZ), m#0_3, n#0_3))
               && $IsA#_module.Nat(_module.__default.add($LS($LZ), n#0_3, m#0_3))
               && 
              _module.__default.add#canCall(m#0_3, n#0_3)
               && _module.__default.add#canCall(n#0_3, m#0_3));
        assert {:subsumption 0} (forall m#0_3: DatatypeType, n#0_3: DatatypeType :: 
          { _module.__default.add($LS($LS($LZ)), n#0_3, m#0_3) } 
            { _module.__default.add($LS($LS($LZ)), m#0_3, n#0_3) } 
          $Is(m#0_3, Tclass._module.Nat()) && $Is(n#0_3, Tclass._module.Nat())
             ==> _module.Nat#Equal(_module.__default.add($LS($LS($LZ)), m#0_3, n#0_3), 
              _module.__default.add($LS($LS($LZ)), n#0_3, m#0_3)));
        assume (forall m#0_3: DatatypeType, n#0_3: DatatypeType :: 
          { _module.__default.add($LS($LZ), n#0_3, m#0_3) } 
            { _module.__default.add($LS($LZ), m#0_3, n#0_3) } 
          $Is(m#0_3, Tclass._module.Nat()) && $Is(n#0_3, Tclass._module.Nat())
             ==> _module.Nat#Equal(_module.__default.add($LS($LZ), m#0_3, n#0_3), 
              _module.__default.add($LS($LZ), n#0_3, m#0_3)));
    }
    else
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(578,5)
        // Begin Comprehension WF check
        havoc x#0;
        havoc y#0;
        if ($Is(x#0, Tclass._module.Nat()) && $Is(y#0, Tclass._module.Nat()))
        {
            ##x#2 := x#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##x#2, Tclass._module.Nat(), $Heap);
            ##y#2 := #_module.Nat.Suc(y#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##y#2, Tclass._module.Nat(), $Heap);
            assume _module.__default.add#canCall(x#0, #_module.Nat.Suc(y#0));
            ##x#3 := x#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##x#3, Tclass._module.Nat(), $Heap);
            ##y#3 := y#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##y#3, Tclass._module.Nat(), $Heap);
            assume _module.__default.add#canCall(x#0, y#0);
        }

        // End Comprehension WF check
        assume (forall x#1: DatatypeType, y#1: DatatypeType :: 
          { #_module.Nat.Suc(_module.__default.add($LS($LZ), x#1, y#1)) } 
            { _module.__default.add($LS($LZ), x#1, #_module.Nat.Suc(y#1)) } 
          $Is(x#1, Tclass._module.Nat()) && $Is(y#1, Tclass._module.Nat())
             ==> $IsA#_module.Nat(_module.__default.add($LS($LZ), x#1, #_module.Nat.Suc(y#1)))
               && 
              _module.__default.add#canCall(x#1, #_module.Nat.Suc(y#1))
               && _module.__default.add#canCall(x#1, y#1));
        assert {:subsumption 0} (forall x#1: DatatypeType, y#1: DatatypeType :: 
          { #_module.Nat.Suc(_module.__default.add($LS($LS($LZ)), x#1, y#1)) } 
            { _module.__default.add($LS($LS($LZ)), x#1, #_module.Nat.Suc(y#1)) } 
          $Is(x#1, Tclass._module.Nat()) && $Is(y#1, Tclass._module.Nat())
             ==> _module.Nat#Equal(_module.__default.add($LS($LS($LZ)), x#1, #_module.Nat.Suc(y#1)), 
              #_module.Nat.Suc(_module.__default.add($LS($LS($LZ)), x#1, y#1))));
        assume (forall x#1: DatatypeType, y#1: DatatypeType :: 
          { #_module.Nat.Suc(_module.__default.add($LS($LZ), x#1, y#1)) } 
            { _module.__default.add($LS($LZ), x#1, #_module.Nat.Suc(y#1)) } 
          $Is(x#1, Tclass._module.Nat()) && $Is(y#1, Tclass._module.Nat())
             ==> _module.Nat#Equal(_module.__default.add($LS($LZ), x#1, #_module.Nat.Suc(y#1)), 
              #_module.Nat.Suc(_module.__default.add($LS($LZ), x#1, y#1))));
    }
}



procedure {:_induction n#0, xs#0} CheckWellformed$$_module.__default.P1__alt(n#0: DatatypeType
       where $Is(n#0, Tclass._module.Nat())
         && $IsAlloc(n#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(n#0), 
    xs#0: DatatypeType
       where $Is(xs#0, Tclass._module.List())
         && $IsAlloc(xs#0, Tclass._module.List(), $Heap)
         && $IsA#_module.List(xs#0));
  free requires 40 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction n#0, xs#0} Call$$_module.__default.P1__alt(n#0: DatatypeType
       where $Is(n#0, Tclass._module.Nat())
         && $IsAlloc(n#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(n#0), 
    xs#0: DatatypeType
       where $Is(xs#0, Tclass._module.List())
         && $IsAlloc(xs#0, Tclass._module.List(), $Heap)
         && $IsA#_module.List(xs#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.List(_module.__default.concat($LS($LZ), 
        _module.__default.take($LS($LZ), n#0, xs#0), 
        _module.__default.drop($LS($LZ), n#0, xs#0)))
     && $IsA#_module.List(xs#0)
     && 
    _module.__default.take#canCall(n#0, xs#0)
     && _module.__default.drop#canCall(n#0, xs#0)
     && _module.__default.concat#canCall(_module.__default.take($LS($LZ), n#0, xs#0), 
      _module.__default.drop($LS($LZ), n#0, xs#0));
  ensures _module.List#Equal(_module.__default.concat($LS($LS($LZ)), 
      _module.__default.take($LS($LS($LZ)), n#0, xs#0), 
      _module.__default.drop($LS($LS($LZ)), n#0, xs#0)), 
    xs#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction n#0, xs#0} Impl$$_module.__default.P1__alt(n#0: DatatypeType
       where $Is(n#0, Tclass._module.Nat())
         && $IsAlloc(n#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(n#0), 
    xs#0: DatatypeType
       where $Is(xs#0, Tclass._module.List())
         && $IsAlloc(xs#0, Tclass._module.List(), $Heap)
         && $IsA#_module.List(xs#0))
   returns ($_reverifyPost: bool);
  free requires 40 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.List(_module.__default.concat($LS($LZ), 
        _module.__default.take($LS($LZ), n#0, xs#0), 
        _module.__default.drop($LS($LZ), n#0, xs#0)))
     && $IsA#_module.List(xs#0)
     && 
    _module.__default.take#canCall(n#0, xs#0)
     && _module.__default.drop#canCall(n#0, xs#0)
     && _module.__default.concat#canCall(_module.__default.take($LS($LZ), n#0, xs#0), 
      _module.__default.drop($LS($LZ), n#0, xs#0));
  ensures _module.List#Equal(_module.__default.concat($LS($LS($LZ)), 
      _module.__default.take($LS($LS($LZ)), n#0, xs#0), 
      _module.__default.drop($LS($LS($LZ)), n#0, xs#0)), 
    xs#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction n#0, xs#0} Impl$$_module.__default.P1__alt(n#0: DatatypeType, xs#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;

    // AddMethodImpl: P1_alt, Impl$$_module.__default.P1__alt
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(587,0): initial state"} true;
    assume $IsA#_module.Nat(n#0);
    assume $IsA#_module.List(xs#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#n0#0: DatatypeType, $ih#xs0#0: DatatypeType :: 
      $Is($ih#n0#0, Tclass._module.Nat())
           && $Is($ih#xs0#0, Tclass._module.List())
           && Lit(true)
           && (DtRank($ih#n0#0) < DtRank(n#0)
             || (DtRank($ih#n0#0) == DtRank(n#0) && DtRank($ih#xs0#0) < DtRank(xs#0)))
         ==> _module.List#Equal(_module.__default.concat($LS($LZ), 
            _module.__default.take($LS($LZ), $ih#n0#0, $ih#xs0#0), 
            _module.__default.drop($LS($LZ), $ih#n0#0, $ih#xs0#0)), 
          $ih#xs0#0));
    $_reverifyPost := false;
}



procedure {:_induction n#0, xs#0, ys#0} CheckWellformed$$_module.__default.P2__alt(n#0: DatatypeType
       where $Is(n#0, Tclass._module.Nat())
         && $IsAlloc(n#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(n#0), 
    xs#0: DatatypeType
       where $Is(xs#0, Tclass._module.List())
         && $IsAlloc(xs#0, Tclass._module.List(), $Heap)
         && $IsA#_module.List(xs#0), 
    ys#0: DatatypeType
       where $Is(ys#0, Tclass._module.List())
         && $IsAlloc(ys#0, Tclass._module.List(), $Heap)
         && $IsA#_module.List(ys#0));
  free requires 41 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction n#0, xs#0, ys#0} Call$$_module.__default.P2__alt(n#0: DatatypeType
       where $Is(n#0, Tclass._module.Nat())
         && $IsAlloc(n#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(n#0), 
    xs#0: DatatypeType
       where $Is(xs#0, Tclass._module.List())
         && $IsAlloc(xs#0, Tclass._module.List(), $Heap)
         && $IsA#_module.List(xs#0), 
    ys#0: DatatypeType
       where $Is(ys#0, Tclass._module.List())
         && $IsAlloc(ys#0, Tclass._module.List(), $Heap)
         && $IsA#_module.List(ys#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Nat(_module.__default.add($LS($LZ), 
        _module.__default.count($LS($LZ), n#0, xs#0), 
        _module.__default.count($LS($LZ), n#0, ys#0)))
     && $IsA#_module.Nat(_module.__default.count($LS($LZ), n#0, _module.__default.concat($LS($LZ), xs#0, ys#0)))
     && 
    _module.__default.count#canCall(n#0, xs#0)
     && _module.__default.count#canCall(n#0, ys#0)
     && _module.__default.add#canCall(_module.__default.count($LS($LZ), n#0, xs#0), 
      _module.__default.count($LS($LZ), n#0, ys#0))
     && 
    _module.__default.concat#canCall(xs#0, ys#0)
     && _module.__default.count#canCall(n#0, _module.__default.concat($LS($LZ), xs#0, ys#0));
  ensures _module.Nat#Equal(_module.__default.add($LS($LS($LZ)), 
      _module.__default.count($LS($LS($LZ)), n#0, xs#0), 
      _module.__default.count($LS($LS($LZ)), n#0, ys#0)), 
    _module.__default.count($LS($LS($LZ)), n#0, _module.__default.concat($LS($LS($LZ)), xs#0, ys#0)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction n#0, xs#0, ys#0} Impl$$_module.__default.P2__alt(n#0: DatatypeType
       where $Is(n#0, Tclass._module.Nat())
         && $IsAlloc(n#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(n#0), 
    xs#0: DatatypeType
       where $Is(xs#0, Tclass._module.List())
         && $IsAlloc(xs#0, Tclass._module.List(), $Heap)
         && $IsA#_module.List(xs#0), 
    ys#0: DatatypeType
       where $Is(ys#0, Tclass._module.List())
         && $IsAlloc(ys#0, Tclass._module.List(), $Heap)
         && $IsA#_module.List(ys#0))
   returns ($_reverifyPost: bool);
  free requires 41 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Nat(_module.__default.add($LS($LZ), 
        _module.__default.count($LS($LZ), n#0, xs#0), 
        _module.__default.count($LS($LZ), n#0, ys#0)))
     && $IsA#_module.Nat(_module.__default.count($LS($LZ), n#0, _module.__default.concat($LS($LZ), xs#0, ys#0)))
     && 
    _module.__default.count#canCall(n#0, xs#0)
     && _module.__default.count#canCall(n#0, ys#0)
     && _module.__default.add#canCall(_module.__default.count($LS($LZ), n#0, xs#0), 
      _module.__default.count($LS($LZ), n#0, ys#0))
     && 
    _module.__default.concat#canCall(xs#0, ys#0)
     && _module.__default.count#canCall(n#0, _module.__default.concat($LS($LZ), xs#0, ys#0));
  ensures _module.Nat#Equal(_module.__default.add($LS($LS($LZ)), 
      _module.__default.count($LS($LS($LZ)), n#0, xs#0), 
      _module.__default.count($LS($LS($LZ)), n#0, ys#0)), 
    _module.__default.count($LS($LS($LZ)), n#0, _module.__default.concat($LS($LS($LZ)), xs#0, ys#0)));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction n#0, xs#0, ys#0} Impl$$_module.__default.P2__alt(n#0: DatatypeType, xs#0: DatatypeType, ys#0: DatatypeType)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;

    // AddMethodImpl: P2_alt, Impl$$_module.__default.P2__alt
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(592,0): initial state"} true;
    assume $IsA#_module.Nat(n#0);
    assume $IsA#_module.List(xs#0);
    assume $IsA#_module.List(ys#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#n0#0: DatatypeType, $ih#xs0#0: DatatypeType, $ih#ys0#0: DatatypeType :: 
      $Is($ih#n0#0, Tclass._module.Nat())
           && $Is($ih#xs0#0, Tclass._module.List())
           && $Is($ih#ys0#0, Tclass._module.List())
           && Lit(true)
           && (DtRank($ih#n0#0) < DtRank(n#0)
             || (DtRank($ih#n0#0) == DtRank(n#0)
               && (DtRank($ih#xs0#0) < DtRank(xs#0)
                 || (DtRank($ih#xs0#0) == DtRank(xs#0) && DtRank($ih#ys0#0) < DtRank(ys#0)))))
         ==> _module.Nat#Equal(_module.__default.add($LS($LZ), 
            _module.__default.count($LS($LZ), $ih#n0#0, $ih#xs0#0), 
            _module.__default.count($LS($LZ), $ih#n0#0, $ih#ys0#0)), 
          _module.__default.count($LS($LZ), $ih#n0#0, _module.__default.concat($LS($LZ), $ih#xs0#0, $ih#ys0#0))));
    $_reverifyPost := false;
}



procedure {:_induction xs#0, ys#0} CheckWellformed$$_module.__default.Lemma__RevConcat(xs#0: DatatypeType
       where $Is(xs#0, Tclass._module.List())
         && $IsAlloc(xs#0, Tclass._module.List(), $Heap)
         && $IsA#_module.List(xs#0), 
    ys#0: DatatypeType
       where $Is(ys#0, Tclass._module.List())
         && $IsAlloc(ys#0, Tclass._module.List(), $Heap)
         && $IsA#_module.List(ys#0));
  free requires 42 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction xs#0, ys#0} Call$$_module.__default.Lemma__RevConcat(xs#0: DatatypeType
       where $Is(xs#0, Tclass._module.List())
         && $IsAlloc(xs#0, Tclass._module.List(), $Heap)
         && $IsA#_module.List(xs#0), 
    ys#0: DatatypeType
       where $Is(ys#0, Tclass._module.List())
         && $IsAlloc(ys#0, Tclass._module.List(), $Heap)
         && $IsA#_module.List(ys#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.List(_module.__default.reverse($LS($LZ), _module.__default.concat($LS($LZ), xs#0, ys#0)))
     && $IsA#_module.List(_module.__default.concat($LS($LZ), 
        _module.__default.reverse($LS($LZ), ys#0), 
        _module.__default.reverse($LS($LZ), xs#0)))
     && 
    _module.__default.concat#canCall(xs#0, ys#0)
     && _module.__default.reverse#canCall(_module.__default.concat($LS($LZ), xs#0, ys#0))
     && 
    _module.__default.reverse#canCall(ys#0)
     && _module.__default.reverse#canCall(xs#0)
     && _module.__default.concat#canCall(_module.__default.reverse($LS($LZ), ys#0), 
      _module.__default.reverse($LS($LZ), xs#0));
  ensures _module.List#Equal(_module.__default.reverse($LS($LS($LZ)), _module.__default.concat($LS($LS($LZ)), xs#0, ys#0)), 
    _module.__default.concat($LS($LS($LZ)), 
      _module.__default.reverse($LS($LS($LZ)), ys#0), 
      _module.__default.reverse($LS($LS($LZ)), xs#0)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction xs#0, ys#0} Impl$$_module.__default.Lemma__RevConcat(xs#0: DatatypeType
       where $Is(xs#0, Tclass._module.List())
         && $IsAlloc(xs#0, Tclass._module.List(), $Heap)
         && $IsA#_module.List(xs#0), 
    ys#0: DatatypeType
       where $Is(ys#0, Tclass._module.List())
         && $IsAlloc(ys#0, Tclass._module.List(), $Heap)
         && $IsA#_module.List(ys#0))
   returns ($_reverifyPost: bool);
  free requires 42 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.List(_module.__default.reverse($LS($LZ), _module.__default.concat($LS($LZ), xs#0, ys#0)))
     && $IsA#_module.List(_module.__default.concat($LS($LZ), 
        _module.__default.reverse($LS($LZ), ys#0), 
        _module.__default.reverse($LS($LZ), xs#0)))
     && 
    _module.__default.concat#canCall(xs#0, ys#0)
     && _module.__default.reverse#canCall(_module.__default.concat($LS($LZ), xs#0, ys#0))
     && 
    _module.__default.reverse#canCall(ys#0)
     && _module.__default.reverse#canCall(xs#0)
     && _module.__default.concat#canCall(_module.__default.reverse($LS($LZ), ys#0), 
      _module.__default.reverse($LS($LZ), xs#0));
  ensures _module.List#Equal(_module.__default.reverse($LS($LS($LZ)), _module.__default.concat($LS($LS($LZ)), xs#0, ys#0)), 
    _module.__default.concat($LS($LS($LZ)), 
      _module.__default.reverse($LS($LS($LZ)), ys#0), 
      _module.__default.reverse($LS($LS($LZ)), xs#0)));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction xs#0, ys#0} Impl$$_module.__default.Lemma__RevConcat(xs#0: DatatypeType, ys#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var _mcc#0#0_0: DatatypeType;
  var _mcc#1#0_0: DatatypeType;
  var rest#0_0: DatatypeType;
  var let#0_0#0#0: DatatypeType;
  var t#0_0: DatatypeType;
  var let#0_1#0#0: DatatypeType;
  var a#0_0: DatatypeType;
  var b#0_0: DatatypeType;
  var c#0_0: DatatypeType;
  var ##xs#0_0: DatatypeType;
  var ##ys#0_0: DatatypeType;
  var ##xs#0_1: DatatypeType;
  var ##ys#0_1: DatatypeType;
  var ##xs#0_2: DatatypeType;
  var ##ys#0_2: DatatypeType;
  var ##xs#0_3: DatatypeType;
  var ##ys#0_3: DatatypeType;
  var ws#1_0: DatatypeType;
  var ##xs#1_0: DatatypeType;
  var ##ys#1_0: DatatypeType;

    // AddMethodImpl: Lemma_RevConcat, Impl$$_module.__default.Lemma__RevConcat
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(599,0): initial state"} true;
    assume $IsA#_module.List(xs#0);
    assume $IsA#_module.List(ys#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#xs0#0: DatatypeType, $ih#ys0#0: DatatypeType :: 
      $Is($ih#xs0#0, Tclass._module.List())
           && $Is($ih#ys0#0, Tclass._module.List())
           && Lit(true)
           && (DtRank($ih#xs0#0) < DtRank(xs#0)
             || (DtRank($ih#xs0#0) == DtRank(xs#0) && DtRank($ih#ys0#0) < DtRank(ys#0)))
         ==> _module.List#Equal(_module.__default.reverse($LS($LZ), _module.__default.concat($LS($LZ), $ih#xs0#0, $ih#ys0#0)), 
          _module.__default.concat($LS($LZ), 
            _module.__default.reverse($LS($LZ), $ih#ys0#0), 
            _module.__default.reverse($LS($LZ), $ih#xs0#0))));
    $_reverifyPost := false;
    assume true;
    havoc _mcc#0#0_0, _mcc#1#0_0;
    if (xs#0 == #_module.List.Nil())
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(602,7)
        // Begin Comprehension WF check
        havoc ws#1_0;
        if ($Is(ws#1_0, Tclass._module.List()))
        {
            ##xs#1_0 := ws#1_0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##xs#1_0, Tclass._module.List(), $Heap);
            ##ys#1_0 := Lit(#_module.List.Nil());
            // assume allocatedness for argument to function
            assume $IsAlloc(##ys#1_0, Tclass._module.List(), $Heap);
            assume _module.__default.concat#canCall(ws#1_0, Lit(#_module.List.Nil()));
        }

        // End Comprehension WF check
        assume (forall ws#1_1: DatatypeType :: 
          { _module.__default.concat($LS($LZ), ws#1_1, #_module.List.Nil()) } 
          $Is(ws#1_1, Tclass._module.List())
             ==> $IsA#_module.List(_module.__default.concat($LS($LZ), ws#1_1, Lit(#_module.List.Nil())))
               && $IsA#_module.List(ws#1_1)
               && _module.__default.concat#canCall(ws#1_1, Lit(#_module.List.Nil())));
        assert {:subsumption 0} (forall ws#1_1: DatatypeType :: 
          { _module.__default.concat($LS($LS($LZ)), ws#1_1, #_module.List.Nil()) } 
          $Is(ws#1_1, Tclass._module.List())
             ==> _module.List#Equal(_module.__default.concat($LS($LS($LZ)), ws#1_1, Lit(#_module.List.Nil())), 
              ws#1_1));
        assume (forall ws#1_1: DatatypeType :: 
          { _module.__default.concat($LS($LZ), ws#1_1, #_module.List.Nil()) } 
          $Is(ws#1_1, Tclass._module.List())
             ==> _module.List#Equal(_module.__default.concat($LS($LZ), ws#1_1, Lit(#_module.List.Nil())), ws#1_1));
    }
    else if (xs#0 == #_module.List.Cons(_mcc#0#0_0, _mcc#1#0_0))
    {
        assume $Is(_mcc#0#0_0, Tclass._module.Nat());
        assume $Is(_mcc#1#0_0, Tclass._module.List());
        havoc rest#0_0;
        assume $Is(rest#0_0, Tclass._module.List())
           && $IsAlloc(rest#0_0, Tclass._module.List(), $Heap);
        assume let#0_0#0#0 == _mcc#1#0_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_0#0#0, Tclass._module.List());
        assume rest#0_0 == let#0_0#0#0;
        havoc t#0_0;
        assume $Is(t#0_0, Tclass._module.Nat()) && $IsAlloc(t#0_0, Tclass._module.Nat(), $Heap);
        assume let#0_1#0#0 == _mcc#0#0_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_1#0#0, Tclass._module.Nat());
        assume t#0_0 == let#0_1#0#0;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(604,7)
        // Begin Comprehension WF check
        havoc a#0_0;
        havoc b#0_0;
        havoc c#0_0;
        if ($Is(a#0_0, Tclass._module.List())
           && $Is(b#0_0, Tclass._module.List())
           && $Is(c#0_0, Tclass._module.List()))
        {
            ##xs#0_0 := b#0_0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##xs#0_0, Tclass._module.List(), $Heap);
            ##ys#0_0 := c#0_0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##ys#0_0, Tclass._module.List(), $Heap);
            assume _module.__default.concat#canCall(b#0_0, c#0_0);
            ##xs#0_1 := a#0_0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##xs#0_1, Tclass._module.List(), $Heap);
            ##ys#0_1 := _module.__default.concat($LS($LZ), b#0_0, c#0_0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##ys#0_1, Tclass._module.List(), $Heap);
            assume _module.__default.concat#canCall(a#0_0, _module.__default.concat($LS($LZ), b#0_0, c#0_0));
            ##xs#0_2 := a#0_0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##xs#0_2, Tclass._module.List(), $Heap);
            ##ys#0_2 := b#0_0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##ys#0_2, Tclass._module.List(), $Heap);
            assume _module.__default.concat#canCall(a#0_0, b#0_0);
            ##xs#0_3 := _module.__default.concat($LS($LZ), a#0_0, b#0_0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##xs#0_3, Tclass._module.List(), $Heap);
            ##ys#0_3 := c#0_0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##ys#0_3, Tclass._module.List(), $Heap);
            assume _module.__default.concat#canCall(_module.__default.concat($LS($LZ), a#0_0, b#0_0), c#0_0);
        }

        // End Comprehension WF check
        assume (forall a#0_1: DatatypeType, b#0_1: DatatypeType, c#0_1: DatatypeType :: 
          { _module.__default.concat($LS($LZ), _module.__default.concat($LS($LZ), a#0_1, b#0_1), c#0_1) } 
            { _module.__default.concat($LS($LZ), a#0_1, _module.__default.concat($LS($LZ), b#0_1, c#0_1)) } 
          $Is(a#0_1, Tclass._module.List())
               && $Is(b#0_1, Tclass._module.List())
               && $Is(c#0_1, Tclass._module.List())
             ==> $IsA#_module.List(_module.__default.concat($LS($LZ), a#0_1, _module.__default.concat($LS($LZ), b#0_1, c#0_1)))
               && $IsA#_module.List(_module.__default.concat($LS($LZ), _module.__default.concat($LS($LZ), a#0_1, b#0_1), c#0_1))
               && 
              _module.__default.concat#canCall(b#0_1, c#0_1)
               && _module.__default.concat#canCall(a#0_1, _module.__default.concat($LS($LZ), b#0_1, c#0_1))
               && 
              _module.__default.concat#canCall(a#0_1, b#0_1)
               && _module.__default.concat#canCall(_module.__default.concat($LS($LZ), a#0_1, b#0_1), c#0_1));
        assert {:subsumption 0} (forall a#0_1: DatatypeType, b#0_1: DatatypeType, c#0_1: DatatypeType :: 
          { _module.__default.concat($LS($LS($LZ)), _module.__default.concat($LS($LS($LZ)), a#0_1, b#0_1), c#0_1) } 
            { _module.__default.concat($LS($LS($LZ)), a#0_1, _module.__default.concat($LS($LS($LZ)), b#0_1, c#0_1)) } 
          $Is(a#0_1, Tclass._module.List())
               && $Is(b#0_1, Tclass._module.List())
               && $Is(c#0_1, Tclass._module.List())
             ==> _module.List#Equal(_module.__default.concat($LS($LS($LZ)), a#0_1, _module.__default.concat($LS($LS($LZ)), b#0_1, c#0_1)), 
              _module.__default.concat($LS($LS($LZ)), _module.__default.concat($LS($LS($LZ)), a#0_1, b#0_1), c#0_1)));
        assume (forall a#0_1: DatatypeType, b#0_1: DatatypeType, c#0_1: DatatypeType :: 
          { _module.__default.concat($LS($LZ), _module.__default.concat($LS($LZ), a#0_1, b#0_1), c#0_1) } 
            { _module.__default.concat($LS($LZ), a#0_1, _module.__default.concat($LS($LZ), b#0_1, c#0_1)) } 
          $Is(a#0_1, Tclass._module.List())
               && $Is(b#0_1, Tclass._module.List())
               && $Is(c#0_1, Tclass._module.List())
             ==> _module.List#Equal(_module.__default.concat($LS($LZ), a#0_1, _module.__default.concat($LS($LZ), b#0_1, c#0_1)), 
              _module.__default.concat($LS($LZ), _module.__default.concat($LS($LZ), a#0_1, b#0_1), c#0_1)));
    }
    else
    {
        assume false;
    }
}



procedure {:_induction xs#0} CheckWellformed$$_module.__default.Theorem(xs#0: DatatypeType
       where $Is(xs#0, Tclass._module.List())
         && $IsAlloc(xs#0, Tclass._module.List(), $Heap)
         && $IsA#_module.List(xs#0));
  free requires 43 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction xs#0} Call$$_module.__default.Theorem(xs#0: DatatypeType
       where $Is(xs#0, Tclass._module.List())
         && $IsAlloc(xs#0, Tclass._module.List(), $Heap)
         && $IsA#_module.List(xs#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.List(_module.__default.reverse($LS($LZ), _module.__default.reverse($LS($LZ), xs#0)))
     && $IsA#_module.List(xs#0)
     && 
    _module.__default.reverse#canCall(xs#0)
     && _module.__default.reverse#canCall(_module.__default.reverse($LS($LZ), xs#0));
  ensures _module.List#Equal(_module.__default.reverse($LS($LS($LZ)), _module.__default.reverse($LS($LS($LZ)), xs#0)), 
    xs#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction xs#0} Impl$$_module.__default.Theorem(xs#0: DatatypeType
       where $Is(xs#0, Tclass._module.List())
         && $IsAlloc(xs#0, Tclass._module.List(), $Heap)
         && $IsA#_module.List(xs#0))
   returns ($_reverifyPost: bool);
  free requires 43 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.List(_module.__default.reverse($LS($LZ), _module.__default.reverse($LS($LZ), xs#0)))
     && $IsA#_module.List(xs#0)
     && 
    _module.__default.reverse#canCall(xs#0)
     && _module.__default.reverse#canCall(_module.__default.reverse($LS($LZ), xs#0));
  ensures _module.List#Equal(_module.__default.reverse($LS($LS($LZ)), _module.__default.reverse($LS($LS($LZ)), xs#0)), 
    xs#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction xs#0} Impl$$_module.__default.Theorem(xs#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var _mcc#0#0_0: DatatypeType;
  var _mcc#1#0_0: DatatypeType;
  var rest#0_0: DatatypeType;
  var let#0_0#0#0: DatatypeType;
  var t#0_0: DatatypeType;
  var let#0_1#0#0: DatatypeType;
  var xs##0_0: DatatypeType;
  var ##xs#0_0: DatatypeType;
  var ys##0_0: DatatypeType;

    // AddMethodImpl: Theorem, Impl$$_module.__default.Theorem
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(610,0): initial state"} true;
    assume $IsA#_module.List(xs#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#xs0#0: DatatypeType :: 
      $Is($ih#xs0#0, Tclass._module.List())
           && Lit(true)
           && DtRank($ih#xs0#0) < DtRank(xs#0)
         ==> _module.List#Equal(_module.__default.reverse($LS($LZ), _module.__default.reverse($LS($LZ), $ih#xs0#0)), 
          $ih#xs0#0));
    $_reverifyPost := false;
    assume true;
    havoc _mcc#0#0_0, _mcc#1#0_0;
    if (xs#0 == #_module.List.Nil())
    {
    }
    else if (xs#0 == #_module.List.Cons(_mcc#0#0_0, _mcc#1#0_0))
    {
        assume $Is(_mcc#0#0_0, Tclass._module.Nat());
        assume $Is(_mcc#1#0_0, Tclass._module.List());
        havoc rest#0_0;
        assume $Is(rest#0_0, Tclass._module.List())
           && $IsAlloc(rest#0_0, Tclass._module.List(), $Heap);
        assume let#0_0#0#0 == _mcc#1#0_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_0#0#0, Tclass._module.List());
        assume rest#0_0 == let#0_0#0#0;
        havoc t#0_0;
        assume $Is(t#0_0, Tclass._module.Nat()) && $IsAlloc(t#0_0, Tclass._module.Nat(), $Heap);
        assume let#0_1#0#0 == _mcc#0#0_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_1#0#0, Tclass._module.Nat());
        assume t#0_0 == let#0_1#0#0;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(614,22)
        // TrCallStmt: Before ProcessCallStmt
        ##xs#0_0 := rest#0_0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##xs#0_0, Tclass._module.List(), $Heap);
        assume _module.__default.reverse#canCall(rest#0_0);
        assume _module.__default.reverse#canCall(rest#0_0);
        // ProcessCallStmt: CheckSubrange
        xs##0_0 := _module.__default.reverse($LS($LZ), rest#0_0);
        assume true;
        // ProcessCallStmt: CheckSubrange
        ys##0_0 := #_module.List.Cons(t#0_0, Lit(#_module.List.Nil()));
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.Lemma__RevConcat(xs##0_0, ys##0_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/Rippling.dfy(614,50)"} true;
    }
    else
    {
        assume false;
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

const unique tytagFamily$Bool: TyTagFamily;

const unique tytagFamily$Nat: TyTagFamily;

const unique tytagFamily$List: TyTagFamily;

const unique tytagFamily$Pair: TyTagFamily;

const unique tytagFamily$PList: TyTagFamily;

const unique tytagFamily$Tree: TyTagFamily;

const unique tytagFamily$_default: TyTagFamily;
