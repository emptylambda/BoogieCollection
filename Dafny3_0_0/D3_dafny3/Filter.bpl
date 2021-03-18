// Dafny 3.0.0.30204
// Command Line Options: -compile:0 -noVerify /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy -print:./Filter.bpl

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

// Constructor function declaration
function #_module.Stream.Cons(Box, DatatypeType) : DatatypeType;

const unique ##_module.Stream.Cons: DtCtorId;

// Constructor identifier
axiom (forall a#14#0#0: Box, a#14#1#0: DatatypeType :: 
  { #_module.Stream.Cons(a#14#0#0, a#14#1#0) } 
  DatatypeCtorId(#_module.Stream.Cons(a#14#0#0, a#14#1#0))
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
     ==> (exists a#15#0#0: Box, a#15#1#0: DatatypeType :: 
      d == #_module.Stream.Cons(a#15#0#0, a#15#1#0)));

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
axiom (forall _module.Stream$T: Ty, a#16#0#0: Box, a#16#1#0: DatatypeType :: 
  { $Is(#_module.Stream.Cons(a#16#0#0, a#16#1#0), 
      Tclass._module.Stream(_module.Stream$T)) } 
  $Is(#_module.Stream.Cons(a#16#0#0, a#16#1#0), 
      Tclass._module.Stream(_module.Stream$T))
     <==> $IsBox(a#16#0#0, _module.Stream$T)
       && $Is(a#16#1#0, Tclass._module.Stream(_module.Stream$T)));

// Constructor $IsAlloc
axiom (forall _module.Stream$T: Ty, a#17#0#0: Box, a#17#1#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#_module.Stream.Cons(a#17#0#0, a#17#1#0), 
      Tclass._module.Stream(_module.Stream$T), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Stream.Cons(a#17#0#0, a#17#1#0), 
        Tclass._module.Stream(_module.Stream$T), 
        $h)
       <==> $IsAllocBox(a#17#0#0, _module.Stream$T, $h)
         && $IsAlloc(a#17#1#0, Tclass._module.Stream(_module.Stream$T), $h)));

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
axiom (forall a#18#0#0: Box, a#18#1#0: DatatypeType :: 
  { #_module.Stream.Cons(a#18#0#0, a#18#1#0) } 
  _module.Stream.head(#_module.Stream.Cons(a#18#0#0, a#18#1#0)) == a#18#0#0);

function _module.Stream.tail(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#19#0#0: Box, a#19#1#0: DatatypeType :: 
  { #_module.Stream.Cons(a#19#0#0, a#19#1#0) } 
  _module.Stream.tail(#_module.Stream.Cons(a#19#0#0, a#19#1#0)) == a#19#1#0);

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
axiom 2 <= $FunctionContextHeight
   ==> (forall _module._default.Tail$_T0: Ty, $ly: LayerType, s#0: DatatypeType, n#0: int :: 
    { _module.__default.Tail(_module._default.Tail$_T0, $ly, s#0, n#0) } 
    _module.__default.Tail#canCall(_module._default.Tail$_T0, s#0, n#0)
         || (2 != $FunctionContextHeight
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
axiom 2 <= $FunctionContextHeight
   ==> (forall _module._default.Tail$_T0: Ty, $ly: LayerType, s#0: DatatypeType, n#0: int :: 
    { _module.__default.Tail(_module._default.Tail$_T0, $LS($ly), s#0, n#0) } 
    _module.__default.Tail#canCall(_module._default.Tail$_T0, s#0, n#0)
         || (2 != $FunctionContextHeight
           && 
          $Is(s#0, Tclass._module.Stream(_module._default.Tail$_T0))
           && LitInt(0) <= n#0)
       ==> (n#0 != LitInt(0)
           ==> _module.Stream.Cons_q(s#0)
             && _module.__default.Tail#canCall(_module._default.Tail$_T0, _module.Stream.tail(s#0), n#0 - 1))
         && _module.__default.Tail(_module._default.Tail$_T0, $LS($ly), s#0, n#0)
           == (if n#0 == LitInt(0)
             then s#0
             else _module.__default.Tail(_module._default.Tail$_T0, $ly, _module.Stream.tail(s#0), n#0 - 1)));

// definition axiom for _module.__default.Tail for decreasing-related literals (revealed)
axiom 2 <= $FunctionContextHeight
   ==> (forall _module._default.Tail$_T0: Ty, $ly: LayerType, s#0: DatatypeType, n#0: int :: 
    {:weight 3} { _module.__default.Tail(_module._default.Tail$_T0, $LS($ly), s#0, LitInt(n#0)) } 
    _module.__default.Tail#canCall(_module._default.Tail$_T0, s#0, LitInt(n#0))
         || (2 != $FunctionContextHeight
           && 
          $Is(s#0, Tclass._module.Stream(_module._default.Tail$_T0))
           && LitInt(0) <= n#0)
       ==> (LitInt(n#0) != LitInt(0)
           ==> _module.Stream.Cons_q(s#0)
             && _module.__default.Tail#canCall(_module._default.Tail$_T0, _module.Stream.tail(s#0), LitInt(n#0 - 1)))
         && _module.__default.Tail(_module._default.Tail$_T0, $LS($ly), s#0, LitInt(n#0))
           == (if LitInt(n#0) == LitInt(0)
             then s#0
             else _module.__default.Tail(_module._default.Tail$_T0, $LS($ly), _module.Stream.tail(s#0), LitInt(n#0 - 1))));

// definition axiom for _module.__default.Tail for all literals (revealed)
axiom 2 <= $FunctionContextHeight
   ==> (forall _module._default.Tail$_T0: Ty, $ly: LayerType, s#0: DatatypeType, n#0: int :: 
    {:weight 3} { _module.__default.Tail(_module._default.Tail$_T0, $LS($ly), Lit(s#0), LitInt(n#0)) } 
    _module.__default.Tail#canCall(_module._default.Tail$_T0, Lit(s#0), LitInt(n#0))
         || (2 != $FunctionContextHeight
           && 
          $Is(s#0, Tclass._module.Stream(_module._default.Tail$_T0))
           && LitInt(0) <= n#0)
       ==> (LitInt(n#0) != LitInt(0)
           ==> _module.Stream.Cons_q(Lit(s#0))
             && _module.__default.Tail#canCall(_module._default.Tail$_T0, Lit(_module.Stream.tail(Lit(s#0))), LitInt(n#0 - 1)))
         && _module.__default.Tail(_module._default.Tail$_T0, $LS($ly), Lit(s#0), LitInt(n#0))
           == (if LitInt(n#0) == LitInt(0)
             then s#0
             else _module.__default.Tail(_module._default.Tail$_T0, 
              $LS($ly), 
              Lit(_module.Stream.tail(Lit(s#0))), 
              LitInt(n#0 - 1))));

procedure CheckWellformed$$_module.__default.Tail(_module._default.Tail$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Tail$_T0)), 
    n#0: int where LitInt(0) <= n#0);
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Tail(_module._default.Tail$_T0: Ty, s#0: DatatypeType, n#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##s#0: DatatypeType;
  var ##n#0: int;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function Tail
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(6,9): initial state"} true;
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
            assume _module.Stream.Cons_q(s#0);
            ##s#0 := _module.Stream.tail(s#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#0, Tclass._module.Stream(_module._default.Tail$_T0), $Heap);
            assert $Is(n#0 - 1, Tclass._System.nat());
            ##n#0 := n#0 - 1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0 <= n#0 || ##n#0 == n#0;
            assert ##n#0 < n#0;
            assume _module.__default.Tail#canCall(_module._default.Tail$_T0, _module.Stream.tail(s#0), n#0 - 1);
            assume _module.Stream.Cons_q(_module.__default.Tail(_module._default.Tail$_T0, $LS($LZ), _module.Stream.tail(s#0), n#0 - 1));
            assume _module.__default.Tail(_module._default.Tail$_T0, $LS($LZ), s#0, n#0)
               == _module.__default.Tail(_module._default.Tail$_T0, $LS($LZ), _module.Stream.tail(s#0), n#0 - 1);
            assume _module.Stream.Cons_q(s#0)
               && _module.__default.Tail#canCall(_module._default.Tail$_T0, _module.Stream.tail(s#0), n#0 - 1);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.Tail(_module._default.Tail$_T0, $LS($LZ), s#0, n#0), 
              Tclass._module.Stream(_module._default.Tail$_T0));
        }

        assert b$reqreads#0;
    }
}



// function declaration for _module._default.In
function _module.__default.In(_module._default.In$T: Ty, x#0: Box, s#0: DatatypeType) : bool;

function _module.__default.In#canCall(_module._default.In$T: Ty, x#0: Box, s#0: DatatypeType) : bool;

// consequence axiom for _module.__default.In
axiom 3 <= $FunctionContextHeight
   ==> (forall _module._default.In$T: Ty, x#0: Box, s#0: DatatypeType :: 
    { _module.__default.In(_module._default.In$T, x#0, s#0) } 
    _module.__default.In#canCall(_module._default.In$T, x#0, s#0)
         || (3 != $FunctionContextHeight
           && 
          $IsBox(x#0, _module._default.In$T)
           && $Is(s#0, Tclass._module.Stream(_module._default.In$T)))
       ==> true);

function _module.__default.In#requires(Ty, Box, DatatypeType) : bool;

// #requires axiom for _module.__default.In
axiom (forall _module._default.In$T: Ty, x#0: Box, s#0: DatatypeType :: 
  { _module.__default.In#requires(_module._default.In$T, x#0, s#0) } 
  $IsBox(x#0, _module._default.In$T)
       && $Is(s#0, Tclass._module.Stream(_module._default.In$T))
     ==> _module.__default.In#requires(_module._default.In$T, x#0, s#0) == true);

// definition axiom for _module.__default.In (revealed)
axiom 3 <= $FunctionContextHeight
   ==> (forall _module._default.In$T: Ty, x#0: Box, s#0: DatatypeType :: 
    { _module.__default.In(_module._default.In$T, x#0, s#0) } 
    _module.__default.In#canCall(_module._default.In$T, x#0, s#0)
         || (3 != $FunctionContextHeight
           && 
          $IsBox(x#0, _module._default.In$T)
           && $Is(s#0, Tclass._module.Stream(_module._default.In$T)))
       ==> (forall n#0: int :: 
          { _module.__default.Tail(_module._default.In$T, $LS($LZ), s#0, n#0) } 
          LitInt(0) <= n#0
             ==> 
            LitInt(0) <= n#0
             ==> _module.__default.Tail#canCall(_module._default.In$T, s#0, n#0)
               && _module.Stream.Cons_q(_module.__default.Tail(_module._default.In$T, $LS($LZ), s#0, n#0)))
         && _module.__default.In(_module._default.In$T, x#0, s#0)
           == (exists n#0: int :: 
            { _module.__default.Tail(_module._default.In$T, $LS($LZ), s#0, n#0) } 
            LitInt(0) <= n#0
               && 
              LitInt(0) <= n#0
               && _module.Stream.head(_module.__default.Tail(_module._default.In$T, $LS($LZ), s#0, n#0))
                 == x#0));

// definition axiom for _module.__default.In for all literals (revealed)
axiom 3 <= $FunctionContextHeight
   ==> (forall _module._default.In$T: Ty, x#0: Box, s#0: DatatypeType :: 
    {:weight 3} { _module.__default.In(_module._default.In$T, Lit(x#0), Lit(s#0)) } 
    _module.__default.In#canCall(_module._default.In$T, Lit(x#0), Lit(s#0))
         || (3 != $FunctionContextHeight
           && 
          $IsBox(x#0, _module._default.In$T)
           && $Is(s#0, Tclass._module.Stream(_module._default.In$T)))
       ==> (forall n#1: int :: 
          { _module.__default.Tail(_module._default.In$T, $LS($LZ), s#0, n#1) } 
          LitInt(0) <= n#1
             ==> 
            LitInt(0) <= n#1
             ==> _module.__default.Tail#canCall(_module._default.In$T, Lit(s#0), n#1)
               && _module.Stream.Cons_q(_module.__default.Tail(_module._default.In$T, $LS($LZ), Lit(s#0), n#1)))
         && _module.__default.In(_module._default.In$T, Lit(x#0), Lit(s#0))
           == (exists n#1: int :: 
            { _module.__default.Tail(_module._default.In$T, $LS($LZ), s#0, n#1) } 
            LitInt(0) <= n#1
               && 
              LitInt(0) <= n#1
               && _module.Stream.head(_module.__default.Tail(_module._default.In$T, $LS($LZ), Lit(s#0), n#1))
                 == Lit(x#0)));

procedure CheckWellformed$$_module.__default.In(_module._default.In$T: Ty, 
    x#0: Box where $IsBox(x#0, _module._default.In$T), 
    s#0: DatatypeType where $Is(s#0, Tclass._module.Stream(_module._default.In$T)));
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.In(_module._default.In$T: Ty, x#0: Box, s#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var n#2: int;
  var ##s#0: DatatypeType;
  var ##n#0: int;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function In
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(10,10): initial state"} true;
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
                ##s#0 := s#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#0, Tclass._module.Stream(_module._default.In$T), $Heap);
                ##n#0 := n#2;
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
                b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assume _module.__default.Tail#canCall(_module._default.In$T, s#0, n#2);
                assume _module.Stream.Cons_q(_module.__default.Tail(_module._default.In$T, $LS($LZ), s#0, n#2));
                assume _module.Stream.Cons_q(_module.__default.Tail(_module._default.In$T, $LS($LZ), s#0, n#2));
            }
        }

        // End Comprehension WF check
        assume _module.__default.In(_module._default.In$T, x#0, s#0)
           == (exists n#3: int :: 
            { _module.__default.Tail(_module._default.In$T, $LS($LZ), s#0, n#3) } 
            LitInt(0) <= n#3
               && 
              LitInt(0) <= n#3
               && _module.Stream.head(_module.__default.Tail(_module._default.In$T, $LS($LZ), s#0, n#3))
                 == x#0);
        assume (forall n#3: int :: 
          { _module.__default.Tail(_module._default.In$T, $LS($LZ), s#0, n#3) } 
          LitInt(0) <= n#3
             ==> 
            LitInt(0) <= n#3
             ==> _module.__default.Tail#canCall(_module._default.In$T, s#0, n#3)
               && _module.Stream.Cons_q(_module.__default.Tail(_module._default.In$T, $LS($LZ), s#0, n#3)));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.In(_module._default.In$T, x#0, s#0), TBool);
        assert b$reqreads#0;
    }
}



// function declaration for _module._default.IsSubStream
function _module.__default.IsSubStream(_module._default.IsSubStream$_T0: Ty, 
    $ly: LayerType, 
    s#0: DatatypeType, 
    u#0: DatatypeType)
   : bool;

function _module.__default.IsSubStream#canCall(_module._default.IsSubStream$_T0: Ty, s#0: DatatypeType, u#0: DatatypeType)
   : bool;

// layer synonym axiom
axiom (forall _module._default.IsSubStream$_T0: Ty, 
    $ly: LayerType, 
    s#0: DatatypeType, 
    u#0: DatatypeType :: 
  { _module.__default.IsSubStream(_module._default.IsSubStream$_T0, $LS($ly), s#0, u#0) } 
  _module.__default.IsSubStream(_module._default.IsSubStream$_T0, $LS($ly), s#0, u#0)
     == _module.__default.IsSubStream(_module._default.IsSubStream$_T0, $ly, s#0, u#0));

// fuel synonym axiom
axiom (forall _module._default.IsSubStream$_T0: Ty, 
    $ly: LayerType, 
    s#0: DatatypeType, 
    u#0: DatatypeType :: 
  { _module.__default.IsSubStream(_module._default.IsSubStream$_T0, AsFuelBottom($ly), s#0, u#0) } 
  _module.__default.IsSubStream(_module._default.IsSubStream$_T0, $ly, s#0, u#0)
     == _module.__default.IsSubStream(_module._default.IsSubStream$_T0, $LZ, s#0, u#0));

// consequence axiom for _module.__default.IsSubStream
axiom 4 <= $FunctionContextHeight
   ==> (forall _module._default.IsSubStream$_T0: Ty, 
      $ly: LayerType, 
      s#0: DatatypeType, 
      u#0: DatatypeType :: 
    { _module.__default.IsSubStream(_module._default.IsSubStream$_T0, $ly, s#0, u#0) } 
    _module.__default.IsSubStream#canCall(_module._default.IsSubStream$_T0, s#0, u#0)
         || (4 != $FunctionContextHeight
           && 
          $Is(s#0, Tclass._module.Stream(_module._default.IsSubStream$_T0))
           && $Is(u#0, Tclass._module.Stream(_module._default.IsSubStream$_T0)))
       ==> true);

function _module.__default.IsSubStream#requires(Ty, LayerType, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.IsSubStream
axiom (forall _module._default.IsSubStream$_T0: Ty, 
    $ly: LayerType, 
    s#0: DatatypeType, 
    u#0: DatatypeType :: 
  { _module.__default.IsSubStream#requires(_module._default.IsSubStream$_T0, $ly, s#0, u#0) } 
  $Is(s#0, Tclass._module.Stream(_module._default.IsSubStream$_T0))
       && $Is(u#0, Tclass._module.Stream(_module._default.IsSubStream$_T0))
     ==> _module.__default.IsSubStream#requires(_module._default.IsSubStream$_T0, $ly, s#0, u#0)
       == true);

// definition axiom for _module.__default.IsSubStream (revealed)
axiom 4 <= $FunctionContextHeight
   ==> (forall _module._default.IsSubStream$_T0: Ty, 
      $ly: LayerType, 
      s#0: DatatypeType, 
      u#0: DatatypeType :: 
    { _module.__default.IsSubStream(_module._default.IsSubStream$_T0, $LS($ly), s#0, u#0) } 
    _module.__default.IsSubStream#canCall(_module._default.IsSubStream$_T0, s#0, u#0)
         || (4 != $FunctionContextHeight
           && 
          $Is(s#0, Tclass._module.Stream(_module._default.IsSubStream$_T0))
           && $Is(u#0, Tclass._module.Stream(_module._default.IsSubStream$_T0)))
       ==> _module.Stream.Cons_q(s#0)
         && _module.__default.In#canCall(_module._default.IsSubStream$_T0, _module.Stream.head(s#0), u#0)
         && (_module.__default.In(_module._default.IsSubStream$_T0, _module.Stream.head(s#0), u#0)
           ==> _module.Stream.Cons_q(s#0)
             && _module.__default.IsSubStream#canCall(_module._default.IsSubStream$_T0, _module.Stream.tail(s#0), u#0))
         && _module.__default.IsSubStream(_module._default.IsSubStream$_T0, $LS($ly), s#0, u#0)
           == (_module.__default.In(_module._default.IsSubStream$_T0, _module.Stream.head(s#0), u#0)
             && _module.__default.IsSubStream(_module._default.IsSubStream$_T0, $ly, _module.Stream.tail(s#0), u#0)));

// 1st prefix predicate axiom for _module.__default.IsSubStream_h
axiom 5 <= $FunctionContextHeight
   ==> (forall _module._default.IsSubStream#$_T0: Ty, 
      $ly: LayerType, 
      s#0: DatatypeType, 
      u#0: DatatypeType :: 
    { _module.__default.IsSubStream(_module._default.IsSubStream#$_T0, $LS($ly), s#0, u#0) } 
    $Is(s#0, Tclass._module.Stream(_module._default.IsSubStream#$_T0))
         && $Is(u#0, Tclass._module.Stream(_module._default.IsSubStream#$_T0))
         && _module.__default.IsSubStream(_module._default.IsSubStream#$_T0, $LS($ly), s#0, u#0)
       ==> (forall _k#0: int :: 
        { _module.__default.IsSubStream_h(_module._default.IsSubStream#$_T0, $LS($ly), _k#0, s#0, u#0) } 
        LitInt(0) <= _k#0
           ==> _module.__default.IsSubStream_h(_module._default.IsSubStream#$_T0, $LS($ly), _k#0, s#0, u#0)));

// 2nd prefix predicate axiom
axiom 5 <= $FunctionContextHeight
   ==> (forall _module._default.IsSubStream#$_T0: Ty, 
      $ly: LayerType, 
      s#0: DatatypeType, 
      u#0: DatatypeType :: 
    { _module.__default.IsSubStream(_module._default.IsSubStream#$_T0, $LS($ly), s#0, u#0) } 
    $Is(s#0, Tclass._module.Stream(_module._default.IsSubStream#$_T0))
         && $Is(u#0, Tclass._module.Stream(_module._default.IsSubStream#$_T0))
         && (forall _k#0: int :: 
          { _module.__default.IsSubStream_h(_module._default.IsSubStream#$_T0, $LS($ly), _k#0, s#0, u#0) } 
          LitInt(0) <= _k#0
             ==> _module.__default.IsSubStream_h(_module._default.IsSubStream#$_T0, $LS($ly), _k#0, s#0, u#0))
       ==> _module.__default.IsSubStream(_module._default.IsSubStream#$_T0, $LS($ly), s#0, u#0));

// 3rd prefix predicate axiom
axiom 5 <= $FunctionContextHeight
   ==> (forall _module._default.IsSubStream#$_T0: Ty, 
      $ly: LayerType, 
      s#0: DatatypeType, 
      u#0: DatatypeType, 
      _k#0: int :: 
    { _module.__default.IsSubStream_h(_module._default.IsSubStream#$_T0, $ly, _k#0, s#0, u#0) } 
    $Is(s#0, Tclass._module.Stream(_module._default.IsSubStream#$_T0))
         && $Is(u#0, Tclass._module.Stream(_module._default.IsSubStream#$_T0))
         && _k#0 == 0
       ==> _module.__default.IsSubStream_h(_module._default.IsSubStream#$_T0, $ly, _k#0, s#0, u#0));

procedure CheckWellformed$$_module.__default.IsSubStream(_module._default.IsSubStream$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.IsSubStream$_T0)), 
    u#0: DatatypeType
       where $Is(u#0, Tclass._module.Stream(_module._default.IsSubStream$_T0)));
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.IsSubStream(_module._default.IsSubStream$_T0: Ty, s#0: DatatypeType, u#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##x#0: Box;
  var ##s#0: DatatypeType;
  var ##s#1: DatatypeType;
  var ##u#0: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function IsSubStream
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(14,19): initial state"} true;
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
        assume _module.Stream.Cons_q(s#0);
        ##x#0 := _module.Stream.head(s#0);
        // assume allocatedness for argument to function
        assume $IsAllocBox(##x#0, _module._default.IsSubStream$_T0, $Heap);
        ##s#0 := u#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#0, Tclass._module.Stream(_module._default.IsSubStream$_T0), $Heap);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.In#canCall(_module._default.IsSubStream$_T0, _module.Stream.head(s#0), u#0);
        if (_module.__default.In(_module._default.IsSubStream$_T0, _module.Stream.head(s#0), u#0))
        {
            assume _module.Stream.Cons_q(s#0);
            ##s#1 := _module.Stream.tail(s#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#1, Tclass._module.Stream(_module._default.IsSubStream$_T0), $Heap);
            ##u#0 := u#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##u#0, Tclass._module.Stream(_module._default.IsSubStream$_T0), $Heap);
            b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.IsSubStream#canCall(_module._default.IsSubStream$_T0, _module.Stream.tail(s#0), u#0);
        }

        assume _module.__default.IsSubStream(_module._default.IsSubStream$_T0, $LS($LZ), s#0, u#0)
           == (_module.__default.In(_module._default.IsSubStream$_T0, _module.Stream.head(s#0), u#0)
             && _module.__default.IsSubStream(_module._default.IsSubStream$_T0, $LS($LZ), _module.Stream.tail(s#0), u#0));
        assume _module.Stream.Cons_q(s#0)
           && _module.__default.In#canCall(_module._default.IsSubStream$_T0, _module.Stream.head(s#0), u#0)
           && (_module.__default.In(_module._default.IsSubStream$_T0, _module.Stream.head(s#0), u#0)
             ==> _module.Stream.Cons_q(s#0)
               && _module.__default.IsSubStream#canCall(_module._default.IsSubStream$_T0, _module.Stream.tail(s#0), u#0));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.IsSubStream(_module._default.IsSubStream$_T0, $LS($LZ), s#0, u#0), 
          TBool);
        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



// function declaration for _module._default.IsSubStream#
function _module.__default.IsSubStream_h(_module._default.IsSubStream#$_T0: Ty, 
    $ly: LayerType, 
    _k#0: int, 
    s#0: DatatypeType, 
    u#0: DatatypeType)
   : bool;

function _module.__default.IsSubStream_h#canCall(_module._default.IsSubStream#$_T0: Ty, 
    _k#0: int, 
    s#0: DatatypeType, 
    u#0: DatatypeType)
   : bool;

// layer synonym axiom
axiom (forall _module._default.IsSubStream#$_T0: Ty, 
    $ly: LayerType, 
    _k#0: int, 
    s#0: DatatypeType, 
    u#0: DatatypeType :: 
  { _module.__default.IsSubStream_h(_module._default.IsSubStream#$_T0, $LS($ly), _k#0, s#0, u#0) } 
  _module.__default.IsSubStream_h(_module._default.IsSubStream#$_T0, $LS($ly), _k#0, s#0, u#0)
     == _module.__default.IsSubStream_h(_module._default.IsSubStream#$_T0, $ly, _k#0, s#0, u#0));

// fuel synonym axiom
axiom (forall _module._default.IsSubStream#$_T0: Ty, 
    $ly: LayerType, 
    _k#0: int, 
    s#0: DatatypeType, 
    u#0: DatatypeType :: 
  { _module.__default.IsSubStream_h(_module._default.IsSubStream#$_T0, AsFuelBottom($ly), _k#0, s#0, u#0) } 
  _module.__default.IsSubStream_h(_module._default.IsSubStream#$_T0, $ly, _k#0, s#0, u#0)
     == _module.__default.IsSubStream_h(_module._default.IsSubStream#$_T0, $LZ, _k#0, s#0, u#0));

// consequence axiom for _module.__default.IsSubStream_h
axiom 5 <= $FunctionContextHeight
   ==> (forall _module._default.IsSubStream#$_T0: Ty, 
      $ly: LayerType, 
      _k#0: int, 
      s#0: DatatypeType, 
      u#0: DatatypeType :: 
    { _module.__default.IsSubStream_h(_module._default.IsSubStream#$_T0, $ly, _k#0, s#0, u#0) } 
    _module.__default.IsSubStream_h#canCall(_module._default.IsSubStream#$_T0, _k#0, s#0, u#0)
         || (5 != $FunctionContextHeight
           && 
          LitInt(0) <= _k#0
           && $Is(s#0, Tclass._module.Stream(_module._default.IsSubStream#$_T0))
           && $Is(u#0, Tclass._module.Stream(_module._default.IsSubStream#$_T0)))
       ==> true);

function _module.__default.IsSubStream_h#requires(Ty, LayerType, int, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.IsSubStream_h
axiom (forall _module._default.IsSubStream#$_T0: Ty, 
    $ly: LayerType, 
    _k#0: int, 
    s#0: DatatypeType, 
    u#0: DatatypeType :: 
  { _module.__default.IsSubStream_h#requires(_module._default.IsSubStream#$_T0, $ly, _k#0, s#0, u#0) } 
  LitInt(0) <= _k#0
       && $Is(s#0, Tclass._module.Stream(_module._default.IsSubStream#$_T0))
       && $Is(u#0, Tclass._module.Stream(_module._default.IsSubStream#$_T0))
     ==> _module.__default.IsSubStream_h#requires(_module._default.IsSubStream#$_T0, $ly, _k#0, s#0, u#0)
       == true);

// definition axiom for _module.__default.IsSubStream_h (revealed)
axiom 5 <= $FunctionContextHeight
   ==> (forall _module._default.IsSubStream#$_T0: Ty, 
      $ly: LayerType, 
      _k#0: int, 
      s#0: DatatypeType, 
      u#0: DatatypeType :: 
    { _module.__default.IsSubStream_h(_module._default.IsSubStream#$_T0, $LS($ly), _k#0, s#0, u#0) } 
    _module.__default.IsSubStream_h#canCall(_module._default.IsSubStream#$_T0, _k#0, s#0, u#0)
         || (5 != $FunctionContextHeight
           && 
          LitInt(0) <= _k#0
           && $Is(s#0, Tclass._module.Stream(_module._default.IsSubStream#$_T0))
           && $Is(u#0, Tclass._module.Stream(_module._default.IsSubStream#$_T0)))
       ==> (0 < _k#0
           ==> _module.Stream.Cons_q(s#0)
             && _module.__default.In#canCall(_module._default.IsSubStream#$_T0, _module.Stream.head(s#0), u#0)
             && (_module.__default.In(_module._default.IsSubStream#$_T0, _module.Stream.head(s#0), u#0)
               ==> _module.Stream.Cons_q(s#0)
                 && _module.__default.IsSubStream_h#canCall(_module._default.IsSubStream#$_T0, _k#0 - 1, _module.Stream.tail(s#0), u#0)))
         && _module.__default.IsSubStream_h(_module._default.IsSubStream#$_T0, $LS($ly), _k#0, s#0, u#0)
           == (0 < _k#0
             ==> _module.__default.In(_module._default.IsSubStream#$_T0, _module.Stream.head(s#0), u#0)
               && _module.__default.IsSubStream_h(_module._default.IsSubStream#$_T0, $ly, _k#0 - 1, _module.Stream.tail(s#0), u#0)));

// definition axiom for _module.__default.IsSubStream_h for decreasing-related literals (revealed)
axiom 5 <= $FunctionContextHeight
   ==> (forall _module._default.IsSubStream#$_T0: Ty, 
      $ly: LayerType, 
      _k#0: int, 
      s#0: DatatypeType, 
      u#0: DatatypeType :: 
    {:weight 3} { _module.__default.IsSubStream_h(_module._default.IsSubStream#$_T0, $LS($ly), LitInt(_k#0), s#0, u#0) } 
    _module.__default.IsSubStream_h#canCall(_module._default.IsSubStream#$_T0, LitInt(_k#0), s#0, u#0)
         || (5 != $FunctionContextHeight
           && 
          LitInt(0) <= _k#0
           && $Is(s#0, Tclass._module.Stream(_module._default.IsSubStream#$_T0))
           && $Is(u#0, Tclass._module.Stream(_module._default.IsSubStream#$_T0)))
       ==> (0 < _k#0
           ==> _module.Stream.Cons_q(s#0)
             && _module.__default.In#canCall(_module._default.IsSubStream#$_T0, _module.Stream.head(s#0), u#0)
             && (_module.__default.In(_module._default.IsSubStream#$_T0, _module.Stream.head(s#0), u#0)
               ==> _module.Stream.Cons_q(s#0)
                 && _module.__default.IsSubStream_h#canCall(_module._default.IsSubStream#$_T0, _k#0 - 1, _module.Stream.tail(s#0), u#0)))
         && _module.__default.IsSubStream_h(_module._default.IsSubStream#$_T0, $LS($ly), LitInt(_k#0), s#0, u#0)
           == (0 < _k#0
             ==> _module.__default.In(_module._default.IsSubStream#$_T0, _module.Stream.head(s#0), u#0)
               && _module.__default.IsSubStream_h(_module._default.IsSubStream#$_T0, 
                $LS($ly), 
                _k#0 - 1, 
                _module.Stream.tail(s#0), 
                u#0)));

// definition axiom for _module.__default.IsSubStream_h for all literals (revealed)
axiom 5 <= $FunctionContextHeight
   ==> (forall _module._default.IsSubStream#$_T0: Ty, 
      $ly: LayerType, 
      _k#0: int, 
      s#0: DatatypeType, 
      u#0: DatatypeType :: 
    {:weight 3} { _module.__default.IsSubStream_h(_module._default.IsSubStream#$_T0, $LS($ly), LitInt(_k#0), Lit(s#0), Lit(u#0)) } 
    _module.__default.IsSubStream_h#canCall(_module._default.IsSubStream#$_T0, LitInt(_k#0), Lit(s#0), Lit(u#0))
         || (5 != $FunctionContextHeight
           && 
          LitInt(0) <= _k#0
           && $Is(s#0, Tclass._module.Stream(_module._default.IsSubStream#$_T0))
           && $Is(u#0, Tclass._module.Stream(_module._default.IsSubStream#$_T0)))
       ==> (0 < _k#0
           ==> _module.Stream.Cons_q(s#0)
             && _module.__default.In#canCall(_module._default.IsSubStream#$_T0, _module.Stream.head(s#0), u#0)
             && (_module.__default.In(_module._default.IsSubStream#$_T0, _module.Stream.head(s#0), u#0)
               ==> _module.Stream.Cons_q(s#0)
                 && _module.__default.IsSubStream_h#canCall(_module._default.IsSubStream#$_T0, _k#0 - 1, _module.Stream.tail(s#0), u#0)))
         && _module.__default.IsSubStream_h(_module._default.IsSubStream#$_T0, $LS($ly), LitInt(_k#0), Lit(s#0), Lit(u#0))
           == (0 < _k#0
             ==> _module.__default.In(_module._default.IsSubStream#$_T0, _module.Stream.head(s#0), u#0)
               && _module.__default.IsSubStream_h(_module._default.IsSubStream#$_T0, 
                $LS($ly), 
                _k#0 - 1, 
                _module.Stream.tail(s#0), 
                u#0)));

procedure CheckWellformed$$_module.__default.Lemma__InTail(_module._default.Lemma_InTail$T: Ty, 
    x#0: Box
       where $IsBox(x#0, _module._default.Lemma_InTail$T)
         && $IsAllocBox(x#0, _module._default.Lemma_InTail$T, $Heap), 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Lemma_InTail$T))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.Lemma_InTail$T), $Heap)
         && $IsA#_module.Stream(s#0));
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Lemma__InTail(_module._default.Lemma_InTail$T: Ty, 
    x#0: Box
       where $IsBox(x#0, _module._default.Lemma_InTail$T)
         && $IsAllocBox(x#0, _module._default.Lemma_InTail$T, $Heap), 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Lemma_InTail$T))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.Lemma_InTail$T), $Heap)
         && $IsA#_module.Stream(s#0));
  // user-defined preconditions
  requires _module.__default.In#canCall(_module._default.Lemma_InTail$T, x#0, _module.Stream.tail(s#0))
     ==> _module.__default.In(_module._default.Lemma_InTail$T, x#0, _module.Stream.tail(s#0))
       || (exists n#0: int :: 
        { _module.__default.Tail(_module._default.Lemma_InTail$T, $LS($LZ), _module.Stream.tail(s#0), n#0) } 
        LitInt(0) <= n#0
           && 
          LitInt(0) <= n#0
           && _module.Stream.head(_module.__default.Tail(_module._default.Lemma_InTail$T, $LS($LZ), _module.Stream.tail(s#0), n#0))
             == x#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.In#canCall(_module._default.Lemma_InTail$T, x#0, s#0);
  free ensures _module.__default.In#canCall(_module._default.Lemma_InTail$T, x#0, s#0)
     && 
    _module.__default.In(_module._default.Lemma_InTail$T, x#0, s#0)
     && (exists n#1: int :: 
      { _module.__default.Tail(_module._default.Lemma_InTail$T, $LS($LZ), s#0, n#1) } 
      LitInt(0) <= n#1
         && 
        LitInt(0) <= n#1
         && _module.Stream.head(_module.__default.Tail(_module._default.Lemma_InTail$T, $LS($LZ), s#0, n#1))
           == x#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.Lemma__InTail(_module._default.Lemma_InTail$T: Ty, 
    x#0: Box
       where $IsBox(x#0, _module._default.Lemma_InTail$T)
         && $IsAllocBox(x#0, _module._default.Lemma_InTail$T, $Heap), 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Lemma_InTail$T))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.Lemma_InTail$T), $Heap)
         && $IsA#_module.Stream(s#0))
   returns ($_reverifyPost: bool);
  free requires 6 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.__default.In#canCall(_module._default.Lemma_InTail$T, x#0, _module.Stream.tail(s#0))
     && 
    _module.__default.In(_module._default.Lemma_InTail$T, x#0, _module.Stream.tail(s#0))
     && (exists n#2: int :: 
      { _module.__default.Tail(_module._default.Lemma_InTail$T, $LS($LZ), _module.Stream.tail(s#0), n#2) } 
      LitInt(0) <= n#2
         && 
        LitInt(0) <= n#2
         && _module.Stream.head(_module.__default.Tail(_module._default.Lemma_InTail$T, $LS($LZ), _module.Stream.tail(s#0), n#2))
           == x#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.In#canCall(_module._default.Lemma_InTail$T, x#0, s#0);
  ensures _module.__default.In#canCall(_module._default.Lemma_InTail$T, x#0, s#0)
     ==> _module.__default.In(_module._default.Lemma_InTail$T, x#0, s#0)
       || (exists n#3: int :: 
        { _module.__default.Tail(_module._default.Lemma_InTail$T, $LS($LZ), s#0, n#3) } 
        LitInt(0) <= n#3
           && 
          LitInt(0) <= n#3
           && _module.Stream.head(_module.__default.Tail(_module._default.Lemma_InTail$T, $LS($LZ), s#0, n#3))
             == x#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.Lemma__InTail(_module._default.Lemma_InTail$T: Ty, x#0: Box, s#0: DatatypeType)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var n#4: int;
  var n#5: int;
  var ##s#2: DatatypeType;
  var ##n#0: int;
  var ##s#3: DatatypeType;
  var ##n#1: int;

    // AddMethodImpl: Lemma_InTail, Impl$$_module.__default.Lemma__InTail
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(22,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(23,9)
    havoc n#5;
    if (true)
    {
        if (LitInt(0) <= n#5)
        {
            assume _module.Stream.Cons_q(s#0);
            ##s#2 := _module.Stream.tail(s#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#2, Tclass._module.Stream(_module._default.Lemma_InTail$T), $Heap);
            assert $Is(n#5, Tclass._System.nat());
            ##n#0 := n#5;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
            assume _module.__default.Tail#canCall(_module._default.Lemma_InTail$T, _module.Stream.tail(s#0), n#5);
            assume _module.Stream.Cons_q(_module.__default.Tail(_module._default.Lemma_InTail$T, $LS($LZ), _module.Stream.tail(s#0), n#5));
            assume _module.Stream.Cons_q(_module.__default.Tail(_module._default.Lemma_InTail$T, $LS($LZ), _module.Stream.tail(s#0), n#5));
        }

        assume LitInt(0) <= n#5
           ==> _module.Stream.Cons_q(s#0)
             && _module.__default.Tail#canCall(_module._default.Lemma_InTail$T, _module.Stream.tail(s#0), n#5)
             && _module.Stream.Cons_q(_module.__default.Tail(_module._default.Lemma_InTail$T, $LS($LZ), _module.Stream.tail(s#0), n#5));
    }

    assert ($Is(LitInt(0), TInt)
         && 
        LitInt(0) <= LitInt(0)
         && _module.Stream.head(_module.__default.Tail(_module._default.Lemma_InTail$T, $LS($LZ), _module.Stream.tail(s#0), LitInt(0)))
           == x#0)
       || 
      ($Is(LitInt(0), TInt)
         && 
        LitInt(0) <= LitInt(0)
         && _module.Stream.head(_module.__default.Tail(_module._default.Lemma_InTail$T, $LS($LZ), _module.Stream.tail(s#0), LitInt(0)))
           == x#0)
       || (exists $as#n0#0: int :: 
        LitInt(0) <= $as#n0#0
           && _module.Stream.head(_module.__default.Tail(_module._default.Lemma_InTail$T, $LS($LZ), _module.Stream.tail(s#0), $as#n0#0))
             == x#0);
    havoc n#4;
    assume LitInt(0) <= n#4
       && _module.Stream.head(_module.__default.Tail(_module._default.Lemma_InTail$T, $LS($LZ), _module.Stream.tail(s#0), n#4))
         == x#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(23,46)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(24,3)
    ##s#3 := s#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#3, Tclass._module.Stream(_module._default.Lemma_InTail$T), $Heap);
    assert $Is(n#4 + 1, Tclass._System.nat());
    ##n#1 := n#4 + 1;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#1, Tclass._System.nat(), $Heap);
    assume _module.__default.Tail#canCall(_module._default.Lemma_InTail$T, s#0, n#4 + 1);
    assume _module.Stream.Cons_q(_module.__default.Tail(_module._default.Lemma_InTail$T, $LS($LZ), s#0, n#4 + 1));
    assume _module.Stream.Cons_q(_module.__default.Tail(_module._default.Lemma_InTail$T, $LS($LZ), s#0, n#4 + 1));
    assume _module.__default.Tail#canCall(_module._default.Lemma_InTail$T, s#0, n#4 + 1)
       && _module.Stream.Cons_q(_module.__default.Tail(_module._default.Lemma_InTail$T, $LS($LZ), s#0, n#4 + 1));
    assert {:subsumption 0} _module.Stream.head(_module.__default.Tail(_module._default.Lemma_InTail$T, $LS($LS($LZ)), s#0, n#4 + 1))
       == x#0;
    assume _module.Stream.head(_module.__default.Tail(_module._default.Lemma_InTail$T, $LS($LZ), s#0, n#4 + 1))
       == x#0;
}



procedure CheckWellformed$$_module.__default.Lemma__TailSubStream(_module._default.Lemma_TailSubStream$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Lemma_TailSubStream$_T0))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.Lemma_TailSubStream$_T0), $Heap)
         && $IsA#_module.Stream(s#0), 
    u#0: DatatypeType
       where $Is(u#0, Tclass._module.Stream(_module._default.Lemma_TailSubStream$_T0))
         && $IsAlloc(u#0, Tclass._module.Stream(_module._default.Lemma_TailSubStream$_T0), $Heap)
         && $IsA#_module.Stream(u#0));
  free requires 7 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Lemma__TailSubStream(_module._default.Lemma_TailSubStream$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Lemma_TailSubStream$_T0))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.Lemma_TailSubStream$_T0), $Heap)
         && $IsA#_module.Stream(s#0), 
    u#0: DatatypeType
       where $Is(u#0, Tclass._module.Stream(_module._default.Lemma_TailSubStream$_T0))
         && $IsAlloc(u#0, Tclass._module.Stream(_module._default.Lemma_TailSubStream$_T0), $Heap)
         && $IsA#_module.Stream(u#0));
  // user-defined preconditions
  requires _module.__default.IsSubStream#canCall(_module._default.Lemma_TailSubStream$_T0, s#0, _module.Stream.tail(u#0))
     ==> _module.__default.IsSubStream(_module._default.Lemma_TailSubStream$_T0, 
        $LS($LZ), 
        s#0, 
        _module.Stream.tail(u#0))
       || (_module.__default.In#canCall(_module._default.Lemma_TailSubStream$_T0, 
          _module.Stream.head(s#0), 
          _module.Stream.tail(u#0))
         ==> _module.__default.In(_module._default.Lemma_TailSubStream$_T0, 
            _module.Stream.head(s#0), 
            _module.Stream.tail(u#0))
           || (exists n#0: int :: 
            { _module.__default.Tail(_module._default.Lemma_TailSubStream$_T0, 
                $LS($LZ), 
                _module.Stream.tail(u#0), 
                n#0) } 
            LitInt(0) <= n#0
               && 
              LitInt(0) <= n#0
               && _module.Stream.head(_module.__default.Tail(_module._default.Lemma_TailSubStream$_T0, 
                    $LS($LZ), 
                    _module.Stream.tail(u#0), 
                    n#0))
                 == _module.Stream.head(s#0)));
  requires _module.__default.IsSubStream#canCall(_module._default.Lemma_TailSubStream$_T0, s#0, _module.Stream.tail(u#0))
     ==> _module.__default.IsSubStream(_module._default.Lemma_TailSubStream$_T0, 
        $LS($LZ), 
        s#0, 
        _module.Stream.tail(u#0))
       || _module.__default.IsSubStream(_module._default.Lemma_TailSubStream$_T0, 
        $LS($LS($LZ)), 
        _module.Stream.tail(s#0), 
        _module.Stream.tail(u#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.IsSubStream#canCall(_module._default.Lemma_TailSubStream$_T0, s#0, u#0);
  free ensures _module.__default.IsSubStream#canCall(_module._default.Lemma_TailSubStream$_T0, s#0, u#0)
     && 
    _module.__default.IsSubStream(_module._default.Lemma_TailSubStream$_T0, $LS($LZ), s#0, u#0)
     && 
    _module.__default.In(_module._default.Lemma_TailSubStream$_T0, _module.Stream.head(s#0), u#0)
     && _module.__default.IsSubStream(_module._default.Lemma_TailSubStream$_T0, 
      $LS($LZ), 
      _module.Stream.tail(s#0), 
      u#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, s#1, u#1} CoCall$$_module.__default.Lemma__TailSubStream_h(_module._default.Lemma_TailSubStream#$_T0: Ty, 
    _k#0: int where LitInt(0) <= _k#0, 
    s#1: DatatypeType
       where $Is(s#1, Tclass._module.Stream(_module._default.Lemma_TailSubStream#$_T0))
         && $IsAlloc(s#1, Tclass._module.Stream(_module._default.Lemma_TailSubStream#$_T0), $Heap)
         && $IsA#_module.Stream(s#1), 
    u#1: DatatypeType
       where $Is(u#1, Tclass._module.Stream(_module._default.Lemma_TailSubStream#$_T0))
         && $IsAlloc(u#1, Tclass._module.Stream(_module._default.Lemma_TailSubStream#$_T0), $Heap)
         && $IsA#_module.Stream(u#1));
  // user-defined preconditions
  requires _module.__default.IsSubStream#canCall(_module._default.Lemma_TailSubStream#$_T0, s#1, _module.Stream.tail(u#1))
     ==> _module.__default.IsSubStream(_module._default.Lemma_TailSubStream#$_T0, 
        $LS($LZ), 
        s#1, 
        _module.Stream.tail(u#1))
       || (_module.__default.In#canCall(_module._default.Lemma_TailSubStream#$_T0, 
          _module.Stream.head(s#1), 
          _module.Stream.tail(u#1))
         ==> _module.__default.In(_module._default.Lemma_TailSubStream#$_T0, 
            _module.Stream.head(s#1), 
            _module.Stream.tail(u#1))
           || (exists n#2: int :: 
            { _module.__default.Tail(_module._default.Lemma_TailSubStream#$_T0, 
                $LS($LZ), 
                _module.Stream.tail(u#1), 
                n#2) } 
            LitInt(0) <= n#2
               && 
              LitInt(0) <= n#2
               && _module.Stream.head(_module.__default.Tail(_module._default.Lemma_TailSubStream#$_T0, 
                    $LS($LZ), 
                    _module.Stream.tail(u#1), 
                    n#2))
                 == _module.Stream.head(s#1)));
  requires _module.__default.IsSubStream#canCall(_module._default.Lemma_TailSubStream#$_T0, s#1, _module.Stream.tail(u#1))
     ==> _module.__default.IsSubStream(_module._default.Lemma_TailSubStream#$_T0, 
        $LS($LZ), 
        s#1, 
        _module.Stream.tail(u#1))
       || _module.__default.IsSubStream(_module._default.Lemma_TailSubStream#$_T0, 
        $LS($LS($LZ)), 
        _module.Stream.tail(s#1), 
        _module.Stream.tail(u#1));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.IsSubStream_h#canCall(_module._default.Lemma_TailSubStream#$_T0, _k#0, s#1, u#1);
  free ensures _module.__default.IsSubStream_h#canCall(_module._default.Lemma_TailSubStream#$_T0, _k#0, s#1, u#1)
     && 
    _module.__default.IsSubStream_h(_module._default.Lemma_TailSubStream#$_T0, $LS($LZ), _k#0, s#1, u#1)
     && (0 < _k#0
       ==> _module.__default.In(_module._default.Lemma_TailSubStream#$_T0, _module.Stream.head(s#1), u#1)
         && _module.__default.IsSubStream_h(_module._default.Lemma_TailSubStream#$_T0, 
          $LS($LZ), 
          _k#0 - 1, 
          _module.Stream.tail(s#1), 
          u#1));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, s#1, u#1} Impl$$_module.__default.Lemma__TailSubStream_h(_module._default.Lemma_TailSubStream#$_T0: Ty, 
    _k#0: int where LitInt(0) <= _k#0, 
    s#1: DatatypeType
       where $Is(s#1, Tclass._module.Stream(_module._default.Lemma_TailSubStream#$_T0))
         && $IsAlloc(s#1, Tclass._module.Stream(_module._default.Lemma_TailSubStream#$_T0), $Heap)
         && $IsA#_module.Stream(s#1), 
    u#1: DatatypeType
       where $Is(u#1, Tclass._module.Stream(_module._default.Lemma_TailSubStream#$_T0))
         && $IsAlloc(u#1, Tclass._module.Stream(_module._default.Lemma_TailSubStream#$_T0), $Heap)
         && $IsA#_module.Stream(u#1))
   returns ($_reverifyPost: bool);
  free requires 8 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.__default.IsSubStream#canCall(_module._default.Lemma_TailSubStream#$_T0, s#1, _module.Stream.tail(u#1))
     && 
    _module.__default.IsSubStream(_module._default.Lemma_TailSubStream#$_T0, 
      $LS($LZ), 
      s#1, 
      _module.Stream.tail(u#1))
     && 
    _module.__default.In(_module._default.Lemma_TailSubStream#$_T0, 
      _module.Stream.head(s#1), 
      _module.Stream.tail(u#1))
     && _module.__default.IsSubStream(_module._default.Lemma_TailSubStream#$_T0, 
      $LS($LZ), 
      _module.Stream.tail(s#1), 
      _module.Stream.tail(u#1));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.IsSubStream_h#canCall(_module._default.Lemma_TailSubStream#$_T0, _k#0, s#1, u#1);
  ensures _module.__default.IsSubStream_h#canCall(_module._default.Lemma_TailSubStream#$_T0, _k#0, s#1, u#1)
     ==> _module.__default.IsSubStream_h(_module._default.Lemma_TailSubStream#$_T0, $LS($LZ), _k#0, s#1, u#1)
       || (0 < _k#0
         ==> 
        _module.__default.In#canCall(_module._default.Lemma_TailSubStream#$_T0, _module.Stream.head(s#1), u#1)
         ==> _module.__default.In(_module._default.Lemma_TailSubStream#$_T0, _module.Stream.head(s#1), u#1)
           || (exists n#5: int :: 
            { _module.__default.Tail(_module._default.Lemma_TailSubStream#$_T0, $LS($LZ), u#1, n#5) } 
            LitInt(0) <= n#5
               && 
              LitInt(0) <= n#5
               && _module.Stream.head(_module.__default.Tail(_module._default.Lemma_TailSubStream#$_T0, $LS($LZ), u#1, n#5))
                 == _module.Stream.head(s#1)));
  ensures _module.__default.IsSubStream_h#canCall(_module._default.Lemma_TailSubStream#$_T0, _k#0, s#1, u#1)
     ==> _module.__default.IsSubStream_h(_module._default.Lemma_TailSubStream#$_T0, $LS($LZ), _k#0, s#1, u#1)
       || (0 < _k#0
         ==> _module.__default.IsSubStream_h(_module._default.Lemma_TailSubStream#$_T0, 
          $LS($LS($LZ)), 
          _k#0 - 1, 
          _module.Stream.tail(s#1), 
          u#1));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0, s#1, u#1} Impl$$_module.__default.Lemma__TailSubStream_h(_module._default.Lemma_TailSubStream#$_T0: Ty, 
    _k#0: int, 
    s#1: DatatypeType, 
    u#1: DatatypeType)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var x##0: Box;
  var s##0: DatatypeType;

    // AddMethodImpl: Lemma_TailSubStream#, Impl$$_module.__default.Lemma__TailSubStream_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(26,15): initial state"} true;
    assume $IsA#_module.Stream(s#1);
    assume $IsA#_module.Stream(u#1);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: int, $ih#s0#0: DatatypeType, $ih#u0#0: DatatypeType :: 
      LitInt(0) <= $ih#_k0#0
           && $Is($ih#s0#0, Tclass._module.Stream(_module._default.Lemma_TailSubStream#$_T0))
           && $Is($ih#u0#0, Tclass._module.Stream(_module._default.Lemma_TailSubStream#$_T0))
           && _module.__default.IsSubStream(_module._default.Lemma_TailSubStream#$_T0, 
            $LS($LZ), 
            $ih#s0#0, 
            _module.Stream.tail($ih#u0#0))
           && 
          0 <= $ih#_k0#0
           && $ih#_k0#0 < _k#0
         ==> _module.__default.IsSubStream_h(_module._default.Lemma_TailSubStream#$_T0, 
          $LS($LZ), 
          $ih#_k0#0, 
          $ih#s0#0, 
          $ih#u0#0));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(29,1)
    assume true;
    if (0 < _k#0)
    {
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(30,15)
        // TrCallStmt: Before ProcessCallStmt
        assume _module.Stream.Cons_q(s#1);
        assume _module.Stream.Cons_q(s#1);
        // ProcessCallStmt: CheckSubrange
        x##0 := _module.Stream.head(s#1);
        assume true;
        // ProcessCallStmt: CheckSubrange
        s##0 := u#1;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.Lemma__InTail(_module._default.Lemma_TailSubStream#$_T0, x##0, s##0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(30,25)"} true;
    }
    else
    {
    }
}



procedure {:_induction s#0, u#0, k#0} CheckWellformed$$_module.__default.Lemma__TailSubStreamK(_module._default.Lemma_TailSubStreamK$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Lemma_TailSubStreamK$_T0))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.Lemma_TailSubStreamK$_T0), $Heap)
         && $IsA#_module.Stream(s#0), 
    u#0: DatatypeType
       where $Is(u#0, Tclass._module.Stream(_module._default.Lemma_TailSubStreamK$_T0))
         && $IsAlloc(u#0, Tclass._module.Stream(_module._default.Lemma_TailSubStreamK$_T0), $Heap)
         && $IsA#_module.Stream(u#0), 
    k#0: int where LitInt(0) <= k#0);
  free requires 23 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction s#0, u#0, k#0} Call$$_module.__default.Lemma__TailSubStreamK(_module._default.Lemma_TailSubStreamK$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Lemma_TailSubStreamK$_T0))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.Lemma_TailSubStreamK$_T0), $Heap)
         && $IsA#_module.Stream(s#0), 
    u#0: DatatypeType
       where $Is(u#0, Tclass._module.Stream(_module._default.Lemma_TailSubStreamK$_T0))
         && $IsAlloc(u#0, Tclass._module.Stream(_module._default.Lemma_TailSubStreamK$_T0), $Heap)
         && $IsA#_module.Stream(u#0), 
    k#0: int where LitInt(0) <= k#0);
  // user-defined preconditions
  requires _module.__default.IsSubStream_h#canCall(_module._default.Lemma_TailSubStreamK$_T0, k#0, s#0, _module.Stream.tail(u#0))
     ==> _module.__default.IsSubStream_h(_module._default.Lemma_TailSubStreamK$_T0, 
        $LS($LZ), 
        k#0, 
        s#0, 
        _module.Stream.tail(u#0))
       || (0 < k#0
         ==> 
        _module.__default.In#canCall(_module._default.Lemma_TailSubStreamK$_T0, 
          _module.Stream.head(s#0), 
          _module.Stream.tail(u#0))
         ==> _module.__default.In(_module._default.Lemma_TailSubStreamK$_T0, 
            _module.Stream.head(s#0), 
            _module.Stream.tail(u#0))
           || (exists n#0: int :: 
            { _module.__default.Tail(_module._default.Lemma_TailSubStreamK$_T0, 
                $LS($LZ), 
                _module.Stream.tail(u#0), 
                n#0) } 
            LitInt(0) <= n#0
               && 
              LitInt(0) <= n#0
               && _module.Stream.head(_module.__default.Tail(_module._default.Lemma_TailSubStreamK$_T0, 
                    $LS($LZ), 
                    _module.Stream.tail(u#0), 
                    n#0))
                 == _module.Stream.head(s#0)));
  requires _module.__default.IsSubStream_h#canCall(_module._default.Lemma_TailSubStreamK$_T0, k#0, s#0, _module.Stream.tail(u#0))
     ==> _module.__default.IsSubStream_h(_module._default.Lemma_TailSubStreamK$_T0, 
        $LS($LZ), 
        k#0, 
        s#0, 
        _module.Stream.tail(u#0))
       || (0 < k#0
         ==> _module.__default.IsSubStream_h(_module._default.Lemma_TailSubStreamK$_T0, 
          $LS($LS($LZ)), 
          k#0 - 1, 
          _module.Stream.tail(s#0), 
          _module.Stream.tail(u#0)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.IsSubStream_h#canCall(_module._default.Lemma_TailSubStreamK$_T0, k#0, s#0, u#0);
  free ensures _module.__default.IsSubStream_h#canCall(_module._default.Lemma_TailSubStreamK$_T0, k#0, s#0, u#0)
     && 
    _module.__default.IsSubStream_h(_module._default.Lemma_TailSubStreamK$_T0, $LS($LZ), k#0, s#0, u#0)
     && (0 < k#0
       ==> _module.__default.In(_module._default.Lemma_TailSubStreamK$_T0, _module.Stream.head(s#0), u#0)
         && _module.__default.IsSubStream_h(_module._default.Lemma_TailSubStreamK$_T0, 
          $LS($LZ), 
          k#0 - 1, 
          _module.Stream.tail(s#0), 
          u#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction s#0, u#0, k#0} Impl$$_module.__default.Lemma__TailSubStreamK(_module._default.Lemma_TailSubStreamK$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Lemma_TailSubStreamK$_T0))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.Lemma_TailSubStreamK$_T0), $Heap)
         && $IsA#_module.Stream(s#0), 
    u#0: DatatypeType
       where $Is(u#0, Tclass._module.Stream(_module._default.Lemma_TailSubStreamK$_T0))
         && $IsAlloc(u#0, Tclass._module.Stream(_module._default.Lemma_TailSubStreamK$_T0), $Heap)
         && $IsA#_module.Stream(u#0), 
    k#0: int where LitInt(0) <= k#0)
   returns ($_reverifyPost: bool);
  free requires 23 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.__default.IsSubStream_h#canCall(_module._default.Lemma_TailSubStreamK$_T0, k#0, s#0, _module.Stream.tail(u#0))
     && 
    _module.__default.IsSubStream_h(_module._default.Lemma_TailSubStreamK$_T0, 
      $LS($LZ), 
      k#0, 
      s#0, 
      _module.Stream.tail(u#0))
     && (0 < k#0
       ==> _module.__default.In(_module._default.Lemma_TailSubStreamK$_T0, 
          _module.Stream.head(s#0), 
          _module.Stream.tail(u#0))
         && _module.__default.IsSubStream_h(_module._default.Lemma_TailSubStreamK$_T0, 
          $LS($LZ), 
          k#0 - 1, 
          _module.Stream.tail(s#0), 
          _module.Stream.tail(u#0)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.IsSubStream_h#canCall(_module._default.Lemma_TailSubStreamK$_T0, k#0, s#0, u#0);
  ensures _module.__default.IsSubStream_h#canCall(_module._default.Lemma_TailSubStreamK$_T0, k#0, s#0, u#0)
     ==> _module.__default.IsSubStream_h(_module._default.Lemma_TailSubStreamK$_T0, $LS($LZ), k#0, s#0, u#0)
       || (0 < k#0
         ==> 
        _module.__default.In#canCall(_module._default.Lemma_TailSubStreamK$_T0, _module.Stream.head(s#0), u#0)
         ==> _module.__default.In(_module._default.Lemma_TailSubStreamK$_T0, _module.Stream.head(s#0), u#0)
           || (exists n#3: int :: 
            { _module.__default.Tail(_module._default.Lemma_TailSubStreamK$_T0, $LS($LZ), u#0, n#3) } 
            LitInt(0) <= n#3
               && 
              LitInt(0) <= n#3
               && _module.Stream.head(_module.__default.Tail(_module._default.Lemma_TailSubStreamK$_T0, $LS($LZ), u#0, n#3))
                 == _module.Stream.head(s#0)));
  ensures _module.__default.IsSubStream_h#canCall(_module._default.Lemma_TailSubStreamK$_T0, k#0, s#0, u#0)
     ==> _module.__default.IsSubStream_h(_module._default.Lemma_TailSubStreamK$_T0, $LS($LZ), k#0, s#0, u#0)
       || (0 < k#0
         ==> _module.__default.IsSubStream_h(_module._default.Lemma_TailSubStreamK$_T0, 
          $LS($LS($LZ)), 
          k#0 - 1, 
          _module.Stream.tail(s#0), 
          u#0));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction s#0, u#0, k#0} Impl$$_module.__default.Lemma__TailSubStreamK(_module._default.Lemma_TailSubStreamK$_T0: Ty, 
    s#0: DatatypeType, 
    u#0: DatatypeType, 
    k#0: int)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var x##0_0: Box;
  var s##0_0: DatatypeType;

    // AddMethodImpl: Lemma_TailSubStreamK, Impl$$_module.__default.Lemma__TailSubStreamK
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(35,0): initial state"} true;
    assume $IsA#_module.Stream(s#0);
    assume $IsA#_module.Stream(u#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#s0#0: DatatypeType, $ih#u0#0: DatatypeType, $ih#k0#0: int :: 
      $Is($ih#s0#0, Tclass._module.Stream(_module._default.Lemma_TailSubStreamK$_T0))
           && $Is($ih#u0#0, Tclass._module.Stream(_module._default.Lemma_TailSubStreamK$_T0))
           && LitInt(0) <= $ih#k0#0
           && _module.__default.IsSubStream_h(_module._default.Lemma_TailSubStreamK$_T0, 
            $LS($LZ), 
            $ih#k0#0, 
            $ih#s0#0, 
            _module.Stream.tail($ih#u0#0))
           && 
          0 <= $ih#k0#0
           && $ih#k0#0 < k#0
         ==> _module.__default.IsSubStream_h(_module._default.Lemma_TailSubStreamK$_T0, 
          $LS($LZ), 
          $ih#k0#0, 
          $ih#s0#0, 
          $ih#u0#0));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(36,3)
    assume true;
    if (k#0 != 0)
    {
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(37,17)
        // TrCallStmt: Before ProcessCallStmt
        assume _module.Stream.Cons_q(s#0);
        assume _module.Stream.Cons_q(s#0);
        // ProcessCallStmt: CheckSubrange
        x##0_0 := _module.Stream.head(s#0);
        assume true;
        // ProcessCallStmt: CheckSubrange
        s##0_0 := u#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.Lemma__InTail(_module._default.Lemma_TailSubStreamK$_T0, x##0_0, s##0_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(37,27)"} true;
    }
    else
    {
    }
}



procedure {:_induction s#0, u#0} CheckWellformed$$_module.__default.Lemma__InSubStream(_module._default.Lemma_InSubStream$T: Ty, 
    x#0: Box
       where $IsBox(x#0, _module._default.Lemma_InSubStream$T)
         && $IsAllocBox(x#0, _module._default.Lemma_InSubStream$T, $Heap), 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Lemma_InSubStream$T))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.Lemma_InSubStream$T), $Heap)
         && $IsA#_module.Stream(s#0), 
    u#0: DatatypeType
       where $Is(u#0, Tclass._module.Stream(_module._default.Lemma_InSubStream$T))
         && $IsAlloc(u#0, Tclass._module.Stream(_module._default.Lemma_InSubStream$T), $Heap)
         && $IsA#_module.Stream(u#0));
  free requires 36 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction s#0, u#0} Call$$_module.__default.Lemma__InSubStream(_module._default.Lemma_InSubStream$T: Ty, 
    x#0: Box
       where $IsBox(x#0, _module._default.Lemma_InSubStream$T)
         && $IsAllocBox(x#0, _module._default.Lemma_InSubStream$T, $Heap), 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Lemma_InSubStream$T))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.Lemma_InSubStream$T), $Heap)
         && $IsA#_module.Stream(s#0), 
    u#0: DatatypeType
       where $Is(u#0, Tclass._module.Stream(_module._default.Lemma_InSubStream$T))
         && $IsAlloc(u#0, Tclass._module.Stream(_module._default.Lemma_InSubStream$T), $Heap)
         && $IsA#_module.Stream(u#0));
  // user-defined preconditions
  requires _module.__default.In#canCall(_module._default.Lemma_InSubStream$T, x#0, s#0)
     ==> _module.__default.In(_module._default.Lemma_InSubStream$T, x#0, s#0)
       || (exists n#0: int :: 
        { _module.__default.Tail(_module._default.Lemma_InSubStream$T, $LS($LZ), s#0, n#0) } 
        LitInt(0) <= n#0
           && 
          LitInt(0) <= n#0
           && _module.Stream.head(_module.__default.Tail(_module._default.Lemma_InSubStream$T, $LS($LZ), s#0, n#0))
             == x#0);
  requires _module.__default.IsSubStream#canCall(_module._default.Lemma_InSubStream$T, s#0, u#0)
     ==> _module.__default.IsSubStream(_module._default.Lemma_InSubStream$T, $LS($LZ), s#0, u#0)
       || (_module.__default.In#canCall(_module._default.Lemma_InSubStream$T, _module.Stream.head(s#0), u#0)
         ==> _module.__default.In(_module._default.Lemma_InSubStream$T, _module.Stream.head(s#0), u#0)
           || (exists n#1: int :: 
            { _module.__default.Tail(_module._default.Lemma_InSubStream$T, $LS($LZ), u#0, n#1) } 
            LitInt(0) <= n#1
               && 
              LitInt(0) <= n#1
               && _module.Stream.head(_module.__default.Tail(_module._default.Lemma_InSubStream$T, $LS($LZ), u#0, n#1))
                 == _module.Stream.head(s#0)));
  requires _module.__default.IsSubStream#canCall(_module._default.Lemma_InSubStream$T, s#0, u#0)
     ==> _module.__default.IsSubStream(_module._default.Lemma_InSubStream$T, $LS($LZ), s#0, u#0)
       || _module.__default.IsSubStream(_module._default.Lemma_InSubStream$T, 
        $LS($LS($LZ)), 
        _module.Stream.tail(s#0), 
        u#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.In#canCall(_module._default.Lemma_InSubStream$T, x#0, u#0);
  free ensures _module.__default.In#canCall(_module._default.Lemma_InSubStream$T, x#0, u#0)
     && 
    _module.__default.In(_module._default.Lemma_InSubStream$T, x#0, u#0)
     && (exists n#2: int :: 
      { _module.__default.Tail(_module._default.Lemma_InSubStream$T, $LS($LZ), u#0, n#2) } 
      LitInt(0) <= n#2
         && 
        LitInt(0) <= n#2
         && _module.Stream.head(_module.__default.Tail(_module._default.Lemma_InSubStream$T, $LS($LZ), u#0, n#2))
           == x#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction s#0, u#0} Impl$$_module.__default.Lemma__InSubStream(_module._default.Lemma_InSubStream$T: Ty, 
    x#0: Box
       where $IsBox(x#0, _module._default.Lemma_InSubStream$T)
         && $IsAllocBox(x#0, _module._default.Lemma_InSubStream$T, $Heap), 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Lemma_InSubStream$T))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.Lemma_InSubStream$T), $Heap)
         && $IsA#_module.Stream(s#0), 
    u#0: DatatypeType
       where $Is(u#0, Tclass._module.Stream(_module._default.Lemma_InSubStream$T))
         && $IsAlloc(u#0, Tclass._module.Stream(_module._default.Lemma_InSubStream$T), $Heap)
         && $IsA#_module.Stream(u#0))
   returns ($_reverifyPost: bool);
  free requires 36 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.__default.In#canCall(_module._default.Lemma_InSubStream$T, x#0, s#0)
     && 
    _module.__default.In(_module._default.Lemma_InSubStream$T, x#0, s#0)
     && (exists n#3: int :: 
      { _module.__default.Tail(_module._default.Lemma_InSubStream$T, $LS($LZ), s#0, n#3) } 
      LitInt(0) <= n#3
         && 
        LitInt(0) <= n#3
         && _module.Stream.head(_module.__default.Tail(_module._default.Lemma_InSubStream$T, $LS($LZ), s#0, n#3))
           == x#0);
  free requires _module.__default.IsSubStream#canCall(_module._default.Lemma_InSubStream$T, s#0, u#0)
     && 
    _module.__default.IsSubStream(_module._default.Lemma_InSubStream$T, $LS($LZ), s#0, u#0)
     && 
    _module.__default.In(_module._default.Lemma_InSubStream$T, _module.Stream.head(s#0), u#0)
     && _module.__default.IsSubStream(_module._default.Lemma_InSubStream$T, $LS($LZ), _module.Stream.tail(s#0), u#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.In#canCall(_module._default.Lemma_InSubStream$T, x#0, u#0);
  ensures _module.__default.In#canCall(_module._default.Lemma_InSubStream$T, x#0, u#0)
     ==> _module.__default.In(_module._default.Lemma_InSubStream$T, x#0, u#0)
       || (exists n#5: int :: 
        { _module.__default.Tail(_module._default.Lemma_InSubStream$T, $LS($LZ), u#0, n#5) } 
        LitInt(0) <= n#5
           && 
          LitInt(0) <= n#5
           && _module.Stream.head(_module.__default.Tail(_module._default.Lemma_InSubStream$T, $LS($LZ), u#0, n#5))
             == x#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction s#0, u#0} Impl$$_module.__default.Lemma__InSubStream(_module._default.Lemma_InSubStream$T: Ty, 
    x#0: Box, 
    s#0: DatatypeType, 
    u#0: DatatypeType)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var n#6: int where LitInt(0) <= n#6;
  var n#7: int;
  var ##s#3: DatatypeType;
  var ##n#0: int;
  var t#0: DatatypeType
     where $Is(t#0, Tclass._module.Stream(_module._default.Lemma_InSubStream$T))
       && $IsAlloc(t#0, Tclass._module.Stream(_module._default.Lemma_InSubStream$T), $Heap);
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var ##s#4: DatatypeType;
  var ##n#1: int;
  var ##s#5: DatatypeType;
  var ##u#1: DatatypeType;
  var $decr$loop#00: int;
  var $rhs#0_0: DatatypeType
     where $Is($rhs#0_0, Tclass._module.Stream(_module._default.Lemma_InSubStream$T));
  var $rhs#0_1: int where LitInt(0) <= $rhs#0_1;
  var newtype$check#0_0: int;

    // AddMethodImpl: Lemma_InSubStream, Impl$$_module.__default.Lemma__InSubStream
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(44,0): initial state"} true;
    assume $IsA#_module.Stream(s#0);
    assume $IsA#_module.Stream(u#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#s0#0: DatatypeType, $ih#u0#0: DatatypeType :: 
      $Is($ih#s0#0, Tclass._module.Stream(_module._default.Lemma_InSubStream$T))
           && $Is($ih#u0#0, Tclass._module.Stream(_module._default.Lemma_InSubStream$T))
           && 
          _module.__default.In(_module._default.Lemma_InSubStream$T, x#0, $ih#s0#0)
           && _module.__default.IsSubStream(_module._default.Lemma_InSubStream$T, $LS($LZ), $ih#s0#0, $ih#u0#0)
           && false
         ==> _module.__default.In(_module._default.Lemma_InSubStream$T, x#0, $ih#u0#0));
    $_reverifyPost := false;
    // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(45,9)
    havoc n#7;
    if (LitInt(0) <= n#7)
    {
        if (LitInt(0) <= n#7)
        {
            ##s#3 := s#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#3, Tclass._module.Stream(_module._default.Lemma_InSubStream$T), $Heap);
            ##n#0 := n#7;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
            assume _module.__default.Tail#canCall(_module._default.Lemma_InSubStream$T, s#0, n#7);
            assume _module.Stream.Cons_q(_module.__default.Tail(_module._default.Lemma_InSubStream$T, $LS($LZ), s#0, n#7));
            assume _module.Stream.Cons_q(_module.__default.Tail(_module._default.Lemma_InSubStream$T, $LS($LZ), s#0, n#7));
        }

        assume LitInt(0) <= n#7
           ==> _module.__default.Tail#canCall(_module._default.Lemma_InSubStream$T, s#0, n#7)
             && _module.Stream.Cons_q(_module.__default.Tail(_module._default.Lemma_InSubStream$T, $LS($LZ), s#0, n#7));
    }

    assert ($Is(LitInt(0), Tclass._System.nat())
         && 
        LitInt(0) <= LitInt(0)
         && _module.Stream.head(_module.__default.Tail(_module._default.Lemma_InSubStream$T, $LS($LZ), s#0, LitInt(0)))
           == x#0)
       || 
      ($Is(LitInt(0), Tclass._System.nat())
         && 
        LitInt(0) <= LitInt(0)
         && _module.Stream.head(_module.__default.Tail(_module._default.Lemma_InSubStream$T, $LS($LZ), s#0, LitInt(0)))
           == x#0)
       || 
      ($Is(LitInt(0), Tclass._System.nat())
         && 
        LitInt(0) <= LitInt(0)
         && _module.Stream.head(_module.__default.Tail(_module._default.Lemma_InSubStream$T, $LS($LZ), s#0, LitInt(0)))
           == x#0)
       || (exists $as#n0#0: int :: 
        LitInt(0) <= $as#n0#0
           && 
          LitInt(0) <= $as#n0#0
           && _module.Stream.head(_module.__default.Tail(_module._default.Lemma_InSubStream$T, $LS($LZ), s#0, $as#n0#0))
             == x#0);
    havoc n#6;
    assume LitInt(0) <= n#6
       && _module.Stream.head(_module.__default.Tail(_module._default.Lemma_InSubStream$T, $LS($LZ), s#0, n#6))
         == x#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(45,41)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(46,9)
    assume true;
    assume true;
    t#0 := s#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(46,12)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(47,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := (if n#6 <= LitInt(0) then 0 - n#6 else n#6 - 0);
    havoc $w$loop#0;
    while (true)
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> LitInt(0) <= n#6;
      free invariant $w$loop#0
         ==> _module.__default.Tail#canCall(_module._default.Lemma_InSubStream$T, t#0, n#6)
           && _module.Stream.Cons_q(_module.__default.Tail(_module._default.Lemma_InSubStream$T, $LS($LZ), t#0, n#6));
      invariant $w$loop#0
         ==> _module.Stream.head(_module.__default.Tail(_module._default.Lemma_InSubStream$T, $LS($LS($LZ)), t#0, n#6))
           == x#0;
      free invariant $w$loop#0
         ==> _module.__default.IsSubStream#canCall(_module._default.Lemma_InSubStream$T, t#0, u#0);
      invariant $w$loop#0
         ==> 
        _module.__default.IsSubStream#canCall(_module._default.Lemma_InSubStream$T, t#0, u#0)
         ==> _module.__default.IsSubStream(_module._default.Lemma_InSubStream$T, $LS($LZ), t#0, u#0)
           || (_module.__default.In#canCall(_module._default.Lemma_InSubStream$T, _module.Stream.head(t#0), u#0)
             ==> _module.__default.In(_module._default.Lemma_InSubStream$T, _module.Stream.head(t#0), u#0)
               || (exists n#8: int :: 
                { _module.__default.Tail(_module._default.Lemma_InSubStream$T, $LS($LZ), u#0, n#8) } 
                LitInt(0) <= n#8
                   && 
                  LitInt(0) <= n#8
                   && _module.Stream.head(_module.__default.Tail(_module._default.Lemma_InSubStream$T, $LS($LZ), u#0, n#8))
                     == _module.Stream.head(t#0)));
      invariant $w$loop#0
         ==> 
        _module.__default.IsSubStream#canCall(_module._default.Lemma_InSubStream$T, t#0, u#0)
         ==> _module.__default.IsSubStream(_module._default.Lemma_InSubStream$T, $LS($LZ), t#0, u#0)
           || _module.__default.IsSubStream(_module._default.Lemma_InSubStream$T, 
            $LS($LS($LZ)), 
            _module.Stream.tail(t#0), 
            u#0);
      free invariant $w$loop#0
         ==> _module.__default.IsSubStream#canCall(_module._default.Lemma_InSubStream$T, t#0, u#0)
           && 
          _module.__default.IsSubStream(_module._default.Lemma_InSubStream$T, $LS($LZ), t#0, u#0)
           && 
          _module.__default.In(_module._default.Lemma_InSubStream$T, _module.Stream.head(t#0), u#0)
           && _module.__default.IsSubStream(_module._default.Lemma_InSubStream$T, $LS($LZ), _module.Stream.tail(t#0), u#0);
      free invariant $PreLoopHeap$loop#0 == $Heap;
      free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
        { read($Heap, $o, $f) } 
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
      free invariant (if n#6 <= LitInt(0) then 0 - n#6 else n#6 - 0) <= $decr_init$loop#00
         && ((if n#6 <= LitInt(0) then 0 - n#6 else n#6 - 0) == $decr_init$loop#00 ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(47,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assume true;
            assume LitInt(0) <= n#6;
            ##s#4 := t#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#4, Tclass._module.Stream(_module._default.Lemma_InSubStream$T), $Heap);
            ##n#1 := n#6;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#1, Tclass._System.nat(), $Heap);
            assume _module.__default.Tail#canCall(_module._default.Lemma_InSubStream$T, t#0, n#6);
            assume _module.Stream.Cons_q(_module.__default.Tail(_module._default.Lemma_InSubStream$T, $LS($LZ), t#0, n#6));
            assume _module.Stream.Cons_q(_module.__default.Tail(_module._default.Lemma_InSubStream$T, $LS($LZ), t#0, n#6));
            assume _module.__default.Tail#canCall(_module._default.Lemma_InSubStream$T, t#0, n#6)
               && _module.Stream.Cons_q(_module.__default.Tail(_module._default.Lemma_InSubStream$T, $LS($LZ), t#0, n#6));
            assume _module.Stream.head(_module.__default.Tail(_module._default.Lemma_InSubStream$T, $LS($LZ), t#0, n#6))
               == x#0;
            ##s#5 := t#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#5, Tclass._module.Stream(_module._default.Lemma_InSubStream$T), $Heap);
            ##u#1 := u#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##u#1, Tclass._module.Stream(_module._default.Lemma_InSubStream$T), $Heap);
            assume _module.__default.IsSubStream#canCall(_module._default.Lemma_InSubStream$T, t#0, u#0);
            assume _module.__default.IsSubStream#canCall(_module._default.Lemma_InSubStream$T, t#0, u#0);
            assume _module.__default.IsSubStream(_module._default.Lemma_InSubStream$T, $LS($LZ), t#0, u#0);
            if (n#6 <= LitInt(0))
            {
            }
            else
            {
            }

            assume true;
            assume false;
        }

        assume true;
        if (n#6 == 0)
        {
            break;
        }

        $decr$loop#00 := (if n#6 <= LitInt(0) then 0 - n#6 else n#6 - 0);
        // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(52,10)
        assume true;
        assume true;
        assume _module.Stream.Cons_q(t#0);
        assume _module.Stream.Cons_q(t#0);
        $rhs#0_0 := _module.Stream.tail(t#0);
        newtype$check#0_0 := n#6 - 1;
        assert LitInt(0) <= newtype$check#0_0;
        assume true;
        $rhs#0_1 := n#6 - 1;
        t#0 := $rhs#0_0;
        n#6 := $rhs#0_1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(52,25)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(47,3)
        assert 0 <= $decr$loop#00
           || (if n#6 <= LitInt(0) then 0 - n#6 else n#6 - 0) == $decr$loop#00;
        assert (if n#6 <= LitInt(0) then 0 - n#6 else n#6 - 0) < $decr$loop#00;
        assume true;
        assume _module.__default.Tail#canCall(_module._default.Lemma_InSubStream$T, t#0, n#6)
           && _module.Stream.Cons_q(_module.__default.Tail(_module._default.Lemma_InSubStream$T, $LS($LZ), t#0, n#6));
        assume _module.__default.IsSubStream#canCall(_module._default.Lemma_InSubStream$T, t#0, u#0);
    }
}



// function declaration for _module._default.AllP
function _module.__default.AllP(_module._default.AllP$_T0: Ty, 
    $ly: LayerType, 
    s#0: DatatypeType, 
    P#0: HandleType)
   : bool;

function _module.__default.AllP#canCall(_module._default.AllP$_T0: Ty, s#0: DatatypeType, P#0: HandleType) : bool;

// layer synonym axiom
axiom (forall _module._default.AllP$_T0: Ty, 
    $ly: LayerType, 
    s#0: DatatypeType, 
    P#0: HandleType :: 
  { _module.__default.AllP(_module._default.AllP$_T0, $LS($ly), s#0, P#0) } 
  _module.__default.AllP(_module._default.AllP$_T0, $LS($ly), s#0, P#0)
     == _module.__default.AllP(_module._default.AllP$_T0, $ly, s#0, P#0));

// fuel synonym axiom
axiom (forall _module._default.AllP$_T0: Ty, 
    $ly: LayerType, 
    s#0: DatatypeType, 
    P#0: HandleType :: 
  { _module.__default.AllP(_module._default.AllP$_T0, AsFuelBottom($ly), s#0, P#0) } 
  _module.__default.AllP(_module._default.AllP$_T0, $ly, s#0, P#0)
     == _module.__default.AllP(_module._default.AllP$_T0, $LZ, s#0, P#0));

// consequence axiom for _module.__default.AllP
axiom 11 <= $FunctionContextHeight
   ==> (forall _module._default.AllP$_T0: Ty, 
      $ly: LayerType, 
      s#0: DatatypeType, 
      P#0: HandleType :: 
    { _module.__default.AllP(_module._default.AllP$_T0, $ly, s#0, P#0) } 
    _module.__default.AllP#canCall(_module._default.AllP$_T0, s#0, P#0)
         || (11 != $FunctionContextHeight
           && 
          $Is(s#0, Tclass._module.Stream(_module._default.AllP$_T0))
           && $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.AllP$_T0, TBool)))
       ==> true);

function _module.__default.AllP#requires(Ty, LayerType, DatatypeType, HandleType) : bool;

// #requires axiom for _module.__default.AllP
axiom (forall _module._default.AllP$_T0: Ty, 
    $ly: LayerType, 
    $Heap: Heap, 
    s#0: DatatypeType, 
    P#0: HandleType :: 
  { _module.__default.AllP#requires(_module._default.AllP$_T0, $ly, s#0, P#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && $Is(s#0, Tclass._module.Stream(_module._default.AllP$_T0))
       && $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.AllP$_T0, TBool))
     ==> _module.__default.AllP#requires(_module._default.AllP$_T0, $ly, s#0, P#0)
       == true);

// definition axiom for _module.__default.AllP (revealed)
axiom 11 <= $FunctionContextHeight
   ==> (forall _module._default.AllP$_T0: Ty, 
      $ly: LayerType, 
      $Heap: Heap, 
      s#0: DatatypeType, 
      P#0: HandleType :: 
    { _module.__default.AllP(_module._default.AllP$_T0, $LS($ly), s#0, P#0), $IsGoodHeap($Heap) } 
    _module.__default.AllP#canCall(_module._default.AllP$_T0, s#0, P#0)
         || (11 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(s#0, Tclass._module.Stream(_module._default.AllP$_T0))
           && $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.AllP$_T0, TBool)))
       ==> _module.Stream.Cons_q(s#0)
         && ($Unbox(Apply1(_module._default.AllP$_T0, TBool, $Heap, P#0, _module.Stream.head(s#0))): bool
           ==> _module.Stream.Cons_q(s#0)
             && _module.__default.AllP#canCall(_module._default.AllP$_T0, _module.Stream.tail(s#0), P#0))
         && _module.__default.AllP(_module._default.AllP$_T0, $LS($ly), s#0, P#0)
           == ($Unbox(Apply1(_module._default.AllP$_T0, TBool, $Heap, P#0, _module.Stream.head(s#0))): bool
             && _module.__default.AllP(_module._default.AllP$_T0, $ly, _module.Stream.tail(s#0), P#0)));

// 1st prefix predicate axiom for _module.__default.AllP_h
axiom 12 <= $FunctionContextHeight
   ==> (forall _module._default.AllP#$_T0: Ty, 
      $ly: LayerType, 
      s#0: DatatypeType, 
      P#0: HandleType :: 
    { _module.__default.AllP(_module._default.AllP#$_T0, $LS($ly), s#0, P#0) } 
    $Is(s#0, Tclass._module.Stream(_module._default.AllP#$_T0))
         && $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.AllP#$_T0, TBool))
         && _module.__default.AllP(_module._default.AllP#$_T0, $LS($ly), s#0, P#0)
       ==> (forall _k#0: Box :: 
        { _module.__default.AllP_h(_module._default.AllP#$_T0, $LS($ly), _k#0, s#0, P#0) } 
        _module.__default.AllP_h(_module._default.AllP#$_T0, $LS($ly), _k#0, s#0, P#0)));

// 2nd prefix predicate axiom
axiom 12 <= $FunctionContextHeight
   ==> (forall _module._default.AllP#$_T0: Ty, 
      $ly: LayerType, 
      s#0: DatatypeType, 
      P#0: HandleType :: 
    { _module.__default.AllP(_module._default.AllP#$_T0, $LS($ly), s#0, P#0) } 
    $Is(s#0, Tclass._module.Stream(_module._default.AllP#$_T0))
         && $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.AllP#$_T0, TBool))
         && (forall _k#0: Box :: 
          { _module.__default.AllP_h(_module._default.AllP#$_T0, $LS($ly), _k#0, s#0, P#0) } 
          _module.__default.AllP_h(_module._default.AllP#$_T0, $LS($ly), _k#0, s#0, P#0))
       ==> _module.__default.AllP(_module._default.AllP#$_T0, $LS($ly), s#0, P#0));

// 3rd prefix predicate axiom
axiom 12 <= $FunctionContextHeight
   ==> (forall _module._default.AllP#$_T0: Ty, 
      $ly: LayerType, 
      s#0: DatatypeType, 
      P#0: HandleType, 
      _k#0: Box :: 
    { _module.__default.AllP_h(_module._default.AllP#$_T0, $ly, _k#0, s#0, P#0) } 
    $Is(s#0, Tclass._module.Stream(_module._default.AllP#$_T0))
         && $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.AllP#$_T0, TBool))
         && _k#0 == ORD#FromNat(0)
       ==> _module.__default.AllP_h(_module._default.AllP#$_T0, $ly, _k#0, s#0, P#0));

procedure CheckWellformed$$_module.__default.AllP(_module._default.AllP$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.AllP$_T0)), 
    P#0: HandleType
       where $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.AllP$_T0, TBool)));
  free requires 11 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.AllP(_module._default.AllP$_T0: Ty, s#0: DatatypeType, P#0: HandleType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##s#0: DatatypeType;
  var ##P#0: HandleType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function AllP
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(58,19): initial state"} true;
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
        assume _module.Stream.Cons_q(s#0);
        if ($Unbox(Apply1(_module._default.AllP$_T0, TBool, $Heap, P#0, _module.Stream.head(s#0))): bool)
        {
            assume _module.Stream.Cons_q(s#0);
            ##s#0 := _module.Stream.tail(s#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#0, Tclass._module.Stream(_module._default.AllP$_T0), $Heap);
            ##P#0 := P#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##P#0, Tclass._System.___hTotalFunc1(_module._default.AllP$_T0, TBool), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.AllP#canCall(_module._default.AllP$_T0, _module.Stream.tail(s#0), P#0);
        }

        assume _module.__default.AllP(_module._default.AllP$_T0, $LS($LZ), s#0, P#0)
           == ($Unbox(Apply1(_module._default.AllP$_T0, TBool, $Heap, P#0, _module.Stream.head(s#0))): bool
             && _module.__default.AllP(_module._default.AllP$_T0, $LS($LZ), _module.Stream.tail(s#0), P#0));
        assume _module.Stream.Cons_q(s#0)
           && ($Unbox(Apply1(_module._default.AllP$_T0, TBool, $Heap, P#0, _module.Stream.head(s#0))): bool
             ==> _module.Stream.Cons_q(s#0)
               && _module.__default.AllP#canCall(_module._default.AllP$_T0, _module.Stream.tail(s#0), P#0));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.AllP(_module._default.AllP$_T0, $LS($LZ), s#0, P#0), TBool);
        assert b$reqreads#0;
    }
}



// function declaration for _module._default.AllP#
function _module.__default.AllP_h(_module._default.AllP#$_T0: Ty, 
    $ly: LayerType, 
    _k#0: Box, 
    s#0: DatatypeType, 
    P#0: HandleType)
   : bool;

function _module.__default.AllP_h#canCall(_module._default.AllP#$_T0: Ty, _k#0: Box, s#0: DatatypeType, P#0: HandleType)
   : bool;

// layer synonym axiom
axiom (forall _module._default.AllP#$_T0: Ty, 
    $ly: LayerType, 
    _k#0: Box, 
    s#0: DatatypeType, 
    P#0: HandleType :: 
  { _module.__default.AllP_h(_module._default.AllP#$_T0, $LS($ly), _k#0, s#0, P#0) } 
  _module.__default.AllP_h(_module._default.AllP#$_T0, $LS($ly), _k#0, s#0, P#0)
     == _module.__default.AllP_h(_module._default.AllP#$_T0, $ly, _k#0, s#0, P#0));

// fuel synonym axiom
axiom (forall _module._default.AllP#$_T0: Ty, 
    $ly: LayerType, 
    _k#0: Box, 
    s#0: DatatypeType, 
    P#0: HandleType :: 
  { _module.__default.AllP_h(_module._default.AllP#$_T0, AsFuelBottom($ly), _k#0, s#0, P#0) } 
  _module.__default.AllP_h(_module._default.AllP#$_T0, $ly, _k#0, s#0, P#0)
     == _module.__default.AllP_h(_module._default.AllP#$_T0, $LZ, _k#0, s#0, P#0));

// consequence axiom for _module.__default.AllP_h
axiom 12 <= $FunctionContextHeight
   ==> (forall _module._default.AllP#$_T0: Ty, 
      $ly: LayerType, 
      _k#0: Box, 
      s#0: DatatypeType, 
      P#0: HandleType :: 
    { _module.__default.AllP_h(_module._default.AllP#$_T0, $ly, _k#0, s#0, P#0) } 
    _module.__default.AllP_h#canCall(_module._default.AllP#$_T0, _k#0, s#0, P#0)
         || (12 != $FunctionContextHeight
           && 
          $Is(s#0, Tclass._module.Stream(_module._default.AllP#$_T0))
           && $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.AllP#$_T0, TBool)))
       ==> true);

function _module.__default.AllP_h#requires(Ty, LayerType, Box, DatatypeType, HandleType) : bool;

// #requires axiom for _module.__default.AllP_h
axiom (forall _module._default.AllP#$_T0: Ty, 
    $ly: LayerType, 
    $Heap: Heap, 
    _k#0: Box, 
    s#0: DatatypeType, 
    P#0: HandleType :: 
  { _module.__default.AllP_h#requires(_module._default.AllP#$_T0, $ly, _k#0, s#0, P#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && $Is(s#0, Tclass._module.Stream(_module._default.AllP#$_T0))
       && $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.AllP#$_T0, TBool))
     ==> _module.__default.AllP_h#requires(_module._default.AllP#$_T0, $ly, _k#0, s#0, P#0)
       == true);

// definition axiom for _module.__default.AllP_h (revealed)
axiom 12 <= $FunctionContextHeight
   ==> (forall _module._default.AllP#$_T0: Ty, 
      $ly: LayerType, 
      $Heap: Heap, 
      _k#0: Box, 
      s#0: DatatypeType, 
      P#0: HandleType :: 
    { _module.__default.AllP_h(_module._default.AllP#$_T0, $LS($ly), _k#0, s#0, P#0), $IsGoodHeap($Heap) } 
    _module.__default.AllP_h#canCall(_module._default.AllP#$_T0, _k#0, s#0, P#0)
         || (12 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(s#0, Tclass._module.Stream(_module._default.AllP#$_T0))
           && $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.AllP#$_T0, TBool)))
       ==> (0 < ORD#Offset(_k#0)
           ==> _module.Stream.Cons_q(s#0)
             && ($Unbox(Apply1(_module._default.AllP#$_T0, TBool, $Heap, P#0, _module.Stream.head(s#0))): bool
               ==> _module.Stream.Cons_q(s#0)
                 && _module.__default.AllP_h#canCall(_module._default.AllP#$_T0, 
                  ORD#Minus(_k#0, ORD#FromNat(1)), 
                  _module.Stream.tail(s#0), 
                  P#0)))
         && (
          (0 < ORD#Offset(_k#0)
           ==> $Unbox(Apply1(_module._default.AllP#$_T0, TBool, $Heap, P#0, _module.Stream.head(s#0))): bool
             && _module.__default.AllP_h(_module._default.AllP#$_T0, 
              $ly, 
              ORD#Minus(_k#0, ORD#FromNat(1)), 
              _module.Stream.tail(s#0), 
              P#0))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#0: Box :: 
            { _module.__default.AllP_h(_module._default.AllP#$_T0, $ly, _k'#0, s#0, P#0) } 
            ORD#Less(_k'#0, _k#0)
               ==> _module.__default.AllP_h#canCall(_module._default.AllP#$_T0, _k'#0, s#0, P#0)))
         && _module.__default.AllP_h(_module._default.AllP#$_T0, $LS($ly), _k#0, s#0, P#0)
           == ((0 < ORD#Offset(_k#0)
               ==> $Unbox(Apply1(_module._default.AllP#$_T0, TBool, $Heap, P#0, _module.Stream.head(s#0))): bool
                 && _module.__default.AllP_h(_module._default.AllP#$_T0, 
                  $ly, 
                  ORD#Minus(_k#0, ORD#FromNat(1)), 
                  _module.Stream.tail(s#0), 
                  P#0))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#0: Box :: 
                { _module.__default.AllP_h(_module._default.AllP#$_T0, $ly, _k'#0, s#0, P#0) } 
                ORD#Less(_k'#0, _k#0)
                   ==> _module.__default.AllP_h(_module._default.AllP#$_T0, $ly, _k'#0, s#0, P#0)))));

// definition axiom for _module.__default.AllP_h for decreasing-related literals (revealed)
axiom 12 <= $FunctionContextHeight
   ==> (forall _module._default.AllP#$_T0: Ty, 
      $ly: LayerType, 
      $Heap: Heap, 
      _k#0: Box, 
      s#0: DatatypeType, 
      P#0: HandleType :: 
    {:weight 3} { _module.__default.AllP_h(_module._default.AllP#$_T0, $LS($ly), Lit(_k#0), s#0, P#0), $IsGoodHeap($Heap) } 
    _module.__default.AllP_h#canCall(_module._default.AllP#$_T0, Lit(_k#0), s#0, P#0)
         || (12 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(s#0, Tclass._module.Stream(_module._default.AllP#$_T0))
           && $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.AllP#$_T0, TBool)))
       ==> (0 < ORD#Offset(_k#0)
           ==> _module.Stream.Cons_q(s#0)
             && ($Unbox(Apply1(_module._default.AllP#$_T0, TBool, $Heap, P#0, _module.Stream.head(s#0))): bool
               ==> _module.Stream.Cons_q(s#0)
                 && _module.__default.AllP_h#canCall(_module._default.AllP#$_T0, 
                  ORD#Minus(_k#0, ORD#FromNat(1)), 
                  _module.Stream.tail(s#0), 
                  P#0)))
         && (
          (0 < ORD#Offset(_k#0)
           ==> $Unbox(Apply1(_module._default.AllP#$_T0, TBool, $Heap, P#0, _module.Stream.head(s#0))): bool
             && _module.__default.AllP_h(_module._default.AllP#$_T0, 
              $LS($ly), 
              ORD#Minus(_k#0, ORD#FromNat(1)), 
              _module.Stream.tail(s#0), 
              P#0))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#1: Box :: 
            { _module.__default.AllP_h(_module._default.AllP#$_T0, $LS($ly), _k'#1, s#0, P#0) } 
            ORD#Less(_k'#1, _k#0)
               ==> _module.__default.AllP_h#canCall(_module._default.AllP#$_T0, _k'#1, s#0, P#0)))
         && _module.__default.AllP_h(_module._default.AllP#$_T0, $LS($ly), Lit(_k#0), s#0, P#0)
           == ((0 < ORD#Offset(_k#0)
               ==> $Unbox(Apply1(_module._default.AllP#$_T0, TBool, $Heap, P#0, _module.Stream.head(s#0))): bool
                 && _module.__default.AllP_h(_module._default.AllP#$_T0, 
                  $LS($ly), 
                  ORD#Minus(_k#0, ORD#FromNat(1)), 
                  _module.Stream.tail(s#0), 
                  P#0))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#1: Box :: 
                { _module.__default.AllP_h(_module._default.AllP#$_T0, $LS($ly), _k'#1, s#0, P#0) } 
                ORD#Less(_k'#1, _k#0)
                   ==> _module.__default.AllP_h(_module._default.AllP#$_T0, $LS($ly), _k'#1, s#0, P#0)))));

// definition axiom for _module.__default.AllP_h for all literals (revealed)
axiom 12 <= $FunctionContextHeight
   ==> (forall _module._default.AllP#$_T0: Ty, 
      $ly: LayerType, 
      $Heap: Heap, 
      _k#0: Box, 
      s#0: DatatypeType, 
      P#0: HandleType :: 
    {:weight 3} { _module.__default.AllP_h(_module._default.AllP#$_T0, $LS($ly), Lit(_k#0), Lit(s#0), Lit(P#0)), $IsGoodHeap($Heap) } 
    _module.__default.AllP_h#canCall(_module._default.AllP#$_T0, Lit(_k#0), Lit(s#0), Lit(P#0))
         || (12 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(s#0, Tclass._module.Stream(_module._default.AllP#$_T0))
           && $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.AllP#$_T0, TBool)))
       ==> (0 < ORD#Offset(_k#0)
           ==> _module.Stream.Cons_q(s#0)
             && ($Unbox(Apply1(_module._default.AllP#$_T0, TBool, $Heap, P#0, _module.Stream.head(s#0))): bool
               ==> _module.Stream.Cons_q(s#0)
                 && _module.__default.AllP_h#canCall(_module._default.AllP#$_T0, 
                  ORD#Minus(_k#0, ORD#FromNat(1)), 
                  _module.Stream.tail(s#0), 
                  P#0)))
         && (
          (0 < ORD#Offset(_k#0)
           ==> $Unbox(Apply1(_module._default.AllP#$_T0, TBool, $Heap, P#0, _module.Stream.head(s#0))): bool
             && _module.__default.AllP_h(_module._default.AllP#$_T0, 
              $LS($ly), 
              ORD#Minus(_k#0, ORD#FromNat(1)), 
              _module.Stream.tail(s#0), 
              P#0))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#2: Box :: 
            { _module.__default.AllP_h(_module._default.AllP#$_T0, $LS($ly), _k'#2, s#0, P#0) } 
            ORD#Less(_k'#2, _k#0)
               ==> _module.__default.AllP_h#canCall(_module._default.AllP#$_T0, _k'#2, s#0, P#0)))
         && _module.__default.AllP_h(_module._default.AllP#$_T0, $LS($ly), Lit(_k#0), Lit(s#0), Lit(P#0))
           == ((0 < ORD#Offset(_k#0)
               ==> $Unbox(Apply1(_module._default.AllP#$_T0, TBool, $Heap, P#0, _module.Stream.head(s#0))): bool
                 && _module.__default.AllP_h(_module._default.AllP#$_T0, 
                  $LS($ly), 
                  ORD#Minus(_k#0, ORD#FromNat(1)), 
                  _module.Stream.tail(s#0), 
                  P#0))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#2: Box :: 
                { _module.__default.AllP_h(_module._default.AllP#$_T0, $LS($ly), _k'#2, s#0, P#0) } 
                ORD#Less(_k'#2, _k#0)
                   ==> _module.__default.AllP_h(_module._default.AllP#$_T0, $LS($ly), _k'#2, s#0, P#0)))));

procedure {:_induction s#0, P#0} CheckWellformed$$_module.__default.Lemma__InAllP(_module._default.Lemma_InAllP$T: Ty, 
    x#0: Box
       where $IsBox(x#0, _module._default.Lemma_InAllP$T)
         && $IsAllocBox(x#0, _module._default.Lemma_InAllP$T, $Heap), 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Lemma_InAllP$T))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.Lemma_InAllP$T), $Heap)
         && $IsA#_module.Stream(s#0), 
    P#0: HandleType
       where $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.Lemma_InAllP$T, TBool))
         && $IsAlloc(P#0, 
          Tclass._System.___hTotalFunc1(_module._default.Lemma_InAllP$T, TBool), 
          $Heap));
  free requires 37 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction s#0, P#0} Call$$_module.__default.Lemma__InAllP(_module._default.Lemma_InAllP$T: Ty, 
    x#0: Box
       where $IsBox(x#0, _module._default.Lemma_InAllP$T)
         && $IsAllocBox(x#0, _module._default.Lemma_InAllP$T, $Heap), 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Lemma_InAllP$T))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.Lemma_InAllP$T), $Heap)
         && $IsA#_module.Stream(s#0), 
    P#0: HandleType
       where $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.Lemma_InAllP$T, TBool))
         && $IsAlloc(P#0, 
          Tclass._System.___hTotalFunc1(_module._default.Lemma_InAllP$T, TBool), 
          $Heap));
  // user-defined preconditions
  requires _module.__default.In#canCall(_module._default.Lemma_InAllP$T, x#0, s#0)
     ==> _module.__default.In(_module._default.Lemma_InAllP$T, x#0, s#0)
       || (exists n#0: int :: 
        { _module.__default.Tail(_module._default.Lemma_InAllP$T, $LS($LZ), s#0, n#0) } 
        LitInt(0) <= n#0
           && 
          LitInt(0) <= n#0
           && _module.Stream.head(_module.__default.Tail(_module._default.Lemma_InAllP$T, $LS($LZ), s#0, n#0))
             == x#0);
  requires _module.__default.AllP#canCall(_module._default.Lemma_InAllP$T, s#0, P#0)
     ==> _module.__default.AllP(_module._default.Lemma_InAllP$T, $LS($LZ), s#0, P#0)
       || $Unbox(Apply1(_module._default.Lemma_InAllP$T, TBool, $Heap, P#0, _module.Stream.head(s#0))): bool;
  requires _module.__default.AllP#canCall(_module._default.Lemma_InAllP$T, s#0, P#0)
     ==> _module.__default.AllP(_module._default.Lemma_InAllP$T, $LS($LZ), s#0, P#0)
       || _module.__default.AllP(_module._default.Lemma_InAllP$T, $LS($LS($LZ)), _module.Stream.tail(s#0), P#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures $Unbox(Apply1(_module._default.Lemma_InAllP$T, TBool, $Heap, P#0, x#0)): bool;
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction s#0, P#0} Impl$$_module.__default.Lemma__InAllP(_module._default.Lemma_InAllP$T: Ty, 
    x#0: Box
       where $IsBox(x#0, _module._default.Lemma_InAllP$T)
         && $IsAllocBox(x#0, _module._default.Lemma_InAllP$T, $Heap), 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Lemma_InAllP$T))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.Lemma_InAllP$T), $Heap)
         && $IsA#_module.Stream(s#0), 
    P#0: HandleType
       where $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.Lemma_InAllP$T, TBool))
         && $IsAlloc(P#0, 
          Tclass._System.___hTotalFunc1(_module._default.Lemma_InAllP$T, TBool), 
          $Heap))
   returns ($_reverifyPost: bool);
  free requires 37 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.__default.In#canCall(_module._default.Lemma_InAllP$T, x#0, s#0)
     && 
    _module.__default.In(_module._default.Lemma_InAllP$T, x#0, s#0)
     && (exists n#1: int :: 
      { _module.__default.Tail(_module._default.Lemma_InAllP$T, $LS($LZ), s#0, n#1) } 
      LitInt(0) <= n#1
         && 
        LitInt(0) <= n#1
         && _module.Stream.head(_module.__default.Tail(_module._default.Lemma_InAllP$T, $LS($LZ), s#0, n#1))
           == x#0);
  free requires _module.__default.AllP#canCall(_module._default.Lemma_InAllP$T, s#0, P#0)
     && 
    _module.__default.AllP(_module._default.Lemma_InAllP$T, $LS($LZ), s#0, P#0)
     && 
    $Unbox(Apply1(_module._default.Lemma_InAllP$T, TBool, $Heap, P#0, _module.Stream.head(s#0))): bool
     && _module.__default.AllP(_module._default.Lemma_InAllP$T, $LS($LZ), _module.Stream.tail(s#0), P#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures $Unbox(Apply1(_module._default.Lemma_InAllP$T, TBool, $Heap, P#0, x#0)): bool;
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction s#0, P#0} Impl$$_module.__default.Lemma__InAllP(_module._default.Lemma_InAllP$T: Ty, 
    x#0: Box, 
    s#0: DatatypeType, 
    P#0: HandleType)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var n#2: int where LitInt(0) <= n#2;
  var n#3: int;
  var ##s#2: DatatypeType;
  var ##n#0: int;
  var t#0: DatatypeType
     where $Is(t#0, Tclass._module.Stream(_module._default.Lemma_InAllP$T))
       && $IsAlloc(t#0, Tclass._module.Stream(_module._default.Lemma_InAllP$T), $Heap);
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var ##s#3: DatatypeType;
  var ##n#1: int;
  var ##s#4: DatatypeType;
  var ##P#1: HandleType;
  var $decr$loop#00: int;
  var $rhs#0_0: DatatypeType
     where $Is($rhs#0_0, Tclass._module.Stream(_module._default.Lemma_InAllP$T));
  var $rhs#0_1: int where LitInt(0) <= $rhs#0_1;
  var newtype$check#0_0: int;

    // AddMethodImpl: Lemma_InAllP, Impl$$_module.__default.Lemma__InAllP
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(65,0): initial state"} true;
    assume $IsA#_module.Stream(s#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#s0#0: DatatypeType, $ih#P0#0: HandleType :: 
      $Is($ih#s0#0, Tclass._module.Stream(_module._default.Lemma_InAllP$T))
           && $Is($ih#P0#0, Tclass._System.___hTotalFunc1(_module._default.Lemma_InAllP$T, TBool))
           && 
          _module.__default.In(_module._default.Lemma_InAllP$T, x#0, $ih#s0#0)
           && _module.__default.AllP(_module._default.Lemma_InAllP$T, $LS($LZ), $ih#s0#0, $ih#P0#0)
           && false
         ==> $Unbox(Apply1(_module._default.Lemma_InAllP$T, TBool, $Heap, $ih#P0#0, x#0)): bool);
    $_reverifyPost := false;
    // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(66,9)
    havoc n#3;
    if (LitInt(0) <= n#3)
    {
        if (LitInt(0) <= n#3)
        {
            ##s#2 := s#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#2, Tclass._module.Stream(_module._default.Lemma_InAllP$T), $Heap);
            ##n#0 := n#3;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
            assume _module.__default.Tail#canCall(_module._default.Lemma_InAllP$T, s#0, n#3);
            assume _module.Stream.Cons_q(_module.__default.Tail(_module._default.Lemma_InAllP$T, $LS($LZ), s#0, n#3));
            assume _module.Stream.Cons_q(_module.__default.Tail(_module._default.Lemma_InAllP$T, $LS($LZ), s#0, n#3));
        }

        assume LitInt(0) <= n#3
           ==> _module.__default.Tail#canCall(_module._default.Lemma_InAllP$T, s#0, n#3)
             && _module.Stream.Cons_q(_module.__default.Tail(_module._default.Lemma_InAllP$T, $LS($LZ), s#0, n#3));
    }

    assert ($Is(LitInt(0), Tclass._System.nat())
         && 
        LitInt(0) <= LitInt(0)
         && _module.Stream.head(_module.__default.Tail(_module._default.Lemma_InAllP$T, $LS($LZ), s#0, LitInt(0)))
           == x#0)
       || 
      ($Is(LitInt(0), Tclass._System.nat())
         && 
        LitInt(0) <= LitInt(0)
         && _module.Stream.head(_module.__default.Tail(_module._default.Lemma_InAllP$T, $LS($LZ), s#0, LitInt(0)))
           == x#0)
       || 
      ($Is(LitInt(0), Tclass._System.nat())
         && 
        LitInt(0) <= LitInt(0)
         && _module.Stream.head(_module.__default.Tail(_module._default.Lemma_InAllP$T, $LS($LZ), s#0, LitInt(0)))
           == x#0)
       || (exists $as#n0#0: int :: 
        LitInt(0) <= $as#n0#0
           && 
          LitInt(0) <= $as#n0#0
           && _module.Stream.head(_module.__default.Tail(_module._default.Lemma_InAllP$T, $LS($LZ), s#0, $as#n0#0))
             == x#0);
    havoc n#2;
    assume LitInt(0) <= n#2
       && _module.Stream.head(_module.__default.Tail(_module._default.Lemma_InAllP$T, $LS($LZ), s#0, n#2))
         == x#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(66,41)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(67,9)
    assume true;
    assume true;
    t#0 := s#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(67,12)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(68,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := (if n#2 <= LitInt(0) then 0 - n#2 else n#2 - 0);
    havoc $w$loop#0;
    while (true)
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> LitInt(0) <= n#2;
      free invariant $w$loop#0
         ==> _module.__default.Tail#canCall(_module._default.Lemma_InAllP$T, t#0, n#2)
           && _module.Stream.Cons_q(_module.__default.Tail(_module._default.Lemma_InAllP$T, $LS($LZ), t#0, n#2));
      invariant $w$loop#0
         ==> _module.Stream.head(_module.__default.Tail(_module._default.Lemma_InAllP$T, $LS($LS($LZ)), t#0, n#2))
           == x#0;
      free invariant $w$loop#0
         ==> _module.__default.AllP#canCall(_module._default.Lemma_InAllP$T, t#0, P#0);
      invariant $w$loop#0
         ==> 
        _module.__default.AllP#canCall(_module._default.Lemma_InAllP$T, t#0, P#0)
         ==> _module.__default.AllP(_module._default.Lemma_InAllP$T, $LS($LZ), t#0, P#0)
           || $Unbox(Apply1(_module._default.Lemma_InAllP$T, TBool, $Heap, P#0, _module.Stream.head(t#0))): bool;
      invariant $w$loop#0
         ==> 
        _module.__default.AllP#canCall(_module._default.Lemma_InAllP$T, t#0, P#0)
         ==> _module.__default.AllP(_module._default.Lemma_InAllP$T, $LS($LZ), t#0, P#0)
           || _module.__default.AllP(_module._default.Lemma_InAllP$T, $LS($LS($LZ)), _module.Stream.tail(t#0), P#0);
      free invariant $w$loop#0
         ==> _module.__default.AllP#canCall(_module._default.Lemma_InAllP$T, t#0, P#0)
           && 
          _module.__default.AllP(_module._default.Lemma_InAllP$T, $LS($LZ), t#0, P#0)
           && 
          $Unbox(Apply1(_module._default.Lemma_InAllP$T, TBool, $Heap, P#0, _module.Stream.head(t#0))): bool
           && _module.__default.AllP(_module._default.Lemma_InAllP$T, $LS($LZ), _module.Stream.tail(t#0), P#0);
      free invariant $PreLoopHeap$loop#0 == $Heap;
      free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
        { read($Heap, $o, $f) } 
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
      free invariant (if n#2 <= LitInt(0) then 0 - n#2 else n#2 - 0) <= $decr_init$loop#00
         && ((if n#2 <= LitInt(0) then 0 - n#2 else n#2 - 0) == $decr_init$loop#00 ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(68,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assume true;
            assume LitInt(0) <= n#2;
            ##s#3 := t#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#3, Tclass._module.Stream(_module._default.Lemma_InAllP$T), $Heap);
            ##n#1 := n#2;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#1, Tclass._System.nat(), $Heap);
            assume _module.__default.Tail#canCall(_module._default.Lemma_InAllP$T, t#0, n#2);
            assume _module.Stream.Cons_q(_module.__default.Tail(_module._default.Lemma_InAllP$T, $LS($LZ), t#0, n#2));
            assume _module.Stream.Cons_q(_module.__default.Tail(_module._default.Lemma_InAllP$T, $LS($LZ), t#0, n#2));
            assume _module.__default.Tail#canCall(_module._default.Lemma_InAllP$T, t#0, n#2)
               && _module.Stream.Cons_q(_module.__default.Tail(_module._default.Lemma_InAllP$T, $LS($LZ), t#0, n#2));
            assume _module.Stream.head(_module.__default.Tail(_module._default.Lemma_InAllP$T, $LS($LZ), t#0, n#2))
               == x#0;
            ##s#4 := t#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#4, Tclass._module.Stream(_module._default.Lemma_InAllP$T), $Heap);
            ##P#1 := P#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##P#1, 
              Tclass._System.___hTotalFunc1(_module._default.Lemma_InAllP$T, TBool), 
              $Heap);
            assume _module.__default.AllP#canCall(_module._default.Lemma_InAllP$T, t#0, P#0);
            assume _module.__default.AllP#canCall(_module._default.Lemma_InAllP$T, t#0, P#0);
            assume _module.__default.AllP(_module._default.Lemma_InAllP$T, $LS($LZ), t#0, P#0);
            if (n#2 <= LitInt(0))
            {
            }
            else
            {
            }

            assume true;
            assume false;
        }

        assume true;
        if (n#2 == 0)
        {
            break;
        }

        $decr$loop#00 := (if n#2 <= LitInt(0) then 0 - n#2 else n#2 - 0);
        // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(73,10)
        assume true;
        assume true;
        assume _module.Stream.Cons_q(t#0);
        assume _module.Stream.Cons_q(t#0);
        $rhs#0_0 := _module.Stream.tail(t#0);
        newtype$check#0_0 := n#2 - 1;
        assert LitInt(0) <= newtype$check#0_0;
        assume true;
        $rhs#0_1 := n#2 - 1;
        t#0 := $rhs#0_0;
        n#2 := $rhs#0_1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(73,25)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(68,3)
        assert 0 <= $decr$loop#00
           || (if n#2 <= LitInt(0) then 0 - n#2 else n#2 - 0) == $decr$loop#00;
        assert (if n#2 <= LitInt(0) then 0 - n#2 else n#2 - 0) < $decr$loop#00;
        assume true;
        assume _module.__default.Tail#canCall(_module._default.Lemma_InAllP$T, t#0, n#2)
           && _module.Stream.Cons_q(_module.__default.Tail(_module._default.Lemma_InAllP$T, $LS($LZ), t#0, n#2));
        assume _module.__default.AllP#canCall(_module._default.Lemma_InAllP$T, t#0, P#0);
    }
}



// function declaration for _module._default.IsAnother
function _module.__default.IsAnother(_module._default.IsAnother$_T0: Ty, s#0: DatatypeType, P#0: HandleType) : bool;

function _module.__default.IsAnother#canCall(_module._default.IsAnother$_T0: Ty, s#0: DatatypeType, P#0: HandleType) : bool;

// consequence axiom for _module.__default.IsAnother
axiom 13 <= $FunctionContextHeight
   ==> (forall _module._default.IsAnother$_T0: Ty, s#0: DatatypeType, P#0: HandleType :: 
    { _module.__default.IsAnother(_module._default.IsAnother$_T0, s#0, P#0) } 
    _module.__default.IsAnother#canCall(_module._default.IsAnother$_T0, s#0, P#0)
         || (13 != $FunctionContextHeight
           && 
          $Is(s#0, Tclass._module.Stream(_module._default.IsAnother$_T0))
           && $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.IsAnother$_T0, TBool)))
       ==> true);

function _module.__default.IsAnother#requires(Ty, DatatypeType, HandleType) : bool;

// #requires axiom for _module.__default.IsAnother
axiom (forall _module._default.IsAnother$_T0: Ty, 
    $Heap: Heap, 
    s#0: DatatypeType, 
    P#0: HandleType :: 
  { _module.__default.IsAnother#requires(_module._default.IsAnother$_T0, s#0, P#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && $Is(s#0, Tclass._module.Stream(_module._default.IsAnother$_T0))
       && $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.IsAnother$_T0, TBool))
     ==> _module.__default.IsAnother#requires(_module._default.IsAnother$_T0, s#0, P#0)
       == true);

// definition axiom for _module.__default.IsAnother (revealed)
axiom 13 <= $FunctionContextHeight
   ==> (forall _module._default.IsAnother$_T0: Ty, 
      $Heap: Heap, 
      s#0: DatatypeType, 
      P#0: HandleType :: 
    { _module.__default.IsAnother(_module._default.IsAnother$_T0, s#0, P#0), $IsGoodHeap($Heap) } 
    _module.__default.IsAnother#canCall(_module._default.IsAnother$_T0, s#0, P#0)
         || (13 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(s#0, Tclass._module.Stream(_module._default.IsAnother$_T0))
           && $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.IsAnother$_T0, TBool)))
       ==> (forall n#0: int :: 
          { _module.__default.Tail(_module._default.IsAnother$_T0, $LS($LZ), s#0, n#0) } 
          LitInt(0) <= n#0
             ==> 
            LitInt(0) <= n#0
             ==> _module.__default.Tail#canCall(_module._default.IsAnother$_T0, s#0, n#0)
               && _module.Stream.Cons_q(_module.__default.Tail(_module._default.IsAnother$_T0, $LS($LZ), s#0, n#0)))
         && _module.__default.IsAnother(_module._default.IsAnother$_T0, s#0, P#0)
           == (exists n#0: int :: 
            { _module.__default.Tail(_module._default.IsAnother$_T0, $LS($LZ), s#0, n#0) } 
            LitInt(0) <= n#0
               && 
              LitInt(0) <= n#0
               && $Unbox(Apply1(_module._default.IsAnother$_T0, 
                  TBool, 
                  $Heap, 
                  P#0, 
                  _module.Stream.head(_module.__default.Tail(_module._default.IsAnother$_T0, $LS($LZ), s#0, n#0)))): bool));

// definition axiom for _module.__default.IsAnother for all literals (revealed)
axiom 13 <= $FunctionContextHeight
   ==> (forall _module._default.IsAnother$_T0: Ty, 
      $Heap: Heap, 
      s#0: DatatypeType, 
      P#0: HandleType :: 
    {:weight 3} { _module.__default.IsAnother(_module._default.IsAnother$_T0, Lit(s#0), Lit(P#0)), $IsGoodHeap($Heap) } 
    _module.__default.IsAnother#canCall(_module._default.IsAnother$_T0, Lit(s#0), Lit(P#0))
         || (13 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(s#0, Tclass._module.Stream(_module._default.IsAnother$_T0))
           && $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.IsAnother$_T0, TBool)))
       ==> (forall n#1: int :: 
          { _module.__default.Tail(_module._default.IsAnother$_T0, $LS($LZ), s#0, n#1) } 
          LitInt(0) <= n#1
             ==> 
            LitInt(0) <= n#1
             ==> _module.__default.Tail#canCall(_module._default.IsAnother$_T0, Lit(s#0), n#1)
               && _module.Stream.Cons_q(_module.__default.Tail(_module._default.IsAnother$_T0, $LS($LZ), Lit(s#0), n#1)))
         && _module.__default.IsAnother(_module._default.IsAnother$_T0, Lit(s#0), Lit(P#0))
           == (exists n#1: int :: 
            { _module.__default.Tail(_module._default.IsAnother$_T0, $LS($LZ), s#0, n#1) } 
            LitInt(0) <= n#1
               && 
              LitInt(0) <= n#1
               && $Unbox(Apply1(_module._default.IsAnother$_T0, 
                  TBool, 
                  $Heap, 
                  Lit(P#0), 
                  _module.Stream.head(_module.__default.Tail(_module._default.IsAnother$_T0, $LS($LZ), Lit(s#0), n#1)))): bool));

procedure CheckWellformed$$_module.__default.IsAnother(_module._default.IsAnother$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.IsAnother$_T0)), 
    P#0: HandleType
       where $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.IsAnother$_T0, TBool)));
  free requires 13 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.IsAnother(_module._default.IsAnother$_T0: Ty, s#0: DatatypeType, P#0: HandleType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var n#2: int;
  var ##s#0: DatatypeType;
  var ##n#0: int;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function IsAnother
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(77,10): initial state"} true;
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
                ##s#0 := s#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#0, Tclass._module.Stream(_module._default.IsAnother$_T0), $Heap);
                ##n#0 := n#2;
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
                b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assume _module.__default.Tail#canCall(_module._default.IsAnother$_T0, s#0, n#2);
                assume _module.Stream.Cons_q(_module.__default.Tail(_module._default.IsAnother$_T0, $LS($LZ), s#0, n#2));
                assume _module.Stream.Cons_q(_module.__default.Tail(_module._default.IsAnother$_T0, $LS($LZ), s#0, n#2));
            }
        }

        // End Comprehension WF check
        assume _module.__default.IsAnother(_module._default.IsAnother$_T0, s#0, P#0)
           == (exists n#3: int :: 
            { _module.__default.Tail(_module._default.IsAnother$_T0, $LS($LZ), s#0, n#3) } 
            LitInt(0) <= n#3
               && 
              LitInt(0) <= n#3
               && $Unbox(Apply1(_module._default.IsAnother$_T0, 
                  TBool, 
                  $Heap, 
                  P#0, 
                  _module.Stream.head(_module.__default.Tail(_module._default.IsAnother$_T0, $LS($LZ), s#0, n#3)))): bool);
        assume (forall n#3: int :: 
          { _module.__default.Tail(_module._default.IsAnother$_T0, $LS($LZ), s#0, n#3) } 
          LitInt(0) <= n#3
             ==> 
            LitInt(0) <= n#3
             ==> _module.__default.Tail#canCall(_module._default.IsAnother$_T0, s#0, n#3)
               && _module.Stream.Cons_q(_module.__default.Tail(_module._default.IsAnother$_T0, $LS($LZ), s#0, n#3)));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.IsAnother(_module._default.IsAnother$_T0, s#0, P#0), TBool);
        assert b$reqreads#0;
    }
}



// function declaration for _module._default.AlwaysAnother
function _module.__default.AlwaysAnother(_module._default.AlwaysAnother$_T0: Ty, 
    $ly: LayerType, 
    s#0: DatatypeType, 
    P#0: HandleType)
   : bool;

function _module.__default.AlwaysAnother#canCall(_module._default.AlwaysAnother$_T0: Ty, s#0: DatatypeType, P#0: HandleType)
   : bool;

// layer synonym axiom
axiom (forall _module._default.AlwaysAnother$_T0: Ty, 
    $ly: LayerType, 
    s#0: DatatypeType, 
    P#0: HandleType :: 
  { _module.__default.AlwaysAnother(_module._default.AlwaysAnother$_T0, $LS($ly), s#0, P#0) } 
  _module.__default.AlwaysAnother(_module._default.AlwaysAnother$_T0, $LS($ly), s#0, P#0)
     == _module.__default.AlwaysAnother(_module._default.AlwaysAnother$_T0, $ly, s#0, P#0));

// fuel synonym axiom
axiom (forall _module._default.AlwaysAnother$_T0: Ty, 
    $ly: LayerType, 
    s#0: DatatypeType, 
    P#0: HandleType :: 
  { _module.__default.AlwaysAnother(_module._default.AlwaysAnother$_T0, AsFuelBottom($ly), s#0, P#0) } 
  _module.__default.AlwaysAnother(_module._default.AlwaysAnother$_T0, $ly, s#0, P#0)
     == _module.__default.AlwaysAnother(_module._default.AlwaysAnother$_T0, $LZ, s#0, P#0));

// consequence axiom for _module.__default.AlwaysAnother
axiom 14 <= $FunctionContextHeight
   ==> (forall _module._default.AlwaysAnother$_T0: Ty, 
      $ly: LayerType, 
      s#0: DatatypeType, 
      P#0: HandleType :: 
    { _module.__default.AlwaysAnother(_module._default.AlwaysAnother$_T0, $ly, s#0, P#0) } 
    _module.__default.AlwaysAnother#canCall(_module._default.AlwaysAnother$_T0, s#0, P#0)
         || (14 != $FunctionContextHeight
           && 
          $Is(s#0, Tclass._module.Stream(_module._default.AlwaysAnother$_T0))
           && $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.AlwaysAnother$_T0, TBool)))
       ==> true);

function _module.__default.AlwaysAnother#requires(Ty, LayerType, DatatypeType, HandleType) : bool;

// #requires axiom for _module.__default.AlwaysAnother
axiom (forall _module._default.AlwaysAnother$_T0: Ty, 
    $ly: LayerType, 
    s#0: DatatypeType, 
    P#0: HandleType :: 
  { _module.__default.AlwaysAnother#requires(_module._default.AlwaysAnother$_T0, $ly, s#0, P#0) } 
  $Is(s#0, Tclass._module.Stream(_module._default.AlwaysAnother$_T0))
       && $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.AlwaysAnother$_T0, TBool))
     ==> _module.__default.AlwaysAnother#requires(_module._default.AlwaysAnother$_T0, $ly, s#0, P#0)
       == true);

// definition axiom for _module.__default.AlwaysAnother (revealed)
axiom 14 <= $FunctionContextHeight
   ==> (forall _module._default.AlwaysAnother$_T0: Ty, 
      $ly: LayerType, 
      s#0: DatatypeType, 
      P#0: HandleType :: 
    { _module.__default.AlwaysAnother(_module._default.AlwaysAnother$_T0, $LS($ly), s#0, P#0) } 
    _module.__default.AlwaysAnother#canCall(_module._default.AlwaysAnother$_T0, s#0, P#0)
         || (14 != $FunctionContextHeight
           && 
          $Is(s#0, Tclass._module.Stream(_module._default.AlwaysAnother$_T0))
           && $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.AlwaysAnother$_T0, TBool)))
       ==> _module.__default.IsAnother#canCall(_module._default.AlwaysAnother$_T0, s#0, P#0)
         && (_module.__default.IsAnother(_module._default.AlwaysAnother$_T0, s#0, P#0)
           ==> _module.Stream.Cons_q(s#0)
             && _module.__default.AlwaysAnother#canCall(_module._default.AlwaysAnother$_T0, _module.Stream.tail(s#0), P#0))
         && _module.__default.AlwaysAnother(_module._default.AlwaysAnother$_T0, $LS($ly), s#0, P#0)
           == (_module.__default.IsAnother(_module._default.AlwaysAnother$_T0, s#0, P#0)
             && _module.__default.AlwaysAnother(_module._default.AlwaysAnother$_T0, $ly, _module.Stream.tail(s#0), P#0)));

// 1st prefix predicate axiom for _module.__default.AlwaysAnother_h
axiom 15 <= $FunctionContextHeight
   ==> (forall _module._default.AlwaysAnother#$_T0: Ty, 
      $ly: LayerType, 
      s#0: DatatypeType, 
      P#0: HandleType :: 
    { _module.__default.AlwaysAnother(_module._default.AlwaysAnother#$_T0, $LS($ly), s#0, P#0) } 
    $Is(s#0, Tclass._module.Stream(_module._default.AlwaysAnother#$_T0))
         && $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.AlwaysAnother#$_T0, TBool))
         && _module.__default.AlwaysAnother(_module._default.AlwaysAnother#$_T0, $LS($ly), s#0, P#0)
       ==> (forall _k#0: Box :: 
        { _module.__default.AlwaysAnother_h(_module._default.AlwaysAnother#$_T0, $LS($ly), _k#0, s#0, P#0) } 
        _module.__default.AlwaysAnother_h(_module._default.AlwaysAnother#$_T0, $LS($ly), _k#0, s#0, P#0)));

// 2nd prefix predicate axiom
axiom 15 <= $FunctionContextHeight
   ==> (forall _module._default.AlwaysAnother#$_T0: Ty, 
      $ly: LayerType, 
      s#0: DatatypeType, 
      P#0: HandleType :: 
    { _module.__default.AlwaysAnother(_module._default.AlwaysAnother#$_T0, $LS($ly), s#0, P#0) } 
    $Is(s#0, Tclass._module.Stream(_module._default.AlwaysAnother#$_T0))
         && $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.AlwaysAnother#$_T0, TBool))
         && (forall _k#0: Box :: 
          { _module.__default.AlwaysAnother_h(_module._default.AlwaysAnother#$_T0, $LS($ly), _k#0, s#0, P#0) } 
          _module.__default.AlwaysAnother_h(_module._default.AlwaysAnother#$_T0, $LS($ly), _k#0, s#0, P#0))
       ==> _module.__default.AlwaysAnother(_module._default.AlwaysAnother#$_T0, $LS($ly), s#0, P#0));

// 3rd prefix predicate axiom
axiom 15 <= $FunctionContextHeight
   ==> (forall _module._default.AlwaysAnother#$_T0: Ty, 
      $ly: LayerType, 
      s#0: DatatypeType, 
      P#0: HandleType, 
      _k#0: Box :: 
    { _module.__default.AlwaysAnother_h(_module._default.AlwaysAnother#$_T0, $ly, _k#0, s#0, P#0) } 
    $Is(s#0, Tclass._module.Stream(_module._default.AlwaysAnother#$_T0))
         && $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.AlwaysAnother#$_T0, TBool))
         && _k#0 == ORD#FromNat(0)
       ==> _module.__default.AlwaysAnother_h(_module._default.AlwaysAnother#$_T0, $ly, _k#0, s#0, P#0));

procedure CheckWellformed$$_module.__default.AlwaysAnother(_module._default.AlwaysAnother$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.AlwaysAnother$_T0)), 
    P#0: HandleType
       where $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.AlwaysAnother$_T0, TBool)));
  free requires 14 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.AlwaysAnother(_module._default.AlwaysAnother$_T0: Ty, s#0: DatatypeType, P#0: HandleType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##s#0: DatatypeType;
  var ##P#0: HandleType;
  var ##s#1: DatatypeType;
  var ##P#1: HandleType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function AlwaysAnother
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(81,19): initial state"} true;
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
        ##s#0 := s#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#0, Tclass._module.Stream(_module._default.AlwaysAnother$_T0), $Heap);
        ##P#0 := P#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##P#0, 
          Tclass._System.___hTotalFunc1(_module._default.AlwaysAnother$_T0, TBool), 
          $Heap);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.IsAnother#canCall(_module._default.AlwaysAnother$_T0, s#0, P#0);
        if (_module.__default.IsAnother(_module._default.AlwaysAnother$_T0, s#0, P#0))
        {
            assume _module.Stream.Cons_q(s#0);
            ##s#1 := _module.Stream.tail(s#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#1, Tclass._module.Stream(_module._default.AlwaysAnother$_T0), $Heap);
            ##P#1 := P#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##P#1, 
              Tclass._System.___hTotalFunc1(_module._default.AlwaysAnother$_T0, TBool), 
              $Heap);
            b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.AlwaysAnother#canCall(_module._default.AlwaysAnother$_T0, _module.Stream.tail(s#0), P#0);
        }

        assume _module.__default.AlwaysAnother(_module._default.AlwaysAnother$_T0, $LS($LZ), s#0, P#0)
           == (_module.__default.IsAnother(_module._default.AlwaysAnother$_T0, s#0, P#0)
             && _module.__default.AlwaysAnother(_module._default.AlwaysAnother$_T0, $LS($LZ), _module.Stream.tail(s#0), P#0));
        assume _module.__default.IsAnother#canCall(_module._default.AlwaysAnother$_T0, s#0, P#0)
           && (_module.__default.IsAnother(_module._default.AlwaysAnother$_T0, s#0, P#0)
             ==> _module.Stream.Cons_q(s#0)
               && _module.__default.AlwaysAnother#canCall(_module._default.AlwaysAnother$_T0, _module.Stream.tail(s#0), P#0));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.AlwaysAnother(_module._default.AlwaysAnother$_T0, $LS($LZ), s#0, P#0), 
          TBool);
        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



// function declaration for _module._default.AlwaysAnother#
function _module.__default.AlwaysAnother_h(_module._default.AlwaysAnother#$_T0: Ty, 
    $ly: LayerType, 
    _k#0: Box, 
    s#0: DatatypeType, 
    P#0: HandleType)
   : bool;

function _module.__default.AlwaysAnother_h#canCall(_module._default.AlwaysAnother#$_T0: Ty, 
    _k#0: Box, 
    s#0: DatatypeType, 
    P#0: HandleType)
   : bool;

// layer synonym axiom
axiom (forall _module._default.AlwaysAnother#$_T0: Ty, 
    $ly: LayerType, 
    _k#0: Box, 
    s#0: DatatypeType, 
    P#0: HandleType :: 
  { _module.__default.AlwaysAnother_h(_module._default.AlwaysAnother#$_T0, $LS($ly), _k#0, s#0, P#0) } 
  _module.__default.AlwaysAnother_h(_module._default.AlwaysAnother#$_T0, $LS($ly), _k#0, s#0, P#0)
     == _module.__default.AlwaysAnother_h(_module._default.AlwaysAnother#$_T0, $ly, _k#0, s#0, P#0));

// fuel synonym axiom
axiom (forall _module._default.AlwaysAnother#$_T0: Ty, 
    $ly: LayerType, 
    _k#0: Box, 
    s#0: DatatypeType, 
    P#0: HandleType :: 
  { _module.__default.AlwaysAnother_h(_module._default.AlwaysAnother#$_T0, AsFuelBottom($ly), _k#0, s#0, P#0) } 
  _module.__default.AlwaysAnother_h(_module._default.AlwaysAnother#$_T0, $ly, _k#0, s#0, P#0)
     == _module.__default.AlwaysAnother_h(_module._default.AlwaysAnother#$_T0, $LZ, _k#0, s#0, P#0));

// consequence axiom for _module.__default.AlwaysAnother_h
axiom 15 <= $FunctionContextHeight
   ==> (forall _module._default.AlwaysAnother#$_T0: Ty, 
      $ly: LayerType, 
      _k#0: Box, 
      s#0: DatatypeType, 
      P#0: HandleType :: 
    { _module.__default.AlwaysAnother_h(_module._default.AlwaysAnother#$_T0, $ly, _k#0, s#0, P#0) } 
    _module.__default.AlwaysAnother_h#canCall(_module._default.AlwaysAnother#$_T0, _k#0, s#0, P#0)
         || (15 != $FunctionContextHeight
           && 
          $Is(s#0, Tclass._module.Stream(_module._default.AlwaysAnother#$_T0))
           && $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.AlwaysAnother#$_T0, TBool)))
       ==> true);

function _module.__default.AlwaysAnother_h#requires(Ty, LayerType, Box, DatatypeType, HandleType) : bool;

// #requires axiom for _module.__default.AlwaysAnother_h
axiom (forall _module._default.AlwaysAnother#$_T0: Ty, 
    $ly: LayerType, 
    _k#0: Box, 
    s#0: DatatypeType, 
    P#0: HandleType :: 
  { _module.__default.AlwaysAnother_h#requires(_module._default.AlwaysAnother#$_T0, $ly, _k#0, s#0, P#0) } 
  $Is(s#0, Tclass._module.Stream(_module._default.AlwaysAnother#$_T0))
       && $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.AlwaysAnother#$_T0, TBool))
     ==> _module.__default.AlwaysAnother_h#requires(_module._default.AlwaysAnother#$_T0, $ly, _k#0, s#0, P#0)
       == true);

// definition axiom for _module.__default.AlwaysAnother_h (revealed)
axiom 15 <= $FunctionContextHeight
   ==> (forall _module._default.AlwaysAnother#$_T0: Ty, 
      $ly: LayerType, 
      _k#0: Box, 
      s#0: DatatypeType, 
      P#0: HandleType :: 
    { _module.__default.AlwaysAnother_h(_module._default.AlwaysAnother#$_T0, $LS($ly), _k#0, s#0, P#0) } 
    _module.__default.AlwaysAnother_h#canCall(_module._default.AlwaysAnother#$_T0, _k#0, s#0, P#0)
         || (15 != $FunctionContextHeight
           && 
          $Is(s#0, Tclass._module.Stream(_module._default.AlwaysAnother#$_T0))
           && $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.AlwaysAnother#$_T0, TBool)))
       ==> (0 < ORD#Offset(_k#0)
           ==> _module.__default.IsAnother#canCall(_module._default.AlwaysAnother#$_T0, s#0, P#0)
             && (_module.__default.IsAnother(_module._default.AlwaysAnother#$_T0, s#0, P#0)
               ==> _module.Stream.Cons_q(s#0)
                 && _module.__default.AlwaysAnother_h#canCall(_module._default.AlwaysAnother#$_T0, 
                  ORD#Minus(_k#0, ORD#FromNat(1)), 
                  _module.Stream.tail(s#0), 
                  P#0)))
         && (
          (0 < ORD#Offset(_k#0)
           ==> _module.__default.IsAnother(_module._default.AlwaysAnother#$_T0, s#0, P#0)
             && _module.__default.AlwaysAnother_h(_module._default.AlwaysAnother#$_T0, 
              $ly, 
              ORD#Minus(_k#0, ORD#FromNat(1)), 
              _module.Stream.tail(s#0), 
              P#0))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#0: Box :: 
            { _module.__default.AlwaysAnother_h(_module._default.AlwaysAnother#$_T0, $ly, _k'#0, s#0, P#0) } 
            ORD#Less(_k'#0, _k#0)
               ==> _module.__default.AlwaysAnother_h#canCall(_module._default.AlwaysAnother#$_T0, _k'#0, s#0, P#0)))
         && _module.__default.AlwaysAnother_h(_module._default.AlwaysAnother#$_T0, $LS($ly), _k#0, s#0, P#0)
           == ((0 < ORD#Offset(_k#0)
               ==> _module.__default.IsAnother(_module._default.AlwaysAnother#$_T0, s#0, P#0)
                 && _module.__default.AlwaysAnother_h(_module._default.AlwaysAnother#$_T0, 
                  $ly, 
                  ORD#Minus(_k#0, ORD#FromNat(1)), 
                  _module.Stream.tail(s#0), 
                  P#0))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#0: Box :: 
                { _module.__default.AlwaysAnother_h(_module._default.AlwaysAnother#$_T0, $ly, _k'#0, s#0, P#0) } 
                ORD#Less(_k'#0, _k#0)
                   ==> _module.__default.AlwaysAnother_h(_module._default.AlwaysAnother#$_T0, $ly, _k'#0, s#0, P#0)))));

// definition axiom for _module.__default.AlwaysAnother_h for decreasing-related literals (revealed)
axiom 15 <= $FunctionContextHeight
   ==> (forall _module._default.AlwaysAnother#$_T0: Ty, 
      $ly: LayerType, 
      _k#0: Box, 
      s#0: DatatypeType, 
      P#0: HandleType :: 
    {:weight 3} { _module.__default.AlwaysAnother_h(_module._default.AlwaysAnother#$_T0, $LS($ly), Lit(_k#0), s#0, P#0) } 
    _module.__default.AlwaysAnother_h#canCall(_module._default.AlwaysAnother#$_T0, Lit(_k#0), s#0, P#0)
         || (15 != $FunctionContextHeight
           && 
          $Is(s#0, Tclass._module.Stream(_module._default.AlwaysAnother#$_T0))
           && $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.AlwaysAnother#$_T0, TBool)))
       ==> (0 < ORD#Offset(_k#0)
           ==> _module.__default.IsAnother#canCall(_module._default.AlwaysAnother#$_T0, s#0, P#0)
             && (_module.__default.IsAnother(_module._default.AlwaysAnother#$_T0, s#0, P#0)
               ==> _module.Stream.Cons_q(s#0)
                 && _module.__default.AlwaysAnother_h#canCall(_module._default.AlwaysAnother#$_T0, 
                  ORD#Minus(_k#0, ORD#FromNat(1)), 
                  _module.Stream.tail(s#0), 
                  P#0)))
         && (
          (0 < ORD#Offset(_k#0)
           ==> _module.__default.IsAnother(_module._default.AlwaysAnother#$_T0, s#0, P#0)
             && _module.__default.AlwaysAnother_h(_module._default.AlwaysAnother#$_T0, 
              $LS($ly), 
              ORD#Minus(_k#0, ORD#FromNat(1)), 
              _module.Stream.tail(s#0), 
              P#0))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#1: Box :: 
            { _module.__default.AlwaysAnother_h(_module._default.AlwaysAnother#$_T0, $LS($ly), _k'#1, s#0, P#0) } 
            ORD#Less(_k'#1, _k#0)
               ==> _module.__default.AlwaysAnother_h#canCall(_module._default.AlwaysAnother#$_T0, _k'#1, s#0, P#0)))
         && _module.__default.AlwaysAnother_h(_module._default.AlwaysAnother#$_T0, $LS($ly), Lit(_k#0), s#0, P#0)
           == ((0 < ORD#Offset(_k#0)
               ==> _module.__default.IsAnother(_module._default.AlwaysAnother#$_T0, s#0, P#0)
                 && _module.__default.AlwaysAnother_h(_module._default.AlwaysAnother#$_T0, 
                  $LS($ly), 
                  ORD#Minus(_k#0, ORD#FromNat(1)), 
                  _module.Stream.tail(s#0), 
                  P#0))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#1: Box :: 
                { _module.__default.AlwaysAnother_h(_module._default.AlwaysAnother#$_T0, $LS($ly), _k'#1, s#0, P#0) } 
                ORD#Less(_k'#1, _k#0)
                   ==> _module.__default.AlwaysAnother_h(_module._default.AlwaysAnother#$_T0, $LS($ly), _k'#1, s#0, P#0)))));

// definition axiom for _module.__default.AlwaysAnother_h for all literals (revealed)
axiom 15 <= $FunctionContextHeight
   ==> (forall _module._default.AlwaysAnother#$_T0: Ty, 
      $ly: LayerType, 
      _k#0: Box, 
      s#0: DatatypeType, 
      P#0: HandleType :: 
    {:weight 3} { _module.__default.AlwaysAnother_h(_module._default.AlwaysAnother#$_T0, $LS($ly), Lit(_k#0), Lit(s#0), Lit(P#0)) } 
    _module.__default.AlwaysAnother_h#canCall(_module._default.AlwaysAnother#$_T0, Lit(_k#0), Lit(s#0), Lit(P#0))
         || (15 != $FunctionContextHeight
           && 
          $Is(s#0, Tclass._module.Stream(_module._default.AlwaysAnother#$_T0))
           && $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.AlwaysAnother#$_T0, TBool)))
       ==> (0 < ORD#Offset(_k#0)
           ==> _module.__default.IsAnother#canCall(_module._default.AlwaysAnother#$_T0, s#0, P#0)
             && (_module.__default.IsAnother(_module._default.AlwaysAnother#$_T0, s#0, P#0)
               ==> _module.Stream.Cons_q(s#0)
                 && _module.__default.AlwaysAnother_h#canCall(_module._default.AlwaysAnother#$_T0, 
                  ORD#Minus(_k#0, ORD#FromNat(1)), 
                  _module.Stream.tail(s#0), 
                  P#0)))
         && (
          (0 < ORD#Offset(_k#0)
           ==> _module.__default.IsAnother(_module._default.AlwaysAnother#$_T0, s#0, P#0)
             && _module.__default.AlwaysAnother_h(_module._default.AlwaysAnother#$_T0, 
              $LS($ly), 
              ORD#Minus(_k#0, ORD#FromNat(1)), 
              _module.Stream.tail(s#0), 
              P#0))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#2: Box :: 
            { _module.__default.AlwaysAnother_h(_module._default.AlwaysAnother#$_T0, $LS($ly), _k'#2, s#0, P#0) } 
            ORD#Less(_k'#2, _k#0)
               ==> _module.__default.AlwaysAnother_h#canCall(_module._default.AlwaysAnother#$_T0, _k'#2, s#0, P#0)))
         && _module.__default.AlwaysAnother_h(_module._default.AlwaysAnother#$_T0, $LS($ly), Lit(_k#0), Lit(s#0), Lit(P#0))
           == ((0 < ORD#Offset(_k#0)
               ==> _module.__default.IsAnother(_module._default.AlwaysAnother#$_T0, s#0, P#0)
                 && _module.__default.AlwaysAnother_h(_module._default.AlwaysAnother#$_T0, 
                  $LS($ly), 
                  ORD#Minus(_k#0, ORD#FromNat(1)), 
                  _module.Stream.tail(s#0), 
                  P#0))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#2: Box :: 
                { _module.__default.AlwaysAnother_h(_module._default.AlwaysAnother#$_T0, $LS($ly), _k'#2, s#0, P#0) } 
                ORD#Less(_k'#2, _k#0)
                   ==> _module.__default.AlwaysAnother_h(_module._default.AlwaysAnother#$_T0, $LS($ly), _k'#2, s#0, P#0)))));

procedure CheckWellformed$$_module.__default.Lemma__AllImpliesAlwaysAnother(_module._default.Lemma_AllImpliesAlwaysAnother$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Lemma_AllImpliesAlwaysAnother$_T0))
         && $IsAlloc(s#0, 
          Tclass._module.Stream(_module._default.Lemma_AllImpliesAlwaysAnother$_T0), 
          $Heap)
         && $IsA#_module.Stream(s#0), 
    P#0: HandleType
       where $Is(P#0, 
          Tclass._System.___hTotalFunc1(_module._default.Lemma_AllImpliesAlwaysAnother$_T0, TBool))
         && $IsAlloc(P#0, 
          Tclass._System.___hTotalFunc1(_module._default.Lemma_AllImpliesAlwaysAnother$_T0, TBool), 
          $Heap));
  free requires 16 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Lemma__AllImpliesAlwaysAnother(_module._default.Lemma_AllImpliesAlwaysAnother$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Lemma_AllImpliesAlwaysAnother$_T0))
         && $IsAlloc(s#0, 
          Tclass._module.Stream(_module._default.Lemma_AllImpliesAlwaysAnother$_T0), 
          $Heap)
         && $IsA#_module.Stream(s#0), 
    P#0: HandleType
       where $Is(P#0, 
          Tclass._System.___hTotalFunc1(_module._default.Lemma_AllImpliesAlwaysAnother$_T0, TBool))
         && $IsAlloc(P#0, 
          Tclass._System.___hTotalFunc1(_module._default.Lemma_AllImpliesAlwaysAnother$_T0, TBool), 
          $Heap));
  // user-defined preconditions
  requires _module.__default.AllP#canCall(_module._default.Lemma_AllImpliesAlwaysAnother$_T0, s#0, P#0)
     ==> _module.__default.AllP(_module._default.Lemma_AllImpliesAlwaysAnother$_T0, $LS($LZ), s#0, P#0)
       || $Unbox(Apply1(_module._default.Lemma_AllImpliesAlwaysAnother$_T0, 
          TBool, 
          $Heap, 
          P#0, 
          _module.Stream.head(s#0))): bool;
  requires _module.__default.AllP#canCall(_module._default.Lemma_AllImpliesAlwaysAnother$_T0, s#0, P#0)
     ==> _module.__default.AllP(_module._default.Lemma_AllImpliesAlwaysAnother$_T0, $LS($LZ), s#0, P#0)
       || _module.__default.AllP(_module._default.Lemma_AllImpliesAlwaysAnother$_T0, 
        $LS($LS($LZ)), 
        _module.Stream.tail(s#0), 
        P#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.AlwaysAnother#canCall(_module._default.Lemma_AllImpliesAlwaysAnother$_T0, s#0, P#0);
  free ensures _module.__default.AlwaysAnother#canCall(_module._default.Lemma_AllImpliesAlwaysAnother$_T0, s#0, P#0)
     && 
    _module.__default.AlwaysAnother(_module._default.Lemma_AllImpliesAlwaysAnother$_T0, $LS($LZ), s#0, P#0)
     && 
    _module.__default.IsAnother(_module._default.Lemma_AllImpliesAlwaysAnother$_T0, s#0, P#0)
     && _module.__default.AlwaysAnother(_module._default.Lemma_AllImpliesAlwaysAnother$_T0, 
      $LS($LZ), 
      _module.Stream.tail(s#0), 
      P#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, s#1, P#1} CoCall$$_module.__default.Lemma__AllImpliesAlwaysAnother_h(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0: Ty, 
    _k#0: Box, 
    s#1: DatatypeType
       where $Is(s#1, Tclass._module.Stream(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0))
         && $IsAlloc(s#1, 
          Tclass._module.Stream(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0), 
          $Heap)
         && $IsA#_module.Stream(s#1), 
    P#1: HandleType
       where $Is(P#1, 
          Tclass._System.___hTotalFunc1(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0, TBool))
         && $IsAlloc(P#1, 
          Tclass._System.___hTotalFunc1(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0, TBool), 
          $Heap));
  // user-defined preconditions
  requires _module.__default.AllP#canCall(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0, s#1, P#1)
     ==> _module.__default.AllP(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0, $LS($LZ), s#1, P#1)
       || $Unbox(Apply1(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0, 
          TBool, 
          $Heap, 
          P#1, 
          _module.Stream.head(s#1))): bool;
  requires _module.__default.AllP#canCall(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0, s#1, P#1)
     ==> _module.__default.AllP(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0, $LS($LZ), s#1, P#1)
       || _module.__default.AllP(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0, 
        $LS($LS($LZ)), 
        _module.Stream.tail(s#1), 
        P#1);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.AlwaysAnother_h#canCall(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0, _k#0, s#1, P#1);
  free ensures _module.__default.AlwaysAnother_h#canCall(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0, _k#0, s#1, P#1)
     && 
    _module.__default.AlwaysAnother_h(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0, $LS($LZ), _k#0, s#1, P#1)
     && 
    (0 < ORD#Offset(_k#0)
       ==> _module.__default.IsAnother(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0, s#1, P#1)
         && _module.__default.AlwaysAnother_h(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0, 
          $LS($LZ), 
          ORD#Minus(_k#0, ORD#FromNat(1)), 
          _module.Stream.tail(s#1), 
          P#1))
     && (LitInt(0) == ORD#Offset(_k#0)
       ==> (forall _k'#0: Box :: 
        { _module.__default.AlwaysAnother_h(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0, $LS($LZ), _k'#0, s#1, P#1) } 
        ORD#Less(_k'#0, _k#0)
           ==> _module.__default.AlwaysAnother_h(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0, $LS($LZ), _k'#0, s#1, P#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, s#1, P#1} Impl$$_module.__default.Lemma__AllImpliesAlwaysAnother_h(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0: Ty, 
    _k#0: Box, 
    s#1: DatatypeType
       where $Is(s#1, Tclass._module.Stream(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0))
         && $IsAlloc(s#1, 
          Tclass._module.Stream(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0), 
          $Heap)
         && $IsA#_module.Stream(s#1), 
    P#1: HandleType
       where $Is(P#1, 
          Tclass._System.___hTotalFunc1(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0, TBool))
         && $IsAlloc(P#1, 
          Tclass._System.___hTotalFunc1(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0, TBool), 
          $Heap))
   returns ($_reverifyPost: bool);
  free requires 17 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.__default.AllP#canCall(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0, s#1, P#1)
     && 
    _module.__default.AllP(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0, $LS($LZ), s#1, P#1)
     && 
    $Unbox(Apply1(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0, 
        TBool, 
        $Heap, 
        P#1, 
        _module.Stream.head(s#1))): bool
     && _module.__default.AllP(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0, 
      $LS($LZ), 
      _module.Stream.tail(s#1), 
      P#1);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.AlwaysAnother_h#canCall(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0, _k#0, s#1, P#1);
  ensures _module.__default.AlwaysAnother_h#canCall(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0, _k#0, s#1, P#1)
     ==> _module.__default.AlwaysAnother_h(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0, $LS($LZ), _k#0, s#1, P#1)
       || (0 < ORD#Offset(_k#0)
         ==> 
        _module.__default.IsAnother#canCall(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0, s#1, P#1)
         ==> _module.__default.IsAnother(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0, s#1, P#1)
           || (exists n#2: int :: 
            { _module.__default.Tail(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0, $LS($LZ), s#1, n#2) } 
            LitInt(0) <= n#2
               && 
              LitInt(0) <= n#2
               && $Unbox(Apply1(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0, 
                  TBool, 
                  $Heap, 
                  P#1, 
                  _module.Stream.head(_module.__default.Tail(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0, $LS($LZ), s#1, n#2)))): bool));
  ensures _module.__default.AlwaysAnother_h#canCall(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0, _k#0, s#1, P#1)
     ==> _module.__default.AlwaysAnother_h(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0, $LS($LZ), _k#0, s#1, P#1)
       || (0 < ORD#Offset(_k#0)
         ==> _module.__default.AlwaysAnother_h(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0, 
          $LS($LS($LZ)), 
          ORD#Minus(_k#0, ORD#FromNat(1)), 
          _module.Stream.tail(s#1), 
          P#1));
  ensures _module.__default.AlwaysAnother_h#canCall(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0, _k#0, s#1, P#1)
     ==> _module.__default.AlwaysAnother_h(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0, $LS($LZ), _k#0, s#1, P#1)
       || (LitInt(0) == ORD#Offset(_k#0)
         ==> (forall _k'#1: Box :: 
          { _module.__default.AlwaysAnother_h(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0, 
              $LS($LS($LZ)), 
              _k'#1, 
              s#1, 
              P#1) } 
          ORD#Less(_k'#1, _k#0)
             ==> _module.__default.AlwaysAnother_h(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0, 
              $LS($LS($LZ)), 
              _k'#1, 
              s#1, 
              P#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0, s#1, P#1} Impl$$_module.__default.Lemma__AllImpliesAlwaysAnother_h(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0: Ty, 
    _k#0: Box, 
    s#1: DatatypeType, 
    P#1: HandleType)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var ##s#2: DatatypeType;
  var ##n#0: int;
  var $initHeapForallStmt#1: Heap;

    // AddMethodImpl: Lemma_AllImpliesAlwaysAnother#, Impl$$_module.__default.Lemma__AllImpliesAlwaysAnother_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(85,15): initial state"} true;
    assume $IsA#_module.Stream(s#1);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: Box, $ih#s0#0: DatatypeType, $ih#P0#0: HandleType :: 
      $Is($ih#s0#0, 
            Tclass._module.Stream(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0))
           && $Is($ih#P0#0, 
            Tclass._System.___hTotalFunc1(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0, TBool))
           && _module.__default.AllP(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0, 
            $LS($LZ), 
            $ih#s0#0, 
            $ih#P0#0)
           && ORD#Less($ih#_k0#0, _k#0)
         ==> _module.__default.AlwaysAnother_h(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0, 
          $LS($LZ), 
          $ih#_k0#0, 
          $ih#s0#0, 
          $ih#P0#0));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(88,1)
    assume true;
    if (0 < ORD#Offset(_k#0))
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(89,3)
        ##s#2 := s#1;
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#2, 
          Tclass._module.Stream(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0), 
          $Heap);
        assert $Is(LitInt(0), Tclass._System.nat());
        ##n#0 := LitInt(0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
        assume _module.__default.Tail#canCall(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0, s#1, LitInt(0));
        assume _module.Stream.Cons_q(_module.__default.Tail(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0, $LS($LZ), s#1, LitInt(0)));
        assume $IsA#_module.Stream(_module.__default.Tail(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0, $LS($LZ), s#1, LitInt(0)))
           && $IsA#_module.Stream(s#1)
           && _module.__default.Tail#canCall(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0, s#1, LitInt(0));
        assert {:subsumption 0} $Eq#_module.Stream(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0, 
          _module._default.Lemma_AllImpliesAlwaysAnother#$_T0, 
          $LS($LS($LZ)), 
          _module.__default.Tail(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0, 
            $LS($LS($LZ)), 
            s#1, 
            LitInt(0)), 
          s#1);
        assume $Eq#_module.Stream(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0, 
          _module._default.Lemma_AllImpliesAlwaysAnother#$_T0, 
          $LS($LS($LZ)), 
          _module.__default.Tail(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0, $LS($LZ), s#1, LitInt(0)), 
          s#1);
    }
    else
    {
        // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(85,16)
        $initHeapForallStmt#1 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#1 == $Heap;
        assume (forall _k'#2: Box, s#2: DatatypeType, P#2: HandleType :: 
          $Is(s#2, Tclass._module.Stream(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0))
               && $Is(P#2, 
                Tclass._System.___hTotalFunc1(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0, TBool))
               && 
              ORD#Less(_k'#2, _k#0)
               && _module.__default.AllP(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0, $LS($LZ), s#2, P#2)
             ==> _module.__default.AlwaysAnother_h(_module._default.Lemma_AllImpliesAlwaysAnother#$_T0, $LS($LZ), _k'#2, s#2, P#2));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(85,15)"} true;
    }
}



// function declaration for _module._default.Next
function _module.__default.Next(_module._default.Next$_T0: Ty, s#0: DatatypeType, P#0: HandleType) : int;

function _module.__default.Next#canCall(_module._default.Next$_T0: Ty, s#0: DatatypeType, P#0: HandleType) : bool;

// consequence axiom for _module.__default.Next
axiom 19 <= $FunctionContextHeight
   ==> (forall _module._default.Next$_T0: Ty, $Heap: Heap, s#0: DatatypeType, P#0: HandleType :: 
    { _module.__default.Next(_module._default.Next$_T0, s#0, P#0), $IsGoodHeap($Heap) } 
    _module.__default.Next#canCall(_module._default.Next$_T0, s#0, P#0)
         || (19 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(s#0, Tclass._module.Stream(_module._default.Next$_T0))
           && $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.Next$_T0, TBool))
           && _module.__default.AlwaysAnother(_module._default.Next$_T0, $LS($LZ), s#0, P#0))
       ==> $Unbox(Apply1(_module._default.Next$_T0, 
            TBool, 
            $Heap, 
            P#0, 
            _module.Stream.head(_module.__default.Tail(_module._default.Next$_T0, 
                $LS($LZ), 
                s#0, 
                _module.__default.Next(_module._default.Next$_T0, s#0, P#0))))): bool
         && (forall i#0: int :: 
          { _module.__default.Tail(_module._default.Next$_T0, $LS($LZ), s#0, i#0) } 
          true
             ==> 
            LitInt(0) <= i#0
               && i#0 < _module.__default.Next(_module._default.Next$_T0, s#0, P#0)
             ==> !$Unbox(Apply1(_module._default.Next$_T0, 
                TBool, 
                $Heap, 
                P#0, 
                _module.Stream.head(_module.__default.Tail(_module._default.Next$_T0, $LS($LZ), s#0, i#0)))): bool)
         && LitInt(0) <= _module.__default.Next(_module._default.Next$_T0, s#0, P#0));

function _module.__default.Next#requires(Ty, DatatypeType, HandleType) : bool;

// #requires axiom for _module.__default.Next
axiom (forall _module._default.Next$_T0: Ty, $Heap: Heap, s#0: DatatypeType, P#0: HandleType :: 
  { _module.__default.Next#requires(_module._default.Next$_T0, s#0, P#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && $Is(s#0, Tclass._module.Stream(_module._default.Next$_T0))
       && $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.Next$_T0, TBool))
     ==> _module.__default.Next#requires(_module._default.Next$_T0, s#0, P#0)
       == _module.__default.AlwaysAnother(_module._default.Next$_T0, $LS($LZ), s#0, P#0));

function $let#0_n(_module._default.Next$_T0: Ty, $heap: Heap, P: HandleType, s: DatatypeType)
   : int;

function $let#0$canCall(_module._default.Next$_T0: Ty, $heap: Heap, P: HandleType, s: DatatypeType)
   : bool;

axiom (forall _module._default.Next$_T0: Ty, $heap: Heap, P: HandleType, s: DatatypeType :: 
  { $let#0_n(_module._default.Next$_T0, $heap, P, s) } 
  $let#0$canCall(_module._default.Next$_T0, $heap, P, s)
     ==> LitInt(0) <= $let#0_n(_module._default.Next$_T0, $heap, P, s)
       && 
      LitInt(0) <= $let#0_n(_module._default.Next$_T0, $heap, P, s)
       && $Unbox(Apply1(_module._default.Next$_T0, 
          TBool, 
          $heap, 
          P, 
          _module.Stream.head(_module.__default.Tail(_module._default.Next$_T0, 
              $LS($LZ), 
              s, 
              $let#0_n(_module._default.Next$_T0, $heap, P, s))))): bool);

// definition axiom for _module.__default.Next (revealed)
axiom 19 <= $FunctionContextHeight
   ==> (forall _module._default.Next$_T0: Ty, $Heap: Heap, s#0: DatatypeType, P#0: HandleType :: 
    { _module.__default.Next(_module._default.Next$_T0, s#0, P#0), $IsGoodHeap($Heap) } 
    _module.__default.Next#canCall(_module._default.Next$_T0, s#0, P#0)
         || (19 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(s#0, Tclass._module.Stream(_module._default.Next$_T0))
           && $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.Next$_T0, TBool))
           && _module.__default.AlwaysAnother(_module._default.Next$_T0, $LS($LZ), s#0, P#0))
       ==> $let#0$canCall(_module._default.Next$_T0, $Heap, P#0, s#0)
         && _module.__default.NextMinimizer#canCall(_module._default.Next$_T0, 
          s#0, 
          P#0, 
          $let#0_n(_module._default.Next$_T0, $Heap, P#0, s#0))
         && _module.__default.Next(_module._default.Next$_T0, s#0, P#0)
           == (var n#0 := $let#0_n(_module._default.Next$_T0, $Heap, P#0, s#0); 
            _module.__default.NextMinimizer(_module._default.Next$_T0, $LS($LZ), s#0, P#0, n#0)));

// definition axiom for _module.__default.Next for all literals (revealed)
axiom 19 <= $FunctionContextHeight
   ==> (forall _module._default.Next$_T0: Ty, $Heap: Heap, s#0: DatatypeType, P#0: HandleType :: 
    {:weight 3} { _module.__default.Next(_module._default.Next$_T0, Lit(s#0), Lit(P#0)), $IsGoodHeap($Heap) } 
    _module.__default.Next#canCall(_module._default.Next$_T0, Lit(s#0), Lit(P#0))
         || (19 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(s#0, Tclass._module.Stream(_module._default.Next$_T0))
           && $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.Next$_T0, TBool))
           && Lit(_module.__default.AlwaysAnother(_module._default.Next$_T0, $LS($LZ), Lit(s#0), Lit(P#0))))
       ==> $let#0$canCall(_module._default.Next$_T0, $Heap, Lit(P#0), Lit(s#0))
         && _module.__default.NextMinimizer#canCall(_module._default.Next$_T0, 
          Lit(s#0), 
          Lit(P#0), 
          $let#0_n(_module._default.Next$_T0, $Heap, Lit(P#0), Lit(s#0)))
         && _module.__default.Next(_module._default.Next$_T0, Lit(s#0), Lit(P#0))
           == (var n#1 := $let#0_n(_module._default.Next$_T0, $Heap, Lit(P#0), Lit(s#0)); 
            _module.__default.NextMinimizer(_module._default.Next$_T0, $LS($LZ), Lit(s#0), Lit(P#0), n#1)));

procedure CheckWellformed$$_module.__default.Next(_module._default.Next$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Next$_T0)), 
    P#0: HandleType
       where $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.Next$_T0, TBool)));
  free requires 19 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures $Unbox(Apply1(_module._default.Next$_T0, 
      TBool, 
      $Heap, 
      P#0, 
      _module.Stream.head(_module.__default.Tail(_module._default.Next$_T0, 
          $LS($LS($LZ)), 
          s#0, 
          _module.__default.Next(_module._default.Next$_T0, s#0, P#0))))): bool;
  ensures (forall i#1: int :: 
    { _module.__default.Tail(_module._default.Next$_T0, $LS($LS($LZ)), s#0, i#1) } 
    true
       ==> 
      LitInt(0) <= i#1
         && i#1 < _module.__default.Next(_module._default.Next$_T0, s#0, P#0)
       ==> !$Unbox(Apply1(_module._default.Next$_T0, 
          TBool, 
          $Heap, 
          P#0, 
          _module.Stream.head(_module.__default.Tail(_module._default.Next$_T0, $LS($LS($LZ)), s#0, i#1)))): bool);



implementation CheckWellformed$$_module.__default.Next(_module._default.Next$_T0: Ty, s#0: DatatypeType, P#0: HandleType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##s#0: DatatypeType;
  var ##P#0: HandleType;
  var b$reqreads#0: bool;
  var ##s#1: DatatypeType;
  var ##P#1: HandleType;
  var ##s#2: DatatypeType;
  var ##n#0: int;
  var i#2: int;
  var ##s#3: DatatypeType;
  var ##P#2: HandleType;
  var ##s#4: DatatypeType;
  var ##n#1: int;
  var n#4: int;
  var ##s#5: DatatypeType;
  var ##n#2: int;
  var ##s#6: DatatypeType;
  var ##P#3: HandleType;
  var ##n#3: int;
  var b$reqreads#1: bool;
  var b$reqreads#2: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;

    // AddWellformednessCheck for function Next
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(92,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    ##s#0 := s#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#0, Tclass._module.Stream(_module._default.Next$_T0), $Heap);
    ##P#0 := P#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##P#0, Tclass._System.___hTotalFunc1(_module._default.Next$_T0, TBool), $Heap);
    b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    assume _module.__default.AlwaysAnother#canCall(_module._default.Next$_T0, s#0, P#0);
    assume _module.__default.AlwaysAnother(_module._default.Next$_T0, $LS($LZ), s#0, P#0);
    assert b$reqreads#0;
    if (*)
    {
        assume LitInt(0) <= _module.__default.Next(_module._default.Next$_T0, s#0, P#0);
        ##s#1 := s#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#1, Tclass._module.Stream(_module._default.Next$_T0), $Heap);
        ##P#1 := P#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##P#1, Tclass._System.___hTotalFunc1(_module._default.Next$_T0, TBool), $Heap);
        assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.Next$_T0, ##s#1, ##P#1)
           ==> _module.__default.AlwaysAnother(_module._default.Next$_T0, $LS($LZ), ##s#1, ##P#1)
             || (_module.__default.IsAnother#canCall(_module._default.Next$_T0, ##s#1, ##P#1)
               ==> _module.__default.IsAnother(_module._default.Next$_T0, ##s#1, ##P#1)
                 || (exists n#2: int :: 
                  { _module.__default.Tail(_module._default.Next$_T0, $LS($LZ), ##s#1, n#2) } 
                  LitInt(0) <= n#2
                     && 
                    LitInt(0) <= n#2
                     && $Unbox(Apply1(_module._default.Next$_T0, 
                        TBool, 
                        $Heap, 
                        ##P#1, 
                        _module.Stream.head(_module.__default.Tail(_module._default.Next$_T0, $LS($LZ), ##s#1, n#2)))): bool));
        assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.Next$_T0, ##s#1, ##P#1)
           ==> _module.__default.AlwaysAnother(_module._default.Next$_T0, $LS($LZ), ##s#1, ##P#1)
             || _module.__default.AlwaysAnother(_module._default.Next$_T0, $LS($LS($LZ)), _module.Stream.tail(##s#1), ##P#1);
        assume _module.__default.AlwaysAnother(_module._default.Next$_T0, $LS($LZ), ##s#1, ##P#1);
        assert s#0 == s#0 && P#0 == P#0;
        assume (s#0 == s#0 && P#0 == P#0)
           || _module.__default.Next#canCall(_module._default.Next$_T0, s#0, P#0);
        ##s#2 := s#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#2, Tclass._module.Stream(_module._default.Next$_T0), $Heap);
        ##n#0 := _module.__default.Next(_module._default.Next$_T0, s#0, P#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
        assume _module.__default.Tail#canCall(_module._default.Next$_T0, 
          s#0, 
          _module.__default.Next(_module._default.Next$_T0, s#0, P#0));
        assume _module.Stream.Cons_q(_module.__default.Tail(_module._default.Next$_T0, 
            $LS($LZ), 
            s#0, 
            _module.__default.Next(_module._default.Next$_T0, s#0, P#0)));
        assume _module.Stream.Cons_q(_module.__default.Tail(_module._default.Next$_T0, 
            $LS($LZ), 
            s#0, 
            _module.__default.Next(_module._default.Next$_T0, s#0, P#0)));
        assume $Unbox(Apply1(_module._default.Next$_T0, 
            TBool, 
            $Heap, 
            P#0, 
            _module.Stream.head(_module.__default.Tail(_module._default.Next$_T0, 
                $LS($LZ), 
                s#0, 
                _module.__default.Next(_module._default.Next$_T0, s#0, P#0))))): bool;
        havoc i#2;
        assume true;
        if (*)
        {
            assume LitInt(0) <= i#2;
            ##s#3 := s#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#3, Tclass._module.Stream(_module._default.Next$_T0), $Heap);
            ##P#2 := P#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##P#2, Tclass._System.___hTotalFunc1(_module._default.Next$_T0, TBool), $Heap);
            assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.Next$_T0, ##s#3, ##P#2)
               ==> _module.__default.AlwaysAnother(_module._default.Next$_T0, $LS($LZ), ##s#3, ##P#2)
                 || (_module.__default.IsAnother#canCall(_module._default.Next$_T0, ##s#3, ##P#2)
                   ==> _module.__default.IsAnother(_module._default.Next$_T0, ##s#3, ##P#2)
                     || (exists n#3: int :: 
                      { _module.__default.Tail(_module._default.Next$_T0, $LS($LZ), ##s#3, n#3) } 
                      LitInt(0) <= n#3
                         && 
                        LitInt(0) <= n#3
                         && $Unbox(Apply1(_module._default.Next$_T0, 
                            TBool, 
                            $Heap, 
                            ##P#2, 
                            _module.Stream.head(_module.__default.Tail(_module._default.Next$_T0, $LS($LZ), ##s#3, n#3)))): bool));
            assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.Next$_T0, ##s#3, ##P#2)
               ==> _module.__default.AlwaysAnother(_module._default.Next$_T0, $LS($LZ), ##s#3, ##P#2)
                 || _module.__default.AlwaysAnother(_module._default.Next$_T0, $LS($LS($LZ)), _module.Stream.tail(##s#3), ##P#2);
            assume _module.__default.AlwaysAnother(_module._default.Next$_T0, $LS($LZ), ##s#3, ##P#2);
            assert s#0 == s#0 && P#0 == P#0;
            assume (s#0 == s#0 && P#0 == P#0)
               || _module.__default.Next#canCall(_module._default.Next$_T0, s#0, P#0);
            assume i#2 < _module.__default.Next(_module._default.Next$_T0, s#0, P#0);
            ##s#4 := s#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#4, Tclass._module.Stream(_module._default.Next$_T0), $Heap);
            assert $Is(i#2, Tclass._System.nat());
            ##n#1 := i#2;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#1, Tclass._System.nat(), $Heap);
            assume _module.__default.Tail#canCall(_module._default.Next$_T0, s#0, i#2);
            assume _module.Stream.Cons_q(_module.__default.Tail(_module._default.Next$_T0, $LS($LZ), s#0, i#2));
            assume _module.Stream.Cons_q(_module.__default.Tail(_module._default.Next$_T0, $LS($LZ), s#0, i#2));
            assume !$Unbox(Apply1(_module._default.Next$_T0, 
                TBool, 
                $Heap, 
                P#0, 
                _module.Stream.head(_module.__default.Tail(_module._default.Next$_T0, $LS($LZ), s#0, i#2)))): bool;
        }
        else
        {
            assume LitInt(0) <= i#2
                 && i#2 < _module.__default.Next(_module._default.Next$_T0, s#0, P#0)
               ==> !$Unbox(Apply1(_module._default.Next$_T0, 
                  TBool, 
                  $Heap, 
                  P#0, 
                  _module.Stream.head(_module.__default.Tail(_module._default.Next$_T0, $LS($LZ), s#0, i#2)))): bool;
        }

        assume (forall i#1: int :: 
          { _module.__default.Tail(_module._default.Next$_T0, $LS($LZ), s#0, i#1) } 
          true
             ==> 
            LitInt(0) <= i#1
               && i#1 < _module.__default.Next(_module._default.Next$_T0, s#0, P#0)
             ==> !$Unbox(Apply1(_module._default.Next$_T0, 
                TBool, 
                $Heap, 
                P#0, 
                _module.Stream.head(_module.__default.Tail(_module._default.Next$_T0, $LS($LZ), s#0, i#1)))): bool);
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        havoc n#4;
        if (LitInt(0) <= n#4)
        {
            if (LitInt(0) <= n#4)
            {
                ##s#5 := s#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#5, Tclass._module.Stream(_module._default.Next$_T0), $Heap);
                ##n#2 := n#4;
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#2, Tclass._System.nat(), $Heap);
                b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assume _module.__default.Tail#canCall(_module._default.Next$_T0, s#0, n#4);
                assume _module.Stream.Cons_q(_module.__default.Tail(_module._default.Next$_T0, $LS($LZ), s#0, n#4));
                assume _module.Stream.Cons_q(_module.__default.Tail(_module._default.Next$_T0, $LS($LZ), s#0, n#4));
            }
        }

        assert ($Is(LitInt(0), Tclass._System.nat())
             && 
            LitInt(0) <= LitInt(0)
             && $Unbox(Apply1(_module._default.Next$_T0, 
                TBool, 
                $Heap, 
                P#0, 
                _module.Stream.head(_module.__default.Tail(_module._default.Next$_T0, $LS($LZ), s#0, LitInt(0))))): bool)
           || 
          ($Is(LitInt(0), Tclass._System.nat())
             && 
            LitInt(0) <= LitInt(0)
             && $Unbox(Apply1(_module._default.Next$_T0, 
                TBool, 
                $Heap, 
                P#0, 
                _module.Stream.head(_module.__default.Tail(_module._default.Next$_T0, $LS($LZ), s#0, LitInt(0))))): bool)
           || 
          ($Is(LitInt(0), Tclass._System.nat())
             && 
            LitInt(0) <= LitInt(0)
             && $Unbox(Apply1(_module._default.Next$_T0, 
                TBool, 
                $Heap, 
                P#0, 
                _module.Stream.head(_module.__default.Tail(_module._default.Next$_T0, $LS($LZ), s#0, LitInt(0))))): bool)
           || (exists n#5: int :: 
            LitInt(0) <= n#5
               && 
              LitInt(0) <= n#5
               && $Unbox(Apply1(_module._default.Next$_T0, 
                  TBool, 
                  $Heap, 
                  P#0, 
                  _module.Stream.head(_module.__default.Tail(_module._default.Next$_T0, $LS($LZ), s#0, n#5)))): bool);
        assume LitInt(0) <= n#4;
        assume LitInt(0) <= n#4
           && $Unbox(Apply1(_module._default.Next$_T0, 
              TBool, 
              $Heap, 
              P#0, 
              _module.Stream.head(_module.__default.Tail(_module._default.Next$_T0, $LS($LZ), s#0, n#4)))): bool;
        ##s#6 := s#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#6, Tclass._module.Stream(_module._default.Next$_T0), $Heap);
        ##P#3 := P#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##P#3, Tclass._System.___hTotalFunc1(_module._default.Next$_T0, TBool), $Heap);
        ##n#3 := n#4;
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#3, Tclass._System.nat(), $Heap);
        assert {:subsumption 0} $Unbox(Apply1(_module._default.Next$_T0, 
            TBool, 
            $Heap, 
            ##P#3, 
            _module.Stream.head(_module.__default.Tail(_module._default.Next$_T0, $LS($LS($LZ)), ##s#6, ##n#3)))): bool;
        assume $Unbox(Apply1(_module._default.Next$_T0, 
            TBool, 
            $Heap, 
            ##P#3, 
            _module.Stream.head(_module.__default.Tail(_module._default.Next$_T0, $LS($LZ), ##s#6, ##n#3)))): bool;
        b$reqreads#2 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.NextMinimizer#canCall(_module._default.Next$_T0, s#0, P#0, n#4);
        assume $let#0$canCall(_module._default.Next$_T0, $Heap, P#0, s#0);
        assume _module.__default.Next(_module._default.Next$_T0, s#0, P#0)
           == _module.__default.NextMinimizer(_module._default.Next$_T0, $LS($LZ), s#0, P#0, n#4);
        assume _module.__default.NextMinimizer#canCall(_module._default.Next$_T0, s#0, P#0, n#4);
        // CheckWellformedWithResult: Let expression
        assume $Is(_module.__default.Next(_module._default.Next$_T0, s#0, P#0), 
          Tclass._System.nat());
        assert b$reqreads#1;
        assert b$reqreads#2;
    }
}



// function declaration for _module._default.NextMinimizer
function _module.__default.NextMinimizer(_module._default.NextMinimizer$_T0: Ty, 
    $ly: LayerType, 
    s#0: DatatypeType, 
    P#0: HandleType, 
    n#0: int)
   : int;

function _module.__default.NextMinimizer#canCall(_module._default.NextMinimizer$_T0: Ty, 
    s#0: DatatypeType, 
    P#0: HandleType, 
    n#0: int)
   : bool;

// layer synonym axiom
axiom (forall _module._default.NextMinimizer$_T0: Ty, 
    $ly: LayerType, 
    s#0: DatatypeType, 
    P#0: HandleType, 
    n#0: int :: 
  { _module.__default.NextMinimizer(_module._default.NextMinimizer$_T0, $LS($ly), s#0, P#0, n#0) } 
  _module.__default.NextMinimizer(_module._default.NextMinimizer$_T0, $LS($ly), s#0, P#0, n#0)
     == _module.__default.NextMinimizer(_module._default.NextMinimizer$_T0, $ly, s#0, P#0, n#0));

// fuel synonym axiom
axiom (forall _module._default.NextMinimizer$_T0: Ty, 
    $ly: LayerType, 
    s#0: DatatypeType, 
    P#0: HandleType, 
    n#0: int :: 
  { _module.__default.NextMinimizer(_module._default.NextMinimizer$_T0, AsFuelBottom($ly), s#0, P#0, n#0) } 
  _module.__default.NextMinimizer(_module._default.NextMinimizer$_T0, $ly, s#0, P#0, n#0)
     == _module.__default.NextMinimizer(_module._default.NextMinimizer$_T0, $LZ, s#0, P#0, n#0));

// consequence axiom for _module.__default.NextMinimizer
axiom 18 <= $FunctionContextHeight
   ==> (forall _module._default.NextMinimizer$_T0: Ty, 
      $ly: LayerType, 
      $Heap: Heap, 
      s#0: DatatypeType, 
      P#0: HandleType, 
      n#0: int :: 
    { _module.__default.NextMinimizer(_module._default.NextMinimizer$_T0, $ly, s#0, P#0, n#0), $IsGoodHeap($Heap) } 
    _module.__default.NextMinimizer#canCall(_module._default.NextMinimizer$_T0, s#0, P#0, n#0)
         || (18 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(s#0, Tclass._module.Stream(_module._default.NextMinimizer$_T0))
           && $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.NextMinimizer$_T0, TBool))
           && LitInt(0) <= n#0
           && $Unbox(Apply1(_module._default.NextMinimizer$_T0, 
              TBool, 
              $Heap, 
              P#0, 
              _module.Stream.head(_module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, n#0)))): bool)
       ==> $Unbox(Apply1(_module._default.NextMinimizer$_T0, 
            TBool, 
            $Heap, 
            P#0, 
            _module.Stream.head(_module.__default.Tail(_module._default.NextMinimizer$_T0, 
                $LS($LZ), 
                s#0, 
                _module.__default.NextMinimizer(_module._default.NextMinimizer$_T0, $ly, s#0, P#0, n#0))))): bool
         && (forall i#0: int :: 
          { _module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, i#0) } 
          true
             ==> 
            LitInt(0) <= i#0
               && i#0
                 < _module.__default.NextMinimizer(_module._default.NextMinimizer$_T0, $ly, s#0, P#0, n#0)
             ==> !$Unbox(Apply1(_module._default.NextMinimizer$_T0, 
                TBool, 
                $Heap, 
                P#0, 
                _module.Stream.head(_module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, i#0)))): bool)
         && LitInt(0)
           <= _module.__default.NextMinimizer(_module._default.NextMinimizer$_T0, $ly, s#0, P#0, n#0));

function _module.__default.NextMinimizer#requires(Ty, LayerType, DatatypeType, HandleType, int) : bool;

// #requires axiom for _module.__default.NextMinimizer
axiom (forall _module._default.NextMinimizer$_T0: Ty, 
    $ly: LayerType, 
    $Heap: Heap, 
    s#0: DatatypeType, 
    P#0: HandleType, 
    n#0: int :: 
  { _module.__default.NextMinimizer#requires(_module._default.NextMinimizer$_T0, $ly, s#0, P#0, n#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && $Is(s#0, Tclass._module.Stream(_module._default.NextMinimizer$_T0))
       && $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.NextMinimizer$_T0, TBool))
       && LitInt(0) <= n#0
     ==> _module.__default.NextMinimizer#requires(_module._default.NextMinimizer$_T0, $ly, s#0, P#0, n#0)
       == $Unbox(Apply1(_module._default.NextMinimizer$_T0, 
          TBool, 
          $Heap, 
          P#0, 
          _module.Stream.head(_module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, n#0)))): bool);

function $let#3_k(_module._default.NextMinimizer$_T0: Ty, 
    $heap: Heap, 
    n: int, 
    P: HandleType, 
    s: DatatypeType)
   : int;

function $let#3$canCall(_module._default.NextMinimizer$_T0: Ty, 
    $heap: Heap, 
    n: int, 
    P: HandleType, 
    s: DatatypeType)
   : bool;

axiom (forall _module._default.NextMinimizer$_T0: Ty, 
    $heap: Heap, 
    n: int, 
    P: HandleType, 
    s: DatatypeType :: 
  { $let#3_k(_module._default.NextMinimizer$_T0, $heap, n, P, s) } 
  $let#3$canCall(_module._default.NextMinimizer$_T0, $heap, n, P, s)
     ==> LitInt(0) <= $let#3_k(_module._default.NextMinimizer$_T0, $heap, n, P, s)
       && $let#3_k(_module._default.NextMinimizer$_T0, $heap, n, P, s) < n
       && $Unbox(Apply1(_module._default.NextMinimizer$_T0, 
          TBool, 
          $heap, 
          P, 
          _module.Stream.head(_module.__default.Tail(_module._default.NextMinimizer$_T0, 
              $LS($LZ), 
              s, 
              $let#3_k(_module._default.NextMinimizer$_T0, $heap, n, P, s))))): bool);

// definition axiom for _module.__default.NextMinimizer (revealed)
axiom 18 <= $FunctionContextHeight
   ==> (forall _module._default.NextMinimizer$_T0: Ty, 
      $ly: LayerType, 
      $Heap: Heap, 
      s#0: DatatypeType, 
      P#0: HandleType, 
      n#0: int :: 
    { _module.__default.NextMinimizer(_module._default.NextMinimizer$_T0, $LS($ly), s#0, P#0, n#0), $IsGoodHeap($Heap) } 
    _module.__default.NextMinimizer#canCall(_module._default.NextMinimizer$_T0, s#0, P#0, n#0)
         || (18 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(s#0, Tclass._module.Stream(_module._default.NextMinimizer$_T0))
           && $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.NextMinimizer$_T0, TBool))
           && LitInt(0) <= n#0
           && $Unbox(Apply1(_module._default.NextMinimizer$_T0, 
              TBool, 
              $Heap, 
              P#0, 
              _module.Stream.head(_module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, n#0)))): bool)
       ==> (forall i#1: int :: 
          { _module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, i#1) } 
          LitInt(0) <= i#1
             ==> 
            i#1 < n#0
             ==> _module.__default.Tail#canCall(_module._default.NextMinimizer$_T0, s#0, i#1)
               && _module.Stream.Cons_q(_module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, i#1)))
         && (!(forall i#1: int :: 
            { _module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, i#1) } 
            true
               ==> 
              LitInt(0) <= i#1 && i#1 < n#0
               ==> !$Unbox(Apply1(_module._default.NextMinimizer$_T0, 
                  TBool, 
                  $Heap, 
                  P#0, 
                  _module.Stream.head(_module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, i#1)))): bool)
           ==> $let#3$canCall(_module._default.NextMinimizer$_T0, $Heap, n#0, P#0, s#0)
             && _module.__default.NextMinimizer#canCall(_module._default.NextMinimizer$_T0, 
              s#0, 
              P#0, 
              $let#3_k(_module._default.NextMinimizer$_T0, $Heap, n#0, P#0, s#0)))
         && _module.__default.NextMinimizer(_module._default.NextMinimizer$_T0, $LS($ly), s#0, P#0, n#0)
           == (if (forall i#1: int :: 
              { _module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, i#1) } 
              true
                 ==> 
                LitInt(0) <= i#1 && i#1 < n#0
                 ==> !$Unbox(Apply1(_module._default.NextMinimizer$_T0, 
                    TBool, 
                    $Heap, 
                    P#0, 
                    _module.Stream.head(_module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, i#1)))): bool)
             then n#0
             else (var k#0 := $let#3_k(_module._default.NextMinimizer$_T0, $Heap, n#0, P#0, s#0); 
              _module.__default.NextMinimizer(_module._default.NextMinimizer$_T0, $ly, s#0, P#0, k#0))));

// definition axiom for _module.__default.NextMinimizer for decreasing-related literals (revealed)
axiom 18 <= $FunctionContextHeight
   ==> (forall _module._default.NextMinimizer$_T0: Ty, 
      $ly: LayerType, 
      $Heap: Heap, 
      s#0: DatatypeType, 
      P#0: HandleType, 
      n#0: int :: 
    {:weight 3} { _module.__default.NextMinimizer(_module._default.NextMinimizer$_T0, $LS($ly), s#0, P#0, LitInt(n#0)), $IsGoodHeap($Heap) } 
    _module.__default.NextMinimizer#canCall(_module._default.NextMinimizer$_T0, s#0, P#0, LitInt(n#0))
         || (18 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(s#0, Tclass._module.Stream(_module._default.NextMinimizer$_T0))
           && $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.NextMinimizer$_T0, TBool))
           && LitInt(0) <= n#0
           && $Unbox(Apply1(_module._default.NextMinimizer$_T0, 
              TBool, 
              $Heap, 
              P#0, 
              _module.Stream.head(_module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, LitInt(n#0))))): bool)
       ==> (forall i#2: int :: 
          { _module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, i#2) } 
          LitInt(0) <= i#2
             ==> 
            i#2 < n#0
             ==> _module.__default.Tail#canCall(_module._default.NextMinimizer$_T0, s#0, i#2)
               && _module.Stream.Cons_q(_module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, i#2)))
         && (!(forall i#2: int :: 
            { _module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, i#2) } 
            true
               ==> 
              LitInt(0) <= i#2 && i#2 < n#0
               ==> !$Unbox(Apply1(_module._default.NextMinimizer$_T0, 
                  TBool, 
                  $Heap, 
                  P#0, 
                  _module.Stream.head(_module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, i#2)))): bool)
           ==> $let#3$canCall(_module._default.NextMinimizer$_T0, $Heap, LitInt(n#0), P#0, s#0)
             && _module.__default.NextMinimizer#canCall(_module._default.NextMinimizer$_T0, 
              s#0, 
              P#0, 
              $let#3_k(_module._default.NextMinimizer$_T0, $Heap, LitInt(n#0), P#0, s#0)))
         && _module.__default.NextMinimizer(_module._default.NextMinimizer$_T0, $LS($ly), s#0, P#0, LitInt(n#0))
           == (if (forall i#2: int :: 
              { _module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, i#2) } 
              true
                 ==> 
                LitInt(0) <= i#2 && i#2 < n#0
                 ==> !$Unbox(Apply1(_module._default.NextMinimizer$_T0, 
                    TBool, 
                    $Heap, 
                    P#0, 
                    _module.Stream.head(_module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, i#2)))): bool)
             then n#0
             else (var k#1 := $let#3_k(_module._default.NextMinimizer$_T0, $Heap, LitInt(n#0), P#0, s#0); 
              _module.__default.NextMinimizer(_module._default.NextMinimizer$_T0, $LS($ly), s#0, P#0, k#1))));

// definition axiom for _module.__default.NextMinimizer for all literals (revealed)
axiom 18 <= $FunctionContextHeight
   ==> (forall _module._default.NextMinimizer$_T0: Ty, 
      $ly: LayerType, 
      $Heap: Heap, 
      s#0: DatatypeType, 
      P#0: HandleType, 
      n#0: int :: 
    {:weight 3} { _module.__default.NextMinimizer(_module._default.NextMinimizer$_T0, $LS($ly), Lit(s#0), Lit(P#0), LitInt(n#0)), $IsGoodHeap($Heap) } 
    _module.__default.NextMinimizer#canCall(_module._default.NextMinimizer$_T0, Lit(s#0), Lit(P#0), LitInt(n#0))
         || (18 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(s#0, Tclass._module.Stream(_module._default.NextMinimizer$_T0))
           && $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.NextMinimizer$_T0, TBool))
           && LitInt(0) <= n#0
           && $Unbox(Apply1(_module._default.NextMinimizer$_T0, 
              TBool, 
              $Heap, 
              Lit(P#0), 
              Lit(_module.Stream.head(Lit(_module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LZ), Lit(s#0), LitInt(n#0))))))): bool)
       ==> (forall i#3: int :: 
          { _module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, i#3) } 
          LitInt(0) <= i#3
             ==> 
            i#3 < n#0
             ==> _module.__default.Tail#canCall(_module._default.NextMinimizer$_T0, Lit(s#0), i#3)
               && _module.Stream.Cons_q(_module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LZ), Lit(s#0), i#3)))
         && (!(forall i#3: int :: 
            { _module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, i#3) } 
            true
               ==> 
              LitInt(0) <= i#3 && i#3 < n#0
               ==> !$Unbox(Apply1(_module._default.NextMinimizer$_T0, 
                  TBool, 
                  $Heap, 
                  Lit(P#0), 
                  _module.Stream.head(_module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LZ), Lit(s#0), i#3)))): bool)
           ==> $let#3$canCall(_module._default.NextMinimizer$_T0, $Heap, LitInt(n#0), Lit(P#0), Lit(s#0))
             && _module.__default.NextMinimizer#canCall(_module._default.NextMinimizer$_T0, 
              Lit(s#0), 
              Lit(P#0), 
              $let#3_k(_module._default.NextMinimizer$_T0, $Heap, LitInt(n#0), Lit(P#0), Lit(s#0))))
         && _module.__default.NextMinimizer(_module._default.NextMinimizer$_T0, $LS($ly), Lit(s#0), Lit(P#0), LitInt(n#0))
           == (if (forall i#3: int :: 
              { _module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, i#3) } 
              true
                 ==> 
                LitInt(0) <= i#3 && i#3 < n#0
                 ==> !$Unbox(Apply1(_module._default.NextMinimizer$_T0, 
                    TBool, 
                    $Heap, 
                    Lit(P#0), 
                    _module.Stream.head(_module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LZ), Lit(s#0), i#3)))): bool)
             then n#0
             else (var k#2 := $let#3_k(_module._default.NextMinimizer$_T0, $Heap, LitInt(n#0), Lit(P#0), Lit(s#0)); 
              _module.__default.NextMinimizer(_module._default.NextMinimizer$_T0, $LS($ly), Lit(s#0), Lit(P#0), k#2))));

procedure CheckWellformed$$_module.__default.NextMinimizer(_module._default.NextMinimizer$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.NextMinimizer$_T0)), 
    P#0: HandleType
       where $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.NextMinimizer$_T0, TBool)), 
    n#0: int where LitInt(0) <= n#0);
  free requires 18 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures $Unbox(Apply1(_module._default.NextMinimizer$_T0, 
      TBool, 
      $Heap, 
      P#0, 
      _module.Stream.head(_module.__default.Tail(_module._default.NextMinimizer$_T0, 
          $LS($LS($LZ)), 
          s#0, 
          _module.__default.NextMinimizer(_module._default.NextMinimizer$_T0, $LS($LS($LZ)), s#0, P#0, n#0))))): bool;
  ensures (forall i#4: int :: 
    { _module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LS($LZ)), s#0, i#4) } 
    true
       ==> 
      LitInt(0) <= i#4
         && i#4
           < _module.__default.NextMinimizer(_module._default.NextMinimizer$_T0, $LS($LS($LZ)), s#0, P#0, n#0)
       ==> !$Unbox(Apply1(_module._default.NextMinimizer$_T0, 
          TBool, 
          $Heap, 
          P#0, 
          _module.Stream.head(_module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LS($LZ)), s#0, i#4)))): bool);



implementation CheckWellformed$$_module.__default.NextMinimizer(_module._default.NextMinimizer$_T0: Ty, 
    s#0: DatatypeType, 
    P#0: HandleType, 
    n#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##s#0: DatatypeType;
  var ##n#0: int;
  var b$reqreads#0: bool;
  var ##s#1: DatatypeType;
  var ##P#0: HandleType;
  var ##n#1: int;
  var ##s#2: DatatypeType;
  var ##n#2: int;
  var i#5: int;
  var ##s#3: DatatypeType;
  var ##P#1: HandleType;
  var ##n#3: int;
  var ##s#4: DatatypeType;
  var ##n#4: int;
  var i#6: int;
  var ##s#5: DatatypeType;
  var ##n#5: int;
  var k#3: int;
  var ##s#6: DatatypeType;
  var ##n#6: int;
  var ##s#7: DatatypeType;
  var ##P#2: HandleType;
  var ##n#7: int;
  var b$reqreads#1: bool;
  var b$reqreads#2: bool;
  var b$reqreads#3: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;
    b$reqreads#3 := true;

    // AddWellformednessCheck for function NextMinimizer
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(101,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    ##s#0 := s#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#0, Tclass._module.Stream(_module._default.NextMinimizer$_T0), $Heap);
    ##n#0 := n#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
    b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    assume _module.__default.Tail#canCall(_module._default.NextMinimizer$_T0, s#0, n#0);
    assume _module.Stream.Cons_q(_module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, n#0));
    assume _module.Stream.Cons_q(_module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, n#0));
    assume $Unbox(Apply1(_module._default.NextMinimizer$_T0, 
        TBool, 
        $Heap, 
        P#0, 
        _module.Stream.head(_module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, n#0)))): bool;
    assert b$reqreads#0;
    if (*)
    {
        assume LitInt(0)
           <= _module.__default.NextMinimizer(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, P#0, n#0);
        ##s#1 := s#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#1, Tclass._module.Stream(_module._default.NextMinimizer$_T0), $Heap);
        ##P#0 := P#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##P#0, 
          Tclass._System.___hTotalFunc1(_module._default.NextMinimizer$_T0, TBool), 
          $Heap);
        ##n#1 := n#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#1, Tclass._System.nat(), $Heap);
        assert {:subsumption 0} $Unbox(Apply1(_module._default.NextMinimizer$_T0, 
            TBool, 
            $Heap, 
            ##P#0, 
            _module.Stream.head(_module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LS($LZ)), ##s#1, ##n#1)))): bool;
        assume $Unbox(Apply1(_module._default.NextMinimizer$_T0, 
            TBool, 
            $Heap, 
            ##P#0, 
            _module.Stream.head(_module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LZ), ##s#1, ##n#1)))): bool;
        assert 0 <= n#0 || ##n#1 == n#0;
        assert (s#0 == s#0 && P#0 == P#0 && n#0 == n#0) || ##n#1 < n#0;
        assume (s#0 == s#0 && P#0 == P#0 && n#0 == n#0)
           || _module.__default.NextMinimizer#canCall(_module._default.NextMinimizer$_T0, s#0, P#0, n#0);
        ##s#2 := s#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#2, Tclass._module.Stream(_module._default.NextMinimizer$_T0), $Heap);
        ##n#2 := _module.__default.NextMinimizer(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, P#0, n#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#2, Tclass._System.nat(), $Heap);
        assume _module.__default.Tail#canCall(_module._default.NextMinimizer$_T0, 
          s#0, 
          _module.__default.NextMinimizer(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, P#0, n#0));
        assume _module.Stream.Cons_q(_module.__default.Tail(_module._default.NextMinimizer$_T0, 
            $LS($LZ), 
            s#0, 
            _module.__default.NextMinimizer(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, P#0, n#0)));
        assume _module.Stream.Cons_q(_module.__default.Tail(_module._default.NextMinimizer$_T0, 
            $LS($LZ), 
            s#0, 
            _module.__default.NextMinimizer(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, P#0, n#0)));
        assume $Unbox(Apply1(_module._default.NextMinimizer$_T0, 
            TBool, 
            $Heap, 
            P#0, 
            _module.Stream.head(_module.__default.Tail(_module._default.NextMinimizer$_T0, 
                $LS($LZ), 
                s#0, 
                _module.__default.NextMinimizer(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, P#0, n#0))))): bool;
        havoc i#5;
        assume true;
        if (*)
        {
            assume LitInt(0) <= i#5;
            ##s#3 := s#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#3, Tclass._module.Stream(_module._default.NextMinimizer$_T0), $Heap);
            ##P#1 := P#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##P#1, 
              Tclass._System.___hTotalFunc1(_module._default.NextMinimizer$_T0, TBool), 
              $Heap);
            ##n#3 := n#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#3, Tclass._System.nat(), $Heap);
            assert {:subsumption 0} $Unbox(Apply1(_module._default.NextMinimizer$_T0, 
                TBool, 
                $Heap, 
                ##P#1, 
                _module.Stream.head(_module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LS($LZ)), ##s#3, ##n#3)))): bool;
            assume $Unbox(Apply1(_module._default.NextMinimizer$_T0, 
                TBool, 
                $Heap, 
                ##P#1, 
                _module.Stream.head(_module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LZ), ##s#3, ##n#3)))): bool;
            assert 0 <= n#0 || ##n#3 == n#0;
            assert (s#0 == s#0 && P#0 == P#0 && n#0 == n#0) || ##n#3 < n#0;
            assume (s#0 == s#0 && P#0 == P#0 && n#0 == n#0)
               || _module.__default.NextMinimizer#canCall(_module._default.NextMinimizer$_T0, s#0, P#0, n#0);
            assume i#5
               < _module.__default.NextMinimizer(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, P#0, n#0);
            ##s#4 := s#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#4, Tclass._module.Stream(_module._default.NextMinimizer$_T0), $Heap);
            assert $Is(i#5, Tclass._System.nat());
            ##n#4 := i#5;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#4, Tclass._System.nat(), $Heap);
            assume _module.__default.Tail#canCall(_module._default.NextMinimizer$_T0, s#0, i#5);
            assume _module.Stream.Cons_q(_module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, i#5));
            assume _module.Stream.Cons_q(_module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, i#5));
            assume !$Unbox(Apply1(_module._default.NextMinimizer$_T0, 
                TBool, 
                $Heap, 
                P#0, 
                _module.Stream.head(_module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, i#5)))): bool;
        }
        else
        {
            assume LitInt(0) <= i#5
                 && i#5
                   < _module.__default.NextMinimizer(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, P#0, n#0)
               ==> !$Unbox(Apply1(_module._default.NextMinimizer$_T0, 
                  TBool, 
                  $Heap, 
                  P#0, 
                  _module.Stream.head(_module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, i#5)))): bool;
        }

        assume (forall i#4: int :: 
          { _module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, i#4) } 
          true
             ==> 
            LitInt(0) <= i#4
               && i#4
                 < _module.__default.NextMinimizer(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, P#0, n#0)
             ==> !$Unbox(Apply1(_module._default.NextMinimizer$_T0, 
                TBool, 
                $Heap, 
                P#0, 
                _module.Stream.head(_module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, i#4)))): bool);
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        // Begin Comprehension WF check
        havoc i#6;
        if (true)
        {
            if (LitInt(0) <= i#6)
            {
            }

            if (LitInt(0) <= i#6 && i#6 < n#0)
            {
                ##s#5 := s#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#5, Tclass._module.Stream(_module._default.NextMinimizer$_T0), $Heap);
                assert $Is(i#6, Tclass._System.nat());
                ##n#5 := i#6;
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#5, Tclass._System.nat(), $Heap);
                b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assume _module.__default.Tail#canCall(_module._default.NextMinimizer$_T0, s#0, i#6);
                assume _module.Stream.Cons_q(_module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, i#6));
                assume _module.Stream.Cons_q(_module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, i#6));
            }
        }

        // End Comprehension WF check
        if ((forall i#7: int :: 
          { _module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, i#7) } 
          true
             ==> 
            LitInt(0) <= i#7 && i#7 < n#0
             ==> !$Unbox(Apply1(_module._default.NextMinimizer$_T0, 
                TBool, 
                $Heap, 
                P#0, 
                _module.Stream.head(_module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, i#7)))): bool))
        {
            assume _module.__default.NextMinimizer(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, P#0, n#0)
               == n#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.NextMinimizer(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, P#0, n#0), 
              Tclass._System.nat());
        }
        else
        {
            havoc k#3;
            if (true)
            {
                if (LitInt(0) <= k#3)
                {
                }

                if (LitInt(0) <= k#3 && k#3 < n#0)
                {
                    ##s#6 := s#0;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s#6, Tclass._module.Stream(_module._default.NextMinimizer$_T0), $Heap);
                    assert $Is(k#3, Tclass._System.nat());
                    ##n#6 := k#3;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##n#6, Tclass._System.nat(), $Heap);
                    b$reqreads#2 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                    assume _module.__default.Tail#canCall(_module._default.NextMinimizer$_T0, s#0, k#3);
                    assume _module.Stream.Cons_q(_module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, k#3));
                    assume _module.Stream.Cons_q(_module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, k#3));
                }
            }

            assert ($Is(n#0 - 1, TInt)
                 && 
                LitInt(0) <= n#0 - 1
                 && n#0 - 1 < n#0
                 && $Unbox(Apply1(_module._default.NextMinimizer$_T0, 
                    TBool, 
                    $Heap, 
                    P#0, 
                    _module.Stream.head(_module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, n#0 - 1)))): bool)
               || 
              ($Is(LitInt(0), TInt)
                 && 
                LitInt(0) <= LitInt(0)
                 && 0 < n#0
                 && $Unbox(Apply1(_module._default.NextMinimizer$_T0, 
                    TBool, 
                    $Heap, 
                    P#0, 
                    _module.Stream.head(_module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, LitInt(0))))): bool)
               || 
              ($Is(LitInt(0), TInt)
                 && 
                LitInt(0) <= LitInt(0)
                 && 0 < n#0
                 && $Unbox(Apply1(_module._default.NextMinimizer$_T0, 
                    TBool, 
                    $Heap, 
                    P#0, 
                    _module.Stream.head(_module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, LitInt(0))))): bool)
               || (exists k#4: int :: 
                LitInt(0) <= k#4
                   && k#4 < n#0
                   && $Unbox(Apply1(_module._default.NextMinimizer$_T0, 
                      TBool, 
                      $Heap, 
                      P#0, 
                      _module.Stream.head(_module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, k#4)))): bool);
            assume true;
            assume LitInt(0) <= k#3
               && k#3 < n#0
               && $Unbox(Apply1(_module._default.NextMinimizer$_T0, 
                  TBool, 
                  $Heap, 
                  P#0, 
                  _module.Stream.head(_module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, k#3)))): bool;
            ##s#7 := s#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#7, Tclass._module.Stream(_module._default.NextMinimizer$_T0), $Heap);
            ##P#2 := P#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##P#2, 
              Tclass._System.___hTotalFunc1(_module._default.NextMinimizer$_T0, TBool), 
              $Heap);
            assert $Is(k#3, Tclass._System.nat());
            ##n#7 := k#3;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#7, Tclass._System.nat(), $Heap);
            assert {:subsumption 0} $Unbox(Apply1(_module._default.NextMinimizer$_T0, 
                TBool, 
                $Heap, 
                ##P#2, 
                _module.Stream.head(_module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LS($LZ)), ##s#7, ##n#7)))): bool;
            assume $Unbox(Apply1(_module._default.NextMinimizer$_T0, 
                TBool, 
                $Heap, 
                ##P#2, 
                _module.Stream.head(_module.__default.Tail(_module._default.NextMinimizer$_T0, $LS($LZ), ##s#7, ##n#7)))): bool;
            b$reqreads#3 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0 <= n#0 || ##n#7 == n#0;
            assert ##n#7 < n#0;
            assume _module.__default.NextMinimizer#canCall(_module._default.NextMinimizer$_T0, s#0, P#0, k#3);
            assume $let#3$canCall(_module._default.NextMinimizer$_T0, $Heap, n#0, P#0, s#0);
            assume _module.__default.NextMinimizer(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, P#0, n#0)
               == _module.__default.NextMinimizer(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, P#0, k#3);
            assume _module.__default.NextMinimizer#canCall(_module._default.NextMinimizer$_T0, s#0, P#0, k#3);
            // CheckWellformedWithResult: Let expression
            assume $Is(_module.__default.NextMinimizer(_module._default.NextMinimizer$_T0, $LS($LZ), s#0, P#0, n#0), 
              Tclass._System.nat());
        }

        assert b$reqreads#1;
        assert b$reqreads#2;
        assert b$reqreads#3;
    }
}



procedure {:_induction s#0, P#0} CheckWellformed$$_module.__default.NextLemma(_module._default.NextLemma$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.NextLemma$_T0))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.NextLemma$_T0), $Heap)
         && $IsA#_module.Stream(s#0), 
    P#0: HandleType
       where $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.NextLemma$_T0, TBool))
         && $IsAlloc(P#0, Tclass._System.___hTotalFunc1(_module._default.NextLemma$_T0, TBool), $Heap));
  free requires 20 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:_induction s#0, P#0} CheckWellformed$$_module.__default.NextLemma(_module._default.NextLemma$_T0: Ty, s#0: DatatypeType, P#0: HandleType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##s#0: DatatypeType;
  var ##P#0: HandleType;
  var ##s#1: DatatypeType;
  var ##P#1: HandleType;
  var ##s#2: DatatypeType;
  var ##P#2: HandleType;

    // AddMethodImpl: NextLemma, CheckWellformed$$_module.__default.NextLemma
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(113,6): initial state"} true;
    ##s#0 := s#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#0, Tclass._module.Stream(_module._default.NextLemma$_T0), $Heap);
    ##P#0 := P#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##P#0, 
      Tclass._System.___hTotalFunc1(_module._default.NextLemma$_T0, TBool), 
      $Heap);
    assume _module.__default.AlwaysAnother#canCall(_module._default.NextLemma$_T0, s#0, P#0);
    assume _module.__default.AlwaysAnother(_module._default.NextLemma$_T0, $LS($LZ), s#0, P#0);
    assume _module.Stream.Cons_q(s#0);
    assume !$Unbox(Apply1(_module._default.NextLemma$_T0, TBool, $Heap, P#0, _module.Stream.head(s#0))): bool;
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(115,26): post-state"} true;
    assume _module.Stream.Cons_q(s#0);
    ##s#1 := _module.Stream.tail(s#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#1, Tclass._module.Stream(_module._default.NextLemma$_T0), $Heap);
    ##P#1 := P#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##P#1, 
      Tclass._System.___hTotalFunc1(_module._default.NextLemma$_T0, TBool), 
      $Heap);
    assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.NextLemma$_T0, ##s#1, ##P#1)
       ==> _module.__default.AlwaysAnother(_module._default.NextLemma$_T0, $LS($LZ), ##s#1, ##P#1)
         || (_module.__default.IsAnother#canCall(_module._default.NextLemma$_T0, ##s#1, ##P#1)
           ==> _module.__default.IsAnother(_module._default.NextLemma$_T0, ##s#1, ##P#1)
             || (exists n#0: int :: 
              { _module.__default.Tail(_module._default.NextLemma$_T0, $LS($LZ), ##s#1, n#0) } 
              LitInt(0) <= n#0
                 && 
                LitInt(0) <= n#0
                 && $Unbox(Apply1(_module._default.NextLemma$_T0, 
                    TBool, 
                    $Heap, 
                    ##P#1, 
                    _module.Stream.head(_module.__default.Tail(_module._default.NextLemma$_T0, $LS($LZ), ##s#1, n#0)))): bool));
    assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.NextLemma$_T0, ##s#1, ##P#1)
       ==> _module.__default.AlwaysAnother(_module._default.NextLemma$_T0, $LS($LZ), ##s#1, ##P#1)
         || _module.__default.AlwaysAnother(_module._default.NextLemma$_T0, $LS($LS($LZ)), _module.Stream.tail(##s#1), ##P#1);
    assume _module.__default.AlwaysAnother(_module._default.NextLemma$_T0, $LS($LZ), ##s#1, ##P#1);
    assume _module.__default.Next#canCall(_module._default.NextLemma$_T0, _module.Stream.tail(s#0), P#0);
    ##s#2 := s#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#2, Tclass._module.Stream(_module._default.NextLemma$_T0), $Heap);
    ##P#2 := P#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##P#2, 
      Tclass._System.___hTotalFunc1(_module._default.NextLemma$_T0, TBool), 
      $Heap);
    assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.NextLemma$_T0, ##s#2, ##P#2)
       ==> _module.__default.AlwaysAnother(_module._default.NextLemma$_T0, $LS($LZ), ##s#2, ##P#2)
         || (_module.__default.IsAnother#canCall(_module._default.NextLemma$_T0, ##s#2, ##P#2)
           ==> _module.__default.IsAnother(_module._default.NextLemma$_T0, ##s#2, ##P#2)
             || (exists n#1: int :: 
              { _module.__default.Tail(_module._default.NextLemma$_T0, $LS($LZ), ##s#2, n#1) } 
              LitInt(0) <= n#1
                 && 
                LitInt(0) <= n#1
                 && $Unbox(Apply1(_module._default.NextLemma$_T0, 
                    TBool, 
                    $Heap, 
                    ##P#2, 
                    _module.Stream.head(_module.__default.Tail(_module._default.NextLemma$_T0, $LS($LZ), ##s#2, n#1)))): bool));
    assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.NextLemma$_T0, ##s#2, ##P#2)
       ==> _module.__default.AlwaysAnother(_module._default.NextLemma$_T0, $LS($LZ), ##s#2, ##P#2)
         || _module.__default.AlwaysAnother(_module._default.NextLemma$_T0, $LS($LS($LZ)), _module.Stream.tail(##s#2), ##P#2);
    assume _module.__default.AlwaysAnother(_module._default.NextLemma$_T0, $LS($LZ), ##s#2, ##P#2);
    assume _module.__default.Next#canCall(_module._default.NextLemma$_T0, s#0, P#0);
    assume _module.__default.Next(_module._default.NextLemma$_T0, _module.Stream.tail(s#0), P#0)
       < _module.__default.Next(_module._default.NextLemma$_T0, s#0, P#0);
}



procedure {:_induction s#0, P#0} Call$$_module.__default.NextLemma(_module._default.NextLemma$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.NextLemma$_T0))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.NextLemma$_T0), $Heap)
         && $IsA#_module.Stream(s#0), 
    P#0: HandleType
       where $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.NextLemma$_T0, TBool))
         && $IsAlloc(P#0, Tclass._System.___hTotalFunc1(_module._default.NextLemma$_T0, TBool), $Heap));
  // user-defined preconditions
  requires _module.__default.AlwaysAnother#canCall(_module._default.NextLemma$_T0, s#0, P#0)
     ==> _module.__default.AlwaysAnother(_module._default.NextLemma$_T0, $LS($LZ), s#0, P#0)
       || (_module.__default.IsAnother#canCall(_module._default.NextLemma$_T0, s#0, P#0)
         ==> _module.__default.IsAnother(_module._default.NextLemma$_T0, s#0, P#0)
           || (exists n#2: int :: 
            { _module.__default.Tail(_module._default.NextLemma$_T0, $LS($LZ), s#0, n#2) } 
            LitInt(0) <= n#2
               && 
              LitInt(0) <= n#2
               && $Unbox(Apply1(_module._default.NextLemma$_T0, 
                  TBool, 
                  $Heap, 
                  P#0, 
                  _module.Stream.head(_module.__default.Tail(_module._default.NextLemma$_T0, $LS($LZ), s#0, n#2)))): bool));
  requires _module.__default.AlwaysAnother#canCall(_module._default.NextLemma$_T0, s#0, P#0)
     ==> _module.__default.AlwaysAnother(_module._default.NextLemma$_T0, $LS($LZ), s#0, P#0)
       || _module.__default.AlwaysAnother(_module._default.NextLemma$_T0, $LS($LS($LZ)), _module.Stream.tail(s#0), P#0);
  requires !$Unbox(Apply1(_module._default.NextLemma$_T0, TBool, $Heap, P#0, _module.Stream.head(s#0))): bool;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Stream.Cons_q(s#0)
     && _module.__default.Next#canCall(_module._default.NextLemma$_T0, _module.Stream.tail(s#0), P#0)
     && _module.__default.Next#canCall(_module._default.NextLemma$_T0, s#0, P#0);
  ensures _module.__default.Next(_module._default.NextLemma$_T0, _module.Stream.tail(s#0), P#0)
     < _module.__default.Next(_module._default.NextLemma$_T0, s#0, P#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction s#0, P#0} Impl$$_module.__default.NextLemma(_module._default.NextLemma$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.NextLemma$_T0))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.NextLemma$_T0), $Heap)
         && $IsA#_module.Stream(s#0), 
    P#0: HandleType
       where $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.NextLemma$_T0, TBool))
         && $IsAlloc(P#0, Tclass._System.___hTotalFunc1(_module._default.NextLemma$_T0, TBool), $Heap))
   returns ($_reverifyPost: bool);
  free requires 20 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.__default.AlwaysAnother#canCall(_module._default.NextLemma$_T0, s#0, P#0)
     && 
    _module.__default.AlwaysAnother(_module._default.NextLemma$_T0, $LS($LZ), s#0, P#0)
     && 
    _module.__default.IsAnother(_module._default.NextLemma$_T0, s#0, P#0)
     && _module.__default.AlwaysAnother(_module._default.NextLemma$_T0, $LS($LZ), _module.Stream.tail(s#0), P#0);
  requires !$Unbox(Apply1(_module._default.NextLemma$_T0, TBool, $Heap, P#0, _module.Stream.head(s#0))): bool;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Stream.Cons_q(s#0)
     && _module.__default.Next#canCall(_module._default.NextLemma$_T0, _module.Stream.tail(s#0), P#0)
     && _module.__default.Next#canCall(_module._default.NextLemma$_T0, s#0, P#0);
  ensures _module.__default.Next(_module._default.NextLemma$_T0, _module.Stream.tail(s#0), P#0)
     < _module.__default.Next(_module._default.NextLemma$_T0, s#0, P#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction s#0, P#0} Impl$$_module.__default.NextLemma(_module._default.NextLemma$_T0: Ty, s#0: DatatypeType, P#0: HandleType)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var i#0: int;
  var ##s#3: DatatypeType;
  var ##n#0: int;
  var ##s#4: DatatypeType;
  var ##n#1: int;

    // AddMethodImpl: NextLemma, Impl$$_module.__default.NextLemma
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(116,0): initial state"} true;
    assume $IsA#_module.Stream(s#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#s0#0: DatatypeType, $ih#P0#0: HandleType :: 
      $Is($ih#s0#0, Tclass._module.Stream(_module._default.NextLemma$_T0))
           && $Is($ih#P0#0, Tclass._System.___hTotalFunc1(_module._default.NextLemma$_T0, TBool))
           && 
          _module.__default.AlwaysAnother(_module._default.NextLemma$_T0, $LS($LZ), $ih#s0#0, $ih#P0#0)
           && !$Unbox(Apply1(_module._default.NextLemma$_T0, 
              TBool, 
              $initHeapForallStmt#0, 
              $ih#P0#0, 
              _module.Stream.head($ih#s0#0))): bool
           && false
         ==> _module.__default.Next(_module._default.NextLemma$_T0, _module.Stream.tail($ih#s0#0), $ih#P0#0)
           < _module.__default.Next(_module._default.NextLemma$_T0, $ih#s0#0, $ih#P0#0));
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(117,3)
    // Begin Comprehension WF check
    havoc i#0;
    if (true)
    {
        if (0 < i#0)
        {
            ##s#3 := s#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#3, Tclass._module.Stream(_module._default.NextLemma$_T0), $Heap);
            assert $Is(i#0, Tclass._System.nat());
            ##n#0 := i#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
            assume _module.__default.Tail#canCall(_module._default.NextLemma$_T0, s#0, i#0);
            assume _module.Stream.Cons_q(_module.__default.Tail(_module._default.NextLemma$_T0, $LS($LZ), s#0, i#0));
            assume _module.Stream.Cons_q(s#0);
            ##s#4 := _module.Stream.tail(s#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#4, Tclass._module.Stream(_module._default.NextLemma$_T0), $Heap);
            assert $Is(i#0 - 1, Tclass._System.nat());
            ##n#1 := i#0 - 1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#1, Tclass._System.nat(), $Heap);
            assume _module.__default.Tail#canCall(_module._default.NextLemma$_T0, _module.Stream.tail(s#0), i#0 - 1);
            assume _module.Stream.Cons_q(_module.__default.Tail(_module._default.NextLemma$_T0, $LS($LZ), _module.Stream.tail(s#0), i#0 - 1));
        }
    }

    // End Comprehension WF check
    assume (forall i#1: int :: 
      { _module.__default.Tail(_module._default.NextLemma$_T0, $LS($LZ), s#0, i#1) } 
      0 < i#1
         ==> $IsA#_module.Stream(_module.__default.Tail(_module._default.NextLemma$_T0, $LS($LZ), s#0, i#1))
           && $IsA#_module.Stream(_module.__default.Tail(_module._default.NextLemma$_T0, $LS($LZ), _module.Stream.tail(s#0), i#1 - 1))
           && 
          _module.__default.Tail#canCall(_module._default.NextLemma$_T0, s#0, i#1)
           && 
          _module.Stream.Cons_q(s#0)
           && _module.__default.Tail#canCall(_module._default.NextLemma$_T0, _module.Stream.tail(s#0), i#1 - 1));
    assert {:subsumption 0} (forall i#1: int :: 
      { _module.__default.Tail(_module._default.NextLemma$_T0, $LS($LS($LZ)), s#0, i#1) } 
      true
         ==> 
        0 < i#1
         ==> $Eq#_module.Stream(_module._default.NextLemma$_T0, 
          _module._default.NextLemma$_T0, 
          $LS($LS($LZ)), 
          _module.__default.Tail(_module._default.NextLemma$_T0, $LS($LS($LZ)), s#0, i#1), 
          _module.__default.Tail(_module._default.NextLemma$_T0, $LS($LS($LZ)), _module.Stream.tail(s#0), i#1 - 1)));
    assume (forall i#1: int :: 
      { _module.__default.Tail(_module._default.NextLemma$_T0, $LS($LZ), s#0, i#1) } 
      true
         ==> 
        0 < i#1
         ==> $Eq#_module.Stream(_module._default.NextLemma$_T0, 
          _module._default.NextLemma$_T0, 
          $LS($LS($LZ)), 
          _module.__default.Tail(_module._default.NextLemma$_T0, $LS($LZ), s#0, i#1), 
          _module.__default.Tail(_module._default.NextLemma$_T0, $LS($LZ), _module.Stream.tail(s#0), i#1 - 1)));
}



// function declaration for _module._default.Filter
function _module.__default.Filter(_module._default.Filter$_T0: Ty, 
    $ly: LayerType, 
    s#0: DatatypeType, 
    P#0: HandleType)
   : DatatypeType;

function _module.__default.Filter#canCall(_module._default.Filter$_T0: Ty, s#0: DatatypeType, P#0: HandleType) : bool;

// layer synonym axiom
axiom (forall _module._default.Filter$_T0: Ty, 
    $ly: LayerType, 
    s#0: DatatypeType, 
    P#0: HandleType :: 
  { _module.__default.Filter(_module._default.Filter$_T0, $LS($ly), s#0, P#0) } 
  _module.__default.Filter(_module._default.Filter$_T0, $LS($ly), s#0, P#0)
     == _module.__default.Filter(_module._default.Filter$_T0, $ly, s#0, P#0));

// fuel synonym axiom
axiom (forall _module._default.Filter$_T0: Ty, 
    $ly: LayerType, 
    s#0: DatatypeType, 
    P#0: HandleType :: 
  { _module.__default.Filter(_module._default.Filter$_T0, AsFuelBottom($ly), s#0, P#0) } 
  _module.__default.Filter(_module._default.Filter$_T0, $ly, s#0, P#0)
     == _module.__default.Filter(_module._default.Filter$_T0, $LZ, s#0, P#0));

// consequence axiom for _module.__default.Filter
axiom 21 <= $FunctionContextHeight
   ==> (forall _module._default.Filter$_T0: Ty, 
      $ly: LayerType, 
      s#0: DatatypeType, 
      P#0: HandleType :: 
    { _module.__default.Filter(_module._default.Filter$_T0, $ly, s#0, P#0) } 
    _module.__default.Filter#canCall(_module._default.Filter$_T0, s#0, P#0)
         || (21 != $FunctionContextHeight
           && 
          $Is(s#0, Tclass._module.Stream(_module._default.Filter$_T0))
           && $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.Filter$_T0, TBool))
           && _module.__default.AlwaysAnother(_module._default.Filter$_T0, $LS($LZ), s#0, P#0))
       ==> $Is(_module.__default.Filter(_module._default.Filter$_T0, $ly, s#0, P#0), 
        Tclass._module.Stream(_module._default.Filter$_T0)));

function _module.__default.Filter#requires(Ty, LayerType, DatatypeType, HandleType) : bool;

// #requires axiom for _module.__default.Filter
axiom (forall _module._default.Filter$_T0: Ty, 
    $ly: LayerType, 
    $Heap: Heap, 
    s#0: DatatypeType, 
    P#0: HandleType :: 
  { _module.__default.Filter#requires(_module._default.Filter$_T0, $ly, s#0, P#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && $Is(s#0, Tclass._module.Stream(_module._default.Filter$_T0))
       && $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.Filter$_T0, TBool))
     ==> _module.__default.Filter#requires(_module._default.Filter$_T0, $ly, s#0, P#0)
       == _module.__default.AlwaysAnother(_module._default.Filter$_T0, $LS($LZ), s#0, P#0));

// definition axiom for _module.__default.Filter (revealed)
axiom 21 <= $FunctionContextHeight
   ==> (forall _module._default.Filter$_T0: Ty, 
      $ly: LayerType, 
      $Heap: Heap, 
      s#0: DatatypeType, 
      P#0: HandleType :: 
    { _module.__default.Filter(_module._default.Filter$_T0, $LS($ly), s#0, P#0), $IsGoodHeap($Heap) } 
    _module.__default.Filter#canCall(_module._default.Filter$_T0, s#0, P#0)
         || (21 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(s#0, Tclass._module.Stream(_module._default.Filter$_T0))
           && $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.Filter$_T0, TBool))
           && _module.__default.AlwaysAnother(_module._default.Filter$_T0, $LS($LZ), s#0, P#0))
       ==> _module.Stream.Cons_q(s#0)
         && ($Unbox(Apply1(_module._default.Filter$_T0, TBool, $Heap, P#0, _module.Stream.head(s#0))): bool
           ==> _module.Stream.Cons_q(s#0)
             && 
            _module.Stream.Cons_q(s#0)
             && _module.__default.Filter#canCall(_module._default.Filter$_T0, _module.Stream.tail(s#0), P#0))
         && (!$Unbox(Apply1(_module._default.Filter$_T0, TBool, $Heap, P#0, _module.Stream.head(s#0))): bool
           ==> _module.Stream.Cons_q(s#0)
             && _module.__default.Filter#canCall(_module._default.Filter$_T0, _module.Stream.tail(s#0), P#0))
         && _module.__default.Filter(_module._default.Filter$_T0, $LS($ly), s#0, P#0)
           == (if $Unbox(Apply1(_module._default.Filter$_T0, TBool, $Heap, P#0, _module.Stream.head(s#0))): bool
             then #_module.Stream.Cons(_module.Stream.head(s#0), 
              _module.__default.Filter(_module._default.Filter$_T0, $ly, _module.Stream.tail(s#0), P#0))
             else _module.__default.Filter(_module._default.Filter$_T0, $ly, _module.Stream.tail(s#0), P#0)));

procedure CheckWellformed$$_module.__default.Filter(_module._default.Filter$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Filter$_T0)), 
    P#0: HandleType
       where $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.Filter$_T0, TBool)));
  free requires 21 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Filter(_module._default.Filter$_T0: Ty, s#0: DatatypeType, P#0: HandleType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##s#0: DatatypeType;
  var ##P#0: HandleType;
  var b$reqreads#0: bool;
  var ##s#1: DatatypeType;
  var ##P#1: HandleType;
  var ##s#2: DatatypeType;
  var ##P#2: HandleType;
  var s##0: DatatypeType;
  var P##0: HandleType;
  var ##s#3: DatatypeType;
  var ##P#3: HandleType;
  var b$reqreads#1: bool;
  var b$reqreads#2: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;

    // AddWellformednessCheck for function Filter
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(120,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    ##s#0 := s#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#0, Tclass._module.Stream(_module._default.Filter$_T0), $Heap);
    ##P#0 := P#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##P#0, Tclass._System.___hTotalFunc1(_module._default.Filter$_T0, TBool), $Heap);
    b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    assume _module.__default.AlwaysAnother#canCall(_module._default.Filter$_T0, s#0, P#0);
    assume _module.__default.AlwaysAnother(_module._default.Filter$_T0, $LS($LZ), s#0, P#0);
    assert b$reqreads#0;
    ##s#1 := s#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#1, Tclass._module.Stream(_module._default.Filter$_T0), $Heap);
    ##P#1 := P#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##P#1, Tclass._System.___hTotalFunc1(_module._default.Filter$_T0, TBool), $Heap);
    assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.Filter$_T0, ##s#1, ##P#1)
       ==> _module.__default.AlwaysAnother(_module._default.Filter$_T0, $LS($LZ), ##s#1, ##P#1)
         || (_module.__default.IsAnother#canCall(_module._default.Filter$_T0, ##s#1, ##P#1)
           ==> _module.__default.IsAnother(_module._default.Filter$_T0, ##s#1, ##P#1)
             || (exists n#0: int :: 
              { _module.__default.Tail(_module._default.Filter$_T0, $LS($LZ), ##s#1, n#0) } 
              LitInt(0) <= n#0
                 && 
                LitInt(0) <= n#0
                 && $Unbox(Apply1(_module._default.Filter$_T0, 
                    TBool, 
                    $Heap, 
                    ##P#1, 
                    _module.Stream.head(_module.__default.Tail(_module._default.Filter$_T0, $LS($LZ), ##s#1, n#0)))): bool));
    assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.Filter$_T0, ##s#1, ##P#1)
       ==> _module.__default.AlwaysAnother(_module._default.Filter$_T0, $LS($LZ), ##s#1, ##P#1)
         || _module.__default.AlwaysAnother(_module._default.Filter$_T0, $LS($LS($LZ)), _module.Stream.tail(##s#1), ##P#1);
    assume _module.__default.AlwaysAnother(_module._default.Filter$_T0, $LS($LZ), ##s#1, ##P#1);
    assume _module.__default.Next#canCall(_module._default.Filter$_T0, s#0, P#0);
    if (*)
    {
        assume $Is(_module.__default.Filter(_module._default.Filter$_T0, $LS($LZ), s#0, P#0), 
          Tclass._module.Stream(_module._default.Filter$_T0));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        assume _module.Stream.Cons_q(s#0);
        if ($Unbox(Apply1(_module._default.Filter$_T0, TBool, $Heap, P#0, _module.Stream.head(s#0))): bool)
        {
            assume _module.Stream.Cons_q(s#0);
            assume _module.Stream.Cons_q(s#0);
            ##s#2 := _module.Stream.tail(s#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#2, Tclass._module.Stream(_module._default.Filter$_T0), $Heap);
            ##P#2 := P#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##P#2, Tclass._System.___hTotalFunc1(_module._default.Filter$_T0, TBool), $Heap);
            assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.Filter$_T0, ##s#2, ##P#2)
               ==> _module.__default.AlwaysAnother(_module._default.Filter$_T0, $LS($LZ), ##s#2, ##P#2)
                 || (_module.__default.IsAnother#canCall(_module._default.Filter$_T0, ##s#2, ##P#2)
                   ==> _module.__default.IsAnother(_module._default.Filter$_T0, ##s#2, ##P#2)
                     || (exists n#1: int :: 
                      { _module.__default.Tail(_module._default.Filter$_T0, $LS($LZ), ##s#2, n#1) } 
                      LitInt(0) <= n#1
                         && 
                        LitInt(0) <= n#1
                         && $Unbox(Apply1(_module._default.Filter$_T0, 
                            TBool, 
                            $Heap, 
                            ##P#2, 
                            _module.Stream.head(_module.__default.Tail(_module._default.Filter$_T0, $LS($LZ), ##s#2, n#1)))): bool));
            assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.Filter$_T0, ##s#2, ##P#2)
               ==> _module.__default.AlwaysAnother(_module._default.Filter$_T0, $LS($LZ), ##s#2, ##P#2)
                 || _module.__default.AlwaysAnother(_module._default.Filter$_T0, $LS($LS($LZ)), _module.Stream.tail(##s#2), ##P#2);
            assume _module.__default.AlwaysAnother(_module._default.Filter$_T0, $LS($LZ), ##s#2, ##P#2);
            b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.Filter#canCall(_module._default.Filter$_T0, _module.Stream.tail(s#0), P#0);
            assume _module.Stream.Cons_q(_module.__default.Filter(_module._default.Filter$_T0, $LS($LZ), _module.Stream.tail(s#0), P#0));
            assume _module.__default.Filter(_module._default.Filter$_T0, $LS($LZ), s#0, P#0)
               == #_module.Stream.Cons(_module.Stream.head(s#0), 
                _module.__default.Filter(_module._default.Filter$_T0, $LS($LZ), _module.Stream.tail(s#0), P#0));
            assume _module.Stream.Cons_q(s#0)
               && 
              _module.Stream.Cons_q(s#0)
               && _module.__default.Filter#canCall(_module._default.Filter$_T0, _module.Stream.tail(s#0), P#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.Filter(_module._default.Filter$_T0, $LS($LZ), s#0, P#0), 
              Tclass._module.Stream(_module._default.Filter$_T0));
        }
        else
        {
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(127,14)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            s##0 := s#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            P##0 := P#0;
            // ProcessCallStmt: Make the call
            call Call$$_module.__default.NextLemma(_module._default.Filter$_T0, s##0, P##0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(127,19)"} true;
            assume _module.Stream.Cons_q(s#0);
            ##s#3 := _module.Stream.tail(s#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#3, Tclass._module.Stream(_module._default.Filter$_T0), $Heap);
            ##P#3 := P#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##P#3, Tclass._System.___hTotalFunc1(_module._default.Filter$_T0, TBool), $Heap);
            assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.Filter$_T0, ##s#3, ##P#3)
               ==> _module.__default.AlwaysAnother(_module._default.Filter$_T0, $LS($LZ), ##s#3, ##P#3)
                 || (_module.__default.IsAnother#canCall(_module._default.Filter$_T0, ##s#3, ##P#3)
                   ==> _module.__default.IsAnother(_module._default.Filter$_T0, ##s#3, ##P#3)
                     || (exists n#2: int :: 
                      { _module.__default.Tail(_module._default.Filter$_T0, $LS($LZ), ##s#3, n#2) } 
                      LitInt(0) <= n#2
                         && 
                        LitInt(0) <= n#2
                         && $Unbox(Apply1(_module._default.Filter$_T0, 
                            TBool, 
                            $Heap, 
                            ##P#3, 
                            _module.Stream.head(_module.__default.Tail(_module._default.Filter$_T0, $LS($LZ), ##s#3, n#2)))): bool));
            assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.Filter$_T0, ##s#3, ##P#3)
               ==> _module.__default.AlwaysAnother(_module._default.Filter$_T0, $LS($LZ), ##s#3, ##P#3)
                 || _module.__default.AlwaysAnother(_module._default.Filter$_T0, $LS($LS($LZ)), _module.Stream.tail(##s#3), ##P#3);
            assume _module.__default.AlwaysAnother(_module._default.Filter$_T0, $LS($LZ), ##s#3, ##P#3);
            b$reqreads#2 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0 <= LitInt(1) || LitInt(1) == LitInt(1);
            assert 0 <= _module.__default.Next(_module._default.Filter$_T0, s#0, P#0)
               || LitInt(1) < LitInt(1)
               || _module.__default.Next(_module._default.Filter$_T0, ##s#3, ##P#3)
                 == _module.__default.Next(_module._default.Filter$_T0, s#0, P#0);
            assert LitInt(1) < LitInt(1)
               || (LitInt(1) == LitInt(1)
                 && _module.__default.Next(_module._default.Filter$_T0, ##s#3, ##P#3)
                   < _module.__default.Next(_module._default.Filter$_T0, s#0, P#0));
            assume _module.__default.Filter#canCall(_module._default.Filter$_T0, _module.Stream.tail(s#0), P#0);
            assume _module.Stream.Cons_q(_module.__default.Filter(_module._default.Filter$_T0, $LS($LZ), _module.Stream.tail(s#0), P#0));
            assume _module.__default.Filter(_module._default.Filter$_T0, $LS($LZ), s#0, P#0)
               == _module.__default.Filter(_module._default.Filter$_T0, $LS($LZ), _module.Stream.tail(s#0), P#0);
            assume _module.Stream.Cons_q(s#0)
               && _module.__default.Filter#canCall(_module._default.Filter$_T0, _module.Stream.tail(s#0), P#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.Filter(_module._default.Filter$_T0, $LS($LZ), s#0, P#0), 
              Tclass._module.Stream(_module._default.Filter$_T0));
        }

        assert b$reqreads#1;
        assert b$reqreads#2;
    }
}



procedure CheckWellformed$$_module.__default.Filter__AlwaysAnother(_module._default.Filter_AlwaysAnother$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Filter_AlwaysAnother$_T0))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.Filter_AlwaysAnother$_T0), $Heap)
         && $IsA#_module.Stream(s#0), 
    P#0: HandleType
       where $Is(P#0, 
          Tclass._System.___hTotalFunc1(_module._default.Filter_AlwaysAnother$_T0, TBool))
         && $IsAlloc(P#0, 
          Tclass._System.___hTotalFunc1(_module._default.Filter_AlwaysAnother$_T0, TBool), 
          $Heap));
  free requires 22 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Filter__AlwaysAnother(_module._default.Filter_AlwaysAnother$_T0: Ty, 
    s#0: DatatypeType, 
    P#0: HandleType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##s#0: DatatypeType;
  var ##P#0: HandleType;
  var ##s#1: DatatypeType;
  var ##P#1: HandleType;
  var ##s#2: DatatypeType;
  var ##P#2: HandleType;
  var ##s#3: DatatypeType;
  var ##P#3: HandleType;

    // AddMethodImpl: Filter_AlwaysAnother, CheckWellformed$$_module.__default.Filter__AlwaysAnother
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(131,15): initial state"} true;
    ##s#0 := s#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#0, Tclass._module.Stream(_module._default.Filter_AlwaysAnother$_T0), $Heap);
    ##P#0 := P#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##P#0, 
      Tclass._System.___hTotalFunc1(_module._default.Filter_AlwaysAnother$_T0, TBool), 
      $Heap);
    assume _module.__default.AlwaysAnother#canCall(_module._default.Filter_AlwaysAnother$_T0, s#0, P#0);
    assume _module.__default.AlwaysAnother(_module._default.Filter_AlwaysAnother$_T0, $LS($LZ), s#0, P#0);
    ##s#1 := s#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#1, Tclass._module.Stream(_module._default.Filter_AlwaysAnother$_T0), $Heap);
    ##P#1 := P#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##P#1, 
      Tclass._System.___hTotalFunc1(_module._default.Filter_AlwaysAnother$_T0, TBool), 
      $Heap);
    assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.Filter_AlwaysAnother$_T0, ##s#1, ##P#1)
       ==> _module.__default.AlwaysAnother(_module._default.Filter_AlwaysAnother$_T0, $LS($LZ), ##s#1, ##P#1)
         || (_module.__default.IsAnother#canCall(_module._default.Filter_AlwaysAnother$_T0, ##s#1, ##P#1)
           ==> _module.__default.IsAnother(_module._default.Filter_AlwaysAnother$_T0, ##s#1, ##P#1)
             || (exists n#0: int :: 
              { _module.__default.Tail(_module._default.Filter_AlwaysAnother$_T0, $LS($LZ), ##s#1, n#0) } 
              LitInt(0) <= n#0
                 && 
                LitInt(0) <= n#0
                 && $Unbox(Apply1(_module._default.Filter_AlwaysAnother$_T0, 
                    TBool, 
                    $Heap, 
                    ##P#1, 
                    _module.Stream.head(_module.__default.Tail(_module._default.Filter_AlwaysAnother$_T0, $LS($LZ), ##s#1, n#0)))): bool));
    assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.Filter_AlwaysAnother$_T0, ##s#1, ##P#1)
       ==> _module.__default.AlwaysAnother(_module._default.Filter_AlwaysAnother$_T0, $LS($LZ), ##s#1, ##P#1)
         || _module.__default.AlwaysAnother(_module._default.Filter_AlwaysAnother$_T0, 
          $LS($LS($LZ)), 
          _module.Stream.tail(##s#1), 
          ##P#1);
    assume _module.__default.AlwaysAnother(_module._default.Filter_AlwaysAnother$_T0, $LS($LZ), ##s#1, ##P#1);
    assume _module.__default.Next#canCall(_module._default.Filter_AlwaysAnother$_T0, s#0, P#0);
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(133,14): post-state"} true;
    ##s#2 := s#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#2, Tclass._module.Stream(_module._default.Filter_AlwaysAnother$_T0), $Heap);
    ##P#2 := P#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##P#2, 
      Tclass._System.___hTotalFunc1(_module._default.Filter_AlwaysAnother$_T0, TBool), 
      $Heap);
    assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.Filter_AlwaysAnother$_T0, ##s#2, ##P#2)
       ==> _module.__default.AlwaysAnother(_module._default.Filter_AlwaysAnother$_T0, $LS($LZ), ##s#2, ##P#2)
         || (_module.__default.IsAnother#canCall(_module._default.Filter_AlwaysAnother$_T0, ##s#2, ##P#2)
           ==> _module.__default.IsAnother(_module._default.Filter_AlwaysAnother$_T0, ##s#2, ##P#2)
             || (exists n#1: int :: 
              { _module.__default.Tail(_module._default.Filter_AlwaysAnother$_T0, $LS($LZ), ##s#2, n#1) } 
              LitInt(0) <= n#1
                 && 
                LitInt(0) <= n#1
                 && $Unbox(Apply1(_module._default.Filter_AlwaysAnother$_T0, 
                    TBool, 
                    $Heap, 
                    ##P#2, 
                    _module.Stream.head(_module.__default.Tail(_module._default.Filter_AlwaysAnother$_T0, $LS($LZ), ##s#2, n#1)))): bool));
    assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.Filter_AlwaysAnother$_T0, ##s#2, ##P#2)
       ==> _module.__default.AlwaysAnother(_module._default.Filter_AlwaysAnother$_T0, $LS($LZ), ##s#2, ##P#2)
         || _module.__default.AlwaysAnother(_module._default.Filter_AlwaysAnother$_T0, 
          $LS($LS($LZ)), 
          _module.Stream.tail(##s#2), 
          ##P#2);
    assume _module.__default.AlwaysAnother(_module._default.Filter_AlwaysAnother$_T0, $LS($LZ), ##s#2, ##P#2);
    assume _module.__default.Filter#canCall(_module._default.Filter_AlwaysAnother$_T0, s#0, P#0);
    assume _module.Stream.Cons_q(_module.__default.Filter(_module._default.Filter_AlwaysAnother$_T0, $LS($LZ), s#0, P#0));
    ##s#3 := _module.__default.Filter(_module._default.Filter_AlwaysAnother$_T0, $LS($LZ), s#0, P#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#3, Tclass._module.Stream(_module._default.Filter_AlwaysAnother$_T0), $Heap);
    ##P#3 := P#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##P#3, 
      Tclass._System.___hTotalFunc1(_module._default.Filter_AlwaysAnother$_T0, TBool), 
      $Heap);
    assume _module.__default.AllP#canCall(_module._default.Filter_AlwaysAnother$_T0, 
      _module.__default.Filter(_module._default.Filter_AlwaysAnother$_T0, $LS($LZ), s#0, P#0), 
      P#0);
    assume _module.__default.AllP(_module._default.Filter_AlwaysAnother$_T0, 
      $LS($LZ), 
      _module.__default.Filter(_module._default.Filter_AlwaysAnother$_T0, $LS($LZ), s#0, P#0), 
      P#0);
}



procedure Call$$_module.__default.Filter__AlwaysAnother(_module._default.Filter_AlwaysAnother$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Filter_AlwaysAnother$_T0))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.Filter_AlwaysAnother$_T0), $Heap)
         && $IsA#_module.Stream(s#0), 
    P#0: HandleType
       where $Is(P#0, 
          Tclass._System.___hTotalFunc1(_module._default.Filter_AlwaysAnother$_T0, TBool))
         && $IsAlloc(P#0, 
          Tclass._System.___hTotalFunc1(_module._default.Filter_AlwaysAnother$_T0, TBool), 
          $Heap));
  // user-defined preconditions
  requires _module.__default.AlwaysAnother#canCall(_module._default.Filter_AlwaysAnother$_T0, s#0, P#0)
     ==> _module.__default.AlwaysAnother(_module._default.Filter_AlwaysAnother$_T0, $LS($LZ), s#0, P#0)
       || (_module.__default.IsAnother#canCall(_module._default.Filter_AlwaysAnother$_T0, s#0, P#0)
         ==> _module.__default.IsAnother(_module._default.Filter_AlwaysAnother$_T0, s#0, P#0)
           || (exists n#2: int :: 
            { _module.__default.Tail(_module._default.Filter_AlwaysAnother$_T0, $LS($LZ), s#0, n#2) } 
            LitInt(0) <= n#2
               && 
              LitInt(0) <= n#2
               && $Unbox(Apply1(_module._default.Filter_AlwaysAnother$_T0, 
                  TBool, 
                  $Heap, 
                  P#0, 
                  _module.Stream.head(_module.__default.Tail(_module._default.Filter_AlwaysAnother$_T0, $LS($LZ), s#0, n#2)))): bool));
  requires _module.__default.AlwaysAnother#canCall(_module._default.Filter_AlwaysAnother$_T0, s#0, P#0)
     ==> _module.__default.AlwaysAnother(_module._default.Filter_AlwaysAnother$_T0, $LS($LZ), s#0, P#0)
       || _module.__default.AlwaysAnother(_module._default.Filter_AlwaysAnother$_T0, 
        $LS($LS($LZ)), 
        _module.Stream.tail(s#0), 
        P#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Filter#canCall(_module._default.Filter_AlwaysAnother$_T0, s#0, P#0)
     && _module.__default.AllP#canCall(_module._default.Filter_AlwaysAnother$_T0, 
      _module.__default.Filter(_module._default.Filter_AlwaysAnother$_T0, $LS($LZ), s#0, P#0), 
      P#0);
  free ensures _module.__default.AllP#canCall(_module._default.Filter_AlwaysAnother$_T0, 
      _module.__default.Filter(_module._default.Filter_AlwaysAnother$_T0, $LS($LZ), s#0, P#0), 
      P#0)
     && 
    _module.__default.AllP(_module._default.Filter_AlwaysAnother$_T0, 
      $LS($LZ), 
      _module.__default.Filter(_module._default.Filter_AlwaysAnother$_T0, $LS($LZ), s#0, P#0), 
      P#0)
     && 
    $Unbox(Apply1(_module._default.Filter_AlwaysAnother$_T0, 
        TBool, 
        $Heap, 
        P#0, 
        _module.Stream.head(_module.__default.Filter(_module._default.Filter_AlwaysAnother$_T0, $LS($LZ), s#0, P#0)))): bool
     && _module.__default.AllP(_module._default.Filter_AlwaysAnother$_T0, 
      $LS($LZ), 
      _module.Stream.tail(_module.__default.Filter(_module._default.Filter_AlwaysAnother$_T0, $LS($LZ), s#0, P#0)), 
      P#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, s#1, P#1} CoCall$$_module.__default.Filter__AlwaysAnother_h(_module._default.Filter_AlwaysAnother#$_T0: Ty, 
    _k#0: Box, 
    s#1: DatatypeType
       where $Is(s#1, Tclass._module.Stream(_module._default.Filter_AlwaysAnother#$_T0))
         && $IsAlloc(s#1, Tclass._module.Stream(_module._default.Filter_AlwaysAnother#$_T0), $Heap)
         && $IsA#_module.Stream(s#1), 
    P#1: HandleType
       where $Is(P#1, 
          Tclass._System.___hTotalFunc1(_module._default.Filter_AlwaysAnother#$_T0, TBool))
         && $IsAlloc(P#1, 
          Tclass._System.___hTotalFunc1(_module._default.Filter_AlwaysAnother#$_T0, TBool), 
          $Heap));
  // user-defined preconditions
  requires _module.__default.AlwaysAnother#canCall(_module._default.Filter_AlwaysAnother#$_T0, s#1, P#1)
     ==> _module.__default.AlwaysAnother(_module._default.Filter_AlwaysAnother#$_T0, $LS($LZ), s#1, P#1)
       || (_module.__default.IsAnother#canCall(_module._default.Filter_AlwaysAnother#$_T0, s#1, P#1)
         ==> _module.__default.IsAnother(_module._default.Filter_AlwaysAnother#$_T0, s#1, P#1)
           || (exists n#3: int :: 
            { _module.__default.Tail(_module._default.Filter_AlwaysAnother#$_T0, $LS($LZ), s#1, n#3) } 
            LitInt(0) <= n#3
               && 
              LitInt(0) <= n#3
               && $Unbox(Apply1(_module._default.Filter_AlwaysAnother#$_T0, 
                  TBool, 
                  $Heap, 
                  P#1, 
                  _module.Stream.head(_module.__default.Tail(_module._default.Filter_AlwaysAnother#$_T0, $LS($LZ), s#1, n#3)))): bool));
  requires _module.__default.AlwaysAnother#canCall(_module._default.Filter_AlwaysAnother#$_T0, s#1, P#1)
     ==> _module.__default.AlwaysAnother(_module._default.Filter_AlwaysAnother#$_T0, $LS($LZ), s#1, P#1)
       || _module.__default.AlwaysAnother(_module._default.Filter_AlwaysAnother#$_T0, 
        $LS($LS($LZ)), 
        _module.Stream.tail(s#1), 
        P#1);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Filter#canCall(_module._default.Filter_AlwaysAnother#$_T0, s#1, P#1)
     && _module.__default.AllP_h#canCall(_module._default.Filter_AlwaysAnother#$_T0, 
      _k#0, 
      _module.__default.Filter(_module._default.Filter_AlwaysAnother#$_T0, $LS($LZ), s#1, P#1), 
      P#1);
  free ensures _module.__default.AllP_h#canCall(_module._default.Filter_AlwaysAnother#$_T0, 
      _k#0, 
      _module.__default.Filter(_module._default.Filter_AlwaysAnother#$_T0, $LS($LZ), s#1, P#1), 
      P#1)
     && 
    _module.__default.AllP_h(_module._default.Filter_AlwaysAnother#$_T0, 
      $LS($LZ), 
      _k#0, 
      _module.__default.Filter(_module._default.Filter_AlwaysAnother#$_T0, $LS($LZ), s#1, P#1), 
      P#1)
     && 
    (0 < ORD#Offset(_k#0)
       ==> $Unbox(Apply1(_module._default.Filter_AlwaysAnother#$_T0, 
            TBool, 
            $Heap, 
            P#1, 
            _module.Stream.head(_module.__default.Filter(_module._default.Filter_AlwaysAnother#$_T0, $LS($LZ), s#1, P#1)))): bool
         && _module.__default.AllP_h(_module._default.Filter_AlwaysAnother#$_T0, 
          $LS($LZ), 
          ORD#Minus(_k#0, ORD#FromNat(1)), 
          _module.Stream.tail(_module.__default.Filter(_module._default.Filter_AlwaysAnother#$_T0, $LS($LZ), s#1, P#1)), 
          P#1))
     && (LitInt(0) == ORD#Offset(_k#0)
       ==> (forall _k'#0: Box :: 
        { _module.__default.AllP_h(_module._default.Filter_AlwaysAnother#$_T0, 
            $LS($LZ), 
            _k'#0, 
            _module.__default.Filter(_module._default.Filter_AlwaysAnother#$_T0, $LS($LZ), s#1, P#1), 
            P#1) } 
        ORD#Less(_k'#0, _k#0)
           ==> _module.__default.AllP_h(_module._default.Filter_AlwaysAnother#$_T0, 
            $LS($LZ), 
            _k'#0, 
            _module.__default.Filter(_module._default.Filter_AlwaysAnother#$_T0, $LS($LZ), s#1, P#1), 
            P#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, s#1, P#1} Impl$$_module.__default.Filter__AlwaysAnother_h(_module._default.Filter_AlwaysAnother#$_T0: Ty, 
    _k#0: Box, 
    s#1: DatatypeType
       where $Is(s#1, Tclass._module.Stream(_module._default.Filter_AlwaysAnother#$_T0))
         && $IsAlloc(s#1, Tclass._module.Stream(_module._default.Filter_AlwaysAnother#$_T0), $Heap)
         && $IsA#_module.Stream(s#1), 
    P#1: HandleType
       where $Is(P#1, 
          Tclass._System.___hTotalFunc1(_module._default.Filter_AlwaysAnother#$_T0, TBool))
         && $IsAlloc(P#1, 
          Tclass._System.___hTotalFunc1(_module._default.Filter_AlwaysAnother#$_T0, TBool), 
          $Heap))
   returns ($_reverifyPost: bool);
  free requires 22 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.__default.AlwaysAnother#canCall(_module._default.Filter_AlwaysAnother#$_T0, s#1, P#1)
     && 
    _module.__default.AlwaysAnother(_module._default.Filter_AlwaysAnother#$_T0, $LS($LZ), s#1, P#1)
     && 
    _module.__default.IsAnother(_module._default.Filter_AlwaysAnother#$_T0, s#1, P#1)
     && _module.__default.AlwaysAnother(_module._default.Filter_AlwaysAnother#$_T0, 
      $LS($LZ), 
      _module.Stream.tail(s#1), 
      P#1);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Filter#canCall(_module._default.Filter_AlwaysAnother#$_T0, s#1, P#1)
     && _module.__default.AllP_h#canCall(_module._default.Filter_AlwaysAnother#$_T0, 
      _k#0, 
      _module.__default.Filter(_module._default.Filter_AlwaysAnother#$_T0, $LS($LZ), s#1, P#1), 
      P#1);
  ensures _module.__default.AllP_h#canCall(_module._default.Filter_AlwaysAnother#$_T0, 
      _k#0, 
      _module.__default.Filter(_module._default.Filter_AlwaysAnother#$_T0, $LS($LZ), s#1, P#1), 
      P#1)
     ==> _module.__default.AllP_h(_module._default.Filter_AlwaysAnother#$_T0, 
        $LS($LZ), 
        _k#0, 
        _module.__default.Filter(_module._default.Filter_AlwaysAnother#$_T0, $LS($LZ), s#1, P#1), 
        P#1)
       || (0 < ORD#Offset(_k#0)
         ==> $Unbox(Apply1(_module._default.Filter_AlwaysAnother#$_T0, 
            TBool, 
            $Heap, 
            P#1, 
            _module.Stream.head(_module.__default.Filter(_module._default.Filter_AlwaysAnother#$_T0, $LS($LS($LZ)), s#1, P#1)))): bool);
  ensures _module.__default.AllP_h#canCall(_module._default.Filter_AlwaysAnother#$_T0, 
      _k#0, 
      _module.__default.Filter(_module._default.Filter_AlwaysAnother#$_T0, $LS($LZ), s#1, P#1), 
      P#1)
     ==> _module.__default.AllP_h(_module._default.Filter_AlwaysAnother#$_T0, 
        $LS($LZ), 
        _k#0, 
        _module.__default.Filter(_module._default.Filter_AlwaysAnother#$_T0, $LS($LZ), s#1, P#1), 
        P#1)
       || (0 < ORD#Offset(_k#0)
         ==> _module.__default.AllP_h(_module._default.Filter_AlwaysAnother#$_T0, 
          $LS($LS($LZ)), 
          ORD#Minus(_k#0, ORD#FromNat(1)), 
          _module.Stream.tail(_module.__default.Filter(_module._default.Filter_AlwaysAnother#$_T0, $LS($LS($LZ)), s#1, P#1)), 
          P#1));
  ensures _module.__default.AllP_h#canCall(_module._default.Filter_AlwaysAnother#$_T0, 
      _k#0, 
      _module.__default.Filter(_module._default.Filter_AlwaysAnother#$_T0, $LS($LZ), s#1, P#1), 
      P#1)
     ==> _module.__default.AllP_h(_module._default.Filter_AlwaysAnother#$_T0, 
        $LS($LZ), 
        _k#0, 
        _module.__default.Filter(_module._default.Filter_AlwaysAnother#$_T0, $LS($LZ), s#1, P#1), 
        P#1)
       || (LitInt(0) == ORD#Offset(_k#0)
         ==> (forall _k'#1: Box :: 
          { _module.__default.AllP_h(_module._default.Filter_AlwaysAnother#$_T0, 
              $LS($LS($LZ)), 
              _k'#1, 
              _module.__default.Filter(_module._default.Filter_AlwaysAnother#$_T0, $LS($LS($LZ)), s#1, P#1), 
              P#1) } 
          ORD#Less(_k'#1, _k#0)
             ==> _module.__default.AllP_h(_module._default.Filter_AlwaysAnother#$_T0, 
              $LS($LS($LZ)), 
              _k'#1, 
              _module.__default.Filter(_module._default.Filter_AlwaysAnother#$_T0, $LS($LS($LZ)), s#1, P#1), 
              P#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0, s#1, P#1} Impl$$_module.__default.Filter__AlwaysAnother_h(_module._default.Filter_AlwaysAnother#$_T0: Ty, 
    _k#0: Box, 
    s#1: DatatypeType, 
    P#1: HandleType)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var _k##0: Box;
  var s##0: DatatypeType;
  var P##0: HandleType;
  var s##1: DatatypeType;
  var P##1: HandleType;
  var _k##1: Box;
  var s##2: DatatypeType;
  var P##2: HandleType;
  var $initHeapForallStmt#1: Heap;

    // AddMethodImpl: Filter_AlwaysAnother#, Impl$$_module.__default.Filter__AlwaysAnother_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(131,15): initial state"} true;
    assume $IsA#_module.Stream(s#1);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: Box, $ih#s0#0: DatatypeType, $ih#P0#0: HandleType :: 
      $Is($ih#s0#0, Tclass._module.Stream(_module._default.Filter_AlwaysAnother#$_T0))
           && $Is($ih#P0#0, 
            Tclass._System.___hTotalFunc1(_module._default.Filter_AlwaysAnother#$_T0, TBool))
           && _module.__default.AlwaysAnother(_module._default.Filter_AlwaysAnother#$_T0, $LS($LZ), $ih#s0#0, $ih#P0#0)
           && (ORD#Less($ih#_k0#0, _k#0)
             || ($ih#_k0#0 == _k#0
               && 
              0
                 <= _module.__default.Next(_module._default.Filter_AlwaysAnother#$_T0, $ih#s0#0, $ih#P0#0)
               && _module.__default.Next(_module._default.Filter_AlwaysAnother#$_T0, $ih#s0#0, $ih#P0#0)
                 < _module.__default.Next(_module._default.Filter_AlwaysAnother#$_T0, s#1, P#1)))
         ==> _module.__default.AllP_h(_module._default.Filter_AlwaysAnother#$_T0, 
          $LS($LZ), 
          $ih#_k0#0, 
          _module.__default.Filter(_module._default.Filter_AlwaysAnother#$_T0, $LS($LZ), $ih#s0#0, $ih#P0#0), 
          $ih#P0#0));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(135,1)
    assume true;
    if (0 < ORD#Offset(_k#0))
    {
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(136,3)
        assume _module.Stream.Cons_q(s#1);
        assume _module.Stream.Cons_q(s#1);
        if ($Unbox(Apply1(_module._default.Filter_AlwaysAnother#$_T0, 
            TBool, 
            $Heap, 
            P#1, 
            _module.Stream.head(s#1))): bool)
        {
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(137,25)
            // TrCallStmt: Before ProcessCallStmt
            assert ORD#IsNat(Lit(ORD#FromNat(1)));
            assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
            assume true;
            // ProcessCallStmt: CheckSubrange
            _k##0 := ORD#Minus(_k#0, ORD#FromNat(1));
            assume _module.Stream.Cons_q(s#1);
            assume _module.Stream.Cons_q(s#1);
            // ProcessCallStmt: CheckSubrange
            s##0 := _module.Stream.tail(s#1);
            assume true;
            // ProcessCallStmt: CheckSubrange
            P##0 := P#1;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0
                 <= _module.__default.Next(_module._default.Filter_AlwaysAnother#$_T0, s#1, P#1)
               || ORD#Less(_k##0, _k#0)
               || _module.__default.Next(_module._default.Filter_AlwaysAnother#$_T0, s##0, P##0)
                 == _module.__default.Next(_module._default.Filter_AlwaysAnother#$_T0, s#1, P#1);
            assert ORD#Less(_k##0, _k#0)
               || (_k##0 == _k#0
                 && _module.__default.Next(_module._default.Filter_AlwaysAnother#$_T0, s##0, P##0)
                   < _module.__default.Next(_module._default.Filter_AlwaysAnother#$_T0, s#1, P#1));
            // ProcessCallStmt: Make the call
            call CoCall$$_module.__default.Filter__AlwaysAnother_h(_module._default.Filter_AlwaysAnother#$_T0, _k##0, s##0, P##0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(137,35)"} true;
        }
        else
        {
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(139,14)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            s##1 := s#1;
            assume true;
            // ProcessCallStmt: CheckSubrange
            P##1 := P#1;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call Call$$_module.__default.NextLemma(_module._default.Filter_AlwaysAnother#$_T0, s##1, P##1);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(139,19)"} true;
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(140,30)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            _k##1 := _k#0;
            assume _module.Stream.Cons_q(s#1);
            assume _module.Stream.Cons_q(s#1);
            // ProcessCallStmt: CheckSubrange
            s##2 := _module.Stream.tail(s#1);
            assume true;
            // ProcessCallStmt: CheckSubrange
            P##2 := P#1;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0
                 <= _module.__default.Next(_module._default.Filter_AlwaysAnother#$_T0, s#1, P#1)
               || ORD#Less(_k##1, _k#0)
               || _module.__default.Next(_module._default.Filter_AlwaysAnother#$_T0, s##2, P##2)
                 == _module.__default.Next(_module._default.Filter_AlwaysAnother#$_T0, s#1, P#1);
            assert ORD#Less(_k##1, _k#0)
               || (_k##1 == _k#0
                 && _module.__default.Next(_module._default.Filter_AlwaysAnother#$_T0, s##2, P##2)
                   < _module.__default.Next(_module._default.Filter_AlwaysAnother#$_T0, s#1, P#1));
            // ProcessCallStmt: Make the call
            call CoCall$$_module.__default.Filter__AlwaysAnother_h(_module._default.Filter_AlwaysAnother#$_T0, _k##1, s##2, P##2);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(140,40)"} true;
        }
    }
    else
    {
        // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(131,16)
        $initHeapForallStmt#1 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#1 == $Heap;
        assume (forall _k'#2: Box, s#2: DatatypeType, P#2: HandleType :: 
          $Is(s#2, Tclass._module.Stream(_module._default.Filter_AlwaysAnother#$_T0))
               && $Is(P#2, 
                Tclass._System.___hTotalFunc1(_module._default.Filter_AlwaysAnother#$_T0, TBool))
               && 
              ORD#Less(_k'#2, _k#0)
               && _module.__default.AlwaysAnother(_module._default.Filter_AlwaysAnother#$_T0, $LS($LZ), s#2, P#2)
             ==> _module.__default.AllP_h(_module._default.Filter_AlwaysAnother#$_T0, 
              $LS($LZ), 
              _k'#2, 
              _module.__default.Filter(_module._default.Filter_AlwaysAnother#$_T0, $LS($LZ), s#2, P#2), 
              P#2));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(131,15)"} true;
    }
}



procedure CheckWellformed$$_module.__default.Filter__IsSubStream(_module._default.Filter_IsSubStream$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Filter_IsSubStream$_T0))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.Filter_IsSubStream$_T0), $Heap)
         && $IsA#_module.Stream(s#0), 
    P#0: HandleType
       where $Is(P#0, 
          Tclass._System.___hTotalFunc1(_module._default.Filter_IsSubStream$_T0, TBool))
         && $IsAlloc(P#0, 
          Tclass._System.___hTotalFunc1(_module._default.Filter_IsSubStream$_T0, TBool), 
          $Heap));
  free requires 24 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Filter__IsSubStream(_module._default.Filter_IsSubStream$_T0: Ty, s#0: DatatypeType, P#0: HandleType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##s#0: DatatypeType;
  var ##P#0: HandleType;
  var ##s#1: DatatypeType;
  var ##P#1: HandleType;
  var ##s#2: DatatypeType;
  var ##P#2: HandleType;
  var ##s#3: DatatypeType;
  var ##u#0: DatatypeType;

    // AddMethodImpl: Filter_IsSubStream, CheckWellformed$$_module.__default.Filter__IsSubStream
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(143,15): initial state"} true;
    ##s#0 := s#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#0, Tclass._module.Stream(_module._default.Filter_IsSubStream$_T0), $Heap);
    ##P#0 := P#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##P#0, 
      Tclass._System.___hTotalFunc1(_module._default.Filter_IsSubStream$_T0, TBool), 
      $Heap);
    assume _module.__default.AlwaysAnother#canCall(_module._default.Filter_IsSubStream$_T0, s#0, P#0);
    assume _module.__default.AlwaysAnother(_module._default.Filter_IsSubStream$_T0, $LS($LZ), s#0, P#0);
    ##s#1 := s#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#1, Tclass._module.Stream(_module._default.Filter_IsSubStream$_T0), $Heap);
    ##P#1 := P#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##P#1, 
      Tclass._System.___hTotalFunc1(_module._default.Filter_IsSubStream$_T0, TBool), 
      $Heap);
    assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.Filter_IsSubStream$_T0, ##s#1, ##P#1)
       ==> _module.__default.AlwaysAnother(_module._default.Filter_IsSubStream$_T0, $LS($LZ), ##s#1, ##P#1)
         || (_module.__default.IsAnother#canCall(_module._default.Filter_IsSubStream$_T0, ##s#1, ##P#1)
           ==> _module.__default.IsAnother(_module._default.Filter_IsSubStream$_T0, ##s#1, ##P#1)
             || (exists n#0: int :: 
              { _module.__default.Tail(_module._default.Filter_IsSubStream$_T0, $LS($LZ), ##s#1, n#0) } 
              LitInt(0) <= n#0
                 && 
                LitInt(0) <= n#0
                 && $Unbox(Apply1(_module._default.Filter_IsSubStream$_T0, 
                    TBool, 
                    $Heap, 
                    ##P#1, 
                    _module.Stream.head(_module.__default.Tail(_module._default.Filter_IsSubStream$_T0, $LS($LZ), ##s#1, n#0)))): bool));
    assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.Filter_IsSubStream$_T0, ##s#1, ##P#1)
       ==> _module.__default.AlwaysAnother(_module._default.Filter_IsSubStream$_T0, $LS($LZ), ##s#1, ##P#1)
         || _module.__default.AlwaysAnother(_module._default.Filter_IsSubStream$_T0, 
          $LS($LS($LZ)), 
          _module.Stream.tail(##s#1), 
          ##P#1);
    assume _module.__default.AlwaysAnother(_module._default.Filter_IsSubStream$_T0, $LS($LZ), ##s#1, ##P#1);
    assume _module.__default.Next#canCall(_module._default.Filter_IsSubStream$_T0, s#0, P#0);
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(145,21): post-state"} true;
    ##s#2 := s#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#2, Tclass._module.Stream(_module._default.Filter_IsSubStream$_T0), $Heap);
    ##P#2 := P#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##P#2, 
      Tclass._System.___hTotalFunc1(_module._default.Filter_IsSubStream$_T0, TBool), 
      $Heap);
    assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.Filter_IsSubStream$_T0, ##s#2, ##P#2)
       ==> _module.__default.AlwaysAnother(_module._default.Filter_IsSubStream$_T0, $LS($LZ), ##s#2, ##P#2)
         || (_module.__default.IsAnother#canCall(_module._default.Filter_IsSubStream$_T0, ##s#2, ##P#2)
           ==> _module.__default.IsAnother(_module._default.Filter_IsSubStream$_T0, ##s#2, ##P#2)
             || (exists n#1: int :: 
              { _module.__default.Tail(_module._default.Filter_IsSubStream$_T0, $LS($LZ), ##s#2, n#1) } 
              LitInt(0) <= n#1
                 && 
                LitInt(0) <= n#1
                 && $Unbox(Apply1(_module._default.Filter_IsSubStream$_T0, 
                    TBool, 
                    $Heap, 
                    ##P#2, 
                    _module.Stream.head(_module.__default.Tail(_module._default.Filter_IsSubStream$_T0, $LS($LZ), ##s#2, n#1)))): bool));
    assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.Filter_IsSubStream$_T0, ##s#2, ##P#2)
       ==> _module.__default.AlwaysAnother(_module._default.Filter_IsSubStream$_T0, $LS($LZ), ##s#2, ##P#2)
         || _module.__default.AlwaysAnother(_module._default.Filter_IsSubStream$_T0, 
          $LS($LS($LZ)), 
          _module.Stream.tail(##s#2), 
          ##P#2);
    assume _module.__default.AlwaysAnother(_module._default.Filter_IsSubStream$_T0, $LS($LZ), ##s#2, ##P#2);
    assume _module.__default.Filter#canCall(_module._default.Filter_IsSubStream$_T0, s#0, P#0);
    assume _module.Stream.Cons_q(_module.__default.Filter(_module._default.Filter_IsSubStream$_T0, $LS($LZ), s#0, P#0));
    ##s#3 := _module.__default.Filter(_module._default.Filter_IsSubStream$_T0, $LS($LZ), s#0, P#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#3, Tclass._module.Stream(_module._default.Filter_IsSubStream$_T0), $Heap);
    ##u#0 := s#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##u#0, Tclass._module.Stream(_module._default.Filter_IsSubStream$_T0), $Heap);
    assume _module.__default.IsSubStream#canCall(_module._default.Filter_IsSubStream$_T0, 
      _module.__default.Filter(_module._default.Filter_IsSubStream$_T0, $LS($LZ), s#0, P#0), 
      s#0);
    assume _module.__default.IsSubStream(_module._default.Filter_IsSubStream$_T0, 
      $LS($LZ), 
      _module.__default.Filter(_module._default.Filter_IsSubStream$_T0, $LS($LZ), s#0, P#0), 
      s#0);
}



procedure Call$$_module.__default.Filter__IsSubStream(_module._default.Filter_IsSubStream$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Filter_IsSubStream$_T0))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.Filter_IsSubStream$_T0), $Heap)
         && $IsA#_module.Stream(s#0), 
    P#0: HandleType
       where $Is(P#0, 
          Tclass._System.___hTotalFunc1(_module._default.Filter_IsSubStream$_T0, TBool))
         && $IsAlloc(P#0, 
          Tclass._System.___hTotalFunc1(_module._default.Filter_IsSubStream$_T0, TBool), 
          $Heap));
  // user-defined preconditions
  requires _module.__default.AlwaysAnother#canCall(_module._default.Filter_IsSubStream$_T0, s#0, P#0)
     ==> _module.__default.AlwaysAnother(_module._default.Filter_IsSubStream$_T0, $LS($LZ), s#0, P#0)
       || (_module.__default.IsAnother#canCall(_module._default.Filter_IsSubStream$_T0, s#0, P#0)
         ==> _module.__default.IsAnother(_module._default.Filter_IsSubStream$_T0, s#0, P#0)
           || (exists n#2: int :: 
            { _module.__default.Tail(_module._default.Filter_IsSubStream$_T0, $LS($LZ), s#0, n#2) } 
            LitInt(0) <= n#2
               && 
              LitInt(0) <= n#2
               && $Unbox(Apply1(_module._default.Filter_IsSubStream$_T0, 
                  TBool, 
                  $Heap, 
                  P#0, 
                  _module.Stream.head(_module.__default.Tail(_module._default.Filter_IsSubStream$_T0, $LS($LZ), s#0, n#2)))): bool));
  requires _module.__default.AlwaysAnother#canCall(_module._default.Filter_IsSubStream$_T0, s#0, P#0)
     ==> _module.__default.AlwaysAnother(_module._default.Filter_IsSubStream$_T0, $LS($LZ), s#0, P#0)
       || _module.__default.AlwaysAnother(_module._default.Filter_IsSubStream$_T0, 
        $LS($LS($LZ)), 
        _module.Stream.tail(s#0), 
        P#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Filter#canCall(_module._default.Filter_IsSubStream$_T0, s#0, P#0)
     && _module.__default.IsSubStream#canCall(_module._default.Filter_IsSubStream$_T0, 
      _module.__default.Filter(_module._default.Filter_IsSubStream$_T0, $LS($LZ), s#0, P#0), 
      s#0);
  free ensures _module.__default.IsSubStream#canCall(_module._default.Filter_IsSubStream$_T0, 
      _module.__default.Filter(_module._default.Filter_IsSubStream$_T0, $LS($LZ), s#0, P#0), 
      s#0)
     && 
    _module.__default.IsSubStream(_module._default.Filter_IsSubStream$_T0, 
      $LS($LZ), 
      _module.__default.Filter(_module._default.Filter_IsSubStream$_T0, $LS($LZ), s#0, P#0), 
      s#0)
     && 
    _module.__default.In(_module._default.Filter_IsSubStream$_T0, 
      _module.Stream.head(_module.__default.Filter(_module._default.Filter_IsSubStream$_T0, $LS($LZ), s#0, P#0)), 
      s#0)
     && _module.__default.IsSubStream(_module._default.Filter_IsSubStream$_T0, 
      $LS($LZ), 
      _module.Stream.tail(_module.__default.Filter(_module._default.Filter_IsSubStream$_T0, $LS($LZ), s#0, P#0)), 
      s#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, s#1, P#1} CoCall$$_module.__default.Filter__IsSubStream_h(_module._default.Filter_IsSubStream#$_T0: Ty, 
    _k#0: int where LitInt(0) <= _k#0, 
    s#1: DatatypeType
       where $Is(s#1, Tclass._module.Stream(_module._default.Filter_IsSubStream#$_T0))
         && $IsAlloc(s#1, Tclass._module.Stream(_module._default.Filter_IsSubStream#$_T0), $Heap)
         && $IsA#_module.Stream(s#1), 
    P#1: HandleType
       where $Is(P#1, 
          Tclass._System.___hTotalFunc1(_module._default.Filter_IsSubStream#$_T0, TBool))
         && $IsAlloc(P#1, 
          Tclass._System.___hTotalFunc1(_module._default.Filter_IsSubStream#$_T0, TBool), 
          $Heap));
  // user-defined preconditions
  requires _module.__default.AlwaysAnother#canCall(_module._default.Filter_IsSubStream#$_T0, s#1, P#1)
     ==> _module.__default.AlwaysAnother(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1)
       || (_module.__default.IsAnother#canCall(_module._default.Filter_IsSubStream#$_T0, s#1, P#1)
         ==> _module.__default.IsAnother(_module._default.Filter_IsSubStream#$_T0, s#1, P#1)
           || (exists n#4: int :: 
            { _module.__default.Tail(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, n#4) } 
            LitInt(0) <= n#4
               && 
              LitInt(0) <= n#4
               && $Unbox(Apply1(_module._default.Filter_IsSubStream#$_T0, 
                  TBool, 
                  $Heap, 
                  P#1, 
                  _module.Stream.head(_module.__default.Tail(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, n#4)))): bool));
  requires _module.__default.AlwaysAnother#canCall(_module._default.Filter_IsSubStream#$_T0, s#1, P#1)
     ==> _module.__default.AlwaysAnother(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1)
       || _module.__default.AlwaysAnother(_module._default.Filter_IsSubStream#$_T0, 
        $LS($LS($LZ)), 
        _module.Stream.tail(s#1), 
        P#1);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Filter#canCall(_module._default.Filter_IsSubStream#$_T0, s#1, P#1)
     && _module.__default.IsSubStream_h#canCall(_module._default.Filter_IsSubStream#$_T0, 
      _k#0, 
      _module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1), 
      s#1);
  free ensures _module.__default.IsSubStream_h#canCall(_module._default.Filter_IsSubStream#$_T0, 
      _k#0, 
      _module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1), 
      s#1)
     && 
    _module.__default.IsSubStream_h(_module._default.Filter_IsSubStream#$_T0, 
      $LS($LZ), 
      _k#0, 
      _module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1), 
      s#1)
     && (0 < _k#0
       ==> _module.__default.In(_module._default.Filter_IsSubStream#$_T0, 
          _module.Stream.head(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1)), 
          s#1)
         && _module.__default.IsSubStream_h(_module._default.Filter_IsSubStream#$_T0, 
          $LS($LZ), 
          _k#0 - 1, 
          _module.Stream.tail(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1)), 
          s#1));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, s#1, P#1} Impl$$_module.__default.Filter__IsSubStream_h(_module._default.Filter_IsSubStream#$_T0: Ty, 
    _k#0: int where LitInt(0) <= _k#0, 
    s#1: DatatypeType
       where $Is(s#1, Tclass._module.Stream(_module._default.Filter_IsSubStream#$_T0))
         && $IsAlloc(s#1, Tclass._module.Stream(_module._default.Filter_IsSubStream#$_T0), $Heap)
         && $IsA#_module.Stream(s#1), 
    P#1: HandleType
       where $Is(P#1, 
          Tclass._System.___hTotalFunc1(_module._default.Filter_IsSubStream#$_T0, TBool))
         && $IsAlloc(P#1, 
          Tclass._System.___hTotalFunc1(_module._default.Filter_IsSubStream#$_T0, TBool), 
          $Heap))
   returns ($_reverifyPost: bool);
  free requires 25 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.__default.AlwaysAnother#canCall(_module._default.Filter_IsSubStream#$_T0, s#1, P#1)
     && 
    _module.__default.AlwaysAnother(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1)
     && 
    _module.__default.IsAnother(_module._default.Filter_IsSubStream#$_T0, s#1, P#1)
     && _module.__default.AlwaysAnother(_module._default.Filter_IsSubStream#$_T0, 
      $LS($LZ), 
      _module.Stream.tail(s#1), 
      P#1);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Filter#canCall(_module._default.Filter_IsSubStream#$_T0, s#1, P#1)
     && _module.__default.IsSubStream_h#canCall(_module._default.Filter_IsSubStream#$_T0, 
      _k#0, 
      _module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1), 
      s#1);
  ensures _module.__default.IsSubStream_h#canCall(_module._default.Filter_IsSubStream#$_T0, 
      _k#0, 
      _module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1), 
      s#1)
     ==> _module.__default.IsSubStream_h(_module._default.Filter_IsSubStream#$_T0, 
        $LS($LZ), 
        _k#0, 
        _module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1), 
        s#1)
       || (0 < _k#0
         ==> 
        _module.__default.In#canCall(_module._default.Filter_IsSubStream#$_T0, 
          _module.Stream.head(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1)), 
          s#1)
         ==> _module.__default.In(_module._default.Filter_IsSubStream#$_T0, 
            _module.Stream.head(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1)), 
            s#1)
           || (exists n#7: int :: 
            { _module.__default.Tail(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, n#7) } 
            LitInt(0) <= n#7
               && 
              LitInt(0) <= n#7
               && _module.Stream.head(_module.__default.Tail(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, n#7))
                 == _module.Stream.head(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1))));
  ensures _module.__default.IsSubStream_h#canCall(_module._default.Filter_IsSubStream#$_T0, 
      _k#0, 
      _module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1), 
      s#1)
     ==> _module.__default.IsSubStream_h(_module._default.Filter_IsSubStream#$_T0, 
        $LS($LZ), 
        _k#0, 
        _module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1), 
        s#1)
       || (0 < _k#0
         ==> _module.__default.IsSubStream_h(_module._default.Filter_IsSubStream#$_T0, 
          $LS($LS($LZ)), 
          _k#0 - 1, 
          _module.Stream.tail(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LS($LZ)), s#1, P#1)), 
          s#1));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0, s#1, P#1} Impl$$_module.__default.Filter__IsSubStream_h(_module._default.Filter_IsSubStream#$_T0: Ty, 
    _k#0: int, 
    s#1: DatatypeType, 
    P#1: HandleType)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var ##s#4: DatatypeType;
  var ##P#3: HandleType;
  var ##_k#0: int;
  var ##s#5: DatatypeType;
  var ##u#1: DatatypeType;
  var s##0: DatatypeType;
  var ##s#6: DatatypeType;
  var ##P#4: HandleType;
  var u##0: DatatypeType;
  var k##0: int;
  var ##s#7: DatatypeType;
  var ##P#5: HandleType;
  var ##_k#1: int;
  var ##s#8: DatatypeType;
  var ##u#2: DatatypeType;
  var ##s#9: DatatypeType;
  var ##P#6: HandleType;
  var ##_k#2: int;
  var ##s#10: DatatypeType;
  var ##u#3: DatatypeType;
  var ##s#11: DatatypeType;
  var ##P#7: HandleType;
  var ##_k#3: int;
  var ##s#12: DatatypeType;
  var ##u#4: DatatypeType;
  var _k##0: int;
  var s##1: DatatypeType;
  var P##0: HandleType;
  var ##s#13: DatatypeType;
  var ##P#8: HandleType;
  var ##_k#4: int;
  var ##s#14: DatatypeType;
  var ##u#5: DatatypeType;
  var ##x#0: Box;
  var ##s#15: DatatypeType;
  var ##s#16: DatatypeType;
  var ##n#0: int;
  var n#15: int;
  var ##s#17: DatatypeType;
  var ##n#1: int;
  var ##s#18: DatatypeType;
  var ##P#9: HandleType;
  var ##x#1: Box;
  var ##s#19: DatatypeType;
  var ##s#20: DatatypeType;
  var ##P#10: HandleType;
  var ##s#21: DatatypeType;
  var ##P#11: HandleType;
  var ##x#2: Box;
  var ##s#22: DatatypeType;
  var s##2: DatatypeType;
  var P##1: HandleType;
  var s##3: DatatypeType;
  var ##s#23: DatatypeType;
  var ##P#12: HandleType;
  var u##1: DatatypeType;
  var k##1: int;

    // AddMethodImpl: Filter_IsSubStream#, Impl$$_module.__default.Filter__IsSubStream_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(143,15): initial state"} true;
    assume $IsA#_module.Stream(s#1);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: int, $ih#s0#0: DatatypeType, $ih#P0#0: HandleType :: 
      LitInt(0) <= $ih#_k0#0
           && $Is($ih#s0#0, Tclass._module.Stream(_module._default.Filter_IsSubStream#$_T0))
           && $Is($ih#P0#0, 
            Tclass._System.___hTotalFunc1(_module._default.Filter_IsSubStream#$_T0, TBool))
           && _module.__default.AlwaysAnother(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), $ih#s0#0, $ih#P0#0)
           && ((0 <= $ih#_k0#0 && $ih#_k0#0 < _k#0)
             || ($ih#_k0#0 == _k#0
               && 
              0
                 <= _module.__default.Next(_module._default.Filter_IsSubStream#$_T0, $ih#s0#0, $ih#P0#0)
               && _module.__default.Next(_module._default.Filter_IsSubStream#$_T0, $ih#s0#0, $ih#P0#0)
                 < _module.__default.Next(_module._default.Filter_IsSubStream#$_T0, s#1, P#1)))
         ==> _module.__default.IsSubStream_h(_module._default.Filter_IsSubStream#$_T0, 
          $LS($LZ), 
          $ih#_k0#0, 
          _module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), $ih#s0#0, $ih#P0#0), 
          $ih#s0#0));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(147,1)
    assume true;
    if (0 < _k#0)
    {
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(148,3)
        assume _module.Stream.Cons_q(s#1);
        assume _module.Stream.Cons_q(s#1);
        if ($Unbox(Apply1(_module._default.Filter_IsSubStream#$_T0, 
            TBool, 
            $Heap, 
            P#1, 
            _module.Stream.head(s#1))): bool)
        {
            // ----- calc statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(150,5)
            // Assume Fuel Constant
            if (*)
            {
                // ----- assert wf[initial] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(150,5)
                assume true;
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(150,5)
                assume true;
                // ----- Hint0 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(150,5)
                // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(152,29)
                // TrCallStmt: Before ProcessCallStmt
                assume true;
                // ProcessCallStmt: CheckSubrange
                assert $Is(_k#0 - 1, Tclass._System.nat());
                _k##0 := _k#0 - 1;
                assume _module.Stream.Cons_q(s#1);
                assume _module.Stream.Cons_q(s#1);
                // ProcessCallStmt: CheckSubrange
                s##1 := _module.Stream.tail(s#1);
                assume true;
                // ProcessCallStmt: CheckSubrange
                P##0 := P#1;
                assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                // ProcessCallStmt: Make the call
                call CoCall$$_module.__default.Filter__IsSubStream_h(_module._default.Filter_IsSubStream#$_T0, _k##0, s##1, P##0);
                // TrCallStmt: After ProcessCallStmt
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(152,39)"} true;
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(150,5)
                assume _module.Stream.Cons_q(s#1);
                ##s#13 := _module.Stream.tail(s#1);
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#13, Tclass._module.Stream(_module._default.Filter_IsSubStream#$_T0), $Heap);
                ##P#8 := P#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##P#8, 
                  Tclass._System.___hTotalFunc1(_module._default.Filter_IsSubStream#$_T0, TBool), 
                  $Heap);
                assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.Filter_IsSubStream#$_T0, ##s#13, ##P#8)
                   ==> _module.__default.AlwaysAnother(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), ##s#13, ##P#8)
                     || (_module.__default.IsAnother#canCall(_module._default.Filter_IsSubStream#$_T0, ##s#13, ##P#8)
                       ==> _module.__default.IsAnother(_module._default.Filter_IsSubStream#$_T0, ##s#13, ##P#8)
                         || (exists n#14: int :: 
                          { _module.__default.Tail(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), ##s#13, n#14) } 
                          LitInt(0) <= n#14
                             && 
                            LitInt(0) <= n#14
                             && $Unbox(Apply1(_module._default.Filter_IsSubStream#$_T0, 
                                TBool, 
                                $Heap, 
                                ##P#8, 
                                _module.Stream.head(_module.__default.Tail(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), ##s#13, n#14)))): bool));
                assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.Filter_IsSubStream#$_T0, ##s#13, ##P#8)
                   ==> _module.__default.AlwaysAnother(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), ##s#13, ##P#8)
                     || _module.__default.AlwaysAnother(_module._default.Filter_IsSubStream#$_T0, 
                      $LS($LS($LZ)), 
                      _module.Stream.tail(##s#13), 
                      ##P#8);
                assume _module.__default.Filter#canCall(_module._default.Filter_IsSubStream#$_T0, _module.Stream.tail(s#1), P#1);
                assume _module.Stream.Cons_q(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, 
                    $LS($LZ), 
                    _module.Stream.tail(s#1), 
                    P#1));
                assume _module.Stream.Cons_q(s#1);
                assert $Is(_k#0 - 1, Tclass._System.nat());
                ##_k#4 := _k#0 - 1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##_k#4, Tclass._System.nat(), $Heap);
                ##s#14 := _module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, 
                  $LS($LZ), 
                  _module.Stream.tail(s#1), 
                  P#1);
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#14, Tclass._module.Stream(_module._default.Filter_IsSubStream#$_T0), $Heap);
                ##u#5 := _module.Stream.tail(s#1);
                // assume allocatedness for argument to function
                assume $IsAlloc(##u#5, Tclass._module.Stream(_module._default.Filter_IsSubStream#$_T0), $Heap);
                assume _module.__default.IsSubStream_h#canCall(_module._default.Filter_IsSubStream#$_T0, 
                  _k#0 - 1, 
                  _module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, 
                    $LS($LZ), 
                    _module.Stream.tail(s#1), 
                    P#1), 
                  _module.Stream.tail(s#1));
                assume _module.Stream.Cons_q(s#1)
                   && _module.__default.Filter#canCall(_module._default.Filter_IsSubStream#$_T0, _module.Stream.tail(s#1), P#1)
                   && _module.Stream.Cons_q(s#1)
                   && _module.__default.IsSubStream_h#canCall(_module._default.Filter_IsSubStream#$_T0, 
                    _k#0 - 1, 
                    _module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, 
                      $LS($LZ), 
                      _module.Stream.tail(s#1), 
                      P#1), 
                    _module.Stream.tail(s#1));
                // ----- assert line0 == line1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(150,5)
                assert {:subsumption 0} Lit(true)
                   == _module.__default.IsSubStream_h(_module._default.Filter_IsSubStream#$_T0, 
                    $LS($LS($LZ)), 
                    _k#0 - 1, 
                    _module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, 
                      $LS($LS($LZ)), 
                      _module.Stream.tail(s#1), 
                      P#1), 
                    _module.Stream.tail(s#1));
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(150,5)
                assume _module.Stream.Cons_q(s#1);
                ##s#9 := _module.Stream.tail(s#1);
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#9, Tclass._module.Stream(_module._default.Filter_IsSubStream#$_T0), $Heap);
                ##P#6 := P#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##P#6, 
                  Tclass._System.___hTotalFunc1(_module._default.Filter_IsSubStream#$_T0, TBool), 
                  $Heap);
                assume {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.Filter_IsSubStream#$_T0, ##s#9, ##P#6)
                   ==> _module.__default.AlwaysAnother(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), ##s#9, ##P#6)
                     || (_module.__default.IsAnother#canCall(_module._default.Filter_IsSubStream#$_T0, ##s#9, ##P#6)
                       ==> _module.__default.IsAnother(_module._default.Filter_IsSubStream#$_T0, ##s#9, ##P#6)
                         || (exists n#12: int :: 
                          { _module.__default.Tail(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), ##s#9, n#12) } 
                          LitInt(0) <= n#12
                             && 
                            LitInt(0) <= n#12
                             && $Unbox(Apply1(_module._default.Filter_IsSubStream#$_T0, 
                                TBool, 
                                $Heap, 
                                ##P#6, 
                                _module.Stream.head(_module.__default.Tail(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), ##s#9, n#12)))): bool));
                assume {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.Filter_IsSubStream#$_T0, ##s#9, ##P#6)
                   ==> _module.__default.AlwaysAnother(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), ##s#9, ##P#6)
                     || _module.__default.AlwaysAnother(_module._default.Filter_IsSubStream#$_T0, 
                      $LS($LS($LZ)), 
                      _module.Stream.tail(##s#9), 
                      ##P#6);
                assume _module.__default.Filter#canCall(_module._default.Filter_IsSubStream#$_T0, _module.Stream.tail(s#1), P#1);
                assume _module.Stream.Cons_q(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, 
                    $LS($LZ), 
                    _module.Stream.tail(s#1), 
                    P#1));
                assume _module.Stream.Cons_q(s#1);
                assume $Is(_k#0 - 1, Tclass._System.nat());
                ##_k#2 := _k#0 - 1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##_k#2, Tclass._System.nat(), $Heap);
                ##s#10 := _module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, 
                  $LS($LZ), 
                  _module.Stream.tail(s#1), 
                  P#1);
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#10, Tclass._module.Stream(_module._default.Filter_IsSubStream#$_T0), $Heap);
                ##u#3 := _module.Stream.tail(s#1);
                // assume allocatedness for argument to function
                assume $IsAlloc(##u#3, Tclass._module.Stream(_module._default.Filter_IsSubStream#$_T0), $Heap);
                assume _module.__default.IsSubStream_h#canCall(_module._default.Filter_IsSubStream#$_T0, 
                  _k#0 - 1, 
                  _module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, 
                    $LS($LZ), 
                    _module.Stream.tail(s#1), 
                    P#1), 
                  _module.Stream.tail(s#1));
                assume _module.Stream.Cons_q(s#1)
                   && _module.__default.Filter#canCall(_module._default.Filter_IsSubStream#$_T0, _module.Stream.tail(s#1), P#1)
                   && _module.Stream.Cons_q(s#1)
                   && _module.__default.IsSubStream_h#canCall(_module._default.Filter_IsSubStream#$_T0, 
                    _k#0 - 1, 
                    _module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, 
                      $LS($LZ), 
                      _module.Stream.tail(s#1), 
                      P#1), 
                    _module.Stream.tail(s#1));
                // ----- Hint1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(150,5)
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(150,5)
                ##s#11 := s#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#11, Tclass._module.Stream(_module._default.Filter_IsSubStream#$_T0), $Heap);
                ##P#7 := P#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##P#7, 
                  Tclass._System.___hTotalFunc1(_module._default.Filter_IsSubStream#$_T0, TBool), 
                  $Heap);
                assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.Filter_IsSubStream#$_T0, ##s#11, ##P#7)
                   ==> _module.__default.AlwaysAnother(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), ##s#11, ##P#7)
                     || (_module.__default.IsAnother#canCall(_module._default.Filter_IsSubStream#$_T0, ##s#11, ##P#7)
                       ==> _module.__default.IsAnother(_module._default.Filter_IsSubStream#$_T0, ##s#11, ##P#7)
                         || (exists n#13: int :: 
                          { _module.__default.Tail(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), ##s#11, n#13) } 
                          LitInt(0) <= n#13
                             && 
                            LitInt(0) <= n#13
                             && $Unbox(Apply1(_module._default.Filter_IsSubStream#$_T0, 
                                TBool, 
                                $Heap, 
                                ##P#7, 
                                _module.Stream.head(_module.__default.Tail(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), ##s#11, n#13)))): bool));
                assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.Filter_IsSubStream#$_T0, ##s#11, ##P#7)
                   ==> _module.__default.AlwaysAnother(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), ##s#11, ##P#7)
                     || _module.__default.AlwaysAnother(_module._default.Filter_IsSubStream#$_T0, 
                      $LS($LS($LZ)), 
                      _module.Stream.tail(##s#11), 
                      ##P#7);
                assume _module.__default.Filter#canCall(_module._default.Filter_IsSubStream#$_T0, s#1, P#1);
                assume _module.Stream.Cons_q(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1));
                assume _module.Stream.Cons_q(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1));
                assume _module.Stream.Cons_q(s#1);
                assert $Is(_k#0 - 1, Tclass._System.nat());
                ##_k#3 := _k#0 - 1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##_k#3, Tclass._System.nat(), $Heap);
                ##s#12 := _module.Stream.tail(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1));
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#12, Tclass._module.Stream(_module._default.Filter_IsSubStream#$_T0), $Heap);
                ##u#4 := _module.Stream.tail(s#1);
                // assume allocatedness for argument to function
                assume $IsAlloc(##u#4, Tclass._module.Stream(_module._default.Filter_IsSubStream#$_T0), $Heap);
                assume _module.__default.IsSubStream_h#canCall(_module._default.Filter_IsSubStream#$_T0, 
                  _k#0 - 1, 
                  _module.Stream.tail(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1)), 
                  _module.Stream.tail(s#1));
                assume _module.__default.Filter#canCall(_module._default.Filter_IsSubStream#$_T0, s#1, P#1)
                   && _module.Stream.Cons_q(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1))
                   && _module.Stream.Cons_q(s#1)
                   && _module.__default.IsSubStream_h#canCall(_module._default.Filter_IsSubStream#$_T0, 
                    _k#0 - 1, 
                    _module.Stream.tail(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1)), 
                    _module.Stream.tail(s#1));
                // ----- assert line1 == line2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(150,5)
                assert {:subsumption 0} _module.__default.IsSubStream_h(_module._default.Filter_IsSubStream#$_T0, 
                    $LS($LS($LZ)), 
                    _k#0 - 1, 
                    _module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, 
                      $LS($LS($LZ)), 
                      _module.Stream.tail(s#1), 
                      P#1), 
                    _module.Stream.tail(s#1))
                   == _module.__default.IsSubStream_h(_module._default.Filter_IsSubStream#$_T0, 
                    $LS($LS($LZ)), 
                    _k#0 - 1, 
                    _module.Stream.tail(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LS($LZ)), s#1, P#1)), 
                    _module.Stream.tail(s#1));
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(150,5)
                ##s#4 := s#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#4, Tclass._module.Stream(_module._default.Filter_IsSubStream#$_T0), $Heap);
                ##P#3 := P#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##P#3, 
                  Tclass._System.___hTotalFunc1(_module._default.Filter_IsSubStream#$_T0, TBool), 
                  $Heap);
                assume {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.Filter_IsSubStream#$_T0, ##s#4, ##P#3)
                   ==> _module.__default.AlwaysAnother(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), ##s#4, ##P#3)
                     || (_module.__default.IsAnother#canCall(_module._default.Filter_IsSubStream#$_T0, ##s#4, ##P#3)
                       ==> _module.__default.IsAnother(_module._default.Filter_IsSubStream#$_T0, ##s#4, ##P#3)
                         || (exists n#8: int :: 
                          { _module.__default.Tail(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), ##s#4, n#8) } 
                          LitInt(0) <= n#8
                             && 
                            LitInt(0) <= n#8
                             && $Unbox(Apply1(_module._default.Filter_IsSubStream#$_T0, 
                                TBool, 
                                $Heap, 
                                ##P#3, 
                                _module.Stream.head(_module.__default.Tail(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), ##s#4, n#8)))): bool));
                assume {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.Filter_IsSubStream#$_T0, ##s#4, ##P#3)
                   ==> _module.__default.AlwaysAnother(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), ##s#4, ##P#3)
                     || _module.__default.AlwaysAnother(_module._default.Filter_IsSubStream#$_T0, 
                      $LS($LS($LZ)), 
                      _module.Stream.tail(##s#4), 
                      ##P#3);
                assume _module.__default.Filter#canCall(_module._default.Filter_IsSubStream#$_T0, s#1, P#1);
                assume _module.Stream.Cons_q(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1));
                assume _module.Stream.Cons_q(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1));
                assume _module.Stream.Cons_q(s#1);
                assume $Is(_k#0 - 1, Tclass._System.nat());
                ##_k#0 := _k#0 - 1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##_k#0, Tclass._System.nat(), $Heap);
                ##s#5 := _module.Stream.tail(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1));
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#5, Tclass._module.Stream(_module._default.Filter_IsSubStream#$_T0), $Heap);
                ##u#1 := _module.Stream.tail(s#1);
                // assume allocatedness for argument to function
                assume $IsAlloc(##u#1, Tclass._module.Stream(_module._default.Filter_IsSubStream#$_T0), $Heap);
                assume _module.__default.IsSubStream_h#canCall(_module._default.Filter_IsSubStream#$_T0, 
                  _k#0 - 1, 
                  _module.Stream.tail(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1)), 
                  _module.Stream.tail(s#1));
                assume _module.__default.Filter#canCall(_module._default.Filter_IsSubStream#$_T0, s#1, P#1)
                   && _module.Stream.Cons_q(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1))
                   && _module.Stream.Cons_q(s#1)
                   && _module.__default.IsSubStream_h#canCall(_module._default.Filter_IsSubStream#$_T0, 
                    _k#0 - 1, 
                    _module.Stream.tail(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1)), 
                    _module.Stream.tail(s#1));
                // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(150,5)
                assume _module.__default.IsSubStream_h(_module._default.Filter_IsSubStream#$_T0, 
                  $LS($LZ), 
                  _k#0 - 1, 
                  _module.Stream.tail(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1)), 
                  _module.Stream.tail(s#1));
                // ----- Hint2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(150,5)
                // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(156,31)
                // TrCallStmt: Before ProcessCallStmt
                ##s#6 := s#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#6, Tclass._module.Stream(_module._default.Filter_IsSubStream#$_T0), $Heap);
                ##P#4 := P#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##P#4, 
                  Tclass._System.___hTotalFunc1(_module._default.Filter_IsSubStream#$_T0, TBool), 
                  $Heap);
                assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.Filter_IsSubStream#$_T0, ##s#6, ##P#4)
                   ==> _module.__default.AlwaysAnother(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), ##s#6, ##P#4)
                     || (_module.__default.IsAnother#canCall(_module._default.Filter_IsSubStream#$_T0, ##s#6, ##P#4)
                       ==> _module.__default.IsAnother(_module._default.Filter_IsSubStream#$_T0, ##s#6, ##P#4)
                         || (exists n#9: int :: 
                          { _module.__default.Tail(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), ##s#6, n#9) } 
                          LitInt(0) <= n#9
                             && 
                            LitInt(0) <= n#9
                             && $Unbox(Apply1(_module._default.Filter_IsSubStream#$_T0, 
                                TBool, 
                                $Heap, 
                                ##P#4, 
                                _module.Stream.head(_module.__default.Tail(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), ##s#6, n#9)))): bool));
                assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.Filter_IsSubStream#$_T0, ##s#6, ##P#4)
                   ==> _module.__default.AlwaysAnother(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), ##s#6, ##P#4)
                     || _module.__default.AlwaysAnother(_module._default.Filter_IsSubStream#$_T0, 
                      $LS($LS($LZ)), 
                      _module.Stream.tail(##s#6), 
                      ##P#4);
                assume _module.__default.AlwaysAnother(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), ##s#6, ##P#4);
                assume _module.__default.Filter#canCall(_module._default.Filter_IsSubStream#$_T0, s#1, P#1);
                assume _module.Stream.Cons_q(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1));
                assume _module.Stream.Cons_q(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1));
                assume _module.__default.Filter#canCall(_module._default.Filter_IsSubStream#$_T0, s#1, P#1)
                   && _module.Stream.Cons_q(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1));
                // ProcessCallStmt: CheckSubrange
                s##0 := _module.Stream.tail(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1));
                assume true;
                // ProcessCallStmt: CheckSubrange
                u##0 := s#1;
                assume true;
                // ProcessCallStmt: CheckSubrange
                assert $Is(_k#0 - 1, Tclass._System.nat());
                k##0 := _k#0 - 1;
                assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                // ProcessCallStmt: Make the call
                call Call$$_module.__default.Lemma__TailSubStreamK(_module._default.Filter_IsSubStream#$_T0, s##0, u##0, k##0);
                // TrCallStmt: After ProcessCallStmt
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(156,58)"} true;
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(150,5)
                ##s#7 := s#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#7, Tclass._module.Stream(_module._default.Filter_IsSubStream#$_T0), $Heap);
                ##P#5 := P#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##P#5, 
                  Tclass._System.___hTotalFunc1(_module._default.Filter_IsSubStream#$_T0, TBool), 
                  $Heap);
                assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.Filter_IsSubStream#$_T0, ##s#7, ##P#5)
                   ==> _module.__default.AlwaysAnother(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), ##s#7, ##P#5)
                     || (_module.__default.IsAnother#canCall(_module._default.Filter_IsSubStream#$_T0, ##s#7, ##P#5)
                       ==> _module.__default.IsAnother(_module._default.Filter_IsSubStream#$_T0, ##s#7, ##P#5)
                         || (exists n#10: int :: 
                          { _module.__default.Tail(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), ##s#7, n#10) } 
                          LitInt(0) <= n#10
                             && 
                            LitInt(0) <= n#10
                             && $Unbox(Apply1(_module._default.Filter_IsSubStream#$_T0, 
                                TBool, 
                                $Heap, 
                                ##P#5, 
                                _module.Stream.head(_module.__default.Tail(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), ##s#7, n#10)))): bool));
                assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.Filter_IsSubStream#$_T0, ##s#7, ##P#5)
                   ==> _module.__default.AlwaysAnother(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), ##s#7, ##P#5)
                     || _module.__default.AlwaysAnother(_module._default.Filter_IsSubStream#$_T0, 
                      $LS($LS($LZ)), 
                      _module.Stream.tail(##s#7), 
                      ##P#5);
                assume _module.__default.Filter#canCall(_module._default.Filter_IsSubStream#$_T0, s#1, P#1);
                assume _module.Stream.Cons_q(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1));
                assume _module.Stream.Cons_q(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1));
                assert $Is(_k#0 - 1, Tclass._System.nat());
                ##_k#1 := _k#0 - 1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##_k#1, Tclass._System.nat(), $Heap);
                ##s#8 := _module.Stream.tail(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1));
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#8, Tclass._module.Stream(_module._default.Filter_IsSubStream#$_T0), $Heap);
                ##u#2 := s#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##u#2, Tclass._module.Stream(_module._default.Filter_IsSubStream#$_T0), $Heap);
                assume _module.__default.IsSubStream_h#canCall(_module._default.Filter_IsSubStream#$_T0, 
                  _k#0 - 1, 
                  _module.Stream.tail(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1)), 
                  s#1);
                assume _module.__default.Filter#canCall(_module._default.Filter_IsSubStream#$_T0, s#1, P#1)
                   && _module.Stream.Cons_q(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1))
                   && _module.__default.IsSubStream_h#canCall(_module._default.Filter_IsSubStream#$_T0, 
                    _k#0 - 1, 
                    _module.Stream.tail(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1)), 
                    s#1);
                // ----- assert line2 ==> line3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(150,5)
                assert {:subsumption 0} _module.__default.IsSubStream_h(_module._default.Filter_IsSubStream#$_T0, 
                    $LS($LZ), 
                    _k#0 - 1, 
                    _module.Stream.tail(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1)), 
                    _module.Stream.tail(s#1))
                   ==> 
                  _module.__default.IsSubStream_h#canCall(_module._default.Filter_IsSubStream#$_T0, 
                    _k#0 - 1, 
                    _module.Stream.tail(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1)), 
                    s#1)
                   ==> _module.__default.IsSubStream_h(_module._default.Filter_IsSubStream#$_T0, 
                      $LS($LZ), 
                      _k#0 - 1, 
                      _module.Stream.tail(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1)), 
                      s#1)
                     || (0 < _k#0 - 1
                       ==> 
                      _module.__default.In#canCall(_module._default.Filter_IsSubStream#$_T0, 
                        _module.Stream.head(_module.Stream.tail(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1))), 
                        s#1)
                       ==> _module.__default.In(_module._default.Filter_IsSubStream#$_T0, 
                          _module.Stream.head(_module.Stream.tail(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1))), 
                          s#1)
                         || (exists n#11: int :: 
                          { _module.__default.Tail(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, n#11) } 
                          LitInt(0) <= n#11
                             && 
                            LitInt(0) <= n#11
                             && _module.Stream.head(_module.__default.Tail(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, n#11))
                               == _module.Stream.head(_module.Stream.tail(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1)))));
                assert {:subsumption 0} _module.__default.IsSubStream_h(_module._default.Filter_IsSubStream#$_T0, 
                    $LS($LZ), 
                    _k#0 - 1, 
                    _module.Stream.tail(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1)), 
                    _module.Stream.tail(s#1))
                   ==> 
                  _module.__default.IsSubStream_h#canCall(_module._default.Filter_IsSubStream#$_T0, 
                    _k#0 - 1, 
                    _module.Stream.tail(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1)), 
                    s#1)
                   ==> _module.__default.IsSubStream_h(_module._default.Filter_IsSubStream#$_T0, 
                      $LS($LZ), 
                      _k#0 - 1, 
                      _module.Stream.tail(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1)), 
                      s#1)
                     || (0 < _k#0 - 1
                       ==> _module.__default.IsSubStream_h(_module._default.Filter_IsSubStream#$_T0, 
                        $LS($LS($LZ)), 
                        _k#0 - 1 - 1, 
                        _module.Stream.tail(_module.Stream.tail(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LS($LZ)), s#1, P#1))), 
                        s#1));
                assume false;
            }

            assume true
               ==> _module.__default.IsSubStream_h(_module._default.Filter_IsSubStream#$_T0, 
                $LS($LZ), 
                _k#0 - 1, 
                _module.Stream.tail(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1)), 
                s#1);
            // ----- calc statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(159,5)
            // Assume Fuel Constant
            if (*)
            {
                // ----- assert wf[initial] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(159,5)
                assume true;
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(159,5)
                ##s#18 := s#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#18, Tclass._module.Stream(_module._default.Filter_IsSubStream#$_T0), $Heap);
                ##P#9 := P#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##P#9, 
                  Tclass._System.___hTotalFunc1(_module._default.Filter_IsSubStream#$_T0, TBool), 
                  $Heap);
                assume {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.Filter_IsSubStream#$_T0, ##s#18, ##P#9)
                   ==> _module.__default.AlwaysAnother(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), ##s#18, ##P#9)
                     || (_module.__default.IsAnother#canCall(_module._default.Filter_IsSubStream#$_T0, ##s#18, ##P#9)
                       ==> _module.__default.IsAnother(_module._default.Filter_IsSubStream#$_T0, ##s#18, ##P#9)
                         || (exists n#17: int :: 
                          { _module.__default.Tail(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), ##s#18, n#17) } 
                          LitInt(0) <= n#17
                             && 
                            LitInt(0) <= n#17
                             && $Unbox(Apply1(_module._default.Filter_IsSubStream#$_T0, 
                                TBool, 
                                $Heap, 
                                ##P#9, 
                                _module.Stream.head(_module.__default.Tail(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), ##s#18, n#17)))): bool));
                assume {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.Filter_IsSubStream#$_T0, ##s#18, ##P#9)
                   ==> _module.__default.AlwaysAnother(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), ##s#18, ##P#9)
                     || _module.__default.AlwaysAnother(_module._default.Filter_IsSubStream#$_T0, 
                      $LS($LS($LZ)), 
                      _module.Stream.tail(##s#18), 
                      ##P#9);
                assume _module.__default.Filter#canCall(_module._default.Filter_IsSubStream#$_T0, s#1, P#1);
                assume _module.Stream.Cons_q(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1));
                assume _module.Stream.Cons_q(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1));
                ##x#1 := _module.Stream.head(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1));
                // assume allocatedness for argument to function
                assume $IsAllocBox(##x#1, _module._default.Filter_IsSubStream#$_T0, $Heap);
                ##s#19 := s#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#19, Tclass._module.Stream(_module._default.Filter_IsSubStream#$_T0), $Heap);
                assume _module.__default.In#canCall(_module._default.Filter_IsSubStream#$_T0, 
                  _module.Stream.head(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1)), 
                  s#1);
                assume _module.__default.Filter#canCall(_module._default.Filter_IsSubStream#$_T0, s#1, P#1)
                   && _module.Stream.Cons_q(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1))
                   && _module.__default.In#canCall(_module._default.Filter_IsSubStream#$_T0, 
                    _module.Stream.head(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1)), 
                    s#1);
                // ----- Hint0 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(159,5)
                // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(161,11)
                ##s#20 := s#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#20, Tclass._module.Stream(_module._default.Filter_IsSubStream#$_T0), $Heap);
                ##P#10 := P#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##P#10, 
                  Tclass._System.___hTotalFunc1(_module._default.Filter_IsSubStream#$_T0, TBool), 
                  $Heap);
                assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.Filter_IsSubStream#$_T0, ##s#20, ##P#10)
                   ==> _module.__default.AlwaysAnother(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), ##s#20, ##P#10)
                     || (_module.__default.IsAnother#canCall(_module._default.Filter_IsSubStream#$_T0, ##s#20, ##P#10)
                       ==> _module.__default.IsAnother(_module._default.Filter_IsSubStream#$_T0, ##s#20, ##P#10)
                         || (exists n#18: int :: 
                          { _module.__default.Tail(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), ##s#20, n#18) } 
                          LitInt(0) <= n#18
                             && 
                            LitInt(0) <= n#18
                             && $Unbox(Apply1(_module._default.Filter_IsSubStream#$_T0, 
                                TBool, 
                                $Heap, 
                                ##P#10, 
                                _module.Stream.head(_module.__default.Tail(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), ##s#20, n#18)))): bool));
                assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.Filter_IsSubStream#$_T0, ##s#20, ##P#10)
                   ==> _module.__default.AlwaysAnother(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), ##s#20, ##P#10)
                     || _module.__default.AlwaysAnother(_module._default.Filter_IsSubStream#$_T0, 
                      $LS($LS($LZ)), 
                      _module.Stream.tail(##s#20), 
                      ##P#10);
                assume _module.__default.Filter#canCall(_module._default.Filter_IsSubStream#$_T0, s#1, P#1);
                assume _module.Stream.Cons_q(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1));
                assume _module.Stream.Cons_q(s#1);
                assume _module.Stream.Cons_q(s#1);
                ##s#21 := _module.Stream.tail(s#1);
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#21, Tclass._module.Stream(_module._default.Filter_IsSubStream#$_T0), $Heap);
                ##P#11 := P#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##P#11, 
                  Tclass._System.___hTotalFunc1(_module._default.Filter_IsSubStream#$_T0, TBool), 
                  $Heap);
                assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.Filter_IsSubStream#$_T0, ##s#21, ##P#11)
                   ==> _module.__default.AlwaysAnother(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), ##s#21, ##P#11)
                     || (_module.__default.IsAnother#canCall(_module._default.Filter_IsSubStream#$_T0, ##s#21, ##P#11)
                       ==> _module.__default.IsAnother(_module._default.Filter_IsSubStream#$_T0, ##s#21, ##P#11)
                         || (exists n#19: int :: 
                          { _module.__default.Tail(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), ##s#21, n#19) } 
                          LitInt(0) <= n#19
                             && 
                            LitInt(0) <= n#19
                             && $Unbox(Apply1(_module._default.Filter_IsSubStream#$_T0, 
                                TBool, 
                                $Heap, 
                                ##P#11, 
                                _module.Stream.head(_module.__default.Tail(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), ##s#21, n#19)))): bool));
                assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.Filter_IsSubStream#$_T0, ##s#21, ##P#11)
                   ==> _module.__default.AlwaysAnother(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), ##s#21, ##P#11)
                     || _module.__default.AlwaysAnother(_module._default.Filter_IsSubStream#$_T0, 
                      $LS($LS($LZ)), 
                      _module.Stream.tail(##s#21), 
                      ##P#11);
                assume _module.__default.Filter#canCall(_module._default.Filter_IsSubStream#$_T0, _module.Stream.tail(s#1), P#1);
                assume _module.Stream.Cons_q(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, 
                    $LS($LZ), 
                    _module.Stream.tail(s#1), 
                    P#1));
                assume $IsA#_module.Stream(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1))
                   && 
                  _module.__default.Filter#canCall(_module._default.Filter_IsSubStream#$_T0, s#1, P#1)
                   && 
                  _module.Stream.Cons_q(s#1)
                   && 
                  _module.Stream.Cons_q(s#1)
                   && _module.__default.Filter#canCall(_module._default.Filter_IsSubStream#$_T0, _module.Stream.tail(s#1), P#1);
                assert {:subsumption 0} $Eq#_module.Stream(_module._default.Filter_IsSubStream#$_T0, 
                  _module._default.Filter_IsSubStream#$_T0, 
                  $LS($LS($LZ)), 
                  _module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LS($LZ)), s#1, P#1), 
                  #_module.Stream.Cons(_module.Stream.head(s#1), 
                    _module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, 
                      $LS($LS($LZ)), 
                      _module.Stream.tail(s#1), 
                      P#1)));
                assume $Eq#_module.Stream(_module._default.Filter_IsSubStream#$_T0, 
                  _module._default.Filter_IsSubStream#$_T0, 
                  $LS($LS($LZ)), 
                  _module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1), 
                  #_module.Stream.Cons(_module.Stream.head(s#1), 
                    _module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, 
                      $LS($LZ), 
                      _module.Stream.tail(s#1), 
                      P#1)));
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(159,5)
                assume _module.Stream.Cons_q(s#1);
                ##x#2 := _module.Stream.head(s#1);
                // assume allocatedness for argument to function
                assume $IsAllocBox(##x#2, _module._default.Filter_IsSubStream#$_T0, $Heap);
                ##s#22 := s#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#22, Tclass._module.Stream(_module._default.Filter_IsSubStream#$_T0), $Heap);
                assume _module.__default.In#canCall(_module._default.Filter_IsSubStream#$_T0, _module.Stream.head(s#1), s#1);
                assume _module.Stream.Cons_q(s#1)
                   && _module.__default.In#canCall(_module._default.Filter_IsSubStream#$_T0, _module.Stream.head(s#1), s#1);
                // ----- assert line0 == line1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(159,5)
                assert {:subsumption 0} _module.__default.In(_module._default.Filter_IsSubStream#$_T0, 
                    _module.Stream.head(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LS($LZ)), s#1, P#1)), 
                    s#1)
                   == _module.__default.In(_module._default.Filter_IsSubStream#$_T0, _module.Stream.head(s#1), s#1);
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(159,5)
                assume _module.Stream.Cons_q(s#1);
                ##x#0 := _module.Stream.head(s#1);
                // assume allocatedness for argument to function
                assume $IsAllocBox(##x#0, _module._default.Filter_IsSubStream#$_T0, $Heap);
                ##s#15 := s#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#15, Tclass._module.Stream(_module._default.Filter_IsSubStream#$_T0), $Heap);
                assume _module.__default.In#canCall(_module._default.Filter_IsSubStream#$_T0, _module.Stream.head(s#1), s#1);
                assume _module.Stream.Cons_q(s#1)
                   && _module.__default.In#canCall(_module._default.Filter_IsSubStream#$_T0, _module.Stream.head(s#1), s#1);
                // ----- Hint1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(159,5)
                // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(163,11)
                ##s#16 := s#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#16, Tclass._module.Stream(_module._default.Filter_IsSubStream#$_T0), $Heap);
                assert $Is(LitInt(0), Tclass._System.nat());
                ##n#0 := LitInt(0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
                assume _module.__default.Tail#canCall(_module._default.Filter_IsSubStream#$_T0, s#1, LitInt(0));
                assume _module.Stream.Cons_q(_module.__default.Tail(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, LitInt(0)));
                assume $IsA#_module.Stream(_module.__default.Tail(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, LitInt(0)))
                   && $IsA#_module.Stream(s#1)
                   && _module.__default.Tail#canCall(_module._default.Filter_IsSubStream#$_T0, s#1, LitInt(0));
                assert {:subsumption 0} $Eq#_module.Stream(_module._default.Filter_IsSubStream#$_T0, 
                  _module._default.Filter_IsSubStream#$_T0, 
                  $LS($LS($LZ)), 
                  _module.__default.Tail(_module._default.Filter_IsSubStream#$_T0, $LS($LS($LZ)), s#1, LitInt(0)), 
                  s#1);
                assume $Eq#_module.Stream(_module._default.Filter_IsSubStream#$_T0, 
                  _module._default.Filter_IsSubStream#$_T0, 
                  $LS($LS($LZ)), 
                  _module.__default.Tail(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, LitInt(0)), 
                  s#1);
                // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(164,11)
                // Begin Comprehension WF check
                havoc n#15;
                if (LitInt(0) <= n#15)
                {
                    if (LitInt(0) <= n#15)
                    {
                        ##s#17 := s#1;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##s#17, Tclass._module.Stream(_module._default.Filter_IsSubStream#$_T0), $Heap);
                        ##n#1 := n#15;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##n#1, Tclass._System.nat(), $Heap);
                        assume _module.__default.Tail#canCall(_module._default.Filter_IsSubStream#$_T0, s#1, n#15);
                        assume _module.Stream.Cons_q(_module.__default.Tail(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, n#15));
                        assume _module.Stream.Cons_q(_module.__default.Tail(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, n#15));
                        assume _module.Stream.Cons_q(s#1);
                    }
                }

                // End Comprehension WF check
                assume (forall n#16: int :: 
                  LitInt(0) <= n#16
                     ==> 
                    LitInt(0) <= n#16
                     ==> _module.__default.Tail#canCall(_module._default.Filter_IsSubStream#$_T0, s#1, n#16)
                       && _module.Stream.Cons_q(_module.__default.Tail(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, n#16))
                       && _module.Stream.Cons_q(s#1));
                assert {:subsumption 0} (exists n#16: int :: 
                  LitInt(0) <= n#16
                     && 
                    LitInt(0) <= n#16
                     && _module.Stream.head(_module.__default.Tail(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, n#16))
                       == _module.Stream.head(s#1));
                assume (exists n#16: int :: 
                  LitInt(0) <= n#16
                     && 
                    LitInt(0) <= n#16
                     && _module.Stream.head(_module.__default.Tail(_module._default.Filter_IsSubStream#$_T0, $LS($LS($LZ)), s#1, n#16))
                       == _module.Stream.head(s#1));
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(159,5)
                assume true;
                // ----- assert line1 == line2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(159,5)
                assert {:subsumption 0} _module.__default.In(_module._default.Filter_IsSubStream#$_T0, _module.Stream.head(s#1), s#1)
                   == Lit(true);
                assume false;
            }

            assume true
               ==> _module.__default.In(_module._default.Filter_IsSubStream#$_T0, 
                _module.Stream.head(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), s#1, P#1)), 
                s#1);
        }
        else
        {
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(169,14)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            s##2 := s#1;
            assume true;
            // ProcessCallStmt: CheckSubrange
            P##1 := P#1;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call Call$$_module.__default.NextLemma(_module._default.Filter_IsSubStream#$_T0, s##2, P##1);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(169,19)"} true;
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(170,25)
            // TrCallStmt: Before ProcessCallStmt
            assume _module.Stream.Cons_q(s#1);
            ##s#23 := _module.Stream.tail(s#1);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#23, Tclass._module.Stream(_module._default.Filter_IsSubStream#$_T0), $Heap);
            ##P#12 := P#1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##P#12, 
              Tclass._System.___hTotalFunc1(_module._default.Filter_IsSubStream#$_T0, TBool), 
              $Heap);
            assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.Filter_IsSubStream#$_T0, ##s#23, ##P#12)
               ==> _module.__default.AlwaysAnother(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), ##s#23, ##P#12)
                 || (_module.__default.IsAnother#canCall(_module._default.Filter_IsSubStream#$_T0, ##s#23, ##P#12)
                   ==> _module.__default.IsAnother(_module._default.Filter_IsSubStream#$_T0, ##s#23, ##P#12)
                     || (exists n#20: int :: 
                      { _module.__default.Tail(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), ##s#23, n#20) } 
                      LitInt(0) <= n#20
                         && 
                        LitInt(0) <= n#20
                         && $Unbox(Apply1(_module._default.Filter_IsSubStream#$_T0, 
                            TBool, 
                            $Heap, 
                            ##P#12, 
                            _module.Stream.head(_module.__default.Tail(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), ##s#23, n#20)))): bool));
            assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.Filter_IsSubStream#$_T0, ##s#23, ##P#12)
               ==> _module.__default.AlwaysAnother(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), ##s#23, ##P#12)
                 || _module.__default.AlwaysAnother(_module._default.Filter_IsSubStream#$_T0, 
                  $LS($LS($LZ)), 
                  _module.Stream.tail(##s#23), 
                  ##P#12);
            assume _module.__default.AlwaysAnother(_module._default.Filter_IsSubStream#$_T0, $LS($LZ), ##s#23, ##P#12);
            assume _module.__default.Filter#canCall(_module._default.Filter_IsSubStream#$_T0, _module.Stream.tail(s#1), P#1);
            assume _module.Stream.Cons_q(_module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, 
                $LS($LZ), 
                _module.Stream.tail(s#1), 
                P#1));
            assume _module.Stream.Cons_q(s#1)
               && _module.__default.Filter#canCall(_module._default.Filter_IsSubStream#$_T0, _module.Stream.tail(s#1), P#1);
            // ProcessCallStmt: CheckSubrange
            s##3 := _module.__default.Filter(_module._default.Filter_IsSubStream#$_T0, 
              $LS($LZ), 
              _module.Stream.tail(s#1), 
              P#1);
            assume true;
            // ProcessCallStmt: CheckSubrange
            u##1 := s#1;
            assume true;
            // ProcessCallStmt: CheckSubrange
            k##1 := _k#0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call Call$$_module.__default.Lemma__TailSubStreamK(_module._default.Filter_IsSubStream#$_T0, s##3, u##1, k##1);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(170,50)"} true;
        }
    }
    else
    {
    }
}



procedure {:_induction s#0, P#0} CheckWellformed$$_module.__default.Theorem__Filter(_module._default.Theorem_Filter$T: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Theorem_Filter$T))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.Theorem_Filter$T), $Heap)
         && $IsA#_module.Stream(s#0), 
    P#0: HandleType
       where $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.Theorem_Filter$T, TBool))
         && $IsAlloc(P#0, 
          Tclass._System.___hTotalFunc1(_module._default.Theorem_Filter$T, TBool), 
          $Heap));
  free requires 40 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:_induction s#0, P#0} CheckWellformed$$_module.__default.Theorem__Filter(_module._default.Theorem_Filter$T: Ty, s#0: DatatypeType, P#0: HandleType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##s#0: DatatypeType;
  var ##P#0: HandleType;
  var x#0: Box;
  var ##s#1: DatatypeType;
  var ##P#1: HandleType;
  var ##x#0: Box;
  var ##s#2: DatatypeType;
  var ##x#1: Box;
  var ##s#3: DatatypeType;

    // AddMethodImpl: Theorem_Filter, CheckWellformed$$_module.__default.Theorem__Filter
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(175,6): initial state"} true;
    ##s#0 := s#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#0, Tclass._module.Stream(_module._default.Theorem_Filter$T), $Heap);
    ##P#0 := P#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##P#0, 
      Tclass._System.___hTotalFunc1(_module._default.Theorem_Filter$T, TBool), 
      $Heap);
    assume _module.__default.AlwaysAnother#canCall(_module._default.Theorem_Filter$T, s#0, P#0);
    assume _module.__default.AlwaysAnother(_module._default.Theorem_Filter$T, $LS($LZ), s#0, P#0);
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(177,10): post-state"} true;
    havoc x#0;
    assume $IsBox(x#0, _module._default.Theorem_Filter$T);
    ##s#1 := s#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#1, Tclass._module.Stream(_module._default.Theorem_Filter$T), $Heap);
    ##P#1 := P#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##P#1, 
      Tclass._System.___hTotalFunc1(_module._default.Theorem_Filter$T, TBool), 
      $Heap);
    assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.Theorem_Filter$T, ##s#1, ##P#1)
       ==> _module.__default.AlwaysAnother(_module._default.Theorem_Filter$T, $LS($LZ), ##s#1, ##P#1)
         || (_module.__default.IsAnother#canCall(_module._default.Theorem_Filter$T, ##s#1, ##P#1)
           ==> _module.__default.IsAnother(_module._default.Theorem_Filter$T, ##s#1, ##P#1)
             || (exists n#0: int :: 
              { _module.__default.Tail(_module._default.Theorem_Filter$T, $LS($LZ), ##s#1, n#0) } 
              LitInt(0) <= n#0
                 && 
                LitInt(0) <= n#0
                 && $Unbox(Apply1(_module._default.Theorem_Filter$T, 
                    TBool, 
                    $Heap, 
                    ##P#1, 
                    _module.Stream.head(_module.__default.Tail(_module._default.Theorem_Filter$T, $LS($LZ), ##s#1, n#0)))): bool));
    assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.Theorem_Filter$T, ##s#1, ##P#1)
       ==> _module.__default.AlwaysAnother(_module._default.Theorem_Filter$T, $LS($LZ), ##s#1, ##P#1)
         || _module.__default.AlwaysAnother(_module._default.Theorem_Filter$T, 
          $LS($LS($LZ)), 
          _module.Stream.tail(##s#1), 
          ##P#1);
    assume _module.__default.AlwaysAnother(_module._default.Theorem_Filter$T, $LS($LZ), ##s#1, ##P#1);
    assume _module.__default.Filter#canCall(_module._default.Theorem_Filter$T, s#0, P#0);
    assume _module.Stream.Cons_q(_module.__default.Filter(_module._default.Theorem_Filter$T, $LS($LZ), s#0, P#0));
    ##x#0 := x#0;
    // assume allocatedness for argument to function
    assume $IsAllocBox(##x#0, _module._default.Theorem_Filter$T, $Heap);
    ##s#2 := _module.__default.Filter(_module._default.Theorem_Filter$T, $LS($LZ), s#0, P#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#2, Tclass._module.Stream(_module._default.Theorem_Filter$T), $Heap);
    assume _module.__default.In#canCall(_module._default.Theorem_Filter$T, 
      x#0, 
      _module.__default.Filter(_module._default.Theorem_Filter$T, $LS($LZ), s#0, P#0));
    ##x#1 := x#0;
    // assume allocatedness for argument to function
    assume $IsAllocBox(##x#1, _module._default.Theorem_Filter$T, $Heap);
    ##s#3 := s#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#3, Tclass._module.Stream(_module._default.Theorem_Filter$T), $Heap);
    assume _module.__default.In#canCall(_module._default.Theorem_Filter$T, x#0, s#0);
    if (_module.__default.In(_module._default.Theorem_Filter$T, x#0, s#0))
    {
    }

    assume _module.__default.In(_module._default.Theorem_Filter$T, 
        x#0, 
        _module.__default.Filter(_module._default.Theorem_Filter$T, $LS($LZ), s#0, P#0))
       <==> _module.__default.In(_module._default.Theorem_Filter$T, x#0, s#0)
         && $Unbox(Apply1(_module._default.Theorem_Filter$T, TBool, $Heap, P#0, x#0)): bool;
    assume (forall x#1: Box :: 
      { $Unbox(Apply1(_module._default.Theorem_Filter$T, TBool, $Heap, P#0, x#1)): bool } 
        { _module.__default.In(_module._default.Theorem_Filter$T, x#1, s#0) } 
        { _module.__default.In(_module._default.Theorem_Filter$T, 
          x#1, 
          _module.__default.Filter(_module._default.Theorem_Filter$T, $LS($LZ), s#0, P#0)) } 
      $IsBox(x#1, _module._default.Theorem_Filter$T)
         ==> (_module.__default.In(_module._default.Theorem_Filter$T, 
            x#1, 
            _module.__default.Filter(_module._default.Theorem_Filter$T, $LS($LZ), s#0, P#0))
           <==> _module.__default.In(_module._default.Theorem_Filter$T, x#1, s#0)
             && $Unbox(Apply1(_module._default.Theorem_Filter$T, TBool, $Heap, P#0, x#1)): bool));
}



procedure {:_induction s#0, P#0} Call$$_module.__default.Theorem__Filter(_module._default.Theorem_Filter$T: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Theorem_Filter$T))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.Theorem_Filter$T), $Heap)
         && $IsA#_module.Stream(s#0), 
    P#0: HandleType
       where $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.Theorem_Filter$T, TBool))
         && $IsAlloc(P#0, 
          Tclass._System.___hTotalFunc1(_module._default.Theorem_Filter$T, TBool), 
          $Heap));
  // user-defined preconditions
  requires _module.__default.AlwaysAnother#canCall(_module._default.Theorem_Filter$T, s#0, P#0)
     ==> _module.__default.AlwaysAnother(_module._default.Theorem_Filter$T, $LS($LZ), s#0, P#0)
       || (_module.__default.IsAnother#canCall(_module._default.Theorem_Filter$T, s#0, P#0)
         ==> _module.__default.IsAnother(_module._default.Theorem_Filter$T, s#0, P#0)
           || (exists n#1: int :: 
            { _module.__default.Tail(_module._default.Theorem_Filter$T, $LS($LZ), s#0, n#1) } 
            LitInt(0) <= n#1
               && 
              LitInt(0) <= n#1
               && $Unbox(Apply1(_module._default.Theorem_Filter$T, 
                  TBool, 
                  $Heap, 
                  P#0, 
                  _module.Stream.head(_module.__default.Tail(_module._default.Theorem_Filter$T, $LS($LZ), s#0, n#1)))): bool));
  requires _module.__default.AlwaysAnother#canCall(_module._default.Theorem_Filter$T, s#0, P#0)
     ==> _module.__default.AlwaysAnother(_module._default.Theorem_Filter$T, $LS($LZ), s#0, P#0)
       || _module.__default.AlwaysAnother(_module._default.Theorem_Filter$T, $LS($LS($LZ)), _module.Stream.tail(s#0), P#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall x#1: Box :: 
    { $Unbox(Apply1(_module._default.Theorem_Filter$T, TBool, $Heap, P#0, x#1)): bool } 
      { _module.__default.In(_module._default.Theorem_Filter$T, x#1, s#0) } 
      { _module.__default.In(_module._default.Theorem_Filter$T, 
        x#1, 
        _module.__default.Filter(_module._default.Theorem_Filter$T, $LS($LZ), s#0, P#0)) } 
    $IsBox(x#1, _module._default.Theorem_Filter$T)
       ==> _module.__default.Filter#canCall(_module._default.Theorem_Filter$T, s#0, P#0)
         && _module.__default.In#canCall(_module._default.Theorem_Filter$T, 
          x#1, 
          _module.__default.Filter(_module._default.Theorem_Filter$T, $LS($LZ), s#0, P#0))
         && _module.__default.In#canCall(_module._default.Theorem_Filter$T, x#1, s#0));
  free ensures (forall x#1: Box :: 
    { $Unbox(Apply1(_module._default.Theorem_Filter$T, TBool, $Heap, P#0, x#1)): bool } 
      { _module.__default.In(_module._default.Theorem_Filter$T, x#1, s#0) } 
      { _module.__default.In(_module._default.Theorem_Filter$T, 
        x#1, 
        _module.__default.Filter(_module._default.Theorem_Filter$T, $LS($LZ), s#0, P#0)) } 
    $IsBox(x#1, _module._default.Theorem_Filter$T)
       ==> (_module.__default.In(_module._default.Theorem_Filter$T, 
          x#1, 
          _module.__default.Filter(_module._default.Theorem_Filter$T, $LS($LZ), s#0, P#0))
         <==> _module.__default.In(_module._default.Theorem_Filter$T, x#1, s#0)
           && $Unbox(Apply1(_module._default.Theorem_Filter$T, TBool, $Heap, P#0, x#1)): bool));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction s#0, P#0} Impl$$_module.__default.Theorem__Filter(_module._default.Theorem_Filter$T: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Theorem_Filter$T))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.Theorem_Filter$T), $Heap)
         && $IsA#_module.Stream(s#0), 
    P#0: HandleType
       where $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.Theorem_Filter$T, TBool))
         && $IsAlloc(P#0, 
          Tclass._System.___hTotalFunc1(_module._default.Theorem_Filter$T, TBool), 
          $Heap))
   returns ($_reverifyPost: bool);
  free requires 40 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.__default.AlwaysAnother#canCall(_module._default.Theorem_Filter$T, s#0, P#0)
     && 
    _module.__default.AlwaysAnother(_module._default.Theorem_Filter$T, $LS($LZ), s#0, P#0)
     && 
    _module.__default.IsAnother(_module._default.Theorem_Filter$T, s#0, P#0)
     && _module.__default.AlwaysAnother(_module._default.Theorem_Filter$T, $LS($LZ), _module.Stream.tail(s#0), P#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall x#1: Box :: 
    { $Unbox(Apply1(_module._default.Theorem_Filter$T, TBool, $Heap, P#0, x#1)): bool } 
      { _module.__default.In(_module._default.Theorem_Filter$T, x#1, s#0) } 
      { _module.__default.In(_module._default.Theorem_Filter$T, 
        x#1, 
        _module.__default.Filter(_module._default.Theorem_Filter$T, $LS($LZ), s#0, P#0)) } 
    $IsBox(x#1, _module._default.Theorem_Filter$T)
       ==> _module.__default.Filter#canCall(_module._default.Theorem_Filter$T, s#0, P#0)
         && _module.__default.In#canCall(_module._default.Theorem_Filter$T, 
          x#1, 
          _module.__default.Filter(_module._default.Theorem_Filter$T, $LS($LZ), s#0, P#0))
         && _module.__default.In#canCall(_module._default.Theorem_Filter$T, x#1, s#0));
  ensures (forall x#1: Box :: 
    { $Unbox(Apply1(_module._default.Theorem_Filter$T, TBool, $Heap, P#0, x#1)): bool } 
      { _module.__default.In(_module._default.Theorem_Filter$T, x#1, s#0) } 
      { _module.__default.In(_module._default.Theorem_Filter$T, 
        x#1, 
        _module.__default.Filter(_module._default.Theorem_Filter$T, $LS($LS($LZ)), s#0, P#0)) } 
    $IsBox(x#1, _module._default.Theorem_Filter$T)
       ==> (_module.__default.In(_module._default.Theorem_Filter$T, 
          x#1, 
          _module.__default.Filter(_module._default.Theorem_Filter$T, $LS($LS($LZ)), s#0, P#0))
         <==> _module.__default.In(_module._default.Theorem_Filter$T, x#1, s#0)
           && $Unbox(Apply1(_module._default.Theorem_Filter$T, TBool, $Heap, P#0, x#1)): bool));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction s#0, P#0} Impl$$_module.__default.Theorem__Filter(_module._default.Theorem_Filter$T: Ty, s#0: DatatypeType, P#0: HandleType)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var x#3: Box;
  var ##s#4: DatatypeType;
  var ##P#2: HandleType;
  var ##x#2: Box;
  var ##s#5: DatatypeType;
  var s##0_0: DatatypeType;
  var P##0_0: HandleType;
  var x##0_0: Box;
  var ##x#3: Box;
  var ##s#6: DatatypeType;
  var k#1_0: int where LitInt(0) <= k#1_0;
  var k#1_1: int;
  var ##s#1_0: DatatypeType;
  var ##n#1_0: int;
  var s##1_0: DatatypeType;
  var P##1_0: HandleType;
  var x##1_0: Box;
  var k##1_0: int;

    // AddMethodImpl: Theorem_Filter, Impl$$_module.__default.Theorem__Filter
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(178,0): initial state"} true;
    assume $IsA#_module.Stream(s#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#s0#0: DatatypeType, $ih#P0#0: HandleType :: 
      $Is($ih#s0#0, Tclass._module.Stream(_module._default.Theorem_Filter$T))
           && $Is($ih#P0#0, 
            Tclass._System.___hTotalFunc1(_module._default.Theorem_Filter$T, TBool))
           && _module.__default.AlwaysAnother(_module._default.Theorem_Filter$T, $LS($LZ), $ih#s0#0, $ih#P0#0)
           && false
         ==> (forall x#2: Box :: 
          { $Unbox(Apply1(_module._default.Theorem_Filter$T, TBool, $Heap, $ih#P0#0, x#2)): bool } 
            { _module.__default.In(_module._default.Theorem_Filter$T, x#2, $ih#s0#0) } 
            { _module.__default.In(_module._default.Theorem_Filter$T, 
              x#2, 
              _module.__default.Filter(_module._default.Theorem_Filter$T, $LS($LZ), $ih#s0#0, $ih#P0#0)) } 
          $IsBox(x#2, _module._default.Theorem_Filter$T)
             ==> (_module.__default.In(_module._default.Theorem_Filter$T, 
                x#2, 
                _module.__default.Filter(_module._default.Theorem_Filter$T, $LS($LZ), $ih#s0#0, $ih#P0#0))
               <==> _module.__default.In(_module._default.Theorem_Filter$T, x#2, $ih#s0#0)
                 && $Unbox(Apply1(_module._default.Theorem_Filter$T, TBool, $Heap, $ih#P0#0, x#2)): bool)));
    $_reverifyPost := false;
    // ----- forall statement (proof) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(179,3)
    if (*)
    {
        // Assume Fuel Constant
        havoc x#3;
        assume $IsBox(x#3, _module._default.Theorem_Filter$T);
        assume true;
        assume true;
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(182,5)
        ##s#4 := s#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#4, Tclass._module.Stream(_module._default.Theorem_Filter$T), $Heap);
        ##P#2 := P#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##P#2, 
          Tclass._System.___hTotalFunc1(_module._default.Theorem_Filter$T, TBool), 
          $Heap);
        assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.Theorem_Filter$T, ##s#4, ##P#2)
           ==> _module.__default.AlwaysAnother(_module._default.Theorem_Filter$T, $LS($LZ), ##s#4, ##P#2)
             || (_module.__default.IsAnother#canCall(_module._default.Theorem_Filter$T, ##s#4, ##P#2)
               ==> _module.__default.IsAnother(_module._default.Theorem_Filter$T, ##s#4, ##P#2)
                 || (exists n#3: int :: 
                  { _module.__default.Tail(_module._default.Theorem_Filter$T, $LS($LZ), ##s#4, n#3) } 
                  LitInt(0) <= n#3
                     && 
                    LitInt(0) <= n#3
                     && $Unbox(Apply1(_module._default.Theorem_Filter$T, 
                        TBool, 
                        $Heap, 
                        ##P#2, 
                        _module.Stream.head(_module.__default.Tail(_module._default.Theorem_Filter$T, $LS($LZ), ##s#4, n#3)))): bool));
        assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.Theorem_Filter$T, ##s#4, ##P#2)
           ==> _module.__default.AlwaysAnother(_module._default.Theorem_Filter$T, $LS($LZ), ##s#4, ##P#2)
             || _module.__default.AlwaysAnother(_module._default.Theorem_Filter$T, 
              $LS($LS($LZ)), 
              _module.Stream.tail(##s#4), 
              ##P#2);
        assume _module.__default.AlwaysAnother(_module._default.Theorem_Filter$T, $LS($LZ), ##s#4, ##P#2);
        assume _module.__default.Filter#canCall(_module._default.Theorem_Filter$T, s#0, P#0);
        assume _module.Stream.Cons_q(_module.__default.Filter(_module._default.Theorem_Filter$T, $LS($LZ), s#0, P#0));
        ##x#2 := x#3;
        // assume allocatedness for argument to function
        assume $IsAllocBox(##x#2, _module._default.Theorem_Filter$T, $Heap);
        ##s#5 := _module.__default.Filter(_module._default.Theorem_Filter$T, $LS($LZ), s#0, P#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#5, Tclass._module.Stream(_module._default.Theorem_Filter$T), $Heap);
        assume _module.__default.In#canCall(_module._default.Theorem_Filter$T, 
          x#3, 
          _module.__default.Filter(_module._default.Theorem_Filter$T, $LS($LZ), s#0, P#0));
        assume _module.__default.Filter#canCall(_module._default.Theorem_Filter$T, s#0, P#0)
           && _module.__default.In#canCall(_module._default.Theorem_Filter$T, 
            x#3, 
            _module.__default.Filter(_module._default.Theorem_Filter$T, $LS($LZ), s#0, P#0));
        if (_module.__default.In(_module._default.Theorem_Filter$T, 
          x#3, 
          _module.__default.Filter(_module._default.Theorem_Filter$T, $LS($LZ), s#0, P#0)))
        {
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(183,14)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            s##0_0 := s#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            P##0_0 := P#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            x##0_0 := x#3;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call Call$$_module.__default.FS__Ping(_module._default.Theorem_Filter$T, s##0_0, P##0_0, x##0_0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(183,22)"} true;
        }
        else
        {
        }

        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(185,5)
        ##x#3 := x#3;
        // assume allocatedness for argument to function
        assume $IsAllocBox(##x#3, _module._default.Theorem_Filter$T, $Heap);
        ##s#6 := s#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#6, Tclass._module.Stream(_module._default.Theorem_Filter$T), $Heap);
        assume _module.__default.In#canCall(_module._default.Theorem_Filter$T, x#3, s#0);
        if (_module.__default.In(_module._default.Theorem_Filter$T, x#3, s#0))
        {
        }

        assume _module.__default.In#canCall(_module._default.Theorem_Filter$T, x#3, s#0);
        if (_module.__default.In(_module._default.Theorem_Filter$T, x#3, s#0)
           && $Unbox(Apply1(_module._default.Theorem_Filter$T, TBool, $Heap, P#0, x#3)): bool)
        {
            // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(186,13)
            havoc k#1_1;
            if (LitInt(0) <= k#1_1)
            {
                if (LitInt(0) <= k#1_1)
                {
                    ##s#1_0 := s#0;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s#1_0, Tclass._module.Stream(_module._default.Theorem_Filter$T), $Heap);
                    ##n#1_0 := k#1_1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##n#1_0, Tclass._System.nat(), $Heap);
                    assume _module.__default.Tail#canCall(_module._default.Theorem_Filter$T, s#0, k#1_1);
                    assume _module.Stream.Cons_q(_module.__default.Tail(_module._default.Theorem_Filter$T, $LS($LZ), s#0, k#1_1));
                    assume _module.Stream.Cons_q(_module.__default.Tail(_module._default.Theorem_Filter$T, $LS($LZ), s#0, k#1_1));
                }

                assume LitInt(0) <= k#1_1
                   ==> _module.__default.Tail#canCall(_module._default.Theorem_Filter$T, s#0, k#1_1)
                     && _module.Stream.Cons_q(_module.__default.Tail(_module._default.Theorem_Filter$T, $LS($LZ), s#0, k#1_1));
            }

            assert ($Is(LitInt(0), Tclass._System.nat())
                 && 
                LitInt(0) <= LitInt(0)
                 && _module.Stream.head(_module.__default.Tail(_module._default.Theorem_Filter$T, $LS($LZ), s#0, LitInt(0)))
                   == x#3)
               || 
              ($Is(LitInt(0), Tclass._System.nat())
                 && 
                LitInt(0) <= LitInt(0)
                 && _module.Stream.head(_module.__default.Tail(_module._default.Theorem_Filter$T, $LS($LZ), s#0, LitInt(0)))
                   == x#3)
               || 
              ($Is(LitInt(0), Tclass._System.nat())
                 && 
                LitInt(0) <= LitInt(0)
                 && _module.Stream.head(_module.__default.Tail(_module._default.Theorem_Filter$T, $LS($LZ), s#0, LitInt(0)))
                   == x#3)
               || (exists $as#k1_0#1_0: int :: 
                LitInt(0) <= $as#k1_0#1_0
                   && 
                  LitInt(0) <= $as#k1_0#1_0
                   && _module.Stream.head(_module.__default.Tail(_module._default.Theorem_Filter$T, $LS($LZ), s#0, $as#k1_0#1_0))
                     == x#3);
            havoc k#1_0;
            assume LitInt(0) <= k#1_0
               && _module.Stream.head(_module.__default.Tail(_module._default.Theorem_Filter$T, $LS($LZ), s#0, k#1_0))
                 == x#3;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(186,45)"} true;
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(187,14)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            s##1_0 := s#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            P##1_0 := P#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            x##1_0 := x#3;
            assume true;
            // ProcessCallStmt: CheckSubrange
            k##1_0 := k#1_0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call Call$$_module.__default.FS__Pong(_module._default.Theorem_Filter$T, s##1_0, P##1_0, x##1_0, k##1_0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(187,25)"} true;
        }
        else
        {
        }

        assert _module.__default.In(_module._default.Theorem_Filter$T, 
            x#3, 
            _module.__default.Filter(_module._default.Theorem_Filter$T, $LS($LS($LZ)), s#0, P#0))
           <==> _module.__default.In(_module._default.Theorem_Filter$T, x#3, s#0)
             && $Unbox(Apply1(_module._default.Theorem_Filter$T, TBool, $Heap, P#0, x#3)): bool;
        assume false;
    }
    else
    {
        assume (forall x#4: Box :: 
          { $Unbox(Apply1(_module._default.Theorem_Filter$T, TBool, $Heap, P#0, x#4)): bool } 
            { _module.__default.In(_module._default.Theorem_Filter$T, x#4, s#0) } 
            { _module.__default.In(_module._default.Theorem_Filter$T, 
              x#4, 
              _module.__default.Filter(_module._default.Theorem_Filter$T, $LS($LZ), s#0, P#0)) } 
          $IsBox(x#4, _module._default.Theorem_Filter$T) && Lit(true)
             ==> (_module.__default.In(_module._default.Theorem_Filter$T, 
                x#4, 
                _module.__default.Filter(_module._default.Theorem_Filter$T, $LS($LZ), s#0, P#0))
               <==> _module.__default.In(_module._default.Theorem_Filter$T, x#4, s#0)
                 && $Unbox(Apply1(_module._default.Theorem_Filter$T, TBool, $Heap, P#0, x#4)): bool));
    }

    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(189,2)"} true;
}



procedure {:_induction s#0, P#0} CheckWellformed$$_module.__default.FS__Ping(_module._default.FS_Ping$T: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.FS_Ping$T))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.FS_Ping$T), $Heap)
         && $IsA#_module.Stream(s#0), 
    P#0: HandleType
       where $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.FS_Ping$T, TBool))
         && $IsAlloc(P#0, Tclass._System.___hTotalFunc1(_module._default.FS_Ping$T, TBool), $Heap), 
    x#0: Box
       where $IsBox(x#0, _module._default.FS_Ping$T)
         && $IsAllocBox(x#0, _module._default.FS_Ping$T, $Heap));
  free requires 38 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:_induction s#0, P#0} CheckWellformed$$_module.__default.FS__Ping(_module._default.FS_Ping$T: Ty, s#0: DatatypeType, P#0: HandleType, x#0: Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##s#0: DatatypeType;
  var ##P#0: HandleType;
  var ##s#1: DatatypeType;
  var ##P#1: HandleType;
  var ##x#0: Box;
  var ##s#2: DatatypeType;
  var ##x#1: Box;
  var ##s#3: DatatypeType;

    // AddMethodImpl: FS_Ping, CheckWellformed$$_module.__default.FS__Ping
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(192,6): initial state"} true;
    ##s#0 := s#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#0, Tclass._module.Stream(_module._default.FS_Ping$T), $Heap);
    ##P#0 := P#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##P#0, Tclass._System.___hTotalFunc1(_module._default.FS_Ping$T, TBool), $Heap);
    assume _module.__default.AlwaysAnother#canCall(_module._default.FS_Ping$T, s#0, P#0);
    assume _module.__default.AlwaysAnother(_module._default.FS_Ping$T, $LS($LZ), s#0, P#0);
    ##s#1 := s#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#1, Tclass._module.Stream(_module._default.FS_Ping$T), $Heap);
    ##P#1 := P#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##P#1, Tclass._System.___hTotalFunc1(_module._default.FS_Ping$T, TBool), $Heap);
    assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.FS_Ping$T, ##s#1, ##P#1)
       ==> _module.__default.AlwaysAnother(_module._default.FS_Ping$T, $LS($LZ), ##s#1, ##P#1)
         || (_module.__default.IsAnother#canCall(_module._default.FS_Ping$T, ##s#1, ##P#1)
           ==> _module.__default.IsAnother(_module._default.FS_Ping$T, ##s#1, ##P#1)
             || (exists n#0: int :: 
              { _module.__default.Tail(_module._default.FS_Ping$T, $LS($LZ), ##s#1, n#0) } 
              LitInt(0) <= n#0
                 && 
                LitInt(0) <= n#0
                 && $Unbox(Apply1(_module._default.FS_Ping$T, 
                    TBool, 
                    $Heap, 
                    ##P#1, 
                    _module.Stream.head(_module.__default.Tail(_module._default.FS_Ping$T, $LS($LZ), ##s#1, n#0)))): bool));
    assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.FS_Ping$T, ##s#1, ##P#1)
       ==> _module.__default.AlwaysAnother(_module._default.FS_Ping$T, $LS($LZ), ##s#1, ##P#1)
         || _module.__default.AlwaysAnother(_module._default.FS_Ping$T, $LS($LS($LZ)), _module.Stream.tail(##s#1), ##P#1);
    assume _module.__default.AlwaysAnother(_module._default.FS_Ping$T, $LS($LZ), ##s#1, ##P#1);
    assume _module.__default.Filter#canCall(_module._default.FS_Ping$T, s#0, P#0);
    assume _module.Stream.Cons_q(_module.__default.Filter(_module._default.FS_Ping$T, $LS($LZ), s#0, P#0));
    ##x#0 := x#0;
    // assume allocatedness for argument to function
    assume $IsAllocBox(##x#0, _module._default.FS_Ping$T, $Heap);
    ##s#2 := _module.__default.Filter(_module._default.FS_Ping$T, $LS($LZ), s#0, P#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#2, Tclass._module.Stream(_module._default.FS_Ping$T), $Heap);
    assume _module.__default.In#canCall(_module._default.FS_Ping$T, 
      x#0, 
      _module.__default.Filter(_module._default.FS_Ping$T, $LS($LZ), s#0, P#0));
    assume _module.__default.In(_module._default.FS_Ping$T, 
      x#0, 
      _module.__default.Filter(_module._default.FS_Ping$T, $LS($LZ), s#0, P#0));
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(194,19): post-state"} true;
    ##x#1 := x#0;
    // assume allocatedness for argument to function
    assume $IsAllocBox(##x#1, _module._default.FS_Ping$T, $Heap);
    ##s#3 := s#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#3, Tclass._module.Stream(_module._default.FS_Ping$T), $Heap);
    assume _module.__default.In#canCall(_module._default.FS_Ping$T, x#0, s#0);
    assume _module.__default.In(_module._default.FS_Ping$T, x#0, s#0);
    assume $Unbox(Apply1(_module._default.FS_Ping$T, TBool, $Heap, P#0, x#0)): bool;
}



procedure {:_induction s#0, P#0} Call$$_module.__default.FS__Ping(_module._default.FS_Ping$T: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.FS_Ping$T))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.FS_Ping$T), $Heap)
         && $IsA#_module.Stream(s#0), 
    P#0: HandleType
       where $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.FS_Ping$T, TBool))
         && $IsAlloc(P#0, Tclass._System.___hTotalFunc1(_module._default.FS_Ping$T, TBool), $Heap), 
    x#0: Box
       where $IsBox(x#0, _module._default.FS_Ping$T)
         && $IsAllocBox(x#0, _module._default.FS_Ping$T, $Heap));
  // user-defined preconditions
  requires _module.__default.AlwaysAnother#canCall(_module._default.FS_Ping$T, s#0, P#0)
     ==> _module.__default.AlwaysAnother(_module._default.FS_Ping$T, $LS($LZ), s#0, P#0)
       || (_module.__default.IsAnother#canCall(_module._default.FS_Ping$T, s#0, P#0)
         ==> _module.__default.IsAnother(_module._default.FS_Ping$T, s#0, P#0)
           || (exists n#1: int :: 
            { _module.__default.Tail(_module._default.FS_Ping$T, $LS($LZ), s#0, n#1) } 
            LitInt(0) <= n#1
               && 
              LitInt(0) <= n#1
               && $Unbox(Apply1(_module._default.FS_Ping$T, 
                  TBool, 
                  $Heap, 
                  P#0, 
                  _module.Stream.head(_module.__default.Tail(_module._default.FS_Ping$T, $LS($LZ), s#0, n#1)))): bool));
  requires _module.__default.AlwaysAnother#canCall(_module._default.FS_Ping$T, s#0, P#0)
     ==> _module.__default.AlwaysAnother(_module._default.FS_Ping$T, $LS($LZ), s#0, P#0)
       || _module.__default.AlwaysAnother(_module._default.FS_Ping$T, $LS($LS($LZ)), _module.Stream.tail(s#0), P#0);
  requires _module.__default.In#canCall(_module._default.FS_Ping$T, 
      x#0, 
      _module.__default.Filter(_module._default.FS_Ping$T, $LS($LZ), s#0, P#0))
     ==> _module.__default.In(_module._default.FS_Ping$T, 
        x#0, 
        _module.__default.Filter(_module._default.FS_Ping$T, $LS($LZ), s#0, P#0))
       || (exists n#2: int :: 
        { _module.__default.Tail(_module._default.FS_Ping$T, 
            $LS($LZ), 
            _module.__default.Filter(_module._default.FS_Ping$T, $LS($LZ), s#0, P#0), 
            n#2) } 
        LitInt(0) <= n#2
           && 
          LitInt(0) <= n#2
           && _module.Stream.head(_module.__default.Tail(_module._default.FS_Ping$T, 
                $LS($LZ), 
                _module.__default.Filter(_module._default.FS_Ping$T, $LS($LZ), s#0, P#0), 
                n#2))
             == x#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.In#canCall(_module._default.FS_Ping$T, x#0, s#0);
  free ensures _module.__default.In#canCall(_module._default.FS_Ping$T, x#0, s#0)
     && 
    _module.__default.In(_module._default.FS_Ping$T, x#0, s#0)
     && (exists n#3: int :: 
      { _module.__default.Tail(_module._default.FS_Ping$T, $LS($LZ), s#0, n#3) } 
      LitInt(0) <= n#3
         && 
        LitInt(0) <= n#3
         && _module.Stream.head(_module.__default.Tail(_module._default.FS_Ping$T, $LS($LZ), s#0, n#3))
           == x#0);
  ensures $Unbox(Apply1(_module._default.FS_Ping$T, TBool, $Heap, P#0, x#0)): bool;
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction s#0, P#0} Impl$$_module.__default.FS__Ping(_module._default.FS_Ping$T: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.FS_Ping$T))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.FS_Ping$T), $Heap)
         && $IsA#_module.Stream(s#0), 
    P#0: HandleType
       where $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.FS_Ping$T, TBool))
         && $IsAlloc(P#0, Tclass._System.___hTotalFunc1(_module._default.FS_Ping$T, TBool), $Heap), 
    x#0: Box
       where $IsBox(x#0, _module._default.FS_Ping$T)
         && $IsAllocBox(x#0, _module._default.FS_Ping$T, $Heap))
   returns ($_reverifyPost: bool);
  free requires 38 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.__default.AlwaysAnother#canCall(_module._default.FS_Ping$T, s#0, P#0)
     && 
    _module.__default.AlwaysAnother(_module._default.FS_Ping$T, $LS($LZ), s#0, P#0)
     && 
    _module.__default.IsAnother(_module._default.FS_Ping$T, s#0, P#0)
     && _module.__default.AlwaysAnother(_module._default.FS_Ping$T, $LS($LZ), _module.Stream.tail(s#0), P#0);
  free requires _module.__default.In#canCall(_module._default.FS_Ping$T, 
      x#0, 
      _module.__default.Filter(_module._default.FS_Ping$T, $LS($LZ), s#0, P#0))
     && 
    _module.__default.In(_module._default.FS_Ping$T, 
      x#0, 
      _module.__default.Filter(_module._default.FS_Ping$T, $LS($LZ), s#0, P#0))
     && (exists n#5: int :: 
      { _module.__default.Tail(_module._default.FS_Ping$T, 
          $LS($LZ), 
          _module.__default.Filter(_module._default.FS_Ping$T, $LS($LZ), s#0, P#0), 
          n#5) } 
      LitInt(0) <= n#5
         && 
        LitInt(0) <= n#5
         && _module.Stream.head(_module.__default.Tail(_module._default.FS_Ping$T, 
              $LS($LZ), 
              _module.__default.Filter(_module._default.FS_Ping$T, $LS($LZ), s#0, P#0), 
              n#5))
           == x#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.In#canCall(_module._default.FS_Ping$T, x#0, s#0);
  ensures _module.__default.In#canCall(_module._default.FS_Ping$T, x#0, s#0)
     ==> _module.__default.In(_module._default.FS_Ping$T, x#0, s#0)
       || (exists n#6: int :: 
        { _module.__default.Tail(_module._default.FS_Ping$T, $LS($LZ), s#0, n#6) } 
        LitInt(0) <= n#6
           && 
          LitInt(0) <= n#6
           && _module.Stream.head(_module.__default.Tail(_module._default.FS_Ping$T, $LS($LZ), s#0, n#6))
             == x#0);
  ensures $Unbox(Apply1(_module._default.FS_Ping$T, TBool, $Heap, P#0, x#0)): bool;
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction s#0, P#0} Impl$$_module.__default.FS__Ping(_module._default.FS_Ping$T: Ty, s#0: DatatypeType, P#0: HandleType, x#0: Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var s##0: DatatypeType;
  var P##0: HandleType;
  var x##0: Box;
  var s##1: DatatypeType;
  var ##s#4: DatatypeType;
  var ##P#2: HandleType;
  var u##0: DatatypeType;
  var s##2: DatatypeType;
  var P##1: HandleType;
  var ##s#5: DatatypeType;
  var ##P#3: HandleType;
  var ##s#6: DatatypeType;
  var ##P#4: HandleType;
  var x##1: Box;
  var s##3: DatatypeType;
  var ##s#7: DatatypeType;
  var ##P#5: HandleType;
  var P##2: HandleType;

    // AddMethodImpl: FS_Ping, Impl$$_module.__default.FS__Ping
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(195,0): initial state"} true;
    assume $IsA#_module.Stream(s#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#s0#0: DatatypeType, $ih#P0#0: HandleType :: 
      $Is($ih#s0#0, Tclass._module.Stream(_module._default.FS_Ping$T))
           && $Is($ih#P0#0, Tclass._System.___hTotalFunc1(_module._default.FS_Ping$T, TBool))
           && 
          _module.__default.AlwaysAnother(_module._default.FS_Ping$T, $LS($LZ), $ih#s0#0, $ih#P0#0)
           && _module.__default.In(_module._default.FS_Ping$T, 
            x#0, 
            _module.__default.Filter(_module._default.FS_Ping$T, $LS($LZ), $ih#s0#0, $ih#P0#0))
           && false
         ==> _module.__default.In(_module._default.FS_Ping$T, x#0, $ih#s0#0)
           && $Unbox(Apply1(_module._default.FS_Ping$T, TBool, $Heap, $ih#P0#0, x#0)): bool);
    $_reverifyPost := false;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(196,21)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    s##0 := s#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    P##0 := P#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.Filter__IsSubStream(_module._default.FS_Ping$T, s##0, P##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(196,26)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(197,20)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##0 := x#0;
    ##s#4 := s#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#4, Tclass._module.Stream(_module._default.FS_Ping$T), $Heap);
    ##P#2 := P#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##P#2, Tclass._System.___hTotalFunc1(_module._default.FS_Ping$T, TBool), $Heap);
    assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.FS_Ping$T, ##s#4, ##P#2)
       ==> _module.__default.AlwaysAnother(_module._default.FS_Ping$T, $LS($LZ), ##s#4, ##P#2)
         || (_module.__default.IsAnother#canCall(_module._default.FS_Ping$T, ##s#4, ##P#2)
           ==> _module.__default.IsAnother(_module._default.FS_Ping$T, ##s#4, ##P#2)
             || (exists n#7: int :: 
              { _module.__default.Tail(_module._default.FS_Ping$T, $LS($LZ), ##s#4, n#7) } 
              LitInt(0) <= n#7
                 && 
                LitInt(0) <= n#7
                 && $Unbox(Apply1(_module._default.FS_Ping$T, 
                    TBool, 
                    $Heap, 
                    ##P#2, 
                    _module.Stream.head(_module.__default.Tail(_module._default.FS_Ping$T, $LS($LZ), ##s#4, n#7)))): bool));
    assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.FS_Ping$T, ##s#4, ##P#2)
       ==> _module.__default.AlwaysAnother(_module._default.FS_Ping$T, $LS($LZ), ##s#4, ##P#2)
         || _module.__default.AlwaysAnother(_module._default.FS_Ping$T, $LS($LS($LZ)), _module.Stream.tail(##s#4), ##P#2);
    assume _module.__default.AlwaysAnother(_module._default.FS_Ping$T, $LS($LZ), ##s#4, ##P#2);
    assume _module.__default.Filter#canCall(_module._default.FS_Ping$T, s#0, P#0);
    assume _module.Stream.Cons_q(_module.__default.Filter(_module._default.FS_Ping$T, $LS($LZ), s#0, P#0));
    assume _module.__default.Filter#canCall(_module._default.FS_Ping$T, s#0, P#0);
    // ProcessCallStmt: CheckSubrange
    s##1 := _module.__default.Filter(_module._default.FS_Ping$T, $LS($LZ), s#0, P#0);
    assume true;
    // ProcessCallStmt: CheckSubrange
    u##0 := s#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.Lemma__InSubStream(_module._default.FS_Ping$T, x##0, s##1, u##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(197,39)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(199,23)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    s##2 := s#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    P##1 := P#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.Filter__AlwaysAnother(_module._default.FS_Ping$T, s##2, P##1);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(199,28)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(200,3)
    ##s#5 := s#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#5, Tclass._module.Stream(_module._default.FS_Ping$T), $Heap);
    ##P#3 := P#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##P#3, Tclass._System.___hTotalFunc1(_module._default.FS_Ping$T, TBool), $Heap);
    assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.FS_Ping$T, ##s#5, ##P#3)
       ==> _module.__default.AlwaysAnother(_module._default.FS_Ping$T, $LS($LZ), ##s#5, ##P#3)
         || (_module.__default.IsAnother#canCall(_module._default.FS_Ping$T, ##s#5, ##P#3)
           ==> _module.__default.IsAnother(_module._default.FS_Ping$T, ##s#5, ##P#3)
             || (exists n#8: int :: 
              { _module.__default.Tail(_module._default.FS_Ping$T, $LS($LZ), ##s#5, n#8) } 
              LitInt(0) <= n#8
                 && 
                LitInt(0) <= n#8
                 && $Unbox(Apply1(_module._default.FS_Ping$T, 
                    TBool, 
                    $Heap, 
                    ##P#3, 
                    _module.Stream.head(_module.__default.Tail(_module._default.FS_Ping$T, $LS($LZ), ##s#5, n#8)))): bool));
    assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.FS_Ping$T, ##s#5, ##P#3)
       ==> _module.__default.AlwaysAnother(_module._default.FS_Ping$T, $LS($LZ), ##s#5, ##P#3)
         || _module.__default.AlwaysAnother(_module._default.FS_Ping$T, $LS($LS($LZ)), _module.Stream.tail(##s#5), ##P#3);
    assume _module.__default.Filter#canCall(_module._default.FS_Ping$T, s#0, P#0);
    assume _module.Stream.Cons_q(_module.__default.Filter(_module._default.FS_Ping$T, $LS($LZ), s#0, P#0));
    ##s#6 := _module.__default.Filter(_module._default.FS_Ping$T, $LS($LZ), s#0, P#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#6, Tclass._module.Stream(_module._default.FS_Ping$T), $Heap);
    ##P#4 := P#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##P#4, Tclass._System.___hTotalFunc1(_module._default.FS_Ping$T, TBool), $Heap);
    assume _module.__default.AllP#canCall(_module._default.FS_Ping$T, 
      _module.__default.Filter(_module._default.FS_Ping$T, $LS($LZ), s#0, P#0), 
      P#0);
    assume _module.__default.Filter#canCall(_module._default.FS_Ping$T, s#0, P#0)
       && _module.__default.AllP#canCall(_module._default.FS_Ping$T, 
        _module.__default.Filter(_module._default.FS_Ping$T, $LS($LZ), s#0, P#0), 
        P#0);
    assert {:subsumption 0} _module.__default.AllP#canCall(_module._default.FS_Ping$T, 
        _module.__default.Filter(_module._default.FS_Ping$T, $LS($LZ), s#0, P#0), 
        P#0)
       ==> _module.__default.AllP(_module._default.FS_Ping$T, 
          $LS($LZ), 
          _module.__default.Filter(_module._default.FS_Ping$T, $LS($LZ), s#0, P#0), 
          P#0)
         || $Unbox(Apply1(_module._default.FS_Ping$T, 
            TBool, 
            $Heap, 
            P#0, 
            _module.Stream.head(_module.__default.Filter(_module._default.FS_Ping$T, $LS($LS($LZ)), s#0, P#0)))): bool;
    assert {:subsumption 0} _module.__default.AllP#canCall(_module._default.FS_Ping$T, 
        _module.__default.Filter(_module._default.FS_Ping$T, $LS($LZ), s#0, P#0), 
        P#0)
       ==> _module.__default.AllP(_module._default.FS_Ping$T, 
          $LS($LZ), 
          _module.__default.Filter(_module._default.FS_Ping$T, $LS($LZ), s#0, P#0), 
          P#0)
         || _module.__default.AllP(_module._default.FS_Ping$T, 
          $LS($LS($LZ)), 
          _module.Stream.tail(_module.__default.Filter(_module._default.FS_Ping$T, $LS($LS($LZ)), s#0, P#0)), 
          P#0);
    assume _module.__default.AllP(_module._default.FS_Ping$T, 
      $LS($LZ), 
      _module.__default.Filter(_module._default.FS_Ping$T, $LS($LZ), s#0, P#0), 
      P#0);
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(201,15)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##1 := x#0;
    ##s#7 := s#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#7, Tclass._module.Stream(_module._default.FS_Ping$T), $Heap);
    ##P#5 := P#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##P#5, Tclass._System.___hTotalFunc1(_module._default.FS_Ping$T, TBool), $Heap);
    assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.FS_Ping$T, ##s#7, ##P#5)
       ==> _module.__default.AlwaysAnother(_module._default.FS_Ping$T, $LS($LZ), ##s#7, ##P#5)
         || (_module.__default.IsAnother#canCall(_module._default.FS_Ping$T, ##s#7, ##P#5)
           ==> _module.__default.IsAnother(_module._default.FS_Ping$T, ##s#7, ##P#5)
             || (exists n#9: int :: 
              { _module.__default.Tail(_module._default.FS_Ping$T, $LS($LZ), ##s#7, n#9) } 
              LitInt(0) <= n#9
                 && 
                LitInt(0) <= n#9
                 && $Unbox(Apply1(_module._default.FS_Ping$T, 
                    TBool, 
                    $Heap, 
                    ##P#5, 
                    _module.Stream.head(_module.__default.Tail(_module._default.FS_Ping$T, $LS($LZ), ##s#7, n#9)))): bool));
    assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.FS_Ping$T, ##s#7, ##P#5)
       ==> _module.__default.AlwaysAnother(_module._default.FS_Ping$T, $LS($LZ), ##s#7, ##P#5)
         || _module.__default.AlwaysAnother(_module._default.FS_Ping$T, $LS($LS($LZ)), _module.Stream.tail(##s#7), ##P#5);
    assume _module.__default.AlwaysAnother(_module._default.FS_Ping$T, $LS($LZ), ##s#7, ##P#5);
    assume _module.__default.Filter#canCall(_module._default.FS_Ping$T, s#0, P#0);
    assume _module.Stream.Cons_q(_module.__default.Filter(_module._default.FS_Ping$T, $LS($LZ), s#0, P#0));
    assume _module.__default.Filter#canCall(_module._default.FS_Ping$T, s#0, P#0);
    // ProcessCallStmt: CheckSubrange
    s##3 := _module.__default.Filter(_module._default.FS_Ping$T, $LS($LZ), s#0, P#0);
    assume true;
    // ProcessCallStmt: CheckSubrange
    P##2 := P#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.Lemma__InAllP(_module._default.FS_Ping$T, x##1, s##3, P##2);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(201,34)"} true;
}



procedure {:_induction s#0, P#0, k#0} CheckWellformed$$_module.__default.FS__Pong(_module._default.FS_Pong$T: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.FS_Pong$T))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.FS_Pong$T), $Heap)
         && $IsA#_module.Stream(s#0), 
    P#0: HandleType
       where $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.FS_Pong$T, TBool))
         && $IsAlloc(P#0, Tclass._System.___hTotalFunc1(_module._default.FS_Pong$T, TBool), $Heap), 
    x#0: Box
       where $IsBox(x#0, _module._default.FS_Pong$T)
         && $IsAllocBox(x#0, _module._default.FS_Pong$T, $Heap), 
    k#0: int where LitInt(0) <= k#0);
  free requires 39 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:_induction s#0, P#0, k#0} CheckWellformed$$_module.__default.FS__Pong(_module._default.FS_Pong$T: Ty, 
    s#0: DatatypeType, 
    P#0: HandleType, 
    x#0: Box, 
    k#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##s#0: DatatypeType;
  var ##P#0: HandleType;
  var ##x#0: Box;
  var ##s#1: DatatypeType;
  var ##s#2: DatatypeType;
  var ##n#0: int;
  var ##s#3: DatatypeType;
  var ##P#1: HandleType;
  var ##x#1: Box;
  var ##s#4: DatatypeType;

    // AddMethodImpl: FS_Pong, CheckWellformed$$_module.__default.FS__Pong
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(204,6): initial state"} true;
    ##s#0 := s#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#0, Tclass._module.Stream(_module._default.FS_Pong$T), $Heap);
    ##P#0 := P#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##P#0, Tclass._System.___hTotalFunc1(_module._default.FS_Pong$T, TBool), $Heap);
    assume _module.__default.AlwaysAnother#canCall(_module._default.FS_Pong$T, s#0, P#0);
    assume _module.__default.AlwaysAnother(_module._default.FS_Pong$T, $LS($LZ), s#0, P#0);
    ##x#0 := x#0;
    // assume allocatedness for argument to function
    assume $IsAllocBox(##x#0, _module._default.FS_Pong$T, $Heap);
    ##s#1 := s#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#1, Tclass._module.Stream(_module._default.FS_Pong$T), $Heap);
    assume _module.__default.In#canCall(_module._default.FS_Pong$T, x#0, s#0);
    assume _module.__default.In(_module._default.FS_Pong$T, x#0, s#0);
    assume $Unbox(Apply1(_module._default.FS_Pong$T, TBool, $Heap, P#0, x#0)): bool;
    ##s#2 := s#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#2, Tclass._module.Stream(_module._default.FS_Pong$T), $Heap);
    ##n#0 := k#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
    assume _module.__default.Tail#canCall(_module._default.FS_Pong$T, s#0, k#0);
    assume _module.Stream.Cons_q(_module.__default.Tail(_module._default.FS_Pong$T, $LS($LZ), s#0, k#0));
    assume _module.Stream.Cons_q(_module.__default.Tail(_module._default.FS_Pong$T, $LS($LZ), s#0, k#0));
    assume _module.Stream.head(_module.__default.Tail(_module._default.FS_Pong$T, $LS($LZ), s#0, k#0))
       == x#0;
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(207,12): post-state"} true;
    ##s#3 := s#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#3, Tclass._module.Stream(_module._default.FS_Pong$T), $Heap);
    ##P#1 := P#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##P#1, Tclass._System.___hTotalFunc1(_module._default.FS_Pong$T, TBool), $Heap);
    assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.FS_Pong$T, ##s#3, ##P#1)
       ==> _module.__default.AlwaysAnother(_module._default.FS_Pong$T, $LS($LZ), ##s#3, ##P#1)
         || (_module.__default.IsAnother#canCall(_module._default.FS_Pong$T, ##s#3, ##P#1)
           ==> _module.__default.IsAnother(_module._default.FS_Pong$T, ##s#3, ##P#1)
             || (exists n#0: int :: 
              { _module.__default.Tail(_module._default.FS_Pong$T, $LS($LZ), ##s#3, n#0) } 
              LitInt(0) <= n#0
                 && 
                LitInt(0) <= n#0
                 && $Unbox(Apply1(_module._default.FS_Pong$T, 
                    TBool, 
                    $Heap, 
                    ##P#1, 
                    _module.Stream.head(_module.__default.Tail(_module._default.FS_Pong$T, $LS($LZ), ##s#3, n#0)))): bool));
    assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.FS_Pong$T, ##s#3, ##P#1)
       ==> _module.__default.AlwaysAnother(_module._default.FS_Pong$T, $LS($LZ), ##s#3, ##P#1)
         || _module.__default.AlwaysAnother(_module._default.FS_Pong$T, $LS($LS($LZ)), _module.Stream.tail(##s#3), ##P#1);
    assume _module.__default.AlwaysAnother(_module._default.FS_Pong$T, $LS($LZ), ##s#3, ##P#1);
    assume _module.__default.Filter#canCall(_module._default.FS_Pong$T, s#0, P#0);
    assume _module.Stream.Cons_q(_module.__default.Filter(_module._default.FS_Pong$T, $LS($LZ), s#0, P#0));
    ##x#1 := x#0;
    // assume allocatedness for argument to function
    assume $IsAllocBox(##x#1, _module._default.FS_Pong$T, $Heap);
    ##s#4 := _module.__default.Filter(_module._default.FS_Pong$T, $LS($LZ), s#0, P#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#4, Tclass._module.Stream(_module._default.FS_Pong$T), $Heap);
    assume _module.__default.In#canCall(_module._default.FS_Pong$T, 
      x#0, 
      _module.__default.Filter(_module._default.FS_Pong$T, $LS($LZ), s#0, P#0));
    assume _module.__default.In(_module._default.FS_Pong$T, 
      x#0, 
      _module.__default.Filter(_module._default.FS_Pong$T, $LS($LZ), s#0, P#0));
}



procedure {:_induction s#0, P#0, k#0} Call$$_module.__default.FS__Pong(_module._default.FS_Pong$T: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.FS_Pong$T))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.FS_Pong$T), $Heap)
         && $IsA#_module.Stream(s#0), 
    P#0: HandleType
       where $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.FS_Pong$T, TBool))
         && $IsAlloc(P#0, Tclass._System.___hTotalFunc1(_module._default.FS_Pong$T, TBool), $Heap), 
    x#0: Box
       where $IsBox(x#0, _module._default.FS_Pong$T)
         && $IsAllocBox(x#0, _module._default.FS_Pong$T, $Heap), 
    k#0: int where LitInt(0) <= k#0);
  // user-defined preconditions
  requires _module.__default.AlwaysAnother#canCall(_module._default.FS_Pong$T, s#0, P#0)
     ==> _module.__default.AlwaysAnother(_module._default.FS_Pong$T, $LS($LZ), s#0, P#0)
       || (_module.__default.IsAnother#canCall(_module._default.FS_Pong$T, s#0, P#0)
         ==> _module.__default.IsAnother(_module._default.FS_Pong$T, s#0, P#0)
           || (exists n#1: int :: 
            { _module.__default.Tail(_module._default.FS_Pong$T, $LS($LZ), s#0, n#1) } 
            LitInt(0) <= n#1
               && 
              LitInt(0) <= n#1
               && $Unbox(Apply1(_module._default.FS_Pong$T, 
                  TBool, 
                  $Heap, 
                  P#0, 
                  _module.Stream.head(_module.__default.Tail(_module._default.FS_Pong$T, $LS($LZ), s#0, n#1)))): bool));
  requires _module.__default.AlwaysAnother#canCall(_module._default.FS_Pong$T, s#0, P#0)
     ==> _module.__default.AlwaysAnother(_module._default.FS_Pong$T, $LS($LZ), s#0, P#0)
       || _module.__default.AlwaysAnother(_module._default.FS_Pong$T, $LS($LS($LZ)), _module.Stream.tail(s#0), P#0);
  requires _module.__default.In#canCall(_module._default.FS_Pong$T, x#0, s#0)
     ==> _module.__default.In(_module._default.FS_Pong$T, x#0, s#0)
       || (exists n#2: int :: 
        { _module.__default.Tail(_module._default.FS_Pong$T, $LS($LZ), s#0, n#2) } 
        LitInt(0) <= n#2
           && 
          LitInt(0) <= n#2
           && _module.Stream.head(_module.__default.Tail(_module._default.FS_Pong$T, $LS($LZ), s#0, n#2))
             == x#0);
  requires $Unbox(Apply1(_module._default.FS_Pong$T, TBool, $Heap, P#0, x#0)): bool;
  requires _module.Stream.head(_module.__default.Tail(_module._default.FS_Pong$T, $LS($LS($LZ)), s#0, k#0))
     == x#0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Filter#canCall(_module._default.FS_Pong$T, s#0, P#0)
     && _module.__default.In#canCall(_module._default.FS_Pong$T, 
      x#0, 
      _module.__default.Filter(_module._default.FS_Pong$T, $LS($LZ), s#0, P#0));
  free ensures _module.__default.In#canCall(_module._default.FS_Pong$T, 
      x#0, 
      _module.__default.Filter(_module._default.FS_Pong$T, $LS($LZ), s#0, P#0))
     && 
    _module.__default.In(_module._default.FS_Pong$T, 
      x#0, 
      _module.__default.Filter(_module._default.FS_Pong$T, $LS($LZ), s#0, P#0))
     && (exists n#3: int :: 
      { _module.__default.Tail(_module._default.FS_Pong$T, 
          $LS($LZ), 
          _module.__default.Filter(_module._default.FS_Pong$T, $LS($LZ), s#0, P#0), 
          n#3) } 
      LitInt(0) <= n#3
         && 
        LitInt(0) <= n#3
         && _module.Stream.head(_module.__default.Tail(_module._default.FS_Pong$T, 
              $LS($LZ), 
              _module.__default.Filter(_module._default.FS_Pong$T, $LS($LZ), s#0, P#0), 
              n#3))
           == x#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction s#0, P#0, k#0} Impl$$_module.__default.FS__Pong(_module._default.FS_Pong$T: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.FS_Pong$T))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.FS_Pong$T), $Heap)
         && $IsA#_module.Stream(s#0), 
    P#0: HandleType
       where $Is(P#0, Tclass._System.___hTotalFunc1(_module._default.FS_Pong$T, TBool))
         && $IsAlloc(P#0, Tclass._System.___hTotalFunc1(_module._default.FS_Pong$T, TBool), $Heap), 
    x#0: Box
       where $IsBox(x#0, _module._default.FS_Pong$T)
         && $IsAllocBox(x#0, _module._default.FS_Pong$T, $Heap), 
    k#0: int where LitInt(0) <= k#0)
   returns ($_reverifyPost: bool);
  free requires 39 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.__default.AlwaysAnother#canCall(_module._default.FS_Pong$T, s#0, P#0)
     && 
    _module.__default.AlwaysAnother(_module._default.FS_Pong$T, $LS($LZ), s#0, P#0)
     && 
    _module.__default.IsAnother(_module._default.FS_Pong$T, s#0, P#0)
     && _module.__default.AlwaysAnother(_module._default.FS_Pong$T, $LS($LZ), _module.Stream.tail(s#0), P#0);
  free requires _module.__default.In#canCall(_module._default.FS_Pong$T, x#0, s#0)
     && 
    _module.__default.In(_module._default.FS_Pong$T, x#0, s#0)
     && (exists n#5: int :: 
      { _module.__default.Tail(_module._default.FS_Pong$T, $LS($LZ), s#0, n#5) } 
      LitInt(0) <= n#5
         && 
        LitInt(0) <= n#5
         && _module.Stream.head(_module.__default.Tail(_module._default.FS_Pong$T, $LS($LZ), s#0, n#5))
           == x#0);
  requires $Unbox(Apply1(_module._default.FS_Pong$T, TBool, $Heap, P#0, x#0)): bool;
  requires _module.Stream.head(_module.__default.Tail(_module._default.FS_Pong$T, $LS($LS($LZ)), s#0, k#0))
     == x#0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Filter#canCall(_module._default.FS_Pong$T, s#0, P#0)
     && _module.__default.In#canCall(_module._default.FS_Pong$T, 
      x#0, 
      _module.__default.Filter(_module._default.FS_Pong$T, $LS($LZ), s#0, P#0));
  ensures _module.__default.In#canCall(_module._default.FS_Pong$T, 
      x#0, 
      _module.__default.Filter(_module._default.FS_Pong$T, $LS($LZ), s#0, P#0))
     ==> _module.__default.In(_module._default.FS_Pong$T, 
        x#0, 
        _module.__default.Filter(_module._default.FS_Pong$T, $LS($LZ), s#0, P#0))
       || (exists n#6: int :: 
        { _module.__default.Tail(_module._default.FS_Pong$T, 
            $LS($LZ), 
            _module.__default.Filter(_module._default.FS_Pong$T, $LS($LZ), s#0, P#0), 
            n#6) } 
        LitInt(0) <= n#6
           && 
          LitInt(0) <= n#6
           && _module.Stream.head(_module.__default.Tail(_module._default.FS_Pong$T, 
                $LS($LZ), 
                _module.__default.Filter(_module._default.FS_Pong$T, $LS($LZ), s#0, P#0), 
                n#6))
             == x#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction s#0, P#0, k#0} Impl$$_module.__default.FS__Pong(_module._default.FS_Pong$T: Ty, 
    s#0: DatatypeType, 
    P#0: HandleType, 
    x#0: Box, 
    k#0: int)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var fs#0: DatatypeType
     where $Is(fs#0, Tclass._module.Stream(_module._default.FS_Pong$T))
       && $IsAlloc(fs#0, Tclass._module.Stream(_module._default.FS_Pong$T), $Heap);
  var ##s#5: DatatypeType;
  var ##P#2: HandleType;
  var ##s#0_0: DatatypeType;
  var ##n#0_0: int;
  var ##s#1_0: DatatypeType;
  var ##P#1_0: HandleType;
  var ##s#1_0_0_0: DatatypeType;
  var ##P#1_0_0_0: HandleType;
  var ##x#1_0_0_0: Box;
  var ##s#1_0_0_1: DatatypeType;
  var x##1_0_0_0: Box;
  var s##1_0_0_0: DatatypeType;
  var ##x#1_0_0_1: Box;
  var ##s#1_0_0_2: DatatypeType;
  var ##s#1_0_1_0: DatatypeType;
  var ##P#1_0_1_0: HandleType;
  var ##x#1_0_1_0: Box;
  var ##s#1_0_1_1: DatatypeType;

    // AddMethodImpl: FS_Pong, Impl$$_module.__default.FS__Pong
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(209,0): initial state"} true;
    assume $IsA#_module.Stream(s#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#s0#0: DatatypeType, $ih#P0#0: HandleType, $ih#k0#0: int :: 
      $Is($ih#s0#0, Tclass._module.Stream(_module._default.FS_Pong$T))
           && $Is($ih#P0#0, Tclass._System.___hTotalFunc1(_module._default.FS_Pong$T, TBool))
           && LitInt(0) <= $ih#k0#0
           && 
          _module.__default.AlwaysAnother(_module._default.FS_Pong$T, $LS($LZ), $ih#s0#0, $ih#P0#0)
           && _module.__default.In(_module._default.FS_Pong$T, x#0, $ih#s0#0)
           && $Unbox(Apply1(_module._default.FS_Pong$T, TBool, $initHeapForallStmt#0, $ih#P0#0, x#0)): bool
           && _module.Stream.head(_module.__default.Tail(_module._default.FS_Pong$T, $LS($LZ), $ih#s0#0, $ih#k0#0))
             == x#0
           && 
          0 <= $ih#k0#0
           && $ih#k0#0 < k#0
         ==> _module.__default.In(_module._default.FS_Pong$T, 
          x#0, 
          _module.__default.Filter(_module._default.FS_Pong$T, $LS($LZ), $ih#s0#0, $ih#P0#0)));
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(210,10)
    assume true;
    ##s#5 := s#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#5, Tclass._module.Stream(_module._default.FS_Pong$T), $Heap);
    ##P#2 := P#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##P#2, Tclass._System.___hTotalFunc1(_module._default.FS_Pong$T, TBool), $Heap);
    assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.FS_Pong$T, ##s#5, ##P#2)
       ==> _module.__default.AlwaysAnother(_module._default.FS_Pong$T, $LS($LZ), ##s#5, ##P#2)
         || (_module.__default.IsAnother#canCall(_module._default.FS_Pong$T, ##s#5, ##P#2)
           ==> _module.__default.IsAnother(_module._default.FS_Pong$T, ##s#5, ##P#2)
             || (exists n#7: int :: 
              { _module.__default.Tail(_module._default.FS_Pong$T, $LS($LZ), ##s#5, n#7) } 
              LitInt(0) <= n#7
                 && 
                LitInt(0) <= n#7
                 && $Unbox(Apply1(_module._default.FS_Pong$T, 
                    TBool, 
                    $Heap, 
                    ##P#2, 
                    _module.Stream.head(_module.__default.Tail(_module._default.FS_Pong$T, $LS($LZ), ##s#5, n#7)))): bool));
    assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.FS_Pong$T, ##s#5, ##P#2)
       ==> _module.__default.AlwaysAnother(_module._default.FS_Pong$T, $LS($LZ), ##s#5, ##P#2)
         || _module.__default.AlwaysAnother(_module._default.FS_Pong$T, $LS($LS($LZ)), _module.Stream.tail(##s#5), ##P#2);
    assume _module.__default.AlwaysAnother(_module._default.FS_Pong$T, $LS($LZ), ##s#5, ##P#2);
    assume _module.__default.Filter#canCall(_module._default.FS_Pong$T, s#0, P#0);
    assume _module.Stream.Cons_q(_module.__default.Filter(_module._default.FS_Pong$T, $LS($LZ), s#0, P#0));
    assume _module.__default.Filter#canCall(_module._default.FS_Pong$T, s#0, P#0);
    fs#0 := _module.__default.Filter(_module._default.FS_Pong$T, $LS($LZ), s#0, P#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(210,24)"} true;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(211,3)
    assume _module.Stream.Cons_q(s#0);
    assume _module.Stream.Cons_q(s#0);
    if (_module.Stream.head(s#0) == x#0)
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(212,5)
        ##s#0_0 := fs#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#0_0, Tclass._module.Stream(_module._default.FS_Pong$T), $Heap);
        assert $Is(LitInt(0), Tclass._System.nat());
        ##n#0_0 := LitInt(0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#0_0, Tclass._System.nat(), $Heap);
        assume _module.__default.Tail#canCall(_module._default.FS_Pong$T, fs#0, LitInt(0));
        assume _module.Stream.Cons_q(_module.__default.Tail(_module._default.FS_Pong$T, $LS($LZ), fs#0, LitInt(0)));
        assume $IsA#_module.Stream(_module.__default.Tail(_module._default.FS_Pong$T, $LS($LZ), fs#0, LitInt(0)))
           && $IsA#_module.Stream(fs#0)
           && _module.__default.Tail#canCall(_module._default.FS_Pong$T, fs#0, LitInt(0));
        assert {:subsumption 0} $Eq#_module.Stream(_module._default.FS_Pong$T, 
          _module._default.FS_Pong$T, 
          $LS($LS($LZ)), 
          _module.__default.Tail(_module._default.FS_Pong$T, $LS($LS($LZ)), fs#0, LitInt(0)), 
          fs#0);
        assume $Eq#_module.Stream(_module._default.FS_Pong$T, 
          _module._default.FS_Pong$T, 
          $LS($LS($LZ)), 
          _module.__default.Tail(_module._default.FS_Pong$T, $LS($LZ), fs#0, LitInt(0)), 
          fs#0);
    }
    else
    {
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(213,10)
        assume _module.Stream.Cons_q(s#0);
        assume _module.Stream.Cons_q(s#0);
        if ($Unbox(Apply1(_module._default.FS_Pong$T, TBool, $Heap, P#0, _module.Stream.head(s#0))): bool)
        {
            // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(214,5)
            assume _module.Stream.Cons_q(s#0);
            assume _module.Stream.Cons_q(s#0);
            ##s#1_0 := _module.Stream.tail(s#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#1_0, Tclass._module.Stream(_module._default.FS_Pong$T), $Heap);
            ##P#1_0 := P#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##P#1_0, Tclass._System.___hTotalFunc1(_module._default.FS_Pong$T, TBool), $Heap);
            assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.FS_Pong$T, ##s#1_0, ##P#1_0)
               ==> _module.__default.AlwaysAnother(_module._default.FS_Pong$T, $LS($LZ), ##s#1_0, ##P#1_0)
                 || (_module.__default.IsAnother#canCall(_module._default.FS_Pong$T, ##s#1_0, ##P#1_0)
                   ==> _module.__default.IsAnother(_module._default.FS_Pong$T, ##s#1_0, ##P#1_0)
                     || (exists n#1_0: int :: 
                      { _module.__default.Tail(_module._default.FS_Pong$T, $LS($LZ), ##s#1_0, n#1_0) } 
                      LitInt(0) <= n#1_0
                         && 
                        LitInt(0) <= n#1_0
                         && $Unbox(Apply1(_module._default.FS_Pong$T, 
                            TBool, 
                            $Heap, 
                            ##P#1_0, 
                            _module.Stream.head(_module.__default.Tail(_module._default.FS_Pong$T, $LS($LZ), ##s#1_0, n#1_0)))): bool));
            assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.FS_Pong$T, ##s#1_0, ##P#1_0)
               ==> _module.__default.AlwaysAnother(_module._default.FS_Pong$T, $LS($LZ), ##s#1_0, ##P#1_0)
                 || _module.__default.AlwaysAnother(_module._default.FS_Pong$T, $LS($LS($LZ)), _module.Stream.tail(##s#1_0), ##P#1_0);
            assume _module.__default.Filter#canCall(_module._default.FS_Pong$T, _module.Stream.tail(s#0), P#0);
            assume _module.Stream.Cons_q(_module.__default.Filter(_module._default.FS_Pong$T, $LS($LZ), _module.Stream.tail(s#0), P#0));
            assume $IsA#_module.Stream(fs#0)
               && 
              _module.Stream.Cons_q(s#0)
               && 
              _module.Stream.Cons_q(s#0)
               && _module.__default.Filter#canCall(_module._default.FS_Pong$T, _module.Stream.tail(s#0), P#0);
            assert {:subsumption 0} $Eq#_module.Stream(_module._default.FS_Pong$T, 
              _module._default.FS_Pong$T, 
              $LS($LS($LZ)), 
              fs#0, 
              #_module.Stream.Cons(_module.Stream.head(s#0), 
                _module.__default.Filter(_module._default.FS_Pong$T, $LS($LS($LZ)), _module.Stream.tail(s#0), P#0)));
            assume $Eq#_module.Stream(_module._default.FS_Pong$T, 
              _module._default.FS_Pong$T, 
              $LS($LS($LZ)), 
              fs#0, 
              #_module.Stream.Cons(_module.Stream.head(s#0), 
                _module.__default.Filter(_module._default.FS_Pong$T, $LS($LZ), _module.Stream.tail(s#0), P#0)));
            // ----- calc statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(215,5)
            // Assume Fuel Constant
            if (*)
            {
                // ----- assert wf[initial] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(215,5)
                assume true;
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(215,5)
                assume true;
                // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(215,5)
                assume true;
                // ----- Hint0 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(215,5)
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(215,5)
                assume _module.Stream.Cons_q(s#0);
                ##s#1_0_1_0 := _module.Stream.tail(s#0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#1_0_1_0, Tclass._module.Stream(_module._default.FS_Pong$T), $Heap);
                ##P#1_0_1_0 := P#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##P#1_0_1_0, 
                  Tclass._System.___hTotalFunc1(_module._default.FS_Pong$T, TBool), 
                  $Heap);
                assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.FS_Pong$T, ##s#1_0_1_0, ##P#1_0_1_0)
                   ==> _module.__default.AlwaysAnother(_module._default.FS_Pong$T, $LS($LZ), ##s#1_0_1_0, ##P#1_0_1_0)
                     || (_module.__default.IsAnother#canCall(_module._default.FS_Pong$T, ##s#1_0_1_0, ##P#1_0_1_0)
                       ==> _module.__default.IsAnother(_module._default.FS_Pong$T, ##s#1_0_1_0, ##P#1_0_1_0)
                         || (exists n#1_0_1_0: int :: 
                          { _module.__default.Tail(_module._default.FS_Pong$T, $LS($LZ), ##s#1_0_1_0, n#1_0_1_0) } 
                          LitInt(0) <= n#1_0_1_0
                             && 
                            LitInt(0) <= n#1_0_1_0
                             && $Unbox(Apply1(_module._default.FS_Pong$T, 
                                TBool, 
                                $Heap, 
                                ##P#1_0_1_0, 
                                _module.Stream.head(_module.__default.Tail(_module._default.FS_Pong$T, $LS($LZ), ##s#1_0_1_0, n#1_0_1_0)))): bool));
                assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.FS_Pong$T, ##s#1_0_1_0, ##P#1_0_1_0)
                   ==> _module.__default.AlwaysAnother(_module._default.FS_Pong$T, $LS($LZ), ##s#1_0_1_0, ##P#1_0_1_0)
                     || _module.__default.AlwaysAnother(_module._default.FS_Pong$T, 
                      $LS($LS($LZ)), 
                      _module.Stream.tail(##s#1_0_1_0), 
                      ##P#1_0_1_0);
                assume _module.__default.Filter#canCall(_module._default.FS_Pong$T, _module.Stream.tail(s#0), P#0);
                assume _module.Stream.Cons_q(_module.__default.Filter(_module._default.FS_Pong$T, $LS($LZ), _module.Stream.tail(s#0), P#0));
                ##x#1_0_1_0 := x#0;
                // assume allocatedness for argument to function
                assume $IsAllocBox(##x#1_0_1_0, _module._default.FS_Pong$T, $Heap);
                ##s#1_0_1_1 := _module.__default.Filter(_module._default.FS_Pong$T, $LS($LZ), _module.Stream.tail(s#0), P#0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#1_0_1_1, Tclass._module.Stream(_module._default.FS_Pong$T), $Heap);
                assume _module.__default.In#canCall(_module._default.FS_Pong$T, 
                  x#0, 
                  _module.__default.Filter(_module._default.FS_Pong$T, $LS($LZ), _module.Stream.tail(s#0), P#0));
                assume _module.Stream.Cons_q(s#0)
                   && _module.__default.Filter#canCall(_module._default.FS_Pong$T, _module.Stream.tail(s#0), P#0)
                   && _module.__default.In#canCall(_module._default.FS_Pong$T, 
                    x#0, 
                    _module.__default.Filter(_module._default.FS_Pong$T, $LS($LZ), _module.Stream.tail(s#0), P#0));
                // ----- assert line0 ==> line1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(215,5)
                assert {:subsumption 0} Lit(true)
                   ==> 
                  _module.__default.In#canCall(_module._default.FS_Pong$T, 
                    x#0, 
                    _module.__default.Filter(_module._default.FS_Pong$T, $LS($LZ), _module.Stream.tail(s#0), P#0))
                   ==> _module.__default.In(_module._default.FS_Pong$T, 
                      x#0, 
                      _module.__default.Filter(_module._default.FS_Pong$T, $LS($LZ), _module.Stream.tail(s#0), P#0))
                     || (exists n#1_0_1_1: int :: 
                      { _module.__default.Tail(_module._default.FS_Pong$T, 
                          $LS($LZ), 
                          _module.__default.Filter(_module._default.FS_Pong$T, $LS($LZ), _module.Stream.tail(s#0), P#0), 
                          n#1_0_1_1) } 
                      LitInt(0) <= n#1_0_1_1
                         && 
                        LitInt(0) <= n#1_0_1_1
                         && _module.Stream.head(_module.__default.Tail(_module._default.FS_Pong$T, 
                              $LS($LZ), 
                              _module.__default.Filter(_module._default.FS_Pong$T, $LS($LZ), _module.Stream.tail(s#0), P#0), 
                              n#1_0_1_1))
                           == x#0);
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(215,5)
                assume _module.Stream.Cons_q(s#0);
                ##s#1_0_0_0 := _module.Stream.tail(s#0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#1_0_0_0, Tclass._module.Stream(_module._default.FS_Pong$T), $Heap);
                ##P#1_0_0_0 := P#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##P#1_0_0_0, 
                  Tclass._System.___hTotalFunc1(_module._default.FS_Pong$T, TBool), 
                  $Heap);
                assume {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.FS_Pong$T, ##s#1_0_0_0, ##P#1_0_0_0)
                   ==> _module.__default.AlwaysAnother(_module._default.FS_Pong$T, $LS($LZ), ##s#1_0_0_0, ##P#1_0_0_0)
                     || (_module.__default.IsAnother#canCall(_module._default.FS_Pong$T, ##s#1_0_0_0, ##P#1_0_0_0)
                       ==> _module.__default.IsAnother(_module._default.FS_Pong$T, ##s#1_0_0_0, ##P#1_0_0_0)
                         || (exists n#1_0_0_0: int :: 
                          { _module.__default.Tail(_module._default.FS_Pong$T, $LS($LZ), ##s#1_0_0_0, n#1_0_0_0) } 
                          LitInt(0) <= n#1_0_0_0
                             && 
                            LitInt(0) <= n#1_0_0_0
                             && $Unbox(Apply1(_module._default.FS_Pong$T, 
                                TBool, 
                                $Heap, 
                                ##P#1_0_0_0, 
                                _module.Stream.head(_module.__default.Tail(_module._default.FS_Pong$T, $LS($LZ), ##s#1_0_0_0, n#1_0_0_0)))): bool));
                assume {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.FS_Pong$T, ##s#1_0_0_0, ##P#1_0_0_0)
                   ==> _module.__default.AlwaysAnother(_module._default.FS_Pong$T, $LS($LZ), ##s#1_0_0_0, ##P#1_0_0_0)
                     || _module.__default.AlwaysAnother(_module._default.FS_Pong$T, 
                      $LS($LS($LZ)), 
                      _module.Stream.tail(##s#1_0_0_0), 
                      ##P#1_0_0_0);
                assume _module.__default.Filter#canCall(_module._default.FS_Pong$T, _module.Stream.tail(s#0), P#0);
                assume _module.Stream.Cons_q(_module.__default.Filter(_module._default.FS_Pong$T, $LS($LZ), _module.Stream.tail(s#0), P#0));
                ##x#1_0_0_0 := x#0;
                // assume allocatedness for argument to function
                assume $IsAllocBox(##x#1_0_0_0, _module._default.FS_Pong$T, $Heap);
                ##s#1_0_0_1 := _module.__default.Filter(_module._default.FS_Pong$T, $LS($LZ), _module.Stream.tail(s#0), P#0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#1_0_0_1, Tclass._module.Stream(_module._default.FS_Pong$T), $Heap);
                assume _module.__default.In#canCall(_module._default.FS_Pong$T, 
                  x#0, 
                  _module.__default.Filter(_module._default.FS_Pong$T, $LS($LZ), _module.Stream.tail(s#0), P#0));
                assume _module.Stream.Cons_q(s#0)
                   && _module.__default.Filter#canCall(_module._default.FS_Pong$T, _module.Stream.tail(s#0), P#0)
                   && _module.__default.In#canCall(_module._default.FS_Pong$T, 
                    x#0, 
                    _module.__default.Filter(_module._default.FS_Pong$T, $LS($LZ), _module.Stream.tail(s#0), P#0));
                // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(215,5)
                assume _module.__default.In(_module._default.FS_Pong$T, 
                  x#0, 
                  _module.__default.Filter(_module._default.FS_Pong$T, $LS($LZ), _module.Stream.tail(s#0), P#0));
                // ----- Hint1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(215,5)
                // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(219,11)
                assume _module.Stream.Cons_q(fs#0);
                assume _module.Stream.Cons_q(fs#0);
                assert _module.Stream.head(fs#0) != x#0;
                // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(219,45)
                // TrCallStmt: Before ProcessCallStmt
                assume true;
                // ProcessCallStmt: CheckSubrange
                x##1_0_0_0 := x#0;
                assume true;
                // ProcessCallStmt: CheckSubrange
                s##1_0_0_0 := fs#0;
                assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                // ProcessCallStmt: Make the call
                call Call$$_module.__default.Lemma__InTail(_module._default.FS_Pong$T, x##1_0_0_0, s##1_0_0_0);
                // TrCallStmt: After ProcessCallStmt
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(219,51)"} true;
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(215,5)
                ##x#1_0_0_1 := x#0;
                // assume allocatedness for argument to function
                assume $IsAllocBox(##x#1_0_0_1, _module._default.FS_Pong$T, $Heap);
                ##s#1_0_0_2 := fs#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#1_0_0_2, Tclass._module.Stream(_module._default.FS_Pong$T), $Heap);
                assume _module.__default.In#canCall(_module._default.FS_Pong$T, x#0, fs#0);
                assume _module.__default.In#canCall(_module._default.FS_Pong$T, x#0, fs#0);
                // ----- assert line1 ==> line2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(215,5)
                assert {:subsumption 0} _module.__default.In(_module._default.FS_Pong$T, 
                    x#0, 
                    _module.__default.Filter(_module._default.FS_Pong$T, $LS($LZ), _module.Stream.tail(s#0), P#0))
                   ==> 
                  _module.__default.In#canCall(_module._default.FS_Pong$T, x#0, fs#0)
                   ==> _module.__default.In(_module._default.FS_Pong$T, x#0, fs#0)
                     || (exists n#1_0_0_1: int :: 
                      { _module.__default.Tail(_module._default.FS_Pong$T, $LS($LZ), fs#0, n#1_0_0_1) } 
                      LitInt(0) <= n#1_0_0_1
                         && 
                        LitInt(0) <= n#1_0_0_1
                         && _module.Stream.head(_module.__default.Tail(_module._default.FS_Pong$T, $LS($LZ), fs#0, n#1_0_0_1))
                           == x#0);
                assume false;
            }

            assume true ==> _module.__default.In(_module._default.FS_Pong$T, x#0, fs#0);
        }
        else
        {
        }
    }
}



// function declaration for _module._default.Increasing
function _module.__default.Increasing(_module._default.Increasing$_T0: Ty, 
    $ly: LayerType, 
    s#0: DatatypeType, 
    ord#0: HandleType)
   : bool;

function _module.__default.Increasing#canCall(_module._default.Increasing$_T0: Ty, s#0: DatatypeType, ord#0: HandleType)
   : bool;

// layer synonym axiom
axiom (forall _module._default.Increasing$_T0: Ty, 
    $ly: LayerType, 
    s#0: DatatypeType, 
    ord#0: HandleType :: 
  { _module.__default.Increasing(_module._default.Increasing$_T0, $LS($ly), s#0, ord#0) } 
  _module.__default.Increasing(_module._default.Increasing$_T0, $LS($ly), s#0, ord#0)
     == _module.__default.Increasing(_module._default.Increasing$_T0, $ly, s#0, ord#0));

// fuel synonym axiom
axiom (forall _module._default.Increasing$_T0: Ty, 
    $ly: LayerType, 
    s#0: DatatypeType, 
    ord#0: HandleType :: 
  { _module.__default.Increasing(_module._default.Increasing$_T0, AsFuelBottom($ly), s#0, ord#0) } 
  _module.__default.Increasing(_module._default.Increasing$_T0, $ly, s#0, ord#0)
     == _module.__default.Increasing(_module._default.Increasing$_T0, $LZ, s#0, ord#0));

// consequence axiom for _module.__default.Increasing
axiom 27 <= $FunctionContextHeight
   ==> (forall _module._default.Increasing$_T0: Ty, 
      $ly: LayerType, 
      s#0: DatatypeType, 
      ord#0: HandleType :: 
    { _module.__default.Increasing(_module._default.Increasing$_T0, $ly, s#0, ord#0) } 
    _module.__default.Increasing#canCall(_module._default.Increasing$_T0, s#0, ord#0)
         || (27 != $FunctionContextHeight
           && 
          $Is(s#0, Tclass._module.Stream(_module._default.Increasing$_T0))
           && $Is(ord#0, Tclass._System.___hTotalFunc1(_module._default.Increasing$_T0, TInt)))
       ==> true);

function _module.__default.Increasing#requires(Ty, LayerType, DatatypeType, HandleType) : bool;

// #requires axiom for _module.__default.Increasing
axiom (forall _module._default.Increasing$_T0: Ty, 
    $ly: LayerType, 
    $Heap: Heap, 
    s#0: DatatypeType, 
    ord#0: HandleType :: 
  { _module.__default.Increasing#requires(_module._default.Increasing$_T0, $ly, s#0, ord#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && $Is(s#0, Tclass._module.Stream(_module._default.Increasing$_T0))
       && $Is(ord#0, Tclass._System.___hTotalFunc1(_module._default.Increasing$_T0, TInt))
     ==> _module.__default.Increasing#requires(_module._default.Increasing$_T0, $ly, s#0, ord#0)
       == true);

// definition axiom for _module.__default.Increasing (revealed)
axiom 27 <= $FunctionContextHeight
   ==> (forall _module._default.Increasing$_T0: Ty, 
      $ly: LayerType, 
      $Heap: Heap, 
      s#0: DatatypeType, 
      ord#0: HandleType :: 
    { _module.__default.Increasing(_module._default.Increasing$_T0, $LS($ly), s#0, ord#0), $IsGoodHeap($Heap) } 
    _module.__default.Increasing#canCall(_module._default.Increasing$_T0, s#0, ord#0)
         || (27 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(s#0, Tclass._module.Stream(_module._default.Increasing$_T0))
           && $Is(ord#0, Tclass._System.___hTotalFunc1(_module._default.Increasing$_T0, TInt)))
       ==> _module.Stream.Cons_q(s#0)
         && 
        _module.Stream.Cons_q(s#0)
         && _module.Stream.Cons_q(_module.Stream.tail(s#0))
         && ($Unbox(Apply1(_module._default.Increasing$_T0, TInt, $Heap, ord#0, _module.Stream.head(s#0))): int
             < $Unbox(Apply1(_module._default.Increasing$_T0, 
                TInt, 
                $Heap, 
                ord#0, 
                _module.Stream.head(_module.Stream.tail(s#0)))): int
           ==> _module.Stream.Cons_q(s#0)
             && _module.__default.Increasing#canCall(_module._default.Increasing$_T0, _module.Stream.tail(s#0), ord#0))
         && _module.__default.Increasing(_module._default.Increasing$_T0, $LS($ly), s#0, ord#0)
           == ($Unbox(Apply1(_module._default.Increasing$_T0, TInt, $Heap, ord#0, _module.Stream.head(s#0))): int
               < $Unbox(Apply1(_module._default.Increasing$_T0, 
                  TInt, 
                  $Heap, 
                  ord#0, 
                  _module.Stream.head(_module.Stream.tail(s#0)))): int
             && _module.__default.Increasing(_module._default.Increasing$_T0, $ly, _module.Stream.tail(s#0), ord#0)));

// 1st prefix predicate axiom for _module.__default.Increasing_h
axiom 28 <= $FunctionContextHeight
   ==> (forall _module._default.Increasing#$_T0: Ty, 
      $ly: LayerType, 
      s#0: DatatypeType, 
      ord#0: HandleType :: 
    { _module.__default.Increasing(_module._default.Increasing#$_T0, $LS($ly), s#0, ord#0) } 
    $Is(s#0, Tclass._module.Stream(_module._default.Increasing#$_T0))
         && $Is(ord#0, Tclass._System.___hTotalFunc1(_module._default.Increasing#$_T0, TInt))
         && _module.__default.Increasing(_module._default.Increasing#$_T0, $LS($ly), s#0, ord#0)
       ==> (forall _k#0: Box :: 
        { _module.__default.Increasing_h(_module._default.Increasing#$_T0, $LS($ly), _k#0, s#0, ord#0) } 
        _module.__default.Increasing_h(_module._default.Increasing#$_T0, $LS($ly), _k#0, s#0, ord#0)));

// 2nd prefix predicate axiom
axiom 28 <= $FunctionContextHeight
   ==> (forall _module._default.Increasing#$_T0: Ty, 
      $ly: LayerType, 
      s#0: DatatypeType, 
      ord#0: HandleType :: 
    { _module.__default.Increasing(_module._default.Increasing#$_T0, $LS($ly), s#0, ord#0) } 
    $Is(s#0, Tclass._module.Stream(_module._default.Increasing#$_T0))
         && $Is(ord#0, Tclass._System.___hTotalFunc1(_module._default.Increasing#$_T0, TInt))
         && (forall _k#0: Box :: 
          { _module.__default.Increasing_h(_module._default.Increasing#$_T0, $LS($ly), _k#0, s#0, ord#0) } 
          _module.__default.Increasing_h(_module._default.Increasing#$_T0, $LS($ly), _k#0, s#0, ord#0))
       ==> _module.__default.Increasing(_module._default.Increasing#$_T0, $LS($ly), s#0, ord#0));

// 3rd prefix predicate axiom
axiom 28 <= $FunctionContextHeight
   ==> (forall _module._default.Increasing#$_T0: Ty, 
      $ly: LayerType, 
      s#0: DatatypeType, 
      ord#0: HandleType, 
      _k#0: Box :: 
    { _module.__default.Increasing_h(_module._default.Increasing#$_T0, $ly, _k#0, s#0, ord#0) } 
    $Is(s#0, Tclass._module.Stream(_module._default.Increasing#$_T0))
         && $Is(ord#0, Tclass._System.___hTotalFunc1(_module._default.Increasing#$_T0, TInt))
         && _k#0 == ORD#FromNat(0)
       ==> _module.__default.Increasing_h(_module._default.Increasing#$_T0, $ly, _k#0, s#0, ord#0));

procedure CheckWellformed$$_module.__default.Increasing(_module._default.Increasing$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Increasing$_T0)), 
    ord#0: HandleType
       where $Is(ord#0, Tclass._System.___hTotalFunc1(_module._default.Increasing$_T0, TInt)));
  free requires 27 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Increasing(_module._default.Increasing$_T0: Ty, s#0: DatatypeType, ord#0: HandleType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##s#0: DatatypeType;
  var ##ord#0: HandleType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function Increasing
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(232,19): initial state"} true;
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
        assume _module.Stream.Cons_q(s#0);
        assume _module.Stream.Cons_q(s#0);
        assume _module.Stream.Cons_q(_module.Stream.tail(s#0));
        if ($Unbox(Apply1(_module._default.Increasing$_T0, TInt, $Heap, ord#0, _module.Stream.head(s#0))): int
           < $Unbox(Apply1(_module._default.Increasing$_T0, 
              TInt, 
              $Heap, 
              ord#0, 
              _module.Stream.head(_module.Stream.tail(s#0)))): int)
        {
            assume _module.Stream.Cons_q(s#0);
            ##s#0 := _module.Stream.tail(s#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#0, Tclass._module.Stream(_module._default.Increasing$_T0), $Heap);
            ##ord#0 := ord#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##ord#0, 
              Tclass._System.___hTotalFunc1(_module._default.Increasing$_T0, TInt), 
              $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.Increasing#canCall(_module._default.Increasing$_T0, _module.Stream.tail(s#0), ord#0);
        }

        assume _module.__default.Increasing(_module._default.Increasing$_T0, $LS($LZ), s#0, ord#0)
           == ($Unbox(Apply1(_module._default.Increasing$_T0, TInt, $Heap, ord#0, _module.Stream.head(s#0))): int
               < $Unbox(Apply1(_module._default.Increasing$_T0, 
                  TInt, 
                  $Heap, 
                  ord#0, 
                  _module.Stream.head(_module.Stream.tail(s#0)))): int
             && _module.__default.Increasing(_module._default.Increasing$_T0, $LS($LZ), _module.Stream.tail(s#0), ord#0));
        assume _module.Stream.Cons_q(s#0)
           && 
          _module.Stream.Cons_q(s#0)
           && _module.Stream.Cons_q(_module.Stream.tail(s#0))
           && ($Unbox(Apply1(_module._default.Increasing$_T0, TInt, $Heap, ord#0, _module.Stream.head(s#0))): int
               < $Unbox(Apply1(_module._default.Increasing$_T0, 
                  TInt, 
                  $Heap, 
                  ord#0, 
                  _module.Stream.head(_module.Stream.tail(s#0)))): int
             ==> _module.Stream.Cons_q(s#0)
               && _module.__default.Increasing#canCall(_module._default.Increasing$_T0, _module.Stream.tail(s#0), ord#0));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.Increasing(_module._default.Increasing$_T0, $LS($LZ), s#0, ord#0), 
          TBool);
        assert b$reqreads#0;
    }
}



// function declaration for _module._default.Increasing#
function _module.__default.Increasing_h(_module._default.Increasing#$_T0: Ty, 
    $ly: LayerType, 
    _k#0: Box, 
    s#0: DatatypeType, 
    ord#0: HandleType)
   : bool;

function _module.__default.Increasing_h#canCall(_module._default.Increasing#$_T0: Ty, 
    _k#0: Box, 
    s#0: DatatypeType, 
    ord#0: HandleType)
   : bool;

// layer synonym axiom
axiom (forall _module._default.Increasing#$_T0: Ty, 
    $ly: LayerType, 
    _k#0: Box, 
    s#0: DatatypeType, 
    ord#0: HandleType :: 
  { _module.__default.Increasing_h(_module._default.Increasing#$_T0, $LS($ly), _k#0, s#0, ord#0) } 
  _module.__default.Increasing_h(_module._default.Increasing#$_T0, $LS($ly), _k#0, s#0, ord#0)
     == _module.__default.Increasing_h(_module._default.Increasing#$_T0, $ly, _k#0, s#0, ord#0));

// fuel synonym axiom
axiom (forall _module._default.Increasing#$_T0: Ty, 
    $ly: LayerType, 
    _k#0: Box, 
    s#0: DatatypeType, 
    ord#0: HandleType :: 
  { _module.__default.Increasing_h(_module._default.Increasing#$_T0, AsFuelBottom($ly), _k#0, s#0, ord#0) } 
  _module.__default.Increasing_h(_module._default.Increasing#$_T0, $ly, _k#0, s#0, ord#0)
     == _module.__default.Increasing_h(_module._default.Increasing#$_T0, $LZ, _k#0, s#0, ord#0));

// consequence axiom for _module.__default.Increasing_h
axiom 28 <= $FunctionContextHeight
   ==> (forall _module._default.Increasing#$_T0: Ty, 
      $ly: LayerType, 
      _k#0: Box, 
      s#0: DatatypeType, 
      ord#0: HandleType :: 
    { _module.__default.Increasing_h(_module._default.Increasing#$_T0, $ly, _k#0, s#0, ord#0) } 
    _module.__default.Increasing_h#canCall(_module._default.Increasing#$_T0, _k#0, s#0, ord#0)
         || (28 != $FunctionContextHeight
           && 
          $Is(s#0, Tclass._module.Stream(_module._default.Increasing#$_T0))
           && $Is(ord#0, Tclass._System.___hTotalFunc1(_module._default.Increasing#$_T0, TInt)))
       ==> true);

function _module.__default.Increasing_h#requires(Ty, LayerType, Box, DatatypeType, HandleType) : bool;

// #requires axiom for _module.__default.Increasing_h
axiom (forall _module._default.Increasing#$_T0: Ty, 
    $ly: LayerType, 
    $Heap: Heap, 
    _k#0: Box, 
    s#0: DatatypeType, 
    ord#0: HandleType :: 
  { _module.__default.Increasing_h#requires(_module._default.Increasing#$_T0, $ly, _k#0, s#0, ord#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && $Is(s#0, Tclass._module.Stream(_module._default.Increasing#$_T0))
       && $Is(ord#0, Tclass._System.___hTotalFunc1(_module._default.Increasing#$_T0, TInt))
     ==> _module.__default.Increasing_h#requires(_module._default.Increasing#$_T0, $ly, _k#0, s#0, ord#0)
       == true);

// definition axiom for _module.__default.Increasing_h (revealed)
axiom 28 <= $FunctionContextHeight
   ==> (forall _module._default.Increasing#$_T0: Ty, 
      $ly: LayerType, 
      $Heap: Heap, 
      _k#0: Box, 
      s#0: DatatypeType, 
      ord#0: HandleType :: 
    { _module.__default.Increasing_h(_module._default.Increasing#$_T0, $LS($ly), _k#0, s#0, ord#0), $IsGoodHeap($Heap) } 
    _module.__default.Increasing_h#canCall(_module._default.Increasing#$_T0, _k#0, s#0, ord#0)
         || (28 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(s#0, Tclass._module.Stream(_module._default.Increasing#$_T0))
           && $Is(ord#0, Tclass._System.___hTotalFunc1(_module._default.Increasing#$_T0, TInt)))
       ==> (0 < ORD#Offset(_k#0)
           ==> _module.Stream.Cons_q(s#0)
             && 
            _module.Stream.Cons_q(s#0)
             && _module.Stream.Cons_q(_module.Stream.tail(s#0))
             && ($Unbox(Apply1(_module._default.Increasing#$_T0, TInt, $Heap, ord#0, _module.Stream.head(s#0))): int
                 < $Unbox(Apply1(_module._default.Increasing#$_T0, 
                    TInt, 
                    $Heap, 
                    ord#0, 
                    _module.Stream.head(_module.Stream.tail(s#0)))): int
               ==> _module.Stream.Cons_q(s#0)
                 && _module.__default.Increasing_h#canCall(_module._default.Increasing#$_T0, 
                  ORD#Minus(_k#0, ORD#FromNat(1)), 
                  _module.Stream.tail(s#0), 
                  ord#0)))
         && (
          (0 < ORD#Offset(_k#0)
           ==> $Unbox(Apply1(_module._default.Increasing#$_T0, TInt, $Heap, ord#0, _module.Stream.head(s#0))): int
               < $Unbox(Apply1(_module._default.Increasing#$_T0, 
                  TInt, 
                  $Heap, 
                  ord#0, 
                  _module.Stream.head(_module.Stream.tail(s#0)))): int
             && _module.__default.Increasing_h(_module._default.Increasing#$_T0, 
              $ly, 
              ORD#Minus(_k#0, ORD#FromNat(1)), 
              _module.Stream.tail(s#0), 
              ord#0))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#0: Box :: 
            { _module.__default.Increasing_h(_module._default.Increasing#$_T0, $ly, _k'#0, s#0, ord#0) } 
            ORD#Less(_k'#0, _k#0)
               ==> _module.__default.Increasing_h#canCall(_module._default.Increasing#$_T0, _k'#0, s#0, ord#0)))
         && _module.__default.Increasing_h(_module._default.Increasing#$_T0, $LS($ly), _k#0, s#0, ord#0)
           == ((0 < ORD#Offset(_k#0)
               ==> $Unbox(Apply1(_module._default.Increasing#$_T0, TInt, $Heap, ord#0, _module.Stream.head(s#0))): int
                   < $Unbox(Apply1(_module._default.Increasing#$_T0, 
                      TInt, 
                      $Heap, 
                      ord#0, 
                      _module.Stream.head(_module.Stream.tail(s#0)))): int
                 && _module.__default.Increasing_h(_module._default.Increasing#$_T0, 
                  $ly, 
                  ORD#Minus(_k#0, ORD#FromNat(1)), 
                  _module.Stream.tail(s#0), 
                  ord#0))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#0: Box :: 
                { _module.__default.Increasing_h(_module._default.Increasing#$_T0, $ly, _k'#0, s#0, ord#0) } 
                ORD#Less(_k'#0, _k#0)
                   ==> _module.__default.Increasing_h(_module._default.Increasing#$_T0, $ly, _k'#0, s#0, ord#0)))));

// definition axiom for _module.__default.Increasing_h for decreasing-related literals (revealed)
axiom 28 <= $FunctionContextHeight
   ==> (forall _module._default.Increasing#$_T0: Ty, 
      $ly: LayerType, 
      $Heap: Heap, 
      _k#0: Box, 
      s#0: DatatypeType, 
      ord#0: HandleType :: 
    {:weight 3} { _module.__default.Increasing_h(_module._default.Increasing#$_T0, $LS($ly), Lit(_k#0), s#0, ord#0), $IsGoodHeap($Heap) } 
    _module.__default.Increasing_h#canCall(_module._default.Increasing#$_T0, Lit(_k#0), s#0, ord#0)
         || (28 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(s#0, Tclass._module.Stream(_module._default.Increasing#$_T0))
           && $Is(ord#0, Tclass._System.___hTotalFunc1(_module._default.Increasing#$_T0, TInt)))
       ==> (0 < ORD#Offset(_k#0)
           ==> _module.Stream.Cons_q(s#0)
             && 
            _module.Stream.Cons_q(s#0)
             && _module.Stream.Cons_q(_module.Stream.tail(s#0))
             && ($Unbox(Apply1(_module._default.Increasing#$_T0, TInt, $Heap, ord#0, _module.Stream.head(s#0))): int
                 < $Unbox(Apply1(_module._default.Increasing#$_T0, 
                    TInt, 
                    $Heap, 
                    ord#0, 
                    _module.Stream.head(_module.Stream.tail(s#0)))): int
               ==> _module.Stream.Cons_q(s#0)
                 && _module.__default.Increasing_h#canCall(_module._default.Increasing#$_T0, 
                  ORD#Minus(_k#0, ORD#FromNat(1)), 
                  _module.Stream.tail(s#0), 
                  ord#0)))
         && (
          (0 < ORD#Offset(_k#0)
           ==> $Unbox(Apply1(_module._default.Increasing#$_T0, TInt, $Heap, ord#0, _module.Stream.head(s#0))): int
               < $Unbox(Apply1(_module._default.Increasing#$_T0, 
                  TInt, 
                  $Heap, 
                  ord#0, 
                  _module.Stream.head(_module.Stream.tail(s#0)))): int
             && _module.__default.Increasing_h(_module._default.Increasing#$_T0, 
              $LS($ly), 
              ORD#Minus(_k#0, ORD#FromNat(1)), 
              _module.Stream.tail(s#0), 
              ord#0))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#1: Box :: 
            { _module.__default.Increasing_h(_module._default.Increasing#$_T0, $LS($ly), _k'#1, s#0, ord#0) } 
            ORD#Less(_k'#1, _k#0)
               ==> _module.__default.Increasing_h#canCall(_module._default.Increasing#$_T0, _k'#1, s#0, ord#0)))
         && _module.__default.Increasing_h(_module._default.Increasing#$_T0, $LS($ly), Lit(_k#0), s#0, ord#0)
           == ((0 < ORD#Offset(_k#0)
               ==> $Unbox(Apply1(_module._default.Increasing#$_T0, TInt, $Heap, ord#0, _module.Stream.head(s#0))): int
                   < $Unbox(Apply1(_module._default.Increasing#$_T0, 
                      TInt, 
                      $Heap, 
                      ord#0, 
                      _module.Stream.head(_module.Stream.tail(s#0)))): int
                 && _module.__default.Increasing_h(_module._default.Increasing#$_T0, 
                  $LS($ly), 
                  ORD#Minus(_k#0, ORD#FromNat(1)), 
                  _module.Stream.tail(s#0), 
                  ord#0))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#1: Box :: 
                { _module.__default.Increasing_h(_module._default.Increasing#$_T0, $LS($ly), _k'#1, s#0, ord#0) } 
                ORD#Less(_k'#1, _k#0)
                   ==> _module.__default.Increasing_h(_module._default.Increasing#$_T0, $LS($ly), _k'#1, s#0, ord#0)))));

// definition axiom for _module.__default.Increasing_h for all literals (revealed)
axiom 28 <= $FunctionContextHeight
   ==> (forall _module._default.Increasing#$_T0: Ty, 
      $ly: LayerType, 
      $Heap: Heap, 
      _k#0: Box, 
      s#0: DatatypeType, 
      ord#0: HandleType :: 
    {:weight 3} { _module.__default.Increasing_h(_module._default.Increasing#$_T0, $LS($ly), Lit(_k#0), Lit(s#0), Lit(ord#0)), $IsGoodHeap($Heap) } 
    _module.__default.Increasing_h#canCall(_module._default.Increasing#$_T0, Lit(_k#0), Lit(s#0), Lit(ord#0))
         || (28 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(s#0, Tclass._module.Stream(_module._default.Increasing#$_T0))
           && $Is(ord#0, Tclass._System.___hTotalFunc1(_module._default.Increasing#$_T0, TInt)))
       ==> (0 < ORD#Offset(_k#0)
           ==> _module.Stream.Cons_q(s#0)
             && 
            _module.Stream.Cons_q(s#0)
             && _module.Stream.Cons_q(_module.Stream.tail(s#0))
             && ($Unbox(Apply1(_module._default.Increasing#$_T0, TInt, $Heap, ord#0, _module.Stream.head(s#0))): int
                 < $Unbox(Apply1(_module._default.Increasing#$_T0, 
                    TInt, 
                    $Heap, 
                    ord#0, 
                    _module.Stream.head(_module.Stream.tail(s#0)))): int
               ==> _module.Stream.Cons_q(s#0)
                 && _module.__default.Increasing_h#canCall(_module._default.Increasing#$_T0, 
                  ORD#Minus(_k#0, ORD#FromNat(1)), 
                  _module.Stream.tail(s#0), 
                  ord#0)))
         && (
          (0 < ORD#Offset(_k#0)
           ==> $Unbox(Apply1(_module._default.Increasing#$_T0, TInt, $Heap, ord#0, _module.Stream.head(s#0))): int
               < $Unbox(Apply1(_module._default.Increasing#$_T0, 
                  TInt, 
                  $Heap, 
                  ord#0, 
                  _module.Stream.head(_module.Stream.tail(s#0)))): int
             && _module.__default.Increasing_h(_module._default.Increasing#$_T0, 
              $LS($ly), 
              ORD#Minus(_k#0, ORD#FromNat(1)), 
              _module.Stream.tail(s#0), 
              ord#0))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#2: Box :: 
            { _module.__default.Increasing_h(_module._default.Increasing#$_T0, $LS($ly), _k'#2, s#0, ord#0) } 
            ORD#Less(_k'#2, _k#0)
               ==> _module.__default.Increasing_h#canCall(_module._default.Increasing#$_T0, _k'#2, s#0, ord#0)))
         && _module.__default.Increasing_h(_module._default.Increasing#$_T0, $LS($ly), Lit(_k#0), Lit(s#0), Lit(ord#0))
           == ((0 < ORD#Offset(_k#0)
               ==> $Unbox(Apply1(_module._default.Increasing#$_T0, TInt, $Heap, ord#0, _module.Stream.head(s#0))): int
                   < $Unbox(Apply1(_module._default.Increasing#$_T0, 
                      TInt, 
                      $Heap, 
                      ord#0, 
                      _module.Stream.head(_module.Stream.tail(s#0)))): int
                 && _module.__default.Increasing_h(_module._default.Increasing#$_T0, 
                  $LS($ly), 
                  ORD#Minus(_k#0, ORD#FromNat(1)), 
                  _module.Stream.tail(s#0), 
                  ord#0))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#2: Box :: 
                { _module.__default.Increasing_h(_module._default.Increasing#$_T0, $LS($ly), _k'#2, s#0, ord#0) } 
                ORD#Less(_k'#2, _k#0)
                   ==> _module.__default.Increasing_h(_module._default.Increasing#$_T0, $LS($ly), _k'#2, s#0, ord#0)))));

// function declaration for _module._default.IncrFrom
function _module.__default.IncrFrom(_module._default.IncrFrom$_T0: Ty, 
    $ly: LayerType, 
    s#0: DatatypeType, 
    low#0: int, 
    ord#0: HandleType)
   : bool;

function _module.__default.IncrFrom#canCall(_module._default.IncrFrom$_T0: Ty, 
    s#0: DatatypeType, 
    low#0: int, 
    ord#0: HandleType)
   : bool;

// layer synonym axiom
axiom (forall _module._default.IncrFrom$_T0: Ty, 
    $ly: LayerType, 
    s#0: DatatypeType, 
    low#0: int, 
    ord#0: HandleType :: 
  { _module.__default.IncrFrom(_module._default.IncrFrom$_T0, $LS($ly), s#0, low#0, ord#0) } 
  _module.__default.IncrFrom(_module._default.IncrFrom$_T0, $LS($ly), s#0, low#0, ord#0)
     == _module.__default.IncrFrom(_module._default.IncrFrom$_T0, $ly, s#0, low#0, ord#0));

// fuel synonym axiom
axiom (forall _module._default.IncrFrom$_T0: Ty, 
    $ly: LayerType, 
    s#0: DatatypeType, 
    low#0: int, 
    ord#0: HandleType :: 
  { _module.__default.IncrFrom(_module._default.IncrFrom$_T0, AsFuelBottom($ly), s#0, low#0, ord#0) } 
  _module.__default.IncrFrom(_module._default.IncrFrom$_T0, $ly, s#0, low#0, ord#0)
     == _module.__default.IncrFrom(_module._default.IncrFrom$_T0, $LZ, s#0, low#0, ord#0));

// consequence axiom for _module.__default.IncrFrom
axiom 29 <= $FunctionContextHeight
   ==> (forall _module._default.IncrFrom$_T0: Ty, 
      $ly: LayerType, 
      s#0: DatatypeType, 
      low#0: int, 
      ord#0: HandleType :: 
    { _module.__default.IncrFrom(_module._default.IncrFrom$_T0, $ly, s#0, low#0, ord#0) } 
    _module.__default.IncrFrom#canCall(_module._default.IncrFrom$_T0, s#0, low#0, ord#0)
         || (29 != $FunctionContextHeight
           && 
          $Is(s#0, Tclass._module.Stream(_module._default.IncrFrom$_T0))
           && $Is(ord#0, Tclass._System.___hTotalFunc1(_module._default.IncrFrom$_T0, TInt)))
       ==> true);

function _module.__default.IncrFrom#requires(Ty, LayerType, DatatypeType, int, HandleType) : bool;

// #requires axiom for _module.__default.IncrFrom
axiom (forall _module._default.IncrFrom$_T0: Ty, 
    $ly: LayerType, 
    $Heap: Heap, 
    s#0: DatatypeType, 
    low#0: int, 
    ord#0: HandleType :: 
  { _module.__default.IncrFrom#requires(_module._default.IncrFrom$_T0, $ly, s#0, low#0, ord#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && $Is(s#0, Tclass._module.Stream(_module._default.IncrFrom$_T0))
       && $Is(ord#0, Tclass._System.___hTotalFunc1(_module._default.IncrFrom$_T0, TInt))
     ==> _module.__default.IncrFrom#requires(_module._default.IncrFrom$_T0, $ly, s#0, low#0, ord#0)
       == true);

// definition axiom for _module.__default.IncrFrom (revealed)
axiom 29 <= $FunctionContextHeight
   ==> (forall _module._default.IncrFrom$_T0: Ty, 
      $ly: LayerType, 
      $Heap: Heap, 
      s#0: DatatypeType, 
      low#0: int, 
      ord#0: HandleType :: 
    { _module.__default.IncrFrom(_module._default.IncrFrom$_T0, $LS($ly), s#0, low#0, ord#0), $IsGoodHeap($Heap) } 
    _module.__default.IncrFrom#canCall(_module._default.IncrFrom$_T0, s#0, low#0, ord#0)
         || (29 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(s#0, Tclass._module.Stream(_module._default.IncrFrom$_T0))
           && $Is(ord#0, Tclass._System.___hTotalFunc1(_module._default.IncrFrom$_T0, TInt)))
       ==> _module.Stream.Cons_q(s#0)
         && (low#0
             <= $Unbox(Apply1(_module._default.IncrFrom$_T0, TInt, $Heap, ord#0, _module.Stream.head(s#0))): int
           ==> _module.Stream.Cons_q(s#0)
             && _module.Stream.Cons_q(s#0)
             && _module.__default.IncrFrom#canCall(_module._default.IncrFrom$_T0, 
              _module.Stream.tail(s#0), 
              $Unbox(Apply1(_module._default.IncrFrom$_T0, TInt, $Heap, ord#0, _module.Stream.head(s#0))): int
                 + 1, 
              ord#0))
         && _module.__default.IncrFrom(_module._default.IncrFrom$_T0, $LS($ly), s#0, low#0, ord#0)
           == (low#0
               <= $Unbox(Apply1(_module._default.IncrFrom$_T0, TInt, $Heap, ord#0, _module.Stream.head(s#0))): int
             && _module.__default.IncrFrom(_module._default.IncrFrom$_T0, 
              $ly, 
              _module.Stream.tail(s#0), 
              $Unbox(Apply1(_module._default.IncrFrom$_T0, TInt, $Heap, ord#0, _module.Stream.head(s#0))): int
                 + 1, 
              ord#0)));

// 1st prefix predicate axiom for _module.__default.IncrFrom_h
axiom 30 <= $FunctionContextHeight
   ==> (forall _module._default.IncrFrom#$_T0: Ty, 
      $ly: LayerType, 
      s#0: DatatypeType, 
      low#0: int, 
      ord#0: HandleType :: 
    { _module.__default.IncrFrom(_module._default.IncrFrom#$_T0, $LS($ly), s#0, low#0, ord#0) } 
    $Is(s#0, Tclass._module.Stream(_module._default.IncrFrom#$_T0))
         && $Is(ord#0, Tclass._System.___hTotalFunc1(_module._default.IncrFrom#$_T0, TInt))
         && _module.__default.IncrFrom(_module._default.IncrFrom#$_T0, $LS($ly), s#0, low#0, ord#0)
       ==> (forall _k#0: int :: 
        { _module.__default.IncrFrom_h(_module._default.IncrFrom#$_T0, $LS($ly), _k#0, s#0, low#0, ord#0) } 
        LitInt(0) <= _k#0
           ==> _module.__default.IncrFrom_h(_module._default.IncrFrom#$_T0, $LS($ly), _k#0, s#0, low#0, ord#0)));

// 2nd prefix predicate axiom
axiom 30 <= $FunctionContextHeight
   ==> (forall _module._default.IncrFrom#$_T0: Ty, 
      $ly: LayerType, 
      s#0: DatatypeType, 
      low#0: int, 
      ord#0: HandleType :: 
    { _module.__default.IncrFrom(_module._default.IncrFrom#$_T0, $LS($ly), s#0, low#0, ord#0) } 
    $Is(s#0, Tclass._module.Stream(_module._default.IncrFrom#$_T0))
         && $Is(ord#0, Tclass._System.___hTotalFunc1(_module._default.IncrFrom#$_T0, TInt))
         && (forall _k#0: int :: 
          { _module.__default.IncrFrom_h(_module._default.IncrFrom#$_T0, $LS($ly), _k#0, s#0, low#0, ord#0) } 
          LitInt(0) <= _k#0
             ==> _module.__default.IncrFrom_h(_module._default.IncrFrom#$_T0, $LS($ly), _k#0, s#0, low#0, ord#0))
       ==> _module.__default.IncrFrom(_module._default.IncrFrom#$_T0, $LS($ly), s#0, low#0, ord#0));

// 3rd prefix predicate axiom
axiom 30 <= $FunctionContextHeight
   ==> (forall _module._default.IncrFrom#$_T0: Ty, 
      $ly: LayerType, 
      s#0: DatatypeType, 
      low#0: int, 
      ord#0: HandleType, 
      _k#0: int :: 
    { _module.__default.IncrFrom_h(_module._default.IncrFrom#$_T0, $ly, _k#0, s#0, low#0, ord#0) } 
    $Is(s#0, Tclass._module.Stream(_module._default.IncrFrom#$_T0))
         && $Is(ord#0, Tclass._System.___hTotalFunc1(_module._default.IncrFrom#$_T0, TInt))
         && _k#0 == 0
       ==> _module.__default.IncrFrom_h(_module._default.IncrFrom#$_T0, $ly, _k#0, s#0, low#0, ord#0));

procedure CheckWellformed$$_module.__default.IncrFrom(_module._default.IncrFrom$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.IncrFrom$_T0)), 
    low#0: int, 
    ord#0: HandleType
       where $Is(ord#0, Tclass._System.___hTotalFunc1(_module._default.IncrFrom$_T0, TInt)));
  free requires 29 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.IncrFrom(_module._default.IncrFrom$_T0: Ty, 
    s#0: DatatypeType, 
    low#0: int, 
    ord#0: HandleType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##s#0: DatatypeType;
  var ##low#0: int;
  var ##ord#0: HandleType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function IncrFrom
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(236,19): initial state"} true;
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
        assume _module.Stream.Cons_q(s#0);
        if (low#0
           <= $Unbox(Apply1(_module._default.IncrFrom$_T0, TInt, $Heap, ord#0, _module.Stream.head(s#0))): int)
        {
            assume _module.Stream.Cons_q(s#0);
            assume _module.Stream.Cons_q(s#0);
            ##s#0 := _module.Stream.tail(s#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#0, Tclass._module.Stream(_module._default.IncrFrom$_T0), $Heap);
            ##low#0 := $Unbox(Apply1(_module._default.IncrFrom$_T0, TInt, $Heap, ord#0, _module.Stream.head(s#0))): int
               + 1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##low#0, TInt, $Heap);
            ##ord#0 := ord#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##ord#0, 
              Tclass._System.___hTotalFunc1(_module._default.IncrFrom$_T0, TInt), 
              $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.IncrFrom#canCall(_module._default.IncrFrom$_T0, 
              _module.Stream.tail(s#0), 
              $Unbox(Apply1(_module._default.IncrFrom$_T0, TInt, $Heap, ord#0, _module.Stream.head(s#0))): int
                 + 1, 
              ord#0);
        }

        assume _module.__default.IncrFrom(_module._default.IncrFrom$_T0, $LS($LZ), s#0, low#0, ord#0)
           == (low#0
               <= $Unbox(Apply1(_module._default.IncrFrom$_T0, TInt, $Heap, ord#0, _module.Stream.head(s#0))): int
             && _module.__default.IncrFrom(_module._default.IncrFrom$_T0, 
              $LS($LZ), 
              _module.Stream.tail(s#0), 
              $Unbox(Apply1(_module._default.IncrFrom$_T0, TInt, $Heap, ord#0, _module.Stream.head(s#0))): int
                 + 1, 
              ord#0));
        assume _module.Stream.Cons_q(s#0)
           && (low#0
               <= $Unbox(Apply1(_module._default.IncrFrom$_T0, TInt, $Heap, ord#0, _module.Stream.head(s#0))): int
             ==> _module.Stream.Cons_q(s#0)
               && _module.Stream.Cons_q(s#0)
               && _module.__default.IncrFrom#canCall(_module._default.IncrFrom$_T0, 
                _module.Stream.tail(s#0), 
                $Unbox(Apply1(_module._default.IncrFrom$_T0, TInt, $Heap, ord#0, _module.Stream.head(s#0))): int
                   + 1, 
                ord#0));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.IncrFrom(_module._default.IncrFrom$_T0, $LS($LZ), s#0, low#0, ord#0), 
          TBool);
        assert b$reqreads#0;
    }
}



// function declaration for _module._default.IncrFrom#
function _module.__default.IncrFrom_h(_module._default.IncrFrom#$_T0: Ty, 
    $ly: LayerType, 
    _k#0: int, 
    s#0: DatatypeType, 
    low#0: int, 
    ord#0: HandleType)
   : bool;

function _module.__default.IncrFrom_h#canCall(_module._default.IncrFrom#$_T0: Ty, 
    _k#0: int, 
    s#0: DatatypeType, 
    low#0: int, 
    ord#0: HandleType)
   : bool;

// layer synonym axiom
axiom (forall _module._default.IncrFrom#$_T0: Ty, 
    $ly: LayerType, 
    _k#0: int, 
    s#0: DatatypeType, 
    low#0: int, 
    ord#0: HandleType :: 
  { _module.__default.IncrFrom_h(_module._default.IncrFrom#$_T0, $LS($ly), _k#0, s#0, low#0, ord#0) } 
  _module.__default.IncrFrom_h(_module._default.IncrFrom#$_T0, $LS($ly), _k#0, s#0, low#0, ord#0)
     == _module.__default.IncrFrom_h(_module._default.IncrFrom#$_T0, $ly, _k#0, s#0, low#0, ord#0));

// fuel synonym axiom
axiom (forall _module._default.IncrFrom#$_T0: Ty, 
    $ly: LayerType, 
    _k#0: int, 
    s#0: DatatypeType, 
    low#0: int, 
    ord#0: HandleType :: 
  { _module.__default.IncrFrom_h(_module._default.IncrFrom#$_T0, AsFuelBottom($ly), _k#0, s#0, low#0, ord#0) } 
  _module.__default.IncrFrom_h(_module._default.IncrFrom#$_T0, $ly, _k#0, s#0, low#0, ord#0)
     == _module.__default.IncrFrom_h(_module._default.IncrFrom#$_T0, $LZ, _k#0, s#0, low#0, ord#0));

// consequence axiom for _module.__default.IncrFrom_h
axiom 30 <= $FunctionContextHeight
   ==> (forall _module._default.IncrFrom#$_T0: Ty, 
      $ly: LayerType, 
      _k#0: int, 
      s#0: DatatypeType, 
      low#0: int, 
      ord#0: HandleType :: 
    { _module.__default.IncrFrom_h(_module._default.IncrFrom#$_T0, $ly, _k#0, s#0, low#0, ord#0) } 
    _module.__default.IncrFrom_h#canCall(_module._default.IncrFrom#$_T0, _k#0, s#0, low#0, ord#0)
         || (30 != $FunctionContextHeight
           && 
          LitInt(0) <= _k#0
           && $Is(s#0, Tclass._module.Stream(_module._default.IncrFrom#$_T0))
           && $Is(ord#0, Tclass._System.___hTotalFunc1(_module._default.IncrFrom#$_T0, TInt)))
       ==> true);

function _module.__default.IncrFrom_h#requires(Ty, LayerType, int, DatatypeType, int, HandleType) : bool;

// #requires axiom for _module.__default.IncrFrom_h
axiom (forall _module._default.IncrFrom#$_T0: Ty, 
    $ly: LayerType, 
    $Heap: Heap, 
    _k#0: int, 
    s#0: DatatypeType, 
    low#0: int, 
    ord#0: HandleType :: 
  { _module.__default.IncrFrom_h#requires(_module._default.IncrFrom#$_T0, $ly, _k#0, s#0, low#0, ord#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && LitInt(0) <= _k#0
       && $Is(s#0, Tclass._module.Stream(_module._default.IncrFrom#$_T0))
       && $Is(ord#0, Tclass._System.___hTotalFunc1(_module._default.IncrFrom#$_T0, TInt))
     ==> _module.__default.IncrFrom_h#requires(_module._default.IncrFrom#$_T0, $ly, _k#0, s#0, low#0, ord#0)
       == true);

// definition axiom for _module.__default.IncrFrom_h (revealed)
axiom 30 <= $FunctionContextHeight
   ==> (forall _module._default.IncrFrom#$_T0: Ty, 
      $ly: LayerType, 
      $Heap: Heap, 
      _k#0: int, 
      s#0: DatatypeType, 
      low#0: int, 
      ord#0: HandleType :: 
    { _module.__default.IncrFrom_h(_module._default.IncrFrom#$_T0, $LS($ly), _k#0, s#0, low#0, ord#0), $IsGoodHeap($Heap) } 
    _module.__default.IncrFrom_h#canCall(_module._default.IncrFrom#$_T0, _k#0, s#0, low#0, ord#0)
         || (30 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && LitInt(0) <= _k#0
           && $Is(s#0, Tclass._module.Stream(_module._default.IncrFrom#$_T0))
           && $Is(ord#0, Tclass._System.___hTotalFunc1(_module._default.IncrFrom#$_T0, TInt)))
       ==> (0 < _k#0
           ==> _module.Stream.Cons_q(s#0)
             && (low#0
                 <= $Unbox(Apply1(_module._default.IncrFrom#$_T0, TInt, $Heap, ord#0, _module.Stream.head(s#0))): int
               ==> _module.Stream.Cons_q(s#0)
                 && _module.Stream.Cons_q(s#0)
                 && _module.__default.IncrFrom_h#canCall(_module._default.IncrFrom#$_T0, 
                  _k#0 - 1, 
                  _module.Stream.tail(s#0), 
                  $Unbox(Apply1(_module._default.IncrFrom#$_T0, TInt, $Heap, ord#0, _module.Stream.head(s#0))): int
                     + 1, 
                  ord#0)))
         && _module.__default.IncrFrom_h(_module._default.IncrFrom#$_T0, $LS($ly), _k#0, s#0, low#0, ord#0)
           == (0 < _k#0
             ==> low#0
                 <= $Unbox(Apply1(_module._default.IncrFrom#$_T0, TInt, $Heap, ord#0, _module.Stream.head(s#0))): int
               && _module.__default.IncrFrom_h(_module._default.IncrFrom#$_T0, 
                $ly, 
                _k#0 - 1, 
                _module.Stream.tail(s#0), 
                $Unbox(Apply1(_module._default.IncrFrom#$_T0, TInt, $Heap, ord#0, _module.Stream.head(s#0))): int
                   + 1, 
                ord#0)));

// definition axiom for _module.__default.IncrFrom_h for decreasing-related literals (revealed)
axiom 30 <= $FunctionContextHeight
   ==> (forall _module._default.IncrFrom#$_T0: Ty, 
      $ly: LayerType, 
      $Heap: Heap, 
      _k#0: int, 
      s#0: DatatypeType, 
      low#0: int, 
      ord#0: HandleType :: 
    {:weight 3} { _module.__default.IncrFrom_h(_module._default.IncrFrom#$_T0, $LS($ly), LitInt(_k#0), s#0, low#0, ord#0), $IsGoodHeap($Heap) } 
    _module.__default.IncrFrom_h#canCall(_module._default.IncrFrom#$_T0, LitInt(_k#0), s#0, low#0, ord#0)
         || (30 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && LitInt(0) <= _k#0
           && $Is(s#0, Tclass._module.Stream(_module._default.IncrFrom#$_T0))
           && $Is(ord#0, Tclass._System.___hTotalFunc1(_module._default.IncrFrom#$_T0, TInt)))
       ==> (0 < _k#0
           ==> _module.Stream.Cons_q(s#0)
             && (low#0
                 <= $Unbox(Apply1(_module._default.IncrFrom#$_T0, TInt, $Heap, ord#0, _module.Stream.head(s#0))): int
               ==> _module.Stream.Cons_q(s#0)
                 && _module.Stream.Cons_q(s#0)
                 && _module.__default.IncrFrom_h#canCall(_module._default.IncrFrom#$_T0, 
                  _k#0 - 1, 
                  _module.Stream.tail(s#0), 
                  $Unbox(Apply1(_module._default.IncrFrom#$_T0, TInt, $Heap, ord#0, _module.Stream.head(s#0))): int
                     + 1, 
                  ord#0)))
         && _module.__default.IncrFrom_h(_module._default.IncrFrom#$_T0, $LS($ly), LitInt(_k#0), s#0, low#0, ord#0)
           == (0 < _k#0
             ==> low#0
                 <= $Unbox(Apply1(_module._default.IncrFrom#$_T0, TInt, $Heap, ord#0, _module.Stream.head(s#0))): int
               && _module.__default.IncrFrom_h(_module._default.IncrFrom#$_T0, 
                $LS($ly), 
                _k#0 - 1, 
                _module.Stream.tail(s#0), 
                $Unbox(Apply1(_module._default.IncrFrom#$_T0, TInt, $Heap, ord#0, _module.Stream.head(s#0))): int
                   + 1, 
                ord#0)));

// definition axiom for _module.__default.IncrFrom_h for all literals (revealed)
axiom 30 <= $FunctionContextHeight
   ==> (forall _module._default.IncrFrom#$_T0: Ty, 
      $ly: LayerType, 
      $Heap: Heap, 
      _k#0: int, 
      s#0: DatatypeType, 
      low#0: int, 
      ord#0: HandleType :: 
    {:weight 3} { _module.__default.IncrFrom_h(_module._default.IncrFrom#$_T0, 
        $LS($ly), 
        LitInt(_k#0), 
        Lit(s#0), 
        LitInt(low#0), 
        Lit(ord#0)), $IsGoodHeap($Heap) } 
    _module.__default.IncrFrom_h#canCall(_module._default.IncrFrom#$_T0, 
          LitInt(_k#0), 
          Lit(s#0), 
          LitInt(low#0), 
          Lit(ord#0))
         || (30 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && LitInt(0) <= _k#0
           && $Is(s#0, Tclass._module.Stream(_module._default.IncrFrom#$_T0))
           && $Is(ord#0, Tclass._System.___hTotalFunc1(_module._default.IncrFrom#$_T0, TInt)))
       ==> (0 < _k#0
           ==> _module.Stream.Cons_q(s#0)
             && (low#0
                 <= $Unbox(Apply1(_module._default.IncrFrom#$_T0, TInt, $Heap, ord#0, _module.Stream.head(s#0))): int
               ==> _module.Stream.Cons_q(s#0)
                 && _module.Stream.Cons_q(s#0)
                 && _module.__default.IncrFrom_h#canCall(_module._default.IncrFrom#$_T0, 
                  _k#0 - 1, 
                  _module.Stream.tail(s#0), 
                  $Unbox(Apply1(_module._default.IncrFrom#$_T0, TInt, $Heap, ord#0, _module.Stream.head(s#0))): int
                     + 1, 
                  ord#0)))
         && _module.__default.IncrFrom_h(_module._default.IncrFrom#$_T0, 
            $LS($ly), 
            LitInt(_k#0), 
            Lit(s#0), 
            LitInt(low#0), 
            Lit(ord#0))
           == (0 < _k#0
             ==> low#0
                 <= $Unbox(Apply1(_module._default.IncrFrom#$_T0, TInt, $Heap, ord#0, _module.Stream.head(s#0))): int
               && _module.__default.IncrFrom_h(_module._default.IncrFrom#$_T0, 
                $LS($ly), 
                _k#0 - 1, 
                _module.Stream.tail(s#0), 
                $Unbox(Apply1(_module._default.IncrFrom#$_T0, TInt, $Heap, ord#0, _module.Stream.head(s#0))): int
                   + 1, 
                ord#0)));

procedure CheckWellformed$$_module.__default.Lemma__Incr0(_module._default.Lemma_Incr0$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Lemma_Incr0$_T0))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.Lemma_Incr0$_T0), $Heap)
         && $IsA#_module.Stream(s#0), 
    low#0: int, 
    ord#0: HandleType
       where $Is(ord#0, Tclass._System.___hTotalFunc1(_module._default.Lemma_Incr0$_T0, TInt))
         && $IsAlloc(ord#0, 
          Tclass._System.___hTotalFunc1(_module._default.Lemma_Incr0$_T0, TInt), 
          $Heap));
  free requires 31 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Lemma__Incr0(_module._default.Lemma_Incr0$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Lemma_Incr0$_T0))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.Lemma_Incr0$_T0), $Heap)
         && $IsA#_module.Stream(s#0), 
    low#0: int, 
    ord#0: HandleType
       where $Is(ord#0, Tclass._System.___hTotalFunc1(_module._default.Lemma_Incr0$_T0, TInt))
         && $IsAlloc(ord#0, 
          Tclass._System.___hTotalFunc1(_module._default.Lemma_Incr0$_T0, TInt), 
          $Heap));
  // user-defined preconditions
  requires _module.__default.IncrFrom#canCall(_module._default.Lemma_Incr0$_T0, s#0, low#0, ord#0)
     ==> _module.__default.IncrFrom(_module._default.Lemma_Incr0$_T0, $LS($LZ), s#0, low#0, ord#0)
       || low#0
         <= $Unbox(Apply1(_module._default.Lemma_Incr0$_T0, TInt, $Heap, ord#0, _module.Stream.head(s#0))): int;
  requires _module.__default.IncrFrom#canCall(_module._default.Lemma_Incr0$_T0, s#0, low#0, ord#0)
     ==> _module.__default.IncrFrom(_module._default.Lemma_Incr0$_T0, $LS($LZ), s#0, low#0, ord#0)
       || _module.__default.IncrFrom(_module._default.Lemma_Incr0$_T0, 
        $LS($LS($LZ)), 
        _module.Stream.tail(s#0), 
        $Unbox(Apply1(_module._default.Lemma_Incr0$_T0, TInt, $Heap, ord#0, _module.Stream.head(s#0))): int
           + 1, 
        ord#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Increasing#canCall(_module._default.Lemma_Incr0$_T0, s#0, ord#0);
  free ensures _module.__default.Increasing#canCall(_module._default.Lemma_Incr0$_T0, s#0, ord#0)
     && 
    _module.__default.Increasing(_module._default.Lemma_Incr0$_T0, $LS($LZ), s#0, ord#0)
     && 
    $Unbox(Apply1(_module._default.Lemma_Incr0$_T0, TInt, $Heap, ord#0, _module.Stream.head(s#0))): int
       < $Unbox(Apply1(_module._default.Lemma_Incr0$_T0, 
          TInt, 
          $Heap, 
          ord#0, 
          _module.Stream.head(_module.Stream.tail(s#0)))): int
     && _module.__default.Increasing(_module._default.Lemma_Incr0$_T0, $LS($LZ), _module.Stream.tail(s#0), ord#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, s#1, low#1, ord#1} CoCall$$_module.__default.Lemma__Incr0_h(_module._default.Lemma_Incr0#$_T0: Ty, 
    _k#0: Box, 
    s#1: DatatypeType
       where $Is(s#1, Tclass._module.Stream(_module._default.Lemma_Incr0#$_T0))
         && $IsAlloc(s#1, Tclass._module.Stream(_module._default.Lemma_Incr0#$_T0), $Heap)
         && $IsA#_module.Stream(s#1), 
    low#1: int, 
    ord#1: HandleType
       where $Is(ord#1, Tclass._System.___hTotalFunc1(_module._default.Lemma_Incr0#$_T0, TInt))
         && $IsAlloc(ord#1, 
          Tclass._System.___hTotalFunc1(_module._default.Lemma_Incr0#$_T0, TInt), 
          $Heap));
  // user-defined preconditions
  requires _module.__default.IncrFrom#canCall(_module._default.Lemma_Incr0#$_T0, s#1, low#1, ord#1)
     ==> _module.__default.IncrFrom(_module._default.Lemma_Incr0#$_T0, $LS($LZ), s#1, low#1, ord#1)
       || low#1
         <= $Unbox(Apply1(_module._default.Lemma_Incr0#$_T0, TInt, $Heap, ord#1, _module.Stream.head(s#1))): int;
  requires _module.__default.IncrFrom#canCall(_module._default.Lemma_Incr0#$_T0, s#1, low#1, ord#1)
     ==> _module.__default.IncrFrom(_module._default.Lemma_Incr0#$_T0, $LS($LZ), s#1, low#1, ord#1)
       || _module.__default.IncrFrom(_module._default.Lemma_Incr0#$_T0, 
        $LS($LS($LZ)), 
        _module.Stream.tail(s#1), 
        $Unbox(Apply1(_module._default.Lemma_Incr0#$_T0, TInt, $Heap, ord#1, _module.Stream.head(s#1))): int
           + 1, 
        ord#1);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Increasing_h#canCall(_module._default.Lemma_Incr0#$_T0, _k#0, s#1, ord#1);
  free ensures _module.__default.Increasing_h#canCall(_module._default.Lemma_Incr0#$_T0, _k#0, s#1, ord#1)
     && 
    _module.__default.Increasing_h(_module._default.Lemma_Incr0#$_T0, $LS($LZ), _k#0, s#1, ord#1)
     && 
    (0 < ORD#Offset(_k#0)
       ==> $Unbox(Apply1(_module._default.Lemma_Incr0#$_T0, TInt, $Heap, ord#1, _module.Stream.head(s#1))): int
           < $Unbox(Apply1(_module._default.Lemma_Incr0#$_T0, 
              TInt, 
              $Heap, 
              ord#1, 
              _module.Stream.head(_module.Stream.tail(s#1)))): int
         && _module.__default.Increasing_h(_module._default.Lemma_Incr0#$_T0, 
          $LS($LZ), 
          ORD#Minus(_k#0, ORD#FromNat(1)), 
          _module.Stream.tail(s#1), 
          ord#1))
     && (LitInt(0) == ORD#Offset(_k#0)
       ==> (forall _k'#0: Box :: 
        { _module.__default.Increasing_h(_module._default.Lemma_Incr0#$_T0, $LS($LZ), _k'#0, s#1, ord#1) } 
        ORD#Less(_k'#0, _k#0)
           ==> _module.__default.Increasing_h(_module._default.Lemma_Incr0#$_T0, $LS($LZ), _k'#0, s#1, ord#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, s#1, low#1, ord#1} Impl$$_module.__default.Lemma__Incr0_h(_module._default.Lemma_Incr0#$_T0: Ty, 
    _k#0: Box, 
    s#1: DatatypeType
       where $Is(s#1, Tclass._module.Stream(_module._default.Lemma_Incr0#$_T0))
         && $IsAlloc(s#1, Tclass._module.Stream(_module._default.Lemma_Incr0#$_T0), $Heap)
         && $IsA#_module.Stream(s#1), 
    low#1: int, 
    ord#1: HandleType
       where $Is(ord#1, Tclass._System.___hTotalFunc1(_module._default.Lemma_Incr0#$_T0, TInt))
         && $IsAlloc(ord#1, 
          Tclass._System.___hTotalFunc1(_module._default.Lemma_Incr0#$_T0, TInt), 
          $Heap))
   returns ($_reverifyPost: bool);
  free requires 32 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.__default.IncrFrom#canCall(_module._default.Lemma_Incr0#$_T0, s#1, low#1, ord#1)
     && 
    _module.__default.IncrFrom(_module._default.Lemma_Incr0#$_T0, $LS($LZ), s#1, low#1, ord#1)
     && 
    low#1
       <= $Unbox(Apply1(_module._default.Lemma_Incr0#$_T0, TInt, $Heap, ord#1, _module.Stream.head(s#1))): int
     && _module.__default.IncrFrom(_module._default.Lemma_Incr0#$_T0, 
      $LS($LZ), 
      _module.Stream.tail(s#1), 
      $Unbox(Apply1(_module._default.Lemma_Incr0#$_T0, TInt, $Heap, ord#1, _module.Stream.head(s#1))): int
         + 1, 
      ord#1);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Increasing_h#canCall(_module._default.Lemma_Incr0#$_T0, _k#0, s#1, ord#1);
  ensures _module.__default.Increasing_h#canCall(_module._default.Lemma_Incr0#$_T0, _k#0, s#1, ord#1)
     ==> _module.__default.Increasing_h(_module._default.Lemma_Incr0#$_T0, $LS($LZ), _k#0, s#1, ord#1)
       || (0 < ORD#Offset(_k#0)
         ==> $Unbox(Apply1(_module._default.Lemma_Incr0#$_T0, TInt, $Heap, ord#1, _module.Stream.head(s#1))): int
           < $Unbox(Apply1(_module._default.Lemma_Incr0#$_T0, 
              TInt, 
              $Heap, 
              ord#1, 
              _module.Stream.head(_module.Stream.tail(s#1)))): int);
  ensures _module.__default.Increasing_h#canCall(_module._default.Lemma_Incr0#$_T0, _k#0, s#1, ord#1)
     ==> _module.__default.Increasing_h(_module._default.Lemma_Incr0#$_T0, $LS($LZ), _k#0, s#1, ord#1)
       || (0 < ORD#Offset(_k#0)
         ==> _module.__default.Increasing_h(_module._default.Lemma_Incr0#$_T0, 
          $LS($LS($LZ)), 
          ORD#Minus(_k#0, ORD#FromNat(1)), 
          _module.Stream.tail(s#1), 
          ord#1));
  ensures _module.__default.Increasing_h#canCall(_module._default.Lemma_Incr0#$_T0, _k#0, s#1, ord#1)
     ==> _module.__default.Increasing_h(_module._default.Lemma_Incr0#$_T0, $LS($LZ), _k#0, s#1, ord#1)
       || (LitInt(0) == ORD#Offset(_k#0)
         ==> (forall _k'#1: Box :: 
          { _module.__default.Increasing_h(_module._default.Lemma_Incr0#$_T0, $LS($LS($LZ)), _k'#1, s#1, ord#1) } 
          ORD#Less(_k'#1, _k#0)
             ==> _module.__default.Increasing_h(_module._default.Lemma_Incr0#$_T0, $LS($LS($LZ)), _k'#1, s#1, ord#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0, s#1, low#1, ord#1} Impl$$_module.__default.Lemma__Incr0_h(_module._default.Lemma_Incr0#$_T0: Ty, 
    _k#0: Box, 
    s#1: DatatypeType, 
    low#1: int, 
    ord#1: HandleType)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var $initHeapForallStmt#1: Heap;

    // AddMethodImpl: Lemma_Incr0#, Impl$$_module.__default.Lemma__Incr0_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(241,15): initial state"} true;
    assume $IsA#_module.Stream(s#1);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: Box, $ih#s0#0: DatatypeType, $ih#low0#0: int, $ih#ord0#0: HandleType :: 
      $Is($ih#s0#0, Tclass._module.Stream(_module._default.Lemma_Incr0#$_T0))
           && $Is($ih#ord0#0, 
            Tclass._System.___hTotalFunc1(_module._default.Lemma_Incr0#$_T0, TInt))
           && _module.__default.IncrFrom(_module._default.Lemma_Incr0#$_T0, $LS($LZ), $ih#s0#0, $ih#low0#0, $ih#ord0#0)
           && (ORD#Less($ih#_k0#0, _k#0)
             || ($ih#_k0#0 == _k#0 && 0 <= $ih#low0#0 && $ih#low0#0 < low#1))
         ==> _module.__default.Increasing_h(_module._default.Lemma_Incr0#$_T0, $LS($LZ), $ih#_k0#0, $ih#s0#0, $ih#ord0#0));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(244,1)
    assume true;
    if (0 < ORD#Offset(_k#0))
    {
    }
    else
    {
        // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(241,16)
        $initHeapForallStmt#1 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#1 == $Heap;
        assume (forall _k'#2: Box, s#2: DatatypeType, low#2: int, ord#2: HandleType :: 
          $Is(s#2, Tclass._module.Stream(_module._default.Lemma_Incr0#$_T0))
               && $Is(ord#2, Tclass._System.___hTotalFunc1(_module._default.Lemma_Incr0#$_T0, TInt))
               && 
              ORD#Less(_k'#2, _k#0)
               && _module.__default.IncrFrom(_module._default.Lemma_Incr0#$_T0, $LS($LZ), s#2, low#2, ord#2)
             ==> _module.__default.Increasing_h(_module._default.Lemma_Incr0#$_T0, $LS($LZ), _k'#2, s#2, ord#2));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(241,15)"} true;
    }
}



procedure CheckWellformed$$_module.__default.Lemma__Incr1(_module._default.Lemma_Incr1$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Lemma_Incr1$_T0))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.Lemma_Incr1$_T0), $Heap)
         && $IsA#_module.Stream(s#0), 
    ord#0: HandleType
       where $Is(ord#0, Tclass._System.___hTotalFunc1(_module._default.Lemma_Incr1$_T0, TInt))
         && $IsAlloc(ord#0, 
          Tclass._System.___hTotalFunc1(_module._default.Lemma_Incr1$_T0, TInt), 
          $Heap));
  free requires 33 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Lemma__Incr1(_module._default.Lemma_Incr1$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Lemma_Incr1$_T0))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.Lemma_Incr1$_T0), $Heap)
         && $IsA#_module.Stream(s#0), 
    ord#0: HandleType
       where $Is(ord#0, Tclass._System.___hTotalFunc1(_module._default.Lemma_Incr1$_T0, TInt))
         && $IsAlloc(ord#0, 
          Tclass._System.___hTotalFunc1(_module._default.Lemma_Incr1$_T0, TInt), 
          $Heap));
  // user-defined preconditions
  requires _module.__default.Increasing#canCall(_module._default.Lemma_Incr1$_T0, s#0, ord#0)
     ==> _module.__default.Increasing(_module._default.Lemma_Incr1$_T0, $LS($LZ), s#0, ord#0)
       || $Unbox(Apply1(_module._default.Lemma_Incr1$_T0, TInt, $Heap, ord#0, _module.Stream.head(s#0))): int
         < $Unbox(Apply1(_module._default.Lemma_Incr1$_T0, 
            TInt, 
            $Heap, 
            ord#0, 
            _module.Stream.head(_module.Stream.tail(s#0)))): int;
  requires _module.__default.Increasing#canCall(_module._default.Lemma_Incr1$_T0, s#0, ord#0)
     ==> _module.__default.Increasing(_module._default.Lemma_Incr1$_T0, $LS($LZ), s#0, ord#0)
       || _module.__default.Increasing(_module._default.Lemma_Incr1$_T0, $LS($LS($LZ)), _module.Stream.tail(s#0), ord#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Stream.Cons_q(s#0)
     && _module.__default.IncrFrom#canCall(_module._default.Lemma_Incr1$_T0, 
      s#0, 
      $Unbox(Apply1(_module._default.Lemma_Incr1$_T0, TInt, $Heap, ord#0, _module.Stream.head(s#0))): int, 
      ord#0);
  free ensures _module.__default.IncrFrom#canCall(_module._default.Lemma_Incr1$_T0, 
      s#0, 
      $Unbox(Apply1(_module._default.Lemma_Incr1$_T0, TInt, $Heap, ord#0, _module.Stream.head(s#0))): int, 
      ord#0)
     && 
    _module.__default.IncrFrom(_module._default.Lemma_Incr1$_T0, 
      $LS($LZ), 
      s#0, 
      $Unbox(Apply1(_module._default.Lemma_Incr1$_T0, TInt, $Heap, ord#0, _module.Stream.head(s#0))): int, 
      ord#0)
     && 
    $Unbox(Apply1(_module._default.Lemma_Incr1$_T0, TInt, $Heap, ord#0, _module.Stream.head(s#0))): int
       <= $Unbox(Apply1(_module._default.Lemma_Incr1$_T0, TInt, $Heap, ord#0, _module.Stream.head(s#0))): int
     && _module.__default.IncrFrom(_module._default.Lemma_Incr1$_T0, 
      $LS($LZ), 
      _module.Stream.tail(s#0), 
      $Unbox(Apply1(_module._default.Lemma_Incr1$_T0, TInt, $Heap, ord#0, _module.Stream.head(s#0))): int
         + 1, 
      ord#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, s#1, ord#1} CoCall$$_module.__default.Lemma__Incr1_h(_module._default.Lemma_Incr1#$_T0: Ty, 
    _k#0: int where LitInt(0) <= _k#0, 
    s#1: DatatypeType
       where $Is(s#1, Tclass._module.Stream(_module._default.Lemma_Incr1#$_T0))
         && $IsAlloc(s#1, Tclass._module.Stream(_module._default.Lemma_Incr1#$_T0), $Heap)
         && $IsA#_module.Stream(s#1), 
    ord#1: HandleType
       where $Is(ord#1, Tclass._System.___hTotalFunc1(_module._default.Lemma_Incr1#$_T0, TInt))
         && $IsAlloc(ord#1, 
          Tclass._System.___hTotalFunc1(_module._default.Lemma_Incr1#$_T0, TInt), 
          $Heap));
  // user-defined preconditions
  requires _module.__default.Increasing#canCall(_module._default.Lemma_Incr1#$_T0, s#1, ord#1)
     ==> _module.__default.Increasing(_module._default.Lemma_Incr1#$_T0, $LS($LZ), s#1, ord#1)
       || $Unbox(Apply1(_module._default.Lemma_Incr1#$_T0, TInt, $Heap, ord#1, _module.Stream.head(s#1))): int
         < $Unbox(Apply1(_module._default.Lemma_Incr1#$_T0, 
            TInt, 
            $Heap, 
            ord#1, 
            _module.Stream.head(_module.Stream.tail(s#1)))): int;
  requires _module.__default.Increasing#canCall(_module._default.Lemma_Incr1#$_T0, s#1, ord#1)
     ==> _module.__default.Increasing(_module._default.Lemma_Incr1#$_T0, $LS($LZ), s#1, ord#1)
       || _module.__default.Increasing(_module._default.Lemma_Incr1#$_T0, 
        $LS($LS($LZ)), 
        _module.Stream.tail(s#1), 
        ord#1);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Stream.Cons_q(s#1)
     && _module.__default.IncrFrom_h#canCall(_module._default.Lemma_Incr1#$_T0, 
      _k#0, 
      s#1, 
      $Unbox(Apply1(_module._default.Lemma_Incr1#$_T0, TInt, $Heap, ord#1, _module.Stream.head(s#1))): int, 
      ord#1);
  free ensures _module.__default.IncrFrom_h#canCall(_module._default.Lemma_Incr1#$_T0, 
      _k#0, 
      s#1, 
      $Unbox(Apply1(_module._default.Lemma_Incr1#$_T0, TInt, $Heap, ord#1, _module.Stream.head(s#1))): int, 
      ord#1)
     && 
    _module.__default.IncrFrom_h(_module._default.Lemma_Incr1#$_T0, 
      $LS($LZ), 
      _k#0, 
      s#1, 
      $Unbox(Apply1(_module._default.Lemma_Incr1#$_T0, TInt, $Heap, ord#1, _module.Stream.head(s#1))): int, 
      ord#1)
     && (0 < _k#0
       ==> $Unbox(Apply1(_module._default.Lemma_Incr1#$_T0, TInt, $Heap, ord#1, _module.Stream.head(s#1))): int
           <= $Unbox(Apply1(_module._default.Lemma_Incr1#$_T0, TInt, $Heap, ord#1, _module.Stream.head(s#1))): int
         && _module.__default.IncrFrom_h(_module._default.Lemma_Incr1#$_T0, 
          $LS($LZ), 
          _k#0 - 1, 
          _module.Stream.tail(s#1), 
          $Unbox(Apply1(_module._default.Lemma_Incr1#$_T0, TInt, $Heap, ord#1, _module.Stream.head(s#1))): int
             + 1, 
          ord#1));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, s#1, ord#1} Impl$$_module.__default.Lemma__Incr1_h(_module._default.Lemma_Incr1#$_T0: Ty, 
    _k#0: int where LitInt(0) <= _k#0, 
    s#1: DatatypeType
       where $Is(s#1, Tclass._module.Stream(_module._default.Lemma_Incr1#$_T0))
         && $IsAlloc(s#1, Tclass._module.Stream(_module._default.Lemma_Incr1#$_T0), $Heap)
         && $IsA#_module.Stream(s#1), 
    ord#1: HandleType
       where $Is(ord#1, Tclass._System.___hTotalFunc1(_module._default.Lemma_Incr1#$_T0, TInt))
         && $IsAlloc(ord#1, 
          Tclass._System.___hTotalFunc1(_module._default.Lemma_Incr1#$_T0, TInt), 
          $Heap))
   returns ($_reverifyPost: bool);
  free requires 34 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.__default.Increasing#canCall(_module._default.Lemma_Incr1#$_T0, s#1, ord#1)
     && 
    _module.__default.Increasing(_module._default.Lemma_Incr1#$_T0, $LS($LZ), s#1, ord#1)
     && 
    $Unbox(Apply1(_module._default.Lemma_Incr1#$_T0, TInt, $Heap, ord#1, _module.Stream.head(s#1))): int
       < $Unbox(Apply1(_module._default.Lemma_Incr1#$_T0, 
          TInt, 
          $Heap, 
          ord#1, 
          _module.Stream.head(_module.Stream.tail(s#1)))): int
     && _module.__default.Increasing(_module._default.Lemma_Incr1#$_T0, $LS($LZ), _module.Stream.tail(s#1), ord#1);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Stream.Cons_q(s#1)
     && _module.__default.IncrFrom_h#canCall(_module._default.Lemma_Incr1#$_T0, 
      _k#0, 
      s#1, 
      $Unbox(Apply1(_module._default.Lemma_Incr1#$_T0, TInt, $Heap, ord#1, _module.Stream.head(s#1))): int, 
      ord#1);
  ensures _module.__default.IncrFrom_h#canCall(_module._default.Lemma_Incr1#$_T0, 
      _k#0, 
      s#1, 
      $Unbox(Apply1(_module._default.Lemma_Incr1#$_T0, TInt, $Heap, ord#1, _module.Stream.head(s#1))): int, 
      ord#1)
     ==> _module.__default.IncrFrom_h(_module._default.Lemma_Incr1#$_T0, 
        $LS($LZ), 
        _k#0, 
        s#1, 
        $Unbox(Apply1(_module._default.Lemma_Incr1#$_T0, TInt, $Heap, ord#1, _module.Stream.head(s#1))): int, 
        ord#1)
       || (0 < _k#0
         ==> $Unbox(Apply1(_module._default.Lemma_Incr1#$_T0, TInt, $Heap, ord#1, _module.Stream.head(s#1))): int
           <= $Unbox(Apply1(_module._default.Lemma_Incr1#$_T0, TInt, $Heap, ord#1, _module.Stream.head(s#1))): int);
  ensures _module.__default.IncrFrom_h#canCall(_module._default.Lemma_Incr1#$_T0, 
      _k#0, 
      s#1, 
      $Unbox(Apply1(_module._default.Lemma_Incr1#$_T0, TInt, $Heap, ord#1, _module.Stream.head(s#1))): int, 
      ord#1)
     ==> _module.__default.IncrFrom_h(_module._default.Lemma_Incr1#$_T0, 
        $LS($LZ), 
        _k#0, 
        s#1, 
        $Unbox(Apply1(_module._default.Lemma_Incr1#$_T0, TInt, $Heap, ord#1, _module.Stream.head(s#1))): int, 
        ord#1)
       || (0 < _k#0
         ==> _module.__default.IncrFrom_h(_module._default.Lemma_Incr1#$_T0, 
          $LS($LS($LZ)), 
          _k#0 - 1, 
          _module.Stream.tail(s#1), 
          $Unbox(Apply1(_module._default.Lemma_Incr1#$_T0, TInt, $Heap, ord#1, _module.Stream.head(s#1))): int
             + 1, 
          ord#1));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0, s#1, ord#1} Impl$$_module.__default.Lemma__Incr1_h(_module._default.Lemma_Incr1#$_T0: Ty, 
    _k#0: int, 
    s#1: DatatypeType, 
    ord#1: HandleType)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var _k##0: int;
  var s##0: DatatypeType;
  var ord##0: HandleType;

    // AddMethodImpl: Lemma_Incr1#, Impl$$_module.__default.Lemma__Incr1_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(246,15): initial state"} true;
    assume $IsA#_module.Stream(s#1);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: int, $ih#s0#0: DatatypeType, $ih#ord0#0: HandleType :: 
      LitInt(0) <= $ih#_k0#0
           && $Is($ih#s0#0, Tclass._module.Stream(_module._default.Lemma_Incr1#$_T0))
           && $Is($ih#ord0#0, 
            Tclass._System.___hTotalFunc1(_module._default.Lemma_Incr1#$_T0, TInt))
           && _module.__default.Increasing(_module._default.Lemma_Incr1#$_T0, $LS($LZ), $ih#s0#0, $ih#ord0#0)
           && 
          0 <= $ih#_k0#0
           && $ih#_k0#0 < _k#0
         ==> _module.__default.IncrFrom_h(_module._default.Lemma_Incr1#$_T0, 
          $LS($LZ), 
          $ih#_k0#0, 
          $ih#s0#0, 
          $Unbox(Apply1(_module._default.Lemma_Incr1#$_T0, 
              TInt, 
              $Heap, 
              $ih#ord0#0, 
              _module.Stream.head($ih#s0#0))): int, 
          $ih#ord0#0));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(249,1)
    assume true;
    if (0 < _k#0)
    {
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(250,14)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        assert $Is(_k#0 - 1, Tclass._System.nat());
        _k##0 := _k#0 - 1;
        assume _module.Stream.Cons_q(s#1);
        assume _module.Stream.Cons_q(s#1);
        // ProcessCallStmt: CheckSubrange
        s##0 := _module.Stream.tail(s#1);
        assume true;
        // ProcessCallStmt: CheckSubrange
        ord##0 := ord#1;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call CoCall$$_module.__default.Lemma__Incr1_h(_module._default.Lemma_Incr1#$_T0, _k##0, s##0, ord##0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(250,26)"} true;
    }
    else
    {
    }
}



procedure {:_induction s#0, P#0, ord#0} CheckWellformed$$_module.__default.Theorem__FilterPreservesOrdering(_module._default.Theorem_FilterPreservesOrdering$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Theorem_FilterPreservesOrdering$_T0))
         && $IsAlloc(s#0, 
          Tclass._module.Stream(_module._default.Theorem_FilterPreservesOrdering$_T0), 
          $Heap)
         && $IsA#_module.Stream(s#0), 
    P#0: HandleType
       where $Is(P#0, 
          Tclass._System.___hTotalFunc1(_module._default.Theorem_FilterPreservesOrdering$_T0, TBool))
         && $IsAlloc(P#0, 
          Tclass._System.___hTotalFunc1(_module._default.Theorem_FilterPreservesOrdering$_T0, TBool), 
          $Heap), 
    ord#0: HandleType
       where $Is(ord#0, 
          Tclass._System.___hTotalFunc1(_module._default.Theorem_FilterPreservesOrdering$_T0, TInt))
         && $IsAlloc(ord#0, 
          Tclass._System.___hTotalFunc1(_module._default.Theorem_FilterPreservesOrdering$_T0, TInt), 
          $Heap));
  free requires 41 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:_induction s#0, P#0, ord#0} CheckWellformed$$_module.__default.Theorem__FilterPreservesOrdering(_module._default.Theorem_FilterPreservesOrdering$_T0: Ty, 
    s#0: DatatypeType, 
    P#0: HandleType, 
    ord#0: HandleType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##s#0: DatatypeType;
  var ##ord#0: HandleType;
  var ##s#1: DatatypeType;
  var ##P#0: HandleType;
  var ##s#2: DatatypeType;
  var ##P#1: HandleType;
  var ##s#3: DatatypeType;
  var ##ord#1: HandleType;

    // AddMethodImpl: Theorem_FilterPreservesOrdering, CheckWellformed$$_module.__default.Theorem__FilterPreservesOrdering
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(253,6): initial state"} true;
    ##s#0 := s#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#0, 
      Tclass._module.Stream(_module._default.Theorem_FilterPreservesOrdering$_T0), 
      $Heap);
    ##ord#0 := ord#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##ord#0, 
      Tclass._System.___hTotalFunc1(_module._default.Theorem_FilterPreservesOrdering$_T0, TInt), 
      $Heap);
    assume _module.__default.Increasing#canCall(_module._default.Theorem_FilterPreservesOrdering$_T0, s#0, ord#0);
    assume _module.__default.Increasing(_module._default.Theorem_FilterPreservesOrdering$_T0, $LS($LZ), s#0, ord#0);
    ##s#1 := s#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#1, 
      Tclass._module.Stream(_module._default.Theorem_FilterPreservesOrdering$_T0), 
      $Heap);
    ##P#0 := P#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##P#0, 
      Tclass._System.___hTotalFunc1(_module._default.Theorem_FilterPreservesOrdering$_T0, TBool), 
      $Heap);
    assume _module.__default.AlwaysAnother#canCall(_module._default.Theorem_FilterPreservesOrdering$_T0, s#0, P#0);
    assume _module.__default.AlwaysAnother(_module._default.Theorem_FilterPreservesOrdering$_T0, $LS($LZ), s#0, P#0);
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(255,20): post-state"} true;
    ##s#2 := s#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#2, 
      Tclass._module.Stream(_module._default.Theorem_FilterPreservesOrdering$_T0), 
      $Heap);
    ##P#1 := P#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##P#1, 
      Tclass._System.___hTotalFunc1(_module._default.Theorem_FilterPreservesOrdering$_T0, TBool), 
      $Heap);
    assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.Theorem_FilterPreservesOrdering$_T0, ##s#2, ##P#1)
       ==> _module.__default.AlwaysAnother(_module._default.Theorem_FilterPreservesOrdering$_T0, $LS($LZ), ##s#2, ##P#1)
         || (_module.__default.IsAnother#canCall(_module._default.Theorem_FilterPreservesOrdering$_T0, ##s#2, ##P#1)
           ==> _module.__default.IsAnother(_module._default.Theorem_FilterPreservesOrdering$_T0, ##s#2, ##P#1)
             || (exists n#0: int :: 
              { _module.__default.Tail(_module._default.Theorem_FilterPreservesOrdering$_T0, $LS($LZ), ##s#2, n#0) } 
              LitInt(0) <= n#0
                 && 
                LitInt(0) <= n#0
                 && $Unbox(Apply1(_module._default.Theorem_FilterPreservesOrdering$_T0, 
                    TBool, 
                    $Heap, 
                    ##P#1, 
                    _module.Stream.head(_module.__default.Tail(_module._default.Theorem_FilterPreservesOrdering$_T0, $LS($LZ), ##s#2, n#0)))): bool));
    assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.Theorem_FilterPreservesOrdering$_T0, ##s#2, ##P#1)
       ==> _module.__default.AlwaysAnother(_module._default.Theorem_FilterPreservesOrdering$_T0, $LS($LZ), ##s#2, ##P#1)
         || _module.__default.AlwaysAnother(_module._default.Theorem_FilterPreservesOrdering$_T0, 
          $LS($LS($LZ)), 
          _module.Stream.tail(##s#2), 
          ##P#1);
    assume _module.__default.AlwaysAnother(_module._default.Theorem_FilterPreservesOrdering$_T0, $LS($LZ), ##s#2, ##P#1);
    assume _module.__default.Filter#canCall(_module._default.Theorem_FilterPreservesOrdering$_T0, s#0, P#0);
    assume _module.Stream.Cons_q(_module.__default.Filter(_module._default.Theorem_FilterPreservesOrdering$_T0, $LS($LZ), s#0, P#0));
    ##s#3 := _module.__default.Filter(_module._default.Theorem_FilterPreservesOrdering$_T0, $LS($LZ), s#0, P#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#3, 
      Tclass._module.Stream(_module._default.Theorem_FilterPreservesOrdering$_T0), 
      $Heap);
    ##ord#1 := ord#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##ord#1, 
      Tclass._System.___hTotalFunc1(_module._default.Theorem_FilterPreservesOrdering$_T0, TInt), 
      $Heap);
    assume _module.__default.Increasing#canCall(_module._default.Theorem_FilterPreservesOrdering$_T0, 
      _module.__default.Filter(_module._default.Theorem_FilterPreservesOrdering$_T0, $LS($LZ), s#0, P#0), 
      ord#0);
    assume _module.__default.Increasing(_module._default.Theorem_FilterPreservesOrdering$_T0, 
      $LS($LZ), 
      _module.__default.Filter(_module._default.Theorem_FilterPreservesOrdering$_T0, $LS($LZ), s#0, P#0), 
      ord#0);
}



procedure {:_induction s#0, P#0, ord#0} Call$$_module.__default.Theorem__FilterPreservesOrdering(_module._default.Theorem_FilterPreservesOrdering$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Theorem_FilterPreservesOrdering$_T0))
         && $IsAlloc(s#0, 
          Tclass._module.Stream(_module._default.Theorem_FilterPreservesOrdering$_T0), 
          $Heap)
         && $IsA#_module.Stream(s#0), 
    P#0: HandleType
       where $Is(P#0, 
          Tclass._System.___hTotalFunc1(_module._default.Theorem_FilterPreservesOrdering$_T0, TBool))
         && $IsAlloc(P#0, 
          Tclass._System.___hTotalFunc1(_module._default.Theorem_FilterPreservesOrdering$_T0, TBool), 
          $Heap), 
    ord#0: HandleType
       where $Is(ord#0, 
          Tclass._System.___hTotalFunc1(_module._default.Theorem_FilterPreservesOrdering$_T0, TInt))
         && $IsAlloc(ord#0, 
          Tclass._System.___hTotalFunc1(_module._default.Theorem_FilterPreservesOrdering$_T0, TInt), 
          $Heap));
  // user-defined preconditions
  requires _module.__default.Increasing#canCall(_module._default.Theorem_FilterPreservesOrdering$_T0, s#0, ord#0)
     ==> _module.__default.Increasing(_module._default.Theorem_FilterPreservesOrdering$_T0, $LS($LZ), s#0, ord#0)
       || $Unbox(Apply1(_module._default.Theorem_FilterPreservesOrdering$_T0, 
            TInt, 
            $Heap, 
            ord#0, 
            _module.Stream.head(s#0))): int
         < $Unbox(Apply1(_module._default.Theorem_FilterPreservesOrdering$_T0, 
            TInt, 
            $Heap, 
            ord#0, 
            _module.Stream.head(_module.Stream.tail(s#0)))): int;
  requires _module.__default.Increasing#canCall(_module._default.Theorem_FilterPreservesOrdering$_T0, s#0, ord#0)
     ==> _module.__default.Increasing(_module._default.Theorem_FilterPreservesOrdering$_T0, $LS($LZ), s#0, ord#0)
       || _module.__default.Increasing(_module._default.Theorem_FilterPreservesOrdering$_T0, 
        $LS($LS($LZ)), 
        _module.Stream.tail(s#0), 
        ord#0);
  requires _module.__default.AlwaysAnother#canCall(_module._default.Theorem_FilterPreservesOrdering$_T0, s#0, P#0)
     ==> _module.__default.AlwaysAnother(_module._default.Theorem_FilterPreservesOrdering$_T0, $LS($LZ), s#0, P#0)
       || (_module.__default.IsAnother#canCall(_module._default.Theorem_FilterPreservesOrdering$_T0, s#0, P#0)
         ==> _module.__default.IsAnother(_module._default.Theorem_FilterPreservesOrdering$_T0, s#0, P#0)
           || (exists n#1: int :: 
            { _module.__default.Tail(_module._default.Theorem_FilterPreservesOrdering$_T0, $LS($LZ), s#0, n#1) } 
            LitInt(0) <= n#1
               && 
              LitInt(0) <= n#1
               && $Unbox(Apply1(_module._default.Theorem_FilterPreservesOrdering$_T0, 
                  TBool, 
                  $Heap, 
                  P#0, 
                  _module.Stream.head(_module.__default.Tail(_module._default.Theorem_FilterPreservesOrdering$_T0, $LS($LZ), s#0, n#1)))): bool));
  requires _module.__default.AlwaysAnother#canCall(_module._default.Theorem_FilterPreservesOrdering$_T0, s#0, P#0)
     ==> _module.__default.AlwaysAnother(_module._default.Theorem_FilterPreservesOrdering$_T0, $LS($LZ), s#0, P#0)
       || _module.__default.AlwaysAnother(_module._default.Theorem_FilterPreservesOrdering$_T0, 
        $LS($LS($LZ)), 
        _module.Stream.tail(s#0), 
        P#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Filter#canCall(_module._default.Theorem_FilterPreservesOrdering$_T0, s#0, P#0)
     && _module.__default.Increasing#canCall(_module._default.Theorem_FilterPreservesOrdering$_T0, 
      _module.__default.Filter(_module._default.Theorem_FilterPreservesOrdering$_T0, $LS($LZ), s#0, P#0), 
      ord#0);
  free ensures _module.__default.Increasing#canCall(_module._default.Theorem_FilterPreservesOrdering$_T0, 
      _module.__default.Filter(_module._default.Theorem_FilterPreservesOrdering$_T0, $LS($LZ), s#0, P#0), 
      ord#0)
     && 
    _module.__default.Increasing(_module._default.Theorem_FilterPreservesOrdering$_T0, 
      $LS($LZ), 
      _module.__default.Filter(_module._default.Theorem_FilterPreservesOrdering$_T0, $LS($LZ), s#0, P#0), 
      ord#0)
     && 
    $Unbox(Apply1(_module._default.Theorem_FilterPreservesOrdering$_T0, 
          TInt, 
          $Heap, 
          ord#0, 
          _module.Stream.head(_module.__default.Filter(_module._default.Theorem_FilterPreservesOrdering$_T0, $LS($LZ), s#0, P#0)))): int
       < $Unbox(Apply1(_module._default.Theorem_FilterPreservesOrdering$_T0, 
          TInt, 
          $Heap, 
          ord#0, 
          _module.Stream.head(_module.Stream.tail(_module.__default.Filter(_module._default.Theorem_FilterPreservesOrdering$_T0, $LS($LZ), s#0, P#0))))): int
     && _module.__default.Increasing(_module._default.Theorem_FilterPreservesOrdering$_T0, 
      $LS($LZ), 
      _module.Stream.tail(_module.__default.Filter(_module._default.Theorem_FilterPreservesOrdering$_T0, $LS($LZ), s#0, P#0)), 
      ord#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction s#0, P#0, ord#0} Impl$$_module.__default.Theorem__FilterPreservesOrdering(_module._default.Theorem_FilterPreservesOrdering$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Theorem_FilterPreservesOrdering$_T0))
         && $IsAlloc(s#0, 
          Tclass._module.Stream(_module._default.Theorem_FilterPreservesOrdering$_T0), 
          $Heap)
         && $IsA#_module.Stream(s#0), 
    P#0: HandleType
       where $Is(P#0, 
          Tclass._System.___hTotalFunc1(_module._default.Theorem_FilterPreservesOrdering$_T0, TBool))
         && $IsAlloc(P#0, 
          Tclass._System.___hTotalFunc1(_module._default.Theorem_FilterPreservesOrdering$_T0, TBool), 
          $Heap), 
    ord#0: HandleType
       where $Is(ord#0, 
          Tclass._System.___hTotalFunc1(_module._default.Theorem_FilterPreservesOrdering$_T0, TInt))
         && $IsAlloc(ord#0, 
          Tclass._System.___hTotalFunc1(_module._default.Theorem_FilterPreservesOrdering$_T0, TInt), 
          $Heap))
   returns ($_reverifyPost: bool);
  free requires 41 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.__default.Increasing#canCall(_module._default.Theorem_FilterPreservesOrdering$_T0, s#0, ord#0)
     && 
    _module.__default.Increasing(_module._default.Theorem_FilterPreservesOrdering$_T0, $LS($LZ), s#0, ord#0)
     && 
    $Unbox(Apply1(_module._default.Theorem_FilterPreservesOrdering$_T0, 
          TInt, 
          $Heap, 
          ord#0, 
          _module.Stream.head(s#0))): int
       < $Unbox(Apply1(_module._default.Theorem_FilterPreservesOrdering$_T0, 
          TInt, 
          $Heap, 
          ord#0, 
          _module.Stream.head(_module.Stream.tail(s#0)))): int
     && _module.__default.Increasing(_module._default.Theorem_FilterPreservesOrdering$_T0, 
      $LS($LZ), 
      _module.Stream.tail(s#0), 
      ord#0);
  free requires _module.__default.AlwaysAnother#canCall(_module._default.Theorem_FilterPreservesOrdering$_T0, s#0, P#0)
     && 
    _module.__default.AlwaysAnother(_module._default.Theorem_FilterPreservesOrdering$_T0, $LS($LZ), s#0, P#0)
     && 
    _module.__default.IsAnother(_module._default.Theorem_FilterPreservesOrdering$_T0, s#0, P#0)
     && _module.__default.AlwaysAnother(_module._default.Theorem_FilterPreservesOrdering$_T0, 
      $LS($LZ), 
      _module.Stream.tail(s#0), 
      P#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Filter#canCall(_module._default.Theorem_FilterPreservesOrdering$_T0, s#0, P#0)
     && _module.__default.Increasing#canCall(_module._default.Theorem_FilterPreservesOrdering$_T0, 
      _module.__default.Filter(_module._default.Theorem_FilterPreservesOrdering$_T0, $LS($LZ), s#0, P#0), 
      ord#0);
  ensures _module.__default.Increasing#canCall(_module._default.Theorem_FilterPreservesOrdering$_T0, 
      _module.__default.Filter(_module._default.Theorem_FilterPreservesOrdering$_T0, $LS($LZ), s#0, P#0), 
      ord#0)
     ==> _module.__default.Increasing(_module._default.Theorem_FilterPreservesOrdering$_T0, 
        $LS($LZ), 
        _module.__default.Filter(_module._default.Theorem_FilterPreservesOrdering$_T0, $LS($LZ), s#0, P#0), 
        ord#0)
       || $Unbox(Apply1(_module._default.Theorem_FilterPreservesOrdering$_T0, 
            TInt, 
            $Heap, 
            ord#0, 
            _module.Stream.head(_module.__default.Filter(_module._default.Theorem_FilterPreservesOrdering$_T0, $LS($LS($LZ)), s#0, P#0)))): int
         < $Unbox(Apply1(_module._default.Theorem_FilterPreservesOrdering$_T0, 
            TInt, 
            $Heap, 
            ord#0, 
            _module.Stream.head(_module.Stream.tail(_module.__default.Filter(_module._default.Theorem_FilterPreservesOrdering$_T0, $LS($LS($LZ)), s#0, P#0))))): int;
  ensures _module.__default.Increasing#canCall(_module._default.Theorem_FilterPreservesOrdering$_T0, 
      _module.__default.Filter(_module._default.Theorem_FilterPreservesOrdering$_T0, $LS($LZ), s#0, P#0), 
      ord#0)
     ==> _module.__default.Increasing(_module._default.Theorem_FilterPreservesOrdering$_T0, 
        $LS($LZ), 
        _module.__default.Filter(_module._default.Theorem_FilterPreservesOrdering$_T0, $LS($LZ), s#0, P#0), 
        ord#0)
       || _module.__default.Increasing(_module._default.Theorem_FilterPreservesOrdering$_T0, 
        $LS($LS($LZ)), 
        _module.Stream.tail(_module.__default.Filter(_module._default.Theorem_FilterPreservesOrdering$_T0, $LS($LS($LZ)), s#0, P#0)), 
        ord#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction s#0, P#0, ord#0} Impl$$_module.__default.Theorem__FilterPreservesOrdering(_module._default.Theorem_FilterPreservesOrdering$_T0: Ty, 
    s#0: DatatypeType, 
    P#0: HandleType, 
    ord#0: HandleType)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var s##0: DatatypeType;
  var ord##0: HandleType;
  var s##1: DatatypeType;
  var P##0: HandleType;
  var low##0: int;
  var ord##1: HandleType;
  var s##2: DatatypeType;
  var ##s#4: DatatypeType;
  var ##P#2: HandleType;
  var low##1: int;
  var ord##2: HandleType;

    // AddMethodImpl: Theorem_FilterPreservesOrdering, Impl$$_module.__default.Theorem__FilterPreservesOrdering
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(256,0): initial state"} true;
    assume $IsA#_module.Stream(s#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#s0#0: DatatypeType, $ih#P0#0: HandleType, $ih#ord0#0: HandleType :: 
      $Is($ih#s0#0, 
            Tclass._module.Stream(_module._default.Theorem_FilterPreservesOrdering$_T0))
           && $Is($ih#P0#0, 
            Tclass._System.___hTotalFunc1(_module._default.Theorem_FilterPreservesOrdering$_T0, TBool))
           && $Is($ih#ord0#0, 
            Tclass._System.___hTotalFunc1(_module._default.Theorem_FilterPreservesOrdering$_T0, TInt))
           && 
          _module.__default.Increasing(_module._default.Theorem_FilterPreservesOrdering$_T0, 
            $LS($LZ), 
            $ih#s0#0, 
            $ih#ord0#0)
           && _module.__default.AlwaysAnother(_module._default.Theorem_FilterPreservesOrdering$_T0, 
            $LS($LZ), 
            $ih#s0#0, 
            $ih#P0#0)
           && false
         ==> _module.__default.Increasing(_module._default.Theorem_FilterPreservesOrdering$_T0, 
          $LS($LZ), 
          _module.__default.Filter(_module._default.Theorem_FilterPreservesOrdering$_T0, 
            $LS($LZ), 
            $ih#s0#0, 
            $ih#P0#0), 
          $ih#ord0#0));
    $_reverifyPost := false;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(257,14)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    s##0 := s#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    ord##0 := ord#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.Lemma__Incr1(_module._default.Theorem_FilterPreservesOrdering$_T0, s##0, ord##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(257,21)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(258,32)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    s##1 := s#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    P##0 := P#0;
    assume _module.Stream.Cons_q(s#0);
    assume _module.Stream.Cons_q(s#0);
    // ProcessCallStmt: CheckSubrange
    low##0 := $Unbox(Apply1(_module._default.Theorem_FilterPreservesOrdering$_T0, 
        TInt, 
        $Heap, 
        ord#0, 
        _module.Stream.head(s#0))): int;
    assume true;
    // ProcessCallStmt: CheckSubrange
    ord##1 := ord#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.Lemma__FilterPreservesIncrFrom(_module._default.Theorem_FilterPreservesOrdering$_T0, s##1, P##0, low##0, ord##1);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(258,55)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(259,14)
    // TrCallStmt: Before ProcessCallStmt
    ##s#4 := s#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#4, 
      Tclass._module.Stream(_module._default.Theorem_FilterPreservesOrdering$_T0), 
      $Heap);
    ##P#2 := P#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##P#2, 
      Tclass._System.___hTotalFunc1(_module._default.Theorem_FilterPreservesOrdering$_T0, TBool), 
      $Heap);
    assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.Theorem_FilterPreservesOrdering$_T0, ##s#4, ##P#2)
       ==> _module.__default.AlwaysAnother(_module._default.Theorem_FilterPreservesOrdering$_T0, $LS($LZ), ##s#4, ##P#2)
         || (_module.__default.IsAnother#canCall(_module._default.Theorem_FilterPreservesOrdering$_T0, ##s#4, ##P#2)
           ==> _module.__default.IsAnother(_module._default.Theorem_FilterPreservesOrdering$_T0, ##s#4, ##P#2)
             || (exists n#3: int :: 
              { _module.__default.Tail(_module._default.Theorem_FilterPreservesOrdering$_T0, $LS($LZ), ##s#4, n#3) } 
              LitInt(0) <= n#3
                 && 
                LitInt(0) <= n#3
                 && $Unbox(Apply1(_module._default.Theorem_FilterPreservesOrdering$_T0, 
                    TBool, 
                    $Heap, 
                    ##P#2, 
                    _module.Stream.head(_module.__default.Tail(_module._default.Theorem_FilterPreservesOrdering$_T0, $LS($LZ), ##s#4, n#3)))): bool));
    assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.Theorem_FilterPreservesOrdering$_T0, ##s#4, ##P#2)
       ==> _module.__default.AlwaysAnother(_module._default.Theorem_FilterPreservesOrdering$_T0, $LS($LZ), ##s#4, ##P#2)
         || _module.__default.AlwaysAnother(_module._default.Theorem_FilterPreservesOrdering$_T0, 
          $LS($LS($LZ)), 
          _module.Stream.tail(##s#4), 
          ##P#2);
    assume _module.__default.AlwaysAnother(_module._default.Theorem_FilterPreservesOrdering$_T0, $LS($LZ), ##s#4, ##P#2);
    assume _module.__default.Filter#canCall(_module._default.Theorem_FilterPreservesOrdering$_T0, s#0, P#0);
    assume _module.Stream.Cons_q(_module.__default.Filter(_module._default.Theorem_FilterPreservesOrdering$_T0, $LS($LZ), s#0, P#0));
    assume _module.__default.Filter#canCall(_module._default.Theorem_FilterPreservesOrdering$_T0, s#0, P#0);
    // ProcessCallStmt: CheckSubrange
    s##2 := _module.__default.Filter(_module._default.Theorem_FilterPreservesOrdering$_T0, $LS($LZ), s#0, P#0);
    assume _module.Stream.Cons_q(s#0);
    assume _module.Stream.Cons_q(s#0);
    // ProcessCallStmt: CheckSubrange
    low##1 := $Unbox(Apply1(_module._default.Theorem_FilterPreservesOrdering$_T0, 
        TInt, 
        $Heap, 
        ord#0, 
        _module.Stream.head(s#0))): int;
    assume true;
    // ProcessCallStmt: CheckSubrange
    ord##2 := ord#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.Lemma__Incr0(_module._default.Theorem_FilterPreservesOrdering$_T0, s##2, low##1, ord##2);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(259,45)"} true;
}



procedure CheckWellformed$$_module.__default.Lemma__FilterPreservesIncrFrom(_module._default.Lemma_FilterPreservesIncrFrom$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Lemma_FilterPreservesIncrFrom$_T0))
         && $IsAlloc(s#0, 
          Tclass._module.Stream(_module._default.Lemma_FilterPreservesIncrFrom$_T0), 
          $Heap)
         && $IsA#_module.Stream(s#0), 
    P#0: HandleType
       where $Is(P#0, 
          Tclass._System.___hTotalFunc1(_module._default.Lemma_FilterPreservesIncrFrom$_T0, TBool))
         && $IsAlloc(P#0, 
          Tclass._System.___hTotalFunc1(_module._default.Lemma_FilterPreservesIncrFrom$_T0, TBool), 
          $Heap), 
    low#0: int, 
    ord#0: HandleType
       where $Is(ord#0, 
          Tclass._System.___hTotalFunc1(_module._default.Lemma_FilterPreservesIncrFrom$_T0, TInt))
         && $IsAlloc(ord#0, 
          Tclass._System.___hTotalFunc1(_module._default.Lemma_FilterPreservesIncrFrom$_T0, TInt), 
          $Heap));
  free requires 35 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Lemma__FilterPreservesIncrFrom(_module._default.Lemma_FilterPreservesIncrFrom$_T0: Ty, 
    s#0: DatatypeType, 
    P#0: HandleType, 
    low#0: int, 
    ord#0: HandleType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##s#0: DatatypeType;
  var ##low#0: int;
  var ##ord#0: HandleType;
  var ##s#1: DatatypeType;
  var ##P#0: HandleType;
  var ##s#2: DatatypeType;
  var ##P#1: HandleType;
  var ##s#3: DatatypeType;
  var ##P#2: HandleType;
  var ##s#4: DatatypeType;
  var ##low#1: int;
  var ##ord#1: HandleType;

    // AddMethodImpl: Lemma_FilterPreservesIncrFrom, CheckWellformed$$_module.__default.Lemma__FilterPreservesIncrFrom
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(261,15): initial state"} true;
    ##s#0 := s#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#0, 
      Tclass._module.Stream(_module._default.Lemma_FilterPreservesIncrFrom$_T0), 
      $Heap);
    ##low#0 := low#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##low#0, TInt, $Heap);
    ##ord#0 := ord#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##ord#0, 
      Tclass._System.___hTotalFunc1(_module._default.Lemma_FilterPreservesIncrFrom$_T0, TInt), 
      $Heap);
    assume _module.__default.IncrFrom#canCall(_module._default.Lemma_FilterPreservesIncrFrom$_T0, s#0, low#0, ord#0);
    assume _module.__default.IncrFrom(_module._default.Lemma_FilterPreservesIncrFrom$_T0, $LS($LZ), s#0, low#0, ord#0);
    ##s#1 := s#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#1, 
      Tclass._module.Stream(_module._default.Lemma_FilterPreservesIncrFrom$_T0), 
      $Heap);
    ##P#0 := P#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##P#0, 
      Tclass._System.___hTotalFunc1(_module._default.Lemma_FilterPreservesIncrFrom$_T0, TBool), 
      $Heap);
    assume _module.__default.AlwaysAnother#canCall(_module._default.Lemma_FilterPreservesIncrFrom$_T0, s#0, P#0);
    assume _module.__default.AlwaysAnother(_module._default.Lemma_FilterPreservesIncrFrom$_T0, $LS($LZ), s#0, P#0);
    assume _module.Stream.Cons_q(s#0);
    assume low#0
       <= $Unbox(Apply1(_module._default.Lemma_FilterPreservesIncrFrom$_T0, 
          TInt, 
          $Heap, 
          ord#0, 
          _module.Stream.head(s#0))): int;
    ##s#2 := s#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#2, 
      Tclass._module.Stream(_module._default.Lemma_FilterPreservesIncrFrom$_T0), 
      $Heap);
    ##P#1 := P#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##P#1, 
      Tclass._System.___hTotalFunc1(_module._default.Lemma_FilterPreservesIncrFrom$_T0, TBool), 
      $Heap);
    assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.Lemma_FilterPreservesIncrFrom$_T0, ##s#2, ##P#1)
       ==> _module.__default.AlwaysAnother(_module._default.Lemma_FilterPreservesIncrFrom$_T0, $LS($LZ), ##s#2, ##P#1)
         || (_module.__default.IsAnother#canCall(_module._default.Lemma_FilterPreservesIncrFrom$_T0, ##s#2, ##P#1)
           ==> _module.__default.IsAnother(_module._default.Lemma_FilterPreservesIncrFrom$_T0, ##s#2, ##P#1)
             || (exists n#0: int :: 
              { _module.__default.Tail(_module._default.Lemma_FilterPreservesIncrFrom$_T0, $LS($LZ), ##s#2, n#0) } 
              LitInt(0) <= n#0
                 && 
                LitInt(0) <= n#0
                 && $Unbox(Apply1(_module._default.Lemma_FilterPreservesIncrFrom$_T0, 
                    TBool, 
                    $Heap, 
                    ##P#1, 
                    _module.Stream.head(_module.__default.Tail(_module._default.Lemma_FilterPreservesIncrFrom$_T0, $LS($LZ), ##s#2, n#0)))): bool));
    assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.Lemma_FilterPreservesIncrFrom$_T0, ##s#2, ##P#1)
       ==> _module.__default.AlwaysAnother(_module._default.Lemma_FilterPreservesIncrFrom$_T0, $LS($LZ), ##s#2, ##P#1)
         || _module.__default.AlwaysAnother(_module._default.Lemma_FilterPreservesIncrFrom$_T0, 
          $LS($LS($LZ)), 
          _module.Stream.tail(##s#2), 
          ##P#1);
    assume _module.__default.AlwaysAnother(_module._default.Lemma_FilterPreservesIncrFrom$_T0, $LS($LZ), ##s#2, ##P#1);
    assume _module.__default.Next#canCall(_module._default.Lemma_FilterPreservesIncrFrom$_T0, s#0, P#0);
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(263,18): post-state"} true;
    ##s#3 := s#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#3, 
      Tclass._module.Stream(_module._default.Lemma_FilterPreservesIncrFrom$_T0), 
      $Heap);
    ##P#2 := P#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##P#2, 
      Tclass._System.___hTotalFunc1(_module._default.Lemma_FilterPreservesIncrFrom$_T0, TBool), 
      $Heap);
    assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.Lemma_FilterPreservesIncrFrom$_T0, ##s#3, ##P#2)
       ==> _module.__default.AlwaysAnother(_module._default.Lemma_FilterPreservesIncrFrom$_T0, $LS($LZ), ##s#3, ##P#2)
         || (_module.__default.IsAnother#canCall(_module._default.Lemma_FilterPreservesIncrFrom$_T0, ##s#3, ##P#2)
           ==> _module.__default.IsAnother(_module._default.Lemma_FilterPreservesIncrFrom$_T0, ##s#3, ##P#2)
             || (exists n#1: int :: 
              { _module.__default.Tail(_module._default.Lemma_FilterPreservesIncrFrom$_T0, $LS($LZ), ##s#3, n#1) } 
              LitInt(0) <= n#1
                 && 
                LitInt(0) <= n#1
                 && $Unbox(Apply1(_module._default.Lemma_FilterPreservesIncrFrom$_T0, 
                    TBool, 
                    $Heap, 
                    ##P#2, 
                    _module.Stream.head(_module.__default.Tail(_module._default.Lemma_FilterPreservesIncrFrom$_T0, $LS($LZ), ##s#3, n#1)))): bool));
    assert {:subsumption 0} _module.__default.AlwaysAnother#canCall(_module._default.Lemma_FilterPreservesIncrFrom$_T0, ##s#3, ##P#2)
       ==> _module.__default.AlwaysAnother(_module._default.Lemma_FilterPreservesIncrFrom$_T0, $LS($LZ), ##s#3, ##P#2)
         || _module.__default.AlwaysAnother(_module._default.Lemma_FilterPreservesIncrFrom$_T0, 
          $LS($LS($LZ)), 
          _module.Stream.tail(##s#3), 
          ##P#2);
    assume _module.__default.AlwaysAnother(_module._default.Lemma_FilterPreservesIncrFrom$_T0, $LS($LZ), ##s#3, ##P#2);
    assume _module.__default.Filter#canCall(_module._default.Lemma_FilterPreservesIncrFrom$_T0, s#0, P#0);
    assume _module.Stream.Cons_q(_module.__default.Filter(_module._default.Lemma_FilterPreservesIncrFrom$_T0, $LS($LZ), s#0, P#0));
    ##s#4 := _module.__default.Filter(_module._default.Lemma_FilterPreservesIncrFrom$_T0, $LS($LZ), s#0, P#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#4, 
      Tclass._module.Stream(_module._default.Lemma_FilterPreservesIncrFrom$_T0), 
      $Heap);
    ##low#1 := low#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##low#1, TInt, $Heap);
    ##ord#1 := ord#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##ord#1, 
      Tclass._System.___hTotalFunc1(_module._default.Lemma_FilterPreservesIncrFrom$_T0, TInt), 
      $Heap);
    assume _module.__default.IncrFrom#canCall(_module._default.Lemma_FilterPreservesIncrFrom$_T0, 
      _module.__default.Filter(_module._default.Lemma_FilterPreservesIncrFrom$_T0, $LS($LZ), s#0, P#0), 
      low#0, 
      ord#0);
    assume _module.__default.IncrFrom(_module._default.Lemma_FilterPreservesIncrFrom$_T0, 
      $LS($LZ), 
      _module.__default.Filter(_module._default.Lemma_FilterPreservesIncrFrom$_T0, $LS($LZ), s#0, P#0), 
      low#0, 
      ord#0);
}



procedure Call$$_module.__default.Lemma__FilterPreservesIncrFrom(_module._default.Lemma_FilterPreservesIncrFrom$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Lemma_FilterPreservesIncrFrom$_T0))
         && $IsAlloc(s#0, 
          Tclass._module.Stream(_module._default.Lemma_FilterPreservesIncrFrom$_T0), 
          $Heap)
         && $IsA#_module.Stream(s#0), 
    P#0: HandleType
       where $Is(P#0, 
          Tclass._System.___hTotalFunc1(_module._default.Lemma_FilterPreservesIncrFrom$_T0, TBool))
         && $IsAlloc(P#0, 
          Tclass._System.___hTotalFunc1(_module._default.Lemma_FilterPreservesIncrFrom$_T0, TBool), 
          $Heap), 
    low#0: int, 
    ord#0: HandleType
       where $Is(ord#0, 
          Tclass._System.___hTotalFunc1(_module._default.Lemma_FilterPreservesIncrFrom$_T0, TInt))
         && $IsAlloc(ord#0, 
          Tclass._System.___hTotalFunc1(_module._default.Lemma_FilterPreservesIncrFrom$_T0, TInt), 
          $Heap));
  // user-defined preconditions
  requires _module.__default.IncrFrom#canCall(_module._default.Lemma_FilterPreservesIncrFrom$_T0, s#0, low#0, ord#0)
     ==> _module.__default.IncrFrom(_module._default.Lemma_FilterPreservesIncrFrom$_T0, $LS($LZ), s#0, low#0, ord#0)
       || low#0
         <= $Unbox(Apply1(_module._default.Lemma_FilterPreservesIncrFrom$_T0, 
            TInt, 
            $Heap, 
            ord#0, 
            _module.Stream.head(s#0))): int;
  requires _module.__default.IncrFrom#canCall(_module._default.Lemma_FilterPreservesIncrFrom$_T0, s#0, low#0, ord#0)
     ==> _module.__default.IncrFrom(_module._default.Lemma_FilterPreservesIncrFrom$_T0, $LS($LZ), s#0, low#0, ord#0)
       || _module.__default.IncrFrom(_module._default.Lemma_FilterPreservesIncrFrom$_T0, 
        $LS($LS($LZ)), 
        _module.Stream.tail(s#0), 
        $Unbox(Apply1(_module._default.Lemma_FilterPreservesIncrFrom$_T0, 
              TInt, 
              $Heap, 
              ord#0, 
              _module.Stream.head(s#0))): int
           + 1, 
        ord#0);
  requires _module.__default.AlwaysAnother#canCall(_module._default.Lemma_FilterPreservesIncrFrom$_T0, s#0, P#0)
     ==> _module.__default.AlwaysAnother(_module._default.Lemma_FilterPreservesIncrFrom$_T0, $LS($LZ), s#0, P#0)
       || (_module.__default.IsAnother#canCall(_module._default.Lemma_FilterPreservesIncrFrom$_T0, s#0, P#0)
         ==> _module.__default.IsAnother(_module._default.Lemma_FilterPreservesIncrFrom$_T0, s#0, P#0)
           || (exists n#2: int :: 
            { _module.__default.Tail(_module._default.Lemma_FilterPreservesIncrFrom$_T0, $LS($LZ), s#0, n#2) } 
            LitInt(0) <= n#2
               && 
              LitInt(0) <= n#2
               && $Unbox(Apply1(_module._default.Lemma_FilterPreservesIncrFrom$_T0, 
                  TBool, 
                  $Heap, 
                  P#0, 
                  _module.Stream.head(_module.__default.Tail(_module._default.Lemma_FilterPreservesIncrFrom$_T0, $LS($LZ), s#0, n#2)))): bool));
  requires _module.__default.AlwaysAnother#canCall(_module._default.Lemma_FilterPreservesIncrFrom$_T0, s#0, P#0)
     ==> _module.__default.AlwaysAnother(_module._default.Lemma_FilterPreservesIncrFrom$_T0, $LS($LZ), s#0, P#0)
       || _module.__default.AlwaysAnother(_module._default.Lemma_FilterPreservesIncrFrom$_T0, 
        $LS($LS($LZ)), 
        _module.Stream.tail(s#0), 
        P#0);
  requires low#0
     <= $Unbox(Apply1(_module._default.Lemma_FilterPreservesIncrFrom$_T0, 
        TInt, 
        $Heap, 
        ord#0, 
        _module.Stream.head(s#0))): int;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Filter#canCall(_module._default.Lemma_FilterPreservesIncrFrom$_T0, s#0, P#0)
     && _module.__default.IncrFrom#canCall(_module._default.Lemma_FilterPreservesIncrFrom$_T0, 
      _module.__default.Filter(_module._default.Lemma_FilterPreservesIncrFrom$_T0, $LS($LZ), s#0, P#0), 
      low#0, 
      ord#0);
  free ensures _module.__default.IncrFrom#canCall(_module._default.Lemma_FilterPreservesIncrFrom$_T0, 
      _module.__default.Filter(_module._default.Lemma_FilterPreservesIncrFrom$_T0, $LS($LZ), s#0, P#0), 
      low#0, 
      ord#0)
     && 
    _module.__default.IncrFrom(_module._default.Lemma_FilterPreservesIncrFrom$_T0, 
      $LS($LZ), 
      _module.__default.Filter(_module._default.Lemma_FilterPreservesIncrFrom$_T0, $LS($LZ), s#0, P#0), 
      low#0, 
      ord#0)
     && 
    low#0
       <= $Unbox(Apply1(_module._default.Lemma_FilterPreservesIncrFrom$_T0, 
          TInt, 
          $Heap, 
          ord#0, 
          _module.Stream.head(_module.__default.Filter(_module._default.Lemma_FilterPreservesIncrFrom$_T0, $LS($LZ), s#0, P#0)))): int
     && _module.__default.IncrFrom(_module._default.Lemma_FilterPreservesIncrFrom$_T0, 
      $LS($LZ), 
      _module.Stream.tail(_module.__default.Filter(_module._default.Lemma_FilterPreservesIncrFrom$_T0, $LS($LZ), s#0, P#0)), 
      $Unbox(Apply1(_module._default.Lemma_FilterPreservesIncrFrom$_T0, 
            TInt, 
            $Heap, 
            ord#0, 
            _module.Stream.head(_module.__default.Filter(_module._default.Lemma_FilterPreservesIncrFrom$_T0, $LS($LZ), s#0, P#0)))): int
         + 1, 
      ord#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, s#1, P#1, low#1, ord#1} CoCall$$_module.__default.Lemma__FilterPreservesIncrFrom_h(_module._default.Lemma_FilterPreservesIncrFrom#$_T0: Ty, 
    _k#0: int where LitInt(0) <= _k#0, 
    s#1: DatatypeType
       where $Is(s#1, Tclass._module.Stream(_module._default.Lemma_FilterPreservesIncrFrom#$_T0))
         && $IsAlloc(s#1, 
          Tclass._module.Stream(_module._default.Lemma_FilterPreservesIncrFrom#$_T0), 
          $Heap)
         && $IsA#_module.Stream(s#1), 
    P#1: HandleType
       where $Is(P#1, 
          Tclass._System.___hTotalFunc1(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, TBool))
         && $IsAlloc(P#1, 
          Tclass._System.___hTotalFunc1(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, TBool), 
          $Heap), 
    low#1: int, 
    ord#1: HandleType
       where $Is(ord#1, 
          Tclass._System.___hTotalFunc1(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, TInt))
         && $IsAlloc(ord#1, 
          Tclass._System.___hTotalFunc1(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, TInt), 
          $Heap));
  // user-defined preconditions
  requires _module.__default.IncrFrom#canCall(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, s#1, low#1, ord#1)
     ==> _module.__default.IncrFrom(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, $LS($LZ), s#1, low#1, ord#1)
       || low#1
         <= $Unbox(Apply1(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, 
            TInt, 
            $Heap, 
            ord#1, 
            _module.Stream.head(s#1))): int;
  requires _module.__default.IncrFrom#canCall(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, s#1, low#1, ord#1)
     ==> _module.__default.IncrFrom(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, $LS($LZ), s#1, low#1, ord#1)
       || _module.__default.IncrFrom(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, 
        $LS($LS($LZ)), 
        _module.Stream.tail(s#1), 
        $Unbox(Apply1(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, 
              TInt, 
              $Heap, 
              ord#1, 
              _module.Stream.head(s#1))): int
           + 1, 
        ord#1);
  requires _module.__default.AlwaysAnother#canCall(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, s#1, P#1)
     ==> _module.__default.AlwaysAnother(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, $LS($LZ), s#1, P#1)
       || (_module.__default.IsAnother#canCall(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, s#1, P#1)
         ==> _module.__default.IsAnother(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, s#1, P#1)
           || (exists n#3: int :: 
            { _module.__default.Tail(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, $LS($LZ), s#1, n#3) } 
            LitInt(0) <= n#3
               && 
              LitInt(0) <= n#3
               && $Unbox(Apply1(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, 
                  TBool, 
                  $Heap, 
                  P#1, 
                  _module.Stream.head(_module.__default.Tail(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, $LS($LZ), s#1, n#3)))): bool));
  requires _module.__default.AlwaysAnother#canCall(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, s#1, P#1)
     ==> _module.__default.AlwaysAnother(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, $LS($LZ), s#1, P#1)
       || _module.__default.AlwaysAnother(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, 
        $LS($LS($LZ)), 
        _module.Stream.tail(s#1), 
        P#1);
  requires low#1
     <= $Unbox(Apply1(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, 
        TInt, 
        $Heap, 
        ord#1, 
        _module.Stream.head(s#1))): int;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Filter#canCall(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, s#1, P#1)
     && _module.__default.IncrFrom_h#canCall(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, 
      _k#0, 
      _module.__default.Filter(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, $LS($LZ), s#1, P#1), 
      low#1, 
      ord#1);
  free ensures _module.__default.IncrFrom_h#canCall(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, 
      _k#0, 
      _module.__default.Filter(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, $LS($LZ), s#1, P#1), 
      low#1, 
      ord#1)
     && 
    _module.__default.IncrFrom_h(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, 
      $LS($LZ), 
      _k#0, 
      _module.__default.Filter(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, $LS($LZ), s#1, P#1), 
      low#1, 
      ord#1)
     && (0 < _k#0
       ==> low#1
           <= $Unbox(Apply1(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, 
              TInt, 
              $Heap, 
              ord#1, 
              _module.Stream.head(_module.__default.Filter(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, $LS($LZ), s#1, P#1)))): int
         && _module.__default.IncrFrom_h(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, 
          $LS($LZ), 
          _k#0 - 1, 
          _module.Stream.tail(_module.__default.Filter(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, $LS($LZ), s#1, P#1)), 
          $Unbox(Apply1(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, 
                TInt, 
                $Heap, 
                ord#1, 
                _module.Stream.head(_module.__default.Filter(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, $LS($LZ), s#1, P#1)))): int
             + 1, 
          ord#1));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, s#1, P#1, low#1, ord#1} Impl$$_module.__default.Lemma__FilterPreservesIncrFrom_h(_module._default.Lemma_FilterPreservesIncrFrom#$_T0: Ty, 
    _k#0: int where LitInt(0) <= _k#0, 
    s#1: DatatypeType
       where $Is(s#1, Tclass._module.Stream(_module._default.Lemma_FilterPreservesIncrFrom#$_T0))
         && $IsAlloc(s#1, 
          Tclass._module.Stream(_module._default.Lemma_FilterPreservesIncrFrom#$_T0), 
          $Heap)
         && $IsA#_module.Stream(s#1), 
    P#1: HandleType
       where $Is(P#1, 
          Tclass._System.___hTotalFunc1(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, TBool))
         && $IsAlloc(P#1, 
          Tclass._System.___hTotalFunc1(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, TBool), 
          $Heap), 
    low#1: int, 
    ord#1: HandleType
       where $Is(ord#1, 
          Tclass._System.___hTotalFunc1(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, TInt))
         && $IsAlloc(ord#1, 
          Tclass._System.___hTotalFunc1(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, TInt), 
          $Heap))
   returns ($_reverifyPost: bool);
  free requires 35 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.__default.IncrFrom#canCall(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, s#1, low#1, ord#1)
     && 
    _module.__default.IncrFrom(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, $LS($LZ), s#1, low#1, ord#1)
     && 
    low#1
       <= $Unbox(Apply1(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, 
          TInt, 
          $Heap, 
          ord#1, 
          _module.Stream.head(s#1))): int
     && _module.__default.IncrFrom(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, 
      $LS($LZ), 
      _module.Stream.tail(s#1), 
      $Unbox(Apply1(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, 
            TInt, 
            $Heap, 
            ord#1, 
            _module.Stream.head(s#1))): int
         + 1, 
      ord#1);
  free requires _module.__default.AlwaysAnother#canCall(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, s#1, P#1)
     && 
    _module.__default.AlwaysAnother(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, $LS($LZ), s#1, P#1)
     && 
    _module.__default.IsAnother(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, s#1, P#1)
     && _module.__default.AlwaysAnother(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, 
      $LS($LZ), 
      _module.Stream.tail(s#1), 
      P#1);
  requires low#1
     <= $Unbox(Apply1(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, 
        TInt, 
        $Heap, 
        ord#1, 
        _module.Stream.head(s#1))): int;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Filter#canCall(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, s#1, P#1)
     && _module.__default.IncrFrom_h#canCall(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, 
      _k#0, 
      _module.__default.Filter(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, $LS($LZ), s#1, P#1), 
      low#1, 
      ord#1);
  ensures _module.__default.IncrFrom_h#canCall(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, 
      _k#0, 
      _module.__default.Filter(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, $LS($LZ), s#1, P#1), 
      low#1, 
      ord#1)
     ==> _module.__default.IncrFrom_h(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, 
        $LS($LZ), 
        _k#0, 
        _module.__default.Filter(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, $LS($LZ), s#1, P#1), 
        low#1, 
        ord#1)
       || (0 < _k#0
         ==> low#1
           <= $Unbox(Apply1(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, 
              TInt, 
              $Heap, 
              ord#1, 
              _module.Stream.head(_module.__default.Filter(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, $LS($LS($LZ)), s#1, P#1)))): int);
  ensures _module.__default.IncrFrom_h#canCall(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, 
      _k#0, 
      _module.__default.Filter(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, $LS($LZ), s#1, P#1), 
      low#1, 
      ord#1)
     ==> _module.__default.IncrFrom_h(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, 
        $LS($LZ), 
        _k#0, 
        _module.__default.Filter(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, $LS($LZ), s#1, P#1), 
        low#1, 
        ord#1)
       || (0 < _k#0
         ==> _module.__default.IncrFrom_h(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, 
          $LS($LS($LZ)), 
          _k#0 - 1, 
          _module.Stream.tail(_module.__default.Filter(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, $LS($LS($LZ)), s#1, P#1)), 
          $Unbox(Apply1(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, 
                TInt, 
                $Heap, 
                ord#1, 
                _module.Stream.head(_module.__default.Filter(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, $LS($LS($LZ)), s#1, P#1)))): int
             + 1, 
          ord#1));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0, s#1, P#1, low#1, ord#1} Impl$$_module.__default.Lemma__FilterPreservesIncrFrom_h(_module._default.Lemma_FilterPreservesIncrFrom#$_T0: Ty, 
    _k#0: int, 
    s#1: DatatypeType, 
    P#1: HandleType, 
    low#1: int, 
    ord#1: HandleType)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var _k##0: int;
  var s##0: DatatypeType;
  var P##0: HandleType;
  var low##0: int;
  var ord##0: HandleType;
  var s##1: DatatypeType;
  var P##1: HandleType;
  var _k##1: int;
  var s##2: DatatypeType;
  var P##2: HandleType;
  var low##1: int;
  var ord##1: HandleType;

    // AddMethodImpl: Lemma_FilterPreservesIncrFrom#, Impl$$_module.__default.Lemma__FilterPreservesIncrFrom_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(261,15): initial state"} true;
    assume $IsA#_module.Stream(s#1);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: int, 
        $ih#s0#0: DatatypeType, 
        $ih#P0#0: HandleType, 
        $ih#low0#0: int, 
        $ih#ord0#0: HandleType :: 
      LitInt(0) <= $ih#_k0#0
           && $Is($ih#s0#0, 
            Tclass._module.Stream(_module._default.Lemma_FilterPreservesIncrFrom#$_T0))
           && $Is($ih#P0#0, 
            Tclass._System.___hTotalFunc1(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, TBool))
           && $Is($ih#ord0#0, 
            Tclass._System.___hTotalFunc1(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, TInt))
           && 
          _module.__default.IncrFrom(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, 
            $LS($LZ), 
            $ih#s0#0, 
            $ih#low0#0, 
            $ih#ord0#0)
           && _module.__default.AlwaysAnother(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, 
            $LS($LZ), 
            $ih#s0#0, 
            $ih#P0#0)
           && $ih#low0#0
             <= $Unbox(Apply1(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, 
                TInt, 
                $initHeapForallStmt#0, 
                $ih#ord0#0, 
                _module.Stream.head($ih#s0#0))): int
           && ((0 <= $ih#_k0#0 && $ih#_k0#0 < _k#0)
             || ($ih#_k0#0 == _k#0
               && 
              0
                 <= _module.__default.Next(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, $ih#s0#0, $ih#P0#0)
               && _module.__default.Next(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, $ih#s0#0, $ih#P0#0)
                 < _module.__default.Next(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, s#1, P#1)))
         ==> _module.__default.IncrFrom_h(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, 
          $LS($LZ), 
          $ih#_k0#0, 
          _module.__default.Filter(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, 
            $LS($LZ), 
            $ih#s0#0, 
            $ih#P0#0), 
          $ih#low0#0, 
          $ih#ord0#0));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(265,1)
    assume true;
    if (0 < _k#0)
    {
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(266,3)
        assume _module.Stream.Cons_q(s#1);
        assume _module.Stream.Cons_q(s#1);
        if ($Unbox(Apply1(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, 
            TBool, 
            $Heap, 
            P#1, 
            _module.Stream.head(s#1))): bool)
        {
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(267,34)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            assert $Is(_k#0 - 1, Tclass._System.nat());
            _k##0 := _k#0 - 1;
            assume _module.Stream.Cons_q(s#1);
            assume _module.Stream.Cons_q(s#1);
            // ProcessCallStmt: CheckSubrange
            s##0 := _module.Stream.tail(s#1);
            assume true;
            // ProcessCallStmt: CheckSubrange
            P##0 := P#1;
            assume _module.Stream.Cons_q(s#1);
            assume _module.Stream.Cons_q(s#1);
            // ProcessCallStmt: CheckSubrange
            low##0 := $Unbox(Apply1(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, 
                  TInt, 
                  $Heap, 
                  ord#1, 
                  _module.Stream.head(s#1))): int
               + 1;
            assume true;
            // ProcessCallStmt: CheckSubrange
            ord##0 := ord#1;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0 <= _k#0 || _k##0 == _k#0;
            assert 0
                 <= _module.__default.Next(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, s#1, P#1)
               || _k##0 < _k#0
               || _module.__default.Next(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, s##0, P##0)
                 == _module.__default.Next(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, s#1, P#1);
            assert _k##0 < _k#0
               || (_k##0 == _k#0
                 && _module.__default.Next(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, s##0, P##0)
                   < _module.__default.Next(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, s#1, P#1));
            // ProcessCallStmt: Make the call
            call CoCall$$_module.__default.Lemma__FilterPreservesIncrFrom_h(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, _k##0, s##0, P##0, low##0, ord##0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(267,64)"} true;
        }
        else
        {
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(269,14)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            s##1 := s#1;
            assume true;
            // ProcessCallStmt: CheckSubrange
            P##1 := P#1;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call Call$$_module.__default.NextLemma(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, s##1, P##1);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(269,19)"} true;
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(270,39)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            _k##1 := _k#0;
            assume _module.Stream.Cons_q(s#1);
            assume _module.Stream.Cons_q(s#1);
            // ProcessCallStmt: CheckSubrange
            s##2 := _module.Stream.tail(s#1);
            assume true;
            // ProcessCallStmt: CheckSubrange
            P##2 := P#1;
            assume true;
            // ProcessCallStmt: CheckSubrange
            low##1 := low#1;
            assume true;
            // ProcessCallStmt: CheckSubrange
            ord##1 := ord#1;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0 <= _k#0 || _k##1 == _k#0;
            assert 0
                 <= _module.__default.Next(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, s#1, P#1)
               || _k##1 < _k#0
               || _module.__default.Next(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, s##2, P##2)
                 == _module.__default.Next(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, s#1, P#1);
            assert _k##1 < _k#0
               || (_k##1 == _k#0
                 && _module.__default.Next(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, s##2, P##2)
                   < _module.__default.Next(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, s#1, P#1));
            // ProcessCallStmt: Make the call
            call CoCall$$_module.__default.Lemma__FilterPreservesIncrFrom_h(_module._default.Lemma_FilterPreservesIncrFrom#$_T0, _k##1, s##2, P##2, low##1, ord##1);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Filter.dfy(270,59)"} true;
        }
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

const unique tytagFamily$_#Func4: TyTagFamily;

const unique tytagFamily$_#PartialFunc4: TyTagFamily;

const unique tytagFamily$_#TotalFunc4: TyTagFamily;

const unique tytagFamily$_tuple#2: TyTagFamily;

const unique tytagFamily$_tuple#0: TyTagFamily;

const unique tytagFamily$Stream: TyTagFamily;

const unique tytagFamily$_default: TyTagFamily;
