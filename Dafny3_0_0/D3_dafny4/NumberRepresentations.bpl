// Dafny 3.0.0.30204
// Command Line Options: -compile:0 -noVerify /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy -print:./NumberRepresentations.bpl

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

// function declaration for _module._default.eval
function _module.__default.eval($ly: LayerType, digits#0: Seq Box, base#0: int) : int;

function _module.__default.eval#canCall(digits#0: Seq Box, base#0: int) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, digits#0: Seq Box, base#0: int :: 
  { _module.__default.eval($LS($ly), digits#0, base#0) } 
  _module.__default.eval($LS($ly), digits#0, base#0)
     == _module.__default.eval($ly, digits#0, base#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, digits#0: Seq Box, base#0: int :: 
  { _module.__default.eval(AsFuelBottom($ly), digits#0, base#0) } 
  _module.__default.eval($ly, digits#0, base#0)
     == _module.__default.eval($LZ, digits#0, base#0));

// consequence axiom for _module.__default.eval
axiom 2 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, digits#0: Seq Box, base#0: int :: 
    { _module.__default.eval($ly, digits#0, base#0) } 
    _module.__default.eval#canCall(digits#0, base#0)
         || (2 != $FunctionContextHeight
           && 
          $Is(digits#0, TSeq(TInt))
           && LitInt(2) <= base#0)
       ==> true);

function _module.__default.eval#requires(LayerType, Seq Box, int) : bool;

// #requires axiom for _module.__default.eval
axiom (forall $ly: LayerType, digits#0: Seq Box, base#0: int :: 
  { _module.__default.eval#requires($ly, digits#0, base#0) } 
  $Is(digits#0, TSeq(TInt))
     ==> _module.__default.eval#requires($ly, digits#0, base#0) == (LitInt(2) <= base#0));

// definition axiom for _module.__default.eval (revealed)
axiom 2 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, digits#0: Seq Box, base#0: int :: 
    { _module.__default.eval($LS($ly), digits#0, base#0) } 
    _module.__default.eval#canCall(digits#0, base#0)
         || (2 != $FunctionContextHeight
           && 
          $Is(digits#0, TSeq(TInt))
           && LitInt(2) <= base#0)
       ==> (Seq#Length(digits#0) != LitInt(0)
           ==> _module.__default.eval#canCall(Seq#Drop(digits#0, LitInt(1)), base#0))
         && _module.__default.eval($LS($ly), digits#0, base#0)
           == (if Seq#Length(digits#0) == LitInt(0)
             then 0
             else $Unbox(Seq#Index(digits#0, LitInt(0))): int
               + Mul(base#0, _module.__default.eval($ly, Seq#Drop(digits#0, LitInt(1)), base#0))));

// definition axiom for _module.__default.eval for decreasing-related literals (revealed)
axiom 2 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, digits#0: Seq Box, base#0: int :: 
    {:weight 3} { _module.__default.eval($LS($ly), Lit(digits#0), base#0) } 
    _module.__default.eval#canCall(Lit(digits#0), base#0)
         || (2 != $FunctionContextHeight
           && 
          $Is(digits#0, TSeq(TInt))
           && LitInt(2) <= base#0)
       ==> (Seq#Length(Lit(digits#0)) != LitInt(0)
           ==> _module.__default.eval#canCall(Lit(Seq#Drop(Lit(digits#0), LitInt(1))), base#0))
         && _module.__default.eval($LS($ly), Lit(digits#0), base#0)
           == (if Seq#Length(Lit(digits#0)) == LitInt(0)
             then 0
             else $Unbox(Seq#Index(Lit(digits#0), LitInt(0))): int
               + Mul(base#0, 
                _module.__default.eval($LS($ly), Lit(Seq#Drop(Lit(digits#0), LitInt(1))), base#0))));

// definition axiom for _module.__default.eval for all literals (revealed)
axiom 2 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, digits#0: Seq Box, base#0: int :: 
    {:weight 3} { _module.__default.eval($LS($ly), Lit(digits#0), LitInt(base#0)) } 
    _module.__default.eval#canCall(Lit(digits#0), LitInt(base#0))
         || (2 != $FunctionContextHeight
           && 
          $Is(digits#0, TSeq(TInt))
           && LitInt(2) <= LitInt(base#0))
       ==> (Seq#Length(Lit(digits#0)) != LitInt(0)
           ==> _module.__default.eval#canCall(Lit(Seq#Drop(Lit(digits#0), LitInt(1))), LitInt(base#0)))
         && _module.__default.eval($LS($ly), Lit(digits#0), LitInt(base#0))
           == (if Seq#Length(Lit(digits#0)) == LitInt(0)
             then 0
             else $Unbox(Seq#Index(Lit(digits#0), LitInt(0))): int
               + Mul(LitInt(base#0), 
                LitInt(_module.__default.eval($LS($ly), Lit(Seq#Drop(Lit(digits#0), LitInt(1))), LitInt(base#0))))));

procedure CheckWellformed$$_module.__default.eval(digits#0: Seq Box where $Is(digits#0, TSeq(TInt)), base#0: int);
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.eval(digits#0: Seq Box, base#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##digits#0: Seq Box;
  var ##base#0: int;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function eval
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(9,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume LitInt(2) <= base#0;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (Seq#Length(digits#0) == LitInt(0))
        {
            assume _module.__default.eval($LS($LZ), digits#0, base#0) == LitInt(0);
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.eval($LS($LZ), digits#0, base#0), TInt);
        }
        else
        {
            assert 0 <= LitInt(0) && LitInt(0) < Seq#Length(digits#0);
            assert 0 <= LitInt(1) && LitInt(1) <= Seq#Length(digits#0);
            ##digits#0 := Seq#Drop(digits#0, LitInt(1));
            // assume allocatedness for argument to function
            assume $IsAlloc(##digits#0, TSeq(TInt), $Heap);
            ##base#0 := base#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##base#0, TInt, $Heap);
            assert {:subsumption 0} LitInt(2) <= ##base#0;
            assume LitInt(2) <= ##base#0;
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert Seq#Rank(##digits#0) < Seq#Rank(digits#0);
            assume _module.__default.eval#canCall(Seq#Drop(digits#0, LitInt(1)), base#0);
            assume _module.__default.eval($LS($LZ), digits#0, base#0)
               == $Unbox(Seq#Index(digits#0, LitInt(0))): int
                 + Mul(base#0, _module.__default.eval($LS($LZ), Seq#Drop(digits#0, LitInt(1)), base#0));
            assume _module.__default.eval#canCall(Seq#Drop(digits#0, LitInt(1)), base#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.eval($LS($LZ), digits#0, base#0), TInt);
        }

        assert b$reqreads#0;
    }
}



procedure CheckWellformed$$_module.__default.test__eval();
  free requires 7 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.test__eval();
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.test__eval() returns ($_reverifyPost: bool);
  free requires 7 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.test__eval() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var base#0: int;
  var ##digits#0: Seq Box;
  var ##base#0: int;
  var base#2: int;
  var ##digits#1: Seq Box;
  var ##base#1: int;
  var base#4: int;
  var ##digits#2: Seq Box;
  var ##base#2: int;
  var ##digits#3: Seq Box;
  var ##base#3: int;
  var oct#0: int;
  var dec#0: int;
  var $rhs#0: int;
  var $rhs#1: int;
  var ##digits#4: Seq Box;
  var ##base#4: int;
  var ##digits#5: Seq Box;
  var ##base#5: int;
  var ##digits#6: Seq Box;
  var ##base#6: int;
  var ##digits#7: Seq Box;
  var ##base#7: int;
  var ##digits#8: Seq Box;
  var ##base#8: int;

    // AddMethodImpl: test_eval, Impl$$_module.__default.test__eval
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(17,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(18,3)
    // Begin Comprehension WF check
    havoc base#0;
    if (true)
    {
        if (LitInt(2) <= base#0)
        {
            ##digits#0 := Lit(Seq#Empty(): Seq Box);
            // assume allocatedness for argument to function
            assume $IsAlloc(##digits#0, TSeq(TInt), $Heap);
            ##base#0 := base#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##base#0, TInt, $Heap);
            assert {:subsumption 0} LitInt(2) <= ##base#0;
            assume _module.__default.eval#canCall(Lit(Seq#Empty(): Seq Box), base#0);
        }
    }

    // End Comprehension WF check
    assume (forall base#1: int :: 
      { _module.__default.eval($LS($LZ), Seq#Empty(): Seq Box, base#1) } 
      LitInt(2) <= base#1
         ==> _module.__default.eval#canCall(Lit(Seq#Empty(): Seq Box), base#1));
    assert {:subsumption 0} (forall base#1: int :: 
      { _module.__default.eval($LS($LS($LZ)), Seq#Empty(): Seq Box, base#1) } 
      true
         ==> 
        LitInt(2) <= base#1
         ==> _module.__default.eval($LS($LS($LZ)), Lit(Seq#Empty(): Seq Box), base#1)
           == LitInt(0));
    assume (forall base#1: int :: 
      { _module.__default.eval($LS($LZ), Seq#Empty(): Seq Box, base#1) } 
      true
         ==> 
        LitInt(2) <= base#1
         ==> _module.__default.eval($LS($LZ), Lit(Seq#Empty(): Seq Box), base#1) == LitInt(0));
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(19,3)
    // Begin Comprehension WF check
    havoc base#2;
    if (true)
    {
        if (LitInt(2) <= base#2)
        {
            ##digits#1 := Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0))));
            // assume allocatedness for argument to function
            assume $IsAlloc(##digits#1, TSeq(TInt), $Heap);
            ##base#1 := base#2;
            // assume allocatedness for argument to function
            assume $IsAlloc(##base#1, TInt, $Heap);
            assert {:subsumption 0} LitInt(2) <= ##base#1;
            assume _module.__default.eval#canCall(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0)))), base#2);
        }
    }

    // End Comprehension WF check
    assume (forall base#3: int :: 
      { _module.__default.eval($LS($LZ), Seq#Build(Seq#Empty(): Seq Box, $Box(0)), base#3) } 
      LitInt(2) <= base#3
         ==> _module.__default.eval#canCall(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0)))), base#3));
    assert {:subsumption 0} (forall base#3: int :: 
      { _module.__default.eval($LS($LS($LZ)), Seq#Build(Seq#Empty(): Seq Box, $Box(0)), base#3) } 
      true
         ==> 
        LitInt(2) <= base#3
         ==> _module.__default.eval($LS($LS($LZ)), Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0)))), base#3)
           == LitInt(0));
    assume (forall base#3: int :: 
      { _module.__default.eval($LS($LZ), Seq#Build(Seq#Empty(): Seq Box, $Box(0)), base#3) } 
      true
         ==> 
        LitInt(2) <= base#3
         ==> _module.__default.eval($LS($LZ), Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0)))), base#3)
           == LitInt(0));
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(24,3)
    // Begin Comprehension WF check
    havoc base#4;
    if (true)
    {
        if (LitInt(2) <= base#4)
        {
            ##digits#2 := Lit(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0))), $Box(LitInt(0))));
            // assume allocatedness for argument to function
            assume $IsAlloc(##digits#2, TSeq(TInt), $Heap);
            ##base#2 := base#4;
            // assume allocatedness for argument to function
            assume $IsAlloc(##base#2, TInt, $Heap);
            assert {:subsumption 0} LitInt(2) <= ##base#2;
            assume _module.__default.eval#canCall(Lit(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0))), $Box(LitInt(0)))), 
              base#4);
        }
    }

    // End Comprehension WF check
    assume (forall base#5: int :: 
      { _module.__default.eval($LS($LZ), Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(0)), $Box(0)), base#5) } 
      LitInt(2) <= base#5
         ==> _module.__default.eval#canCall(Lit(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0))), $Box(LitInt(0)))), 
          base#5));
    assert {:subsumption 0} (forall base#5: int :: 
      { _module.__default.eval($LS($LS($LZ)), 
          Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(0)), $Box(0)), 
          base#5) } 
      true
         ==> 
        LitInt(2) <= base#5
         ==> _module.__default.eval($LS($LS($LZ)), 
            Lit(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0))), $Box(LitInt(0)))), 
            base#5)
           == LitInt(0));
    assume (forall base#5: int :: 
      { _module.__default.eval($LS($LZ), Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(0)), $Box(0)), base#5) } 
      true
         ==> 
        LitInt(2) <= base#5
         ==> _module.__default.eval($LS($LZ), 
            Lit(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0))), $Box(LitInt(0)))), 
            base#5)
           == LitInt(0));
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(26,3)
    ##digits#3 := Lit(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(3))), $Box(LitInt(2))));
    // assume allocatedness for argument to function
    assume $IsAlloc(##digits#3, TSeq(TInt), $Heap);
    ##base#3 := LitInt(10);
    // assume allocatedness for argument to function
    assume $IsAlloc(##base#3, TInt, $Heap);
    assert {:subsumption 0} LitInt(2) <= ##base#3;
    assume _module.__default.eval#canCall(Lit(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(3))), $Box(LitInt(2)))), 
      LitInt(10));
    assume _module.__default.eval#canCall(Lit(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(3))), $Box(LitInt(2)))), 
      LitInt(10));
    assert {:subsumption 0} LitInt(_module.__default.eval($LS($LS($LZ)), 
          Lit(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(3))), $Box(LitInt(2)))), 
          LitInt(10)))
       == LitInt(23);
    assume LitInt(_module.__default.eval($LS($LZ), 
          Lit(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(3))), $Box(LitInt(2)))), 
          LitInt(10)))
       == LitInt(23);
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(28,16)
    assume true;
    assume true;
    assume true;
    $rhs#0 := LitInt(8);
    assume true;
    $rhs#1 := LitInt(10);
    oct#0 := $rhs#0;
    dec#0 := $rhs#1;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(28,23)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(29,3)
    ##digits#4 := Lit(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(1))), $Box(LitInt(3))));
    // assume allocatedness for argument to function
    assume $IsAlloc(##digits#4, TSeq(TInt), $Heap);
    ##base#4 := oct#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##base#4, TInt, $Heap);
    assert {:subsumption 0} LitInt(2) <= ##base#4;
    assume _module.__default.eval#canCall(Lit(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(1))), $Box(LitInt(3)))), 
      oct#0);
    ##digits#5 := Lit(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(5))), $Box(LitInt(2))));
    // assume allocatedness for argument to function
    assume $IsAlloc(##digits#5, TSeq(TInt), $Heap);
    ##base#5 := dec#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##base#5, TInt, $Heap);
    assert {:subsumption 0} LitInt(2) <= ##base#5;
    assume _module.__default.eval#canCall(Lit(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(5))), $Box(LitInt(2)))), 
      dec#0);
    assume _module.__default.eval#canCall(Lit(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(1))), $Box(LitInt(3)))), 
        oct#0)
       && _module.__default.eval#canCall(Lit(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(5))), $Box(LitInt(2)))), 
        dec#0);
    assert {:subsumption 0} _module.__default.eval($LS($LS($LZ)), 
        Lit(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(1))), $Box(LitInt(3)))), 
        oct#0)
       == _module.__default.eval($LS($LS($LZ)), 
        Lit(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(5))), $Box(LitInt(2)))), 
        dec#0);
    assume _module.__default.eval($LS($LZ), 
        Lit(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(1))), $Box(LitInt(3)))), 
        oct#0)
       == _module.__default.eval($LS($LZ), 
        Lit(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(5))), $Box(LitInt(2)))), 
        dec#0);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(31,3)
    ##digits#6 := Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(29))));
    // assume allocatedness for argument to function
    assume $IsAlloc(##digits#6, TSeq(TInt), $Heap);
    ##base#6 := LitInt(420);
    // assume allocatedness for argument to function
    assume $IsAlloc(##base#6, TInt, $Heap);
    assert {:subsumption 0} LitInt(2) <= ##base#6;
    assume _module.__default.eval#canCall(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(29)))), LitInt(420));
    assume _module.__default.eval#canCall(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(29)))), LitInt(420));
    assert {:subsumption 0} LitInt(_module.__default.eval($LS($LS($LZ)), 
          Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(29)))), 
          LitInt(420)))
       == LitInt(29);
    assume LitInt(_module.__default.eval($LS($LZ), Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(29)))), LitInt(420)))
       == LitInt(29);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(32,3)
    ##digits#7 := Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(29))));
    // assume allocatedness for argument to function
    assume $IsAlloc(##digits#7, TSeq(TInt), $Heap);
    ##base#7 := LitInt(8);
    // assume allocatedness for argument to function
    assume $IsAlloc(##base#7, TInt, $Heap);
    assert {:subsumption 0} LitInt(2) <= ##base#7;
    assume _module.__default.eval#canCall(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(29)))), LitInt(8));
    assume _module.__default.eval#canCall(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(29)))), LitInt(8));
    assert {:subsumption 0} LitInt(_module.__default.eval($LS($LS($LZ)), Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(29)))), LitInt(8)))
       == LitInt(29);
    assume LitInt(_module.__default.eval($LS($LZ), Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(29)))), LitInt(8)))
       == LitInt(29);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(34,3)
    ##digits#8 := Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(-2))), $Box(LitInt(1))), 
        $Box(LitInt(-3))));
    // assume allocatedness for argument to function
    assume $IsAlloc(##digits#8, TSeq(TInt), $Heap);
    ##base#8 := LitInt(5);
    // assume allocatedness for argument to function
    assume $IsAlloc(##base#8, TInt, $Heap);
    assert {:subsumption 0} LitInt(2) <= ##base#8;
    assume _module.__default.eval#canCall(Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(-2))), $Box(LitInt(1))), 
          $Box(LitInt(-3)))), 
      LitInt(5));
    assume _module.__default.eval#canCall(Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(-2))), $Box(LitInt(1))), 
          $Box(LitInt(-3)))), 
      LitInt(5));
    assert {:subsumption 0} LitInt(_module.__default.eval($LS($LS($LZ)), 
          Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(-2))), $Box(LitInt(1))), 
              $Box(LitInt(-3)))), 
          LitInt(5)))
       == LitInt(-72);
    assume LitInt(_module.__default.eval($LS($LZ), 
          Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(-2))), $Box(LitInt(1))), 
              $Box(LitInt(-3)))), 
          LitInt(5)))
       == LitInt(-72);
}



// function declaration for _module._default.IsSkewNumber
function _module.__default.IsSkewNumber(digits#0: Seq Box, lowDigit#0: int, base#0: int) : bool;

function _module.__default.IsSkewNumber#canCall(digits#0: Seq Box, lowDigit#0: int, base#0: int) : bool;

// consequence axiom for _module.__default.IsSkewNumber
axiom 1 <= $FunctionContextHeight
   ==> (forall digits#0: Seq Box, lowDigit#0: int, base#0: int :: 
    { _module.__default.IsSkewNumber(digits#0, lowDigit#0, base#0) } 
    _module.__default.IsSkewNumber#canCall(digits#0, lowDigit#0, base#0)
         || (1 != $FunctionContextHeight && $Is(digits#0, TSeq(TInt)))
       ==> true);

function _module.__default.IsSkewNumber#requires(Seq Box, int, int) : bool;

// #requires axiom for _module.__default.IsSkewNumber
axiom (forall digits#0: Seq Box, lowDigit#0: int, base#0: int :: 
  { _module.__default.IsSkewNumber#requires(digits#0, lowDigit#0, base#0) } 
  $Is(digits#0, TSeq(TInt))
     ==> _module.__default.IsSkewNumber#requires(digits#0, lowDigit#0, base#0) == true);

// definition axiom for _module.__default.IsSkewNumber (revealed)
axiom 1 <= $FunctionContextHeight
   ==> (forall digits#0: Seq Box, lowDigit#0: int, base#0: int :: 
    { _module.__default.IsSkewNumber(digits#0, lowDigit#0, base#0) } 
    _module.__default.IsSkewNumber#canCall(digits#0, lowDigit#0, base#0)
         || (1 != $FunctionContextHeight && $Is(digits#0, TSeq(TInt)))
       ==> _module.__default.IsSkewNumber(digits#0, lowDigit#0, base#0)
         == (
          LitInt(2) <= base#0
           && 
          lowDigit#0 <= LitInt(0)
           && 0 < lowDigit#0 + base#0
           && (forall i#0: int :: 
            { $Unbox(Seq#Index(digits#0, i#0)): int } 
            true
               ==> (LitInt(0) <= i#0 && i#0 < Seq#Length(digits#0)
                   ==> lowDigit#0 <= $Unbox(Seq#Index(digits#0, i#0)): int)
                 && (LitInt(0) <= i#0 && i#0 < Seq#Length(digits#0)
                   ==> $Unbox(Seq#Index(digits#0, i#0)): int < lowDigit#0 + base#0))));

// definition axiom for _module.__default.IsSkewNumber for all literals (revealed)
axiom 1 <= $FunctionContextHeight
   ==> (forall digits#0: Seq Box, lowDigit#0: int, base#0: int :: 
    {:weight 3} { _module.__default.IsSkewNumber(Lit(digits#0), LitInt(lowDigit#0), LitInt(base#0)) } 
    _module.__default.IsSkewNumber#canCall(Lit(digits#0), LitInt(lowDigit#0), LitInt(base#0))
         || (1 != $FunctionContextHeight && $Is(digits#0, TSeq(TInt)))
       ==> _module.__default.IsSkewNumber(Lit(digits#0), LitInt(lowDigit#0), LitInt(base#0))
         == (
          LitInt(2) <= LitInt(base#0)
           && 
          LitInt(lowDigit#0) <= LitInt(0)
           && 0 < lowDigit#0 + base#0
           && (forall i#1: int :: 
            { $Unbox(Seq#Index(digits#0, i#1)): int } 
            true
               ==> (LitInt(0) <= i#1 && i#1 < Seq#Length(Lit(digits#0))
                   ==> LitInt(lowDigit#0) <= $Unbox(Seq#Index(Lit(digits#0), i#1)): int)
                 && (LitInt(0) <= i#1 && i#1 < Seq#Length(Lit(digits#0))
                   ==> $Unbox(Seq#Index(Lit(digits#0), i#1)): int < lowDigit#0 + base#0))));

procedure CheckWellformed$$_module.__default.IsSkewNumber(digits#0: Seq Box where $Is(digits#0, TSeq(TInt)), lowDigit#0: int, base#0: int);
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.IsSkewNumber(digits#0: Seq Box, lowDigit#0: int, base#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var i#2: int;


    // AddWellformednessCheck for function IsSkewNumber
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(41,10): initial state"} true;
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
        if (LitInt(2) <= base#0)
        {
            if (lowDigit#0 <= LitInt(0))
            {
            }
        }

        if (LitInt(2) <= base#0 && lowDigit#0 <= LitInt(0) && 0 < lowDigit#0 + base#0)
        {
            // Begin Comprehension WF check
            havoc i#2;
            if (true)
            {
                if (LitInt(0) <= i#2)
                {
                }

                if (LitInt(0) <= i#2 && i#2 < Seq#Length(digits#0))
                {
                    assert 0 <= i#2 && i#2 < Seq#Length(digits#0);
                    if (lowDigit#0 <= $Unbox(Seq#Index(digits#0, i#2)): int)
                    {
                        assert 0 <= i#2 && i#2 < Seq#Length(digits#0);
                    }
                }
            }

            // End Comprehension WF check
        }

        assume _module.__default.IsSkewNumber(digits#0, lowDigit#0, base#0)
           == (
            LitInt(2) <= base#0
             && 
            lowDigit#0 <= LitInt(0)
             && 0 < lowDigit#0 + base#0
             && (forall i#3: int :: 
              { $Unbox(Seq#Index(digits#0, i#3)): int } 
              true
                 ==> (LitInt(0) <= i#3 && i#3 < Seq#Length(digits#0)
                     ==> lowDigit#0 <= $Unbox(Seq#Index(digits#0, i#3)): int)
                   && (LitInt(0) <= i#3 && i#3 < Seq#Length(digits#0)
                     ==> $Unbox(Seq#Index(digits#0, i#3)): int < lowDigit#0 + base#0)));
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.IsSkewNumber(digits#0, lowDigit#0, base#0), TBool);
    }
}



procedure CheckWellformed$$_module.__default.CompleteNat(n#0: int where LitInt(0) <= n#0, base#0: int)
   returns (digits#0: Seq Box
       where $Is(digits#0, TSeq(TInt)) && $IsAlloc(digits#0, TSeq(TInt), $Heap));
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.CompleteNat(n#0: int, base#0: int) returns (digits#0: Seq Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##digits#0: Seq Box;
  var ##lowDigit#0: int;
  var ##base#0: int;
  var ##digits#1: Seq Box;
  var ##base#1: int;

    // AddMethodImpl: CompleteNat, CheckWellformed$$_module.__default.CompleteNat
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(51,6): initial state"} true;
    assume LitInt(2) <= base#0;
    havoc $Heap;
    assume old($Heap) == $Heap;
    havoc digits#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(53,40): post-state"} true;
    ##digits#0 := digits#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##digits#0, TSeq(TInt), $Heap);
    ##lowDigit#0 := LitInt(0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##lowDigit#0, TInt, $Heap);
    ##base#0 := base#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##base#0, TInt, $Heap);
    assume _module.__default.IsSkewNumber#canCall(digits#0, LitInt(0), base#0);
    assume _module.__default.IsSkewNumber(digits#0, LitInt(0), base#0);
    ##digits#1 := digits#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##digits#1, TSeq(TInt), $Heap);
    ##base#1 := base#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##base#1, TInt, $Heap);
    assert {:subsumption 0} LitInt(2) <= ##base#1;
    assume LitInt(2) <= ##base#1;
    assume _module.__default.eval#canCall(digits#0, base#0);
    assume _module.__default.eval($LS($LZ), digits#0, base#0) == n#0;
}



procedure Call$$_module.__default.CompleteNat(n#0: int where LitInt(0) <= n#0, base#0: int)
   returns (digits#0: Seq Box
       where $Is(digits#0, TSeq(TInt)) && $IsAlloc(digits#0, TSeq(TInt), $Heap));
  // user-defined preconditions
  requires LitInt(2) <= base#0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.IsSkewNumber#canCall(digits#0, LitInt(0), base#0)
     && (_module.__default.IsSkewNumber(digits#0, LitInt(0), base#0)
       ==> _module.__default.eval#canCall(digits#0, base#0));
  free ensures _module.__default.IsSkewNumber#canCall(digits#0, LitInt(0), base#0)
     && 
    _module.__default.IsSkewNumber(digits#0, LitInt(0), base#0)
     && 
    LitInt(2) <= base#0
     && 
    LitInt(0) <= LitInt(0)
     && 0 < 0 + base#0
     && (forall i#0: int :: 
      { $Unbox(Seq#Index(digits#0, i#0)): int } 
      true
         ==> (LitInt(0) <= i#0 && i#0 < Seq#Length(digits#0)
             ==> LitInt(0) <= $Unbox(Seq#Index(digits#0, i#0)): int)
           && (LitInt(0) <= i#0 && i#0 < Seq#Length(digits#0)
             ==> $Unbox(Seq#Index(digits#0, i#0)): int < 0 + base#0));
  ensures _module.__default.eval($LS($LS($LZ)), digits#0, base#0) == n#0;
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.CompleteNat(n#0: int where LitInt(0) <= n#0, base#0: int)
   returns (digits#0: Seq Box
       where $Is(digits#0, TSeq(TInt)) && $IsAlloc(digits#0, TSeq(TInt), $Heap), 
    $_reverifyPost: bool);
  free requires 6 == $FunctionContextHeight;
  // user-defined preconditions
  requires LitInt(2) <= base#0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.IsSkewNumber#canCall(digits#0, LitInt(0), base#0)
     && (_module.__default.IsSkewNumber(digits#0, LitInt(0), base#0)
       ==> _module.__default.eval#canCall(digits#0, base#0));
  ensures _module.__default.IsSkewNumber#canCall(digits#0, LitInt(0), base#0)
     ==> _module.__default.IsSkewNumber(digits#0, LitInt(0), base#0)
       || LitInt(2) <= base#0;
  ensures _module.__default.IsSkewNumber#canCall(digits#0, LitInt(0), base#0)
     ==> _module.__default.IsSkewNumber(digits#0, LitInt(0), base#0)
       || LitInt(0) <= LitInt(0);
  ensures _module.__default.IsSkewNumber#canCall(digits#0, LitInt(0), base#0)
     ==> _module.__default.IsSkewNumber(digits#0, LitInt(0), base#0) || 0 < 0 + base#0;
  ensures _module.__default.IsSkewNumber#canCall(digits#0, LitInt(0), base#0)
     ==> _module.__default.IsSkewNumber(digits#0, LitInt(0), base#0)
       || (forall i#1: int :: 
        { $Unbox(Seq#Index(digits#0, i#1)): int } 
        true
           ==> (LitInt(0) <= i#1 && i#1 < Seq#Length(digits#0)
               ==> LitInt(0) <= $Unbox(Seq#Index(digits#0, i#1)): int)
             && (LitInt(0) <= i#1 && i#1 < Seq#Length(digits#0)
               ==> $Unbox(Seq#Index(digits#0, i#1)): int < 0 + base#0));
  ensures _module.__default.eval($LS($LS($LZ)), digits#0, base#0) == n#0;
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.CompleteNat(n#0: int, base#0: int) returns (digits#0: Seq Box, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var d#0: int;
  var m#0: int;
  var $rhs#0: int;
  var $rhs#1: int;
  var n##0: int;
  var base##0: int;
  var d##0: int;
  var $rhs##0: Seq Box
     where $Is($rhs##0, TSeq(TInt)) && $IsAlloc($rhs##0, TSeq(TInt), $Heap);
  var n##1: int;
  var base##1: int;

    // AddMethodImpl: CompleteNat, Impl$$_module.__default.CompleteNat
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(54,0): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(55,3)
    assume true;
    if (n#0 < base#0)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(56,12)
        assume true;
        assume true;
        assert $Is(Seq#Build(Seq#Empty(): Seq Box, $Box(n#0)), TSeq(TInt));
        digits#0 := Seq#Build(Seq#Empty(): Seq Box, $Box(n#0));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(56,17)"} true;
    }
    else
    {
        // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(58,14)
        assume true;
        assume true;
        assert base#0 != 0;
        assume true;
        $rhs#0 := Div(n#0, base#0);
        assert base#0 != 0;
        assume true;
        $rhs#1 := Mod(n#0, base#0);
        d#0 := $rhs#0;
        m#0 := $rhs#1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(58,34)"} true;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(59,5)
        assume true;
        assert Mul(base#0, d#0) + m#0 == n#0;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(60,14)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        n##0 := n#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        base##0 := base#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        d##0 := d#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.DivIsLess(n##0, base##0, d##0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(60,25)"} true;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(61,5)
        if (d#0 < n#0)
        {
        }

        assume true;
        assert {:subsumption 0} d#0 < n#0;
        assert {:subsumption 0} LitInt(0) <= m#0;
        assume d#0 < n#0 && LitInt(0) <= m#0;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(62,26)
        assume true;
        // TrCallStmt: Adding lhs with type seq<int>
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        assert $Is(d#0, Tclass._System.nat());
        n##1 := d#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        base##1 := base#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assert 0 <= n#0 || n##1 == n#0;
        assert 0 <= base#0 || n##1 < n#0 || base##1 == base#0;
        assert n##1 < n#0 || (n##1 == n#0 && base##1 < base#0);
        // ProcessCallStmt: Make the call
        call $rhs##0 := Call$$_module.__default.CompleteNat(n##1, base##1);
        // TrCallStmt: After ProcessCallStmt
        digits#0 := $rhs##0;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(62,34)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(63,12)
        assume true;
        assume true;
        digits#0 := Seq#Append(Seq#Build(Seq#Empty(): Seq Box, $Box(m#0)), digits#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(63,26)"} true;
    }
}



procedure CheckWellformed$$_module.__default.DivIsLess(n#0: int where LitInt(0) <= n#0, base#0: int, d#0: int);
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.DivIsLess(n#0: int, base#0: int, d#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: DivIsLess, CheckWellformed$$_module.__default.DivIsLess
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(67,6): initial state"} true;
    if (LitInt(2) <= base#0)
    {
    }

    assume LitInt(2) <= base#0 && base#0 <= n#0;
    assert base#0 != 0;
    assume d#0 == Div(n#0, base#0);
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(69,12): post-state"} true;
    assume d#0 < n#0;
}



procedure Call$$_module.__default.DivIsLess(n#0: int where LitInt(0) <= n#0, base#0: int, d#0: int);
  // user-defined preconditions
  requires LitInt(2) <= base#0;
  requires base#0 <= n#0;
  requires d#0 == Div(n#0, base#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures d#0 < n#0;
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.DivIsLess(n#0: int where LitInt(0) <= n#0, base#0: int, d#0: int)
   returns ($_reverifyPost: bool);
  free requires 5 == $FunctionContextHeight;
  // user-defined preconditions
  requires LitInt(2) <= base#0;
  requires base#0 <= n#0;
  requires d#0 == Div(n#0, base#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures d#0 < n#0;
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.DivIsLess(n#0: int, base#0: int, d#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var m#0: int;
  var x##0_0_2_0: int;
  var y##0_0_2_0: int;
  var a##0_0_5_0: int;
  var x##0_0_5_0: int;
  var y##0_0_5_0: int;

    // AddMethodImpl: DivIsLess, Impl$$_module.__default.DivIsLess
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(70,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(71,9)
    assume true;
    assert base#0 != 0;
    assume true;
    m#0 := Mod(n#0, base#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(71,19)"} true;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(72,3)
    assume true;
    if (n#0 <= d#0)
    {
        // ----- calc statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(73,5)
        // Assume Fuel Constant
        if (*)
        {
            // ----- assert wf[initial] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(73,5)
            assume true;
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(73,5)
            assume true;
            // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(73,5)
            assume Mul(base#0, d#0) + m#0 == n#0;
            // ----- Hint0 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(73,5)
            // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(75,11)
            assume true;
            assert LitInt(0) <= m#0;
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(73,5)
            assume true;
            // ----- assert line0 ==> line1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(73,5)
            assert {:subsumption 0} Mul(base#0, d#0) + m#0 == n#0 ==> Mul(base#0, d#0) <= n#0;
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(73,5)
            assume true;
            // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(73,5)
            assume Mul(base#0, d#0) <= n#0;
            // ----- Hint1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(73,5)
            // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(77,11)
            assume true;
            assert n#0 <= d#0;
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(77,40)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            a##0_0_5_0 := base#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            x##0_0_5_0 := n#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            y##0_0_5_0 := d#0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call Call$$_module.__default.MulIsMonotonic(a##0_0_5_0, x##0_0_5_0, y##0_0_5_0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(77,51)"} true;
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(73,5)
            assume true;
            // ----- assert line1 ==> line2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(73,5)
            assert {:subsumption 0} Mul(base#0, d#0) <= n#0 ==> Mul(base#0, n#0) <= n#0;
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(73,5)
            assume true;
            // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(73,5)
            assume Mul(base#0, n#0) <= n#0;
            // ----- Hint2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(73,5)
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(73,5)
            assume true;
            // ----- assert line2 ==> line3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(73,5)
            assert {:subsumption 0} Mul(base#0, n#0) <= n#0 ==> Mul(base#0 - 1, n#0) + n#0 <= n#0;
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(73,5)
            assume true;
            // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(73,5)
            assume Mul(base#0 - 1, n#0) + n#0 <= n#0;
            // ----- Hint3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(73,5)
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(73,5)
            assume true;
            // ----- assert line3 ==> line4 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(73,5)
            assert {:subsumption 0} Mul(base#0 - 1, n#0) + n#0 <= n#0 ==> Mul(base#0 - 1, n#0) <= LitInt(0);
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(73,5)
            assume true;
            // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(73,5)
            assume Mul(base#0 - 1, n#0) <= LitInt(0);
            // ----- Hint4 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(73,5)
            // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(81,11)
            assume true;
            assert Mul(base#0 - 1, n#0) <= LitInt(0);
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(81,46)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            x##0_0_2_0 := base#0 - 1;
            assume true;
            // ProcessCallStmt: CheckSubrange
            y##0_0_2_0 := n#0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call Call$$_module.__default.MulSign(x##0_0_2_0, y##0_0_2_0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(81,58)"} true;
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(73,5)
            if (LitInt(0) < base#0 - 1)
            {
            }

            assume true;
            // ----- assert line4 ==> line5 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(73,5)
            assert {:subsumption 0} Mul(base#0 - 1, n#0) <= LitInt(0)
               ==> base#0 - 1 <= LitInt(0) || n#0 <= LitInt(0);
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(73,5)
            if (LitInt(0) < base#0 - 1)
            {
            }

            assume true;
            // ----- Hint5 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(73,5)
            // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(83,11)
            assume true;
            assert 0 < n#0;
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(73,5)
            assume true;
            // ----- assert line5 == line6 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(73,5)
            assert {:subsumption 0} (base#0 - 1 <= LitInt(0) || n#0 <= LitInt(0)) == (base#0 - 1 <= LitInt(0));
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(73,5)
            assume true;
            // ----- Hint6 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(73,5)
            // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(85,11)
            assume true;
            assert LitInt(2) <= base#0;
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(73,5)
            assume true;
            // ----- assert line6 == line7 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(73,5)
            assert {:subsumption 0} (base#0 - 1 <= LitInt(0)) == Lit(false);
            assume false;
        }

        assume Mul(base#0, d#0) + m#0 == n#0 ==> false;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(88,5)
        assume true;
        assert false;
    }
    else
    {
    }
}



procedure CheckWellformed$$_module.__default.MulSign(x#0: int, y#0: int);
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.MulSign(x#0: int, y#0: int);
  // user-defined preconditions
  requires Mul(x#0, y#0) <= LitInt(0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures x#0 <= LitInt(0) || y#0 <= LitInt(0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.MulSign(x#0: int, y#0: int) returns ($_reverifyPost: bool);
  free requires 4 == $FunctionContextHeight;
  // user-defined preconditions
  requires Mul(x#0, y#0) <= LitInt(0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures x#0 <= LitInt(0) || y#0 <= LitInt(0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.MulSign(x#0: int, y#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: MulSign, Impl$$_module.__default.MulSign
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(96,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.Complete(n#0: int, lowDigit#0: int, base#0: int)
   returns (digits#0: Seq Box
       where $Is(digits#0, TSeq(TInt)) && $IsAlloc(digits#0, TSeq(TInt), $Heap));
  free requires 10 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Complete(n#0: int, lowDigit#0: int, base#0: int) returns (digits#0: Seq Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##digits#0: Seq Box;
  var ##lowDigit#0: int;
  var ##base#0: int;
  var ##digits#1: Seq Box;
  var ##base#1: int;

    // AddMethodImpl: Complete, CheckWellformed$$_module.__default.Complete
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(102,6): initial state"} true;
    assume LitInt(2) <= base#0;
    if (lowDigit#0 <= LitInt(0))
    {
    }

    assume lowDigit#0 <= LitInt(0) && 0 < lowDigit#0 + base#0;
    if (*)
    {
        assume LitInt(0) <= lowDigit#0;
        assume LitInt(0) <= n#0;
    }
    else
    {
        assume LitInt(0) <= lowDigit#0 ==> LitInt(0) <= n#0;
    }

    if (*)
    {
        assume lowDigit#0 + base#0 <= LitInt(1);
        assume n#0 <= LitInt(0);
    }
    else
    {
        assume lowDigit#0 + base#0 <= LitInt(1) ==> n#0 <= LitInt(0);
    }

    if (LitInt(0) <= n#0)
    {
    }
    else
    {
    }

    havoc $Heap;
    assume old($Heap) == $Heap;
    havoc digits#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(106,47): post-state"} true;
    ##digits#0 := digits#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##digits#0, TSeq(TInt), $Heap);
    ##lowDigit#0 := lowDigit#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##lowDigit#0, TInt, $Heap);
    ##base#0 := base#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##base#0, TInt, $Heap);
    assume _module.__default.IsSkewNumber#canCall(digits#0, lowDigit#0, base#0);
    assume _module.__default.IsSkewNumber(digits#0, lowDigit#0, base#0);
    ##digits#1 := digits#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##digits#1, TSeq(TInt), $Heap);
    ##base#1 := base#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##base#1, TInt, $Heap);
    assert {:subsumption 0} LitInt(2) <= ##base#1;
    assume LitInt(2) <= ##base#1;
    assume _module.__default.eval#canCall(digits#0, base#0);
    assume _module.__default.eval($LS($LZ), digits#0, base#0) == n#0;
}



procedure Call$$_module.__default.Complete(n#0: int, lowDigit#0: int, base#0: int)
   returns (digits#0: Seq Box
       where $Is(digits#0, TSeq(TInt)) && $IsAlloc(digits#0, TSeq(TInt), $Heap));
  // user-defined preconditions
  requires LitInt(2) <= base#0;
  requires lowDigit#0 <= LitInt(0);
  requires 0 < lowDigit#0 + base#0;
  requires LitInt(0) <= lowDigit#0 ==> LitInt(0) <= n#0;
  requires lowDigit#0 + base#0 <= LitInt(1) ==> n#0 <= LitInt(0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.IsSkewNumber#canCall(digits#0, lowDigit#0, base#0)
     && (_module.__default.IsSkewNumber(digits#0, lowDigit#0, base#0)
       ==> _module.__default.eval#canCall(digits#0, base#0));
  free ensures _module.__default.IsSkewNumber#canCall(digits#0, lowDigit#0, base#0)
     && 
    _module.__default.IsSkewNumber(digits#0, lowDigit#0, base#0)
     && 
    LitInt(2) <= base#0
     && 
    lowDigit#0 <= LitInt(0)
     && 0 < lowDigit#0 + base#0
     && (forall i#0: int :: 
      { $Unbox(Seq#Index(digits#0, i#0)): int } 
      true
         ==> (LitInt(0) <= i#0 && i#0 < Seq#Length(digits#0)
             ==> lowDigit#0 <= $Unbox(Seq#Index(digits#0, i#0)): int)
           && (LitInt(0) <= i#0 && i#0 < Seq#Length(digits#0)
             ==> $Unbox(Seq#Index(digits#0, i#0)): int < lowDigit#0 + base#0));
  ensures _module.__default.eval($LS($LS($LZ)), digits#0, base#0) == n#0;
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.Complete(n#0: int, lowDigit#0: int, base#0: int)
   returns (digits#0: Seq Box
       where $Is(digits#0, TSeq(TInt)) && $IsAlloc(digits#0, TSeq(TInt), $Heap), 
    $_reverifyPost: bool);
  free requires 10 == $FunctionContextHeight;
  // user-defined preconditions
  requires LitInt(2) <= base#0;
  requires lowDigit#0 <= LitInt(0);
  requires 0 < lowDigit#0 + base#0;
  requires LitInt(0) <= lowDigit#0 ==> LitInt(0) <= n#0;
  requires lowDigit#0 + base#0 <= LitInt(1) ==> n#0 <= LitInt(0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.IsSkewNumber#canCall(digits#0, lowDigit#0, base#0)
     && (_module.__default.IsSkewNumber(digits#0, lowDigit#0, base#0)
       ==> _module.__default.eval#canCall(digits#0, base#0));
  ensures _module.__default.IsSkewNumber#canCall(digits#0, lowDigit#0, base#0)
     ==> _module.__default.IsSkewNumber(digits#0, lowDigit#0, base#0)
       || LitInt(2) <= base#0;
  ensures _module.__default.IsSkewNumber#canCall(digits#0, lowDigit#0, base#0)
     ==> _module.__default.IsSkewNumber(digits#0, lowDigit#0, base#0)
       || lowDigit#0 <= LitInt(0);
  ensures _module.__default.IsSkewNumber#canCall(digits#0, lowDigit#0, base#0)
     ==> _module.__default.IsSkewNumber(digits#0, lowDigit#0, base#0)
       || 0 < lowDigit#0 + base#0;
  ensures _module.__default.IsSkewNumber#canCall(digits#0, lowDigit#0, base#0)
     ==> _module.__default.IsSkewNumber(digits#0, lowDigit#0, base#0)
       || (forall i#1: int :: 
        { $Unbox(Seq#Index(digits#0, i#1)): int } 
        true
           ==> (LitInt(0) <= i#1 && i#1 < Seq#Length(digits#0)
               ==> lowDigit#0 <= $Unbox(Seq#Index(digits#0, i#1)): int)
             && (LitInt(0) <= i#1 && i#1 < Seq#Length(digits#0)
               ==> $Unbox(Seq#Index(digits#0, i#1)): int < lowDigit#0 + base#0));
  ensures _module.__default.eval($LS($LS($LZ)), digits#0, base#0) == n#0;
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.Complete(n#0: int, lowDigit#0: int, base#0: int)
   returns (digits#0: Seq Box, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs##1_0: Seq Box
     where $Is($rhs##1_0, TSeq(TInt)) && $IsAlloc($rhs##1_0, TSeq(TInt), $Heap);
  var n##1_0: int;
  var lowDigit##1_0: int;
  var base##1_0: int;
  var $rhs##1_1: Seq Box
     where $Is($rhs##1_1, TSeq(TInt)) && $IsAlloc($rhs##1_1, TSeq(TInt), $Heap);
  var a##1_0: Seq Box;
  var lowDigit##1_1: int;
  var base##1_1: int;
  var $rhs##0: Seq Box
     where $Is($rhs##0, TSeq(TInt)) && $IsAlloc($rhs##0, TSeq(TInt), $Heap);
  var n##0: int;
  var lowDigit##0: int;
  var base##0: int;
  var $rhs##1: Seq Box
     where $Is($rhs##1, TSeq(TInt)) && $IsAlloc($rhs##1, TSeq(TInt), $Heap);
  var a##0: Seq Box;
  var lowDigit##1: int;
  var base##1: int;

    // AddMethodImpl: Complete, Impl$$_module.__default.Complete
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(108,0): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(109,3)
    if (lowDigit#0 <= n#0)
    {
    }

    assume true;
    if (lowDigit#0 <= n#0 && n#0 < lowDigit#0 + base#0)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(110,12)
        assume true;
        assume true;
        digits#0 := Seq#Build(Seq#Empty(): Seq Box, $Box(n#0));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(110,17)"} true;
    }
    else
    {
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(111,10)
        assume true;
        if (0 < n#0)
        {
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(112,23)
            assume true;
            // TrCallStmt: Adding lhs with type seq<int>
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            n##1_0 := n#0 - 1;
            assume true;
            // ProcessCallStmt: CheckSubrange
            lowDigit##1_0 := lowDigit#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            base##1_0 := base#0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0 <= (if LitInt(0) <= n#0 then n#0 else 0 - n#0)
               || (if LitInt(0) <= n##1_0 then n##1_0 else 0 - n##1_0)
                 == (if LitInt(0) <= n#0 then n#0 else 0 - n#0);
            assert (if LitInt(0) <= n##1_0 then n##1_0 else 0 - n##1_0)
               < (if LitInt(0) <= n#0 then n#0 else 0 - n#0);
            // ProcessCallStmt: Make the call
            call $rhs##1_0 := Call$$_module.__default.Complete(n##1_0, lowDigit##1_0, base##1_0);
            // TrCallStmt: After ProcessCallStmt
            digits#0 := $rhs##1_0;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(112,45)"} true;
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(113,18)
            assume true;
            // TrCallStmt: Adding lhs with type seq<int>
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            a##1_0 := digits#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            lowDigit##1_1 := lowDigit#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            base##1_1 := base#0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call $rhs##1_1 := Call$$_module.__default.inc(a##1_0, lowDigit##1_1, base##1_1);
            // TrCallStmt: After ProcessCallStmt
            digits#0 := $rhs##1_1;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(113,41)"} true;
        }
        else
        {
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(115,23)
            assume true;
            // TrCallStmt: Adding lhs with type seq<int>
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            n##0 := n#0 + 1;
            assume true;
            // ProcessCallStmt: CheckSubrange
            lowDigit##0 := lowDigit#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            base##0 := base#0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0 <= (if LitInt(0) <= n#0 then n#0 else 0 - n#0)
               || (if LitInt(0) <= n##0 then n##0 else 0 - n##0)
                 == (if LitInt(0) <= n#0 then n#0 else 0 - n#0);
            assert (if LitInt(0) <= n##0 then n##0 else 0 - n##0)
               < (if LitInt(0) <= n#0 then n#0 else 0 - n#0);
            // ProcessCallStmt: Make the call
            call $rhs##0 := Call$$_module.__default.Complete(n##0, lowDigit##0, base##0);
            // TrCallStmt: After ProcessCallStmt
            digits#0 := $rhs##0;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(115,45)"} true;
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(116,18)
            assume true;
            // TrCallStmt: Adding lhs with type seq<int>
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            a##0 := digits#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            lowDigit##1 := lowDigit#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            base##1 := base#0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call $rhs##1 := Call$$_module.__default.dec(a##0, lowDigit##1, base##1);
            // TrCallStmt: After ProcessCallStmt
            digits#0 := $rhs##1;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(116,41)"} true;
        }
    }
}



procedure CheckWellformed$$_module.__default.inc(a#0: Seq Box where $Is(a#0, TSeq(TInt)) && $IsAlloc(a#0, TSeq(TInt), $Heap), 
    lowDigit#0: int, 
    base#0: int)
   returns (b#0: Seq Box where $Is(b#0, TSeq(TInt)) && $IsAlloc(b#0, TSeq(TInt), $Heap));
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.inc(a#0: Seq Box, lowDigit#0: int, base#0: int) returns (b#0: Seq Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##digits#0: Seq Box;
  var ##lowDigit#0: int;
  var ##base#0: int;
  var ##digits#1: Seq Box;
  var ##base#1: int;
  var ##digits#2: Seq Box;
  var ##lowDigit#1: int;
  var ##base#2: int;
  var ##digits#3: Seq Box;
  var ##base#3: int;
  var ##digits#4: Seq Box;
  var ##base#4: int;

    // AddMethodImpl: inc, CheckWellformed$$_module.__default.inc
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(120,13): initial state"} true;
    ##digits#0 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##digits#0, TSeq(TInt), $Heap);
    ##lowDigit#0 := lowDigit#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##lowDigit#0, TInt, $Heap);
    ##base#0 := base#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##base#0, TInt, $Heap);
    assume _module.__default.IsSkewNumber#canCall(a#0, lowDigit#0, base#0);
    assume _module.__default.IsSkewNumber(a#0, lowDigit#0, base#0);
    if (*)
    {
        ##digits#1 := a#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##digits#1, TSeq(TInt), $Heap);
        ##base#1 := base#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##base#1, TInt, $Heap);
        assert {:subsumption 0} LitInt(2) <= ##base#1;
        assume LitInt(2) <= ##base#1;
        assume _module.__default.eval#canCall(a#0, base#0);
        assume _module.__default.eval($LS($LZ), a#0, base#0) == LitInt(0);
        assume 1 < lowDigit#0 + base#0;
    }
    else
    {
        assume _module.__default.eval($LS($LZ), a#0, base#0) == LitInt(0)
           ==> 1 < lowDigit#0 + base#0;
    }

    havoc $Heap;
    assume old($Heap) == $Heap;
    havoc b#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(123,42): post-state"} true;
    ##digits#2 := b#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##digits#2, TSeq(TInt), $Heap);
    ##lowDigit#1 := lowDigit#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##lowDigit#1, TInt, $Heap);
    ##base#2 := base#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##base#2, TInt, $Heap);
    assume _module.__default.IsSkewNumber#canCall(b#0, lowDigit#0, base#0);
    assume _module.__default.IsSkewNumber(b#0, lowDigit#0, base#0);
    ##digits#3 := b#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##digits#3, TSeq(TInt), $Heap);
    ##base#3 := base#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##base#3, TInt, $Heap);
    assert {:subsumption 0} LitInt(2) <= ##base#3;
    assume LitInt(2) <= ##base#3;
    assume _module.__default.eval#canCall(b#0, base#0);
    ##digits#4 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##digits#4, TSeq(TInt), $Heap);
    ##base#4 := base#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##base#4, TInt, $Heap);
    assert {:subsumption 0} LitInt(2) <= ##base#4;
    assume LitInt(2) <= ##base#4;
    assume _module.__default.eval#canCall(a#0, base#0);
    assume _module.__default.eval($LS($LZ), b#0, base#0)
       == _module.__default.eval($LS($LZ), a#0, base#0) + 1;
}



procedure Call$$_module.__default.inc(a#0: Seq Box where $Is(a#0, TSeq(TInt)) && $IsAlloc(a#0, TSeq(TInt), $Heap), 
    lowDigit#0: int, 
    base#0: int)
   returns (b#0: Seq Box where $Is(b#0, TSeq(TInt)) && $IsAlloc(b#0, TSeq(TInt), $Heap));
  // user-defined preconditions
  requires _module.__default.IsSkewNumber#canCall(a#0, lowDigit#0, base#0)
     ==> _module.__default.IsSkewNumber(a#0, lowDigit#0, base#0) || LitInt(2) <= base#0;
  requires _module.__default.IsSkewNumber#canCall(a#0, lowDigit#0, base#0)
     ==> _module.__default.IsSkewNumber(a#0, lowDigit#0, base#0)
       || lowDigit#0 <= LitInt(0);
  requires _module.__default.IsSkewNumber#canCall(a#0, lowDigit#0, base#0)
     ==> _module.__default.IsSkewNumber(a#0, lowDigit#0, base#0)
       || 0 < lowDigit#0 + base#0;
  requires _module.__default.IsSkewNumber#canCall(a#0, lowDigit#0, base#0)
     ==> _module.__default.IsSkewNumber(a#0, lowDigit#0, base#0)
       || (forall i#0: int :: 
        { $Unbox(Seq#Index(a#0, i#0)): int } 
        true
           ==> (LitInt(0) <= i#0 && i#0 < Seq#Length(a#0)
               ==> lowDigit#0 <= $Unbox(Seq#Index(a#0, i#0)): int)
             && (LitInt(0) <= i#0 && i#0 < Seq#Length(a#0)
               ==> $Unbox(Seq#Index(a#0, i#0)): int < lowDigit#0 + base#0));
  requires _module.__default.eval($LS($LZ), a#0, base#0) == LitInt(0)
     ==> 1 < lowDigit#0 + base#0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.IsSkewNumber#canCall(b#0, lowDigit#0, base#0)
     && (_module.__default.IsSkewNumber(b#0, lowDigit#0, base#0)
       ==> _module.__default.eval#canCall(b#0, base#0)
         && _module.__default.eval#canCall(a#0, base#0));
  free ensures _module.__default.IsSkewNumber#canCall(b#0, lowDigit#0, base#0)
     && 
    _module.__default.IsSkewNumber(b#0, lowDigit#0, base#0)
     && 
    LitInt(2) <= base#0
     && 
    lowDigit#0 <= LitInt(0)
     && 0 < lowDigit#0 + base#0
     && (forall i#1: int :: 
      { $Unbox(Seq#Index(b#0, i#1)): int } 
      true
         ==> (LitInt(0) <= i#1 && i#1 < Seq#Length(b#0)
             ==> lowDigit#0 <= $Unbox(Seq#Index(b#0, i#1)): int)
           && (LitInt(0) <= i#1 && i#1 < Seq#Length(b#0)
             ==> $Unbox(Seq#Index(b#0, i#1)): int < lowDigit#0 + base#0));
  ensures _module.__default.eval($LS($LS($LZ)), b#0, base#0)
     == _module.__default.eval($LS($LS($LZ)), a#0, base#0) + 1;
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.inc(a#0: Seq Box where $Is(a#0, TSeq(TInt)) && $IsAlloc(a#0, TSeq(TInt), $Heap), 
    lowDigit#0: int, 
    base#0: int)
   returns (b#0: Seq Box where $Is(b#0, TSeq(TInt)) && $IsAlloc(b#0, TSeq(TInt), $Heap), 
    $_reverifyPost: bool);
  free requires 8 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.__default.IsSkewNumber#canCall(a#0, lowDigit#0, base#0)
     && 
    _module.__default.IsSkewNumber(a#0, lowDigit#0, base#0)
     && 
    LitInt(2) <= base#0
     && 
    lowDigit#0 <= LitInt(0)
     && 0 < lowDigit#0 + base#0
     && (forall i#2: int :: 
      { $Unbox(Seq#Index(a#0, i#2)): int } 
      true
         ==> (LitInt(0) <= i#2 && i#2 < Seq#Length(a#0)
             ==> lowDigit#0 <= $Unbox(Seq#Index(a#0, i#2)): int)
           && (LitInt(0) <= i#2 && i#2 < Seq#Length(a#0)
             ==> $Unbox(Seq#Index(a#0, i#2)): int < lowDigit#0 + base#0));
  requires _module.__default.eval($LS($LZ), a#0, base#0) == LitInt(0)
     ==> 1 < lowDigit#0 + base#0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.IsSkewNumber#canCall(b#0, lowDigit#0, base#0)
     && (_module.__default.IsSkewNumber(b#0, lowDigit#0, base#0)
       ==> _module.__default.eval#canCall(b#0, base#0)
         && _module.__default.eval#canCall(a#0, base#0));
  ensures _module.__default.IsSkewNumber#canCall(b#0, lowDigit#0, base#0)
     ==> _module.__default.IsSkewNumber(b#0, lowDigit#0, base#0) || LitInt(2) <= base#0;
  ensures _module.__default.IsSkewNumber#canCall(b#0, lowDigit#0, base#0)
     ==> _module.__default.IsSkewNumber(b#0, lowDigit#0, base#0)
       || lowDigit#0 <= LitInt(0);
  ensures _module.__default.IsSkewNumber#canCall(b#0, lowDigit#0, base#0)
     ==> _module.__default.IsSkewNumber(b#0, lowDigit#0, base#0)
       || 0 < lowDigit#0 + base#0;
  ensures _module.__default.IsSkewNumber#canCall(b#0, lowDigit#0, base#0)
     ==> _module.__default.IsSkewNumber(b#0, lowDigit#0, base#0)
       || (forall i#3: int :: 
        { $Unbox(Seq#Index(b#0, i#3)): int } 
        true
           ==> (LitInt(0) <= i#3 && i#3 < Seq#Length(b#0)
               ==> lowDigit#0 <= $Unbox(Seq#Index(b#0, i#3)): int)
             && (LitInt(0) <= i#3 && i#3 < Seq#Length(b#0)
               ==> $Unbox(Seq#Index(b#0, i#3)): int < lowDigit#0 + base#0));
  ensures _module.__default.eval($LS($LS($LZ)), b#0, base#0)
     == _module.__default.eval($LS($LS($LZ)), a#0, base#0) + 1;
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.inc(a#0: Seq Box, lowDigit#0: int, base#0: int)
   returns (b#0: Seq Box, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $Heap_at_0: Heap;
  var a'#0: Seq Box where $Is(a'#0, TSeq(TInt)) && $IsAlloc(a'#0, TSeq(TInt), $Heap);
  var ##digits#5: Seq Box;
  var ##base#5: int;
  var ##digits#6: Seq Box;
  var ##base#6: int;
  var b'#0: Seq Box where $Is(b'#0, TSeq(TInt)) && $IsAlloc(b'#0, TSeq(TInt), $Heap);
  var $rhs##0: Seq Box
     where $Is($rhs##0, TSeq(TInt)) && $IsAlloc($rhs##0, TSeq(TInt), $Heap);
  var a##0: Seq Box;
  var lowDigit##0: int;
  var base##0: int;
  var ##digits#7: Seq Box;
  var ##base#7: int;
  var ##digits#8: Seq Box;
  var ##base#8: int;
  var ##digits#9: Seq Box;
  var ##lowDigit#2: int;
  var ##base#9: int;
  var ##digits#2_0_0: Seq Box;
  var ##base#2_0_0: int;
  var ##digits#2_0_1: Seq Box;
  var ##base#2_0_1: int;
  var ##digits#2_1_0: Seq Box;
  var ##base#2_1_0: int;
  var ##digits#2_1_1: Seq Box;
  var ##base#2_1_1: int;
  var ##digits#2_2_0: Seq Box;
  var ##base#2_2_0: int;
  var ##digits#2_2_1: Seq Box;
  var ##base#2_2_1: int;
  var ##digits#2_3_0: Seq Box;
  var ##base#2_3_0: int;
  var ##digits#2_3_1: Seq Box;
  var ##base#2_3_1: int;
  var ##digits#2_3_2: Seq Box;
  var ##base#2_3_2: int;
  var ##digits#2_3_3: Seq Box;
  var ##base#2_3_3: int;
  var ##digits#2_4_0: Seq Box;
  var ##base#2_4_0: int;
  var ##digits#2_4_1: Seq Box;
  var ##base#2_4_1: int;
  var ##digits#2_5_0: Seq Box;
  var ##base#2_5_0: int;
  var ##digits#2_5_1: Seq Box;
  var ##base#2_5_1: int;
  var ##digits#2_6_0: Seq Box;
  var ##base#2_6_0: int;
  var ##digits#2_6_1: Seq Box;
  var ##base#2_6_1: int;
  var ##digits#2_0: Seq Box;
  var ##base#2_0: int;

    // AddMethodImpl: inc, Impl$$_module.__default.inc
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(124,0): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(125,3)
    assume true;
    if (Seq#Equal(a#0, Seq#Empty(): Seq Box))
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(126,7)
        assume true;
        assume true;
        b#0 := Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(1))));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(126,12)"} true;
    }
    else
    {
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(127,10)
        assert 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
        assume true;
        if ($Unbox(Seq#Index(a#0, LitInt(0))): int + 1 < lowDigit#0 + base#0)
        {
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(128,7)
            assume true;
            assert 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
            assert 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
            assume true;
            b#0 := Seq#Update(a#0, LitInt(0), $Box($Unbox(Seq#Index(a#0, LitInt(0))): int + 1));
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(128,25)"} true;
        }
        else
        {
            // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(131,5)
            assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
            assume true;
            if (*)
            {
                // ----- assert statement proof ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(131,5)
                assert $Unbox(Seq#Index(a#0, LitInt(0))): int + 1 == lowDigit#0 + base#0;
                assume false;
            }

            $Heap_at_0 := $Heap;
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(132,12)
            assume true;
            assert 0 <= LitInt(1) && LitInt(1) <= Seq#Length(a#0);
            assume true;
            a'#0 := Seq#Drop(a#0, LitInt(1));
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(132,20)"} true;
            // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(133,5)
            ##digits#5 := a#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##digits#5, TSeq(TInt), $Heap);
            ##base#5 := base#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##base#5, TInt, $Heap);
            assert {:subsumption 0} LitInt(2) <= ##base#5;
            assume _module.__default.eval#canCall(a#0, base#0);
            assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
            ##digits#6 := a'#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##digits#6, TSeq(TInt), $Heap);
            ##base#6 := base#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##base#6, TInt, $Heap);
            assert {:subsumption 0} LitInt(2) <= ##base#6;
            assume _module.__default.eval#canCall(a'#0, base#0);
            assume _module.__default.eval#canCall(a#0, base#0)
               && _module.__default.eval#canCall(a'#0, base#0);
            assert {:subsumption 0} _module.__default.eval($LS($LS($LZ)), a#0, base#0)
               == $Unbox(Seq#Index(a#0, LitInt(0))): int
                 + Mul(base#0, _module.__default.eval($LS($LS($LZ)), a'#0, base#0));
            assume _module.__default.eval($LS($LZ), a#0, base#0)
               == $Unbox(Seq#Index(a#0, LitInt(0))): int
                 + Mul(base#0, _module.__default.eval($LS($LZ), a'#0, base#0));
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(135,18)
            assume true;
            // TrCallStmt: Adding lhs with type seq<int>
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            a##0 := a'#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            lowDigit##0 := lowDigit#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            base##0 := base#0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0 <= lowDigit#0 || Seq#Rank(a##0) < Seq#Rank(a#0) || lowDigit##0 == lowDigit#0;
            assert 0 <= base#0
               || Seq#Rank(a##0) < Seq#Rank(a#0)
               || lowDigit##0 < lowDigit#0
               || base##0 == base#0;
            assert Seq#Rank(a##0) < Seq#Rank(a#0)
               || (Seq#Rank(a##0) == Seq#Rank(a#0)
                 && (lowDigit##0 < lowDigit#0 || (lowDigit##0 == lowDigit#0 && base##0 < base#0)));
            // ProcessCallStmt: Make the call
            call $rhs##0 := Call$$_module.__default.inc(a##0, lowDigit##0, base##0);
            // TrCallStmt: After ProcessCallStmt
            b'#0 := $rhs##0;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(135,37)"} true;
            // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(136,5)
            ##digits#7 := b'#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##digits#7, TSeq(TInt), $Heap);
            ##base#7 := base#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##base#7, TInt, $Heap);
            assert {:subsumption 0} LitInt(2) <= ##base#7;
            assume _module.__default.eval#canCall(b'#0, base#0);
            ##digits#8 := a'#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##digits#8, TSeq(TInt), $Heap);
            ##base#8 := base#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##base#8, TInt, $Heap);
            assert {:subsumption 0} LitInt(2) <= ##base#8;
            assume _module.__default.eval#canCall(a'#0, base#0);
            assume _module.__default.eval#canCall(b'#0, base#0)
               && _module.__default.eval#canCall(a'#0, base#0);
            assert {:subsumption 0} _module.__default.eval($LS($LS($LZ)), b'#0, base#0)
               == _module.__default.eval($LS($LS($LZ)), a'#0, base#0) + 1;
            assume _module.__default.eval($LS($LZ), b'#0, base#0)
               == _module.__default.eval($LS($LZ), a'#0, base#0) + 1;
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(138,7)
            assume true;
            assume true;
            b#0 := Seq#Append(Seq#Build(Seq#Empty(): Seq Box, $Box(lowDigit#0)), b'#0);
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(138,24)"} true;
            // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(139,5)
            ##digits#9 := b#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##digits#9, TSeq(TInt), $Heap);
            ##lowDigit#2 := lowDigit#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##lowDigit#2, TInt, $Heap);
            ##base#9 := base#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##base#9, TInt, $Heap);
            assume _module.__default.IsSkewNumber#canCall(b#0, lowDigit#0, base#0);
            assume _module.__default.IsSkewNumber#canCall(b#0, lowDigit#0, base#0);
            assert {:subsumption 0} _module.__default.IsSkewNumber#canCall(b#0, lowDigit#0, base#0)
               ==> _module.__default.IsSkewNumber(b#0, lowDigit#0, base#0) || LitInt(2) <= base#0;
            assert {:subsumption 0} _module.__default.IsSkewNumber#canCall(b#0, lowDigit#0, base#0)
               ==> _module.__default.IsSkewNumber(b#0, lowDigit#0, base#0)
                 || lowDigit#0 <= LitInt(0);
            assert {:subsumption 0} _module.__default.IsSkewNumber#canCall(b#0, lowDigit#0, base#0)
               ==> _module.__default.IsSkewNumber(b#0, lowDigit#0, base#0)
                 || 0 < lowDigit#0 + base#0;
            assert {:subsumption 0} _module.__default.IsSkewNumber#canCall(b#0, lowDigit#0, base#0)
               ==> _module.__default.IsSkewNumber(b#0, lowDigit#0, base#0)
                 || (forall i#4: int :: 
                  { $Unbox(Seq#Index(b#0, i#4)): int } 
                  true
                     ==> (LitInt(0) <= i#4 && i#4 < Seq#Length(b#0)
                         ==> lowDigit#0 <= $Unbox(Seq#Index(b#0, i#4)): int)
                       && (LitInt(0) <= i#4 && i#4 < Seq#Length(b#0)
                         ==> $Unbox(Seq#Index(b#0, i#4)): int < lowDigit#0 + base#0));
            assume _module.__default.IsSkewNumber(b#0, lowDigit#0, base#0);
            // ----- calc statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(141,5)
            // Assume Fuel Constant
            if (*)
            {
                // ----- assert wf[initial] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(141,5)
                ##digits#2_0 := b#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##digits#2_0, TSeq(TInt), $Heap);
                ##base#2_0 := base#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##base#2_0, TInt, $Heap);
                assert {:subsumption 0} LitInt(2) <= ##base#2_0;
                assume _module.__default.eval#canCall(b#0, base#0);
                assume _module.__default.eval#canCall(b#0, base#0);
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(141,5)
                ##digits#2_6_0 := b#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##digits#2_6_0, TSeq(TInt), $Heap);
                ##base#2_6_0 := base#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##base#2_6_0, TInt, $Heap);
                assume {:subsumption 0} LitInt(2) <= ##base#2_6_0;
                assume _module.__default.eval#canCall(b#0, base#0);
                assume _module.__default.eval#canCall(b#0, base#0);
                // ----- Hint0 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(141,5)
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(141,5)
                assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(b#0);
                assert {:subsumption 0} 0 <= LitInt(1) && LitInt(1) <= Seq#Length(b#0);
                ##digits#2_6_1 := Seq#Drop(b#0, LitInt(1));
                // assume allocatedness for argument to function
                assume $IsAlloc(##digits#2_6_1, TSeq(TInt), $Heap);
                ##base#2_6_1 := base#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##base#2_6_1, TInt, $Heap);
                assert {:subsumption 0} LitInt(2) <= ##base#2_6_1;
                assume _module.__default.eval#canCall(Seq#Drop(b#0, LitInt(1)), base#0);
                assume _module.__default.eval#canCall(Seq#Drop(b#0, LitInt(1)), base#0);
                // ----- assert line0 == line1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(141,5)
                assert {:subsumption 0} _module.__default.eval($LS($LS($LZ)), b#0, base#0)
                   == $Unbox(Seq#Index(b#0, LitInt(0))): int
                     + Mul(base#0, _module.__default.eval($LS($LS($LZ)), Seq#Drop(b#0, LitInt(1)), base#0));
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(141,5)
                assume {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(b#0);
                assume {:subsumption 0} 0 <= LitInt(1) && LitInt(1) <= Seq#Length(b#0);
                ##digits#2_5_0 := Seq#Drop(b#0, LitInt(1));
                // assume allocatedness for argument to function
                assume $IsAlloc(##digits#2_5_0, TSeq(TInt), $Heap);
                ##base#2_5_0 := base#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##base#2_5_0, TInt, $Heap);
                assume {:subsumption 0} LitInt(2) <= ##base#2_5_0;
                assume _module.__default.eval#canCall(Seq#Drop(b#0, LitInt(1)), base#0);
                assume _module.__default.eval#canCall(Seq#Drop(b#0, LitInt(1)), base#0);
                // ----- Hint1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(141,5)
                // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(145,11)
                assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(b#0);
                assume true;
                assert $Unbox(Seq#Index(b#0, LitInt(0))): int == lowDigit#0;
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(141,5)
                assert {:subsumption 0} 0 <= LitInt(1) && LitInt(1) <= Seq#Length(b#0);
                ##digits#2_5_1 := Seq#Drop(b#0, LitInt(1));
                // assume allocatedness for argument to function
                assume $IsAlloc(##digits#2_5_1, TSeq(TInt), $Heap);
                ##base#2_5_1 := base#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##base#2_5_1, TInt, $Heap);
                assert {:subsumption 0} LitInt(2) <= ##base#2_5_1;
                assume _module.__default.eval#canCall(Seq#Drop(b#0, LitInt(1)), base#0);
                assume _module.__default.eval#canCall(Seq#Drop(b#0, LitInt(1)), base#0);
                // ----- assert line1 == line2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(141,5)
                assert {:subsumption 0} $Unbox(Seq#Index(b#0, LitInt(0))): int
                     + Mul(base#0, _module.__default.eval($LS($LS($LZ)), Seq#Drop(b#0, LitInt(1)), base#0))
                   == lowDigit#0
                     + Mul(base#0, _module.__default.eval($LS($LS($LZ)), Seq#Drop(b#0, LitInt(1)), base#0));
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(141,5)
                assume {:subsumption 0} 0 <= LitInt(1) && LitInt(1) <= Seq#Length(b#0);
                ##digits#2_4_0 := Seq#Drop(b#0, LitInt(1));
                // assume allocatedness for argument to function
                assume $IsAlloc(##digits#2_4_0, TSeq(TInt), $Heap);
                ##base#2_4_0 := base#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##base#2_4_0, TInt, $Heap);
                assume {:subsumption 0} LitInt(2) <= ##base#2_4_0;
                assume _module.__default.eval#canCall(Seq#Drop(b#0, LitInt(1)), base#0);
                assume _module.__default.eval#canCall(Seq#Drop(b#0, LitInt(1)), base#0);
                // ----- Hint2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(141,5)
                // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(147,11)
                assert {:subsumption 0} 0 <= LitInt(1) && LitInt(1) <= Seq#Length(b#0);
                assume true;
                assert Seq#Equal(Seq#Drop(b#0, LitInt(1)), b'#0);
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(141,5)
                ##digits#2_4_1 := b'#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##digits#2_4_1, TSeq(TInt), $Heap);
                ##base#2_4_1 := base#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##base#2_4_1, TInt, $Heap);
                assert {:subsumption 0} LitInt(2) <= ##base#2_4_1;
                assume _module.__default.eval#canCall(b'#0, base#0);
                assume _module.__default.eval#canCall(b'#0, base#0);
                // ----- assert line2 == line3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(141,5)
                assert {:subsumption 0} lowDigit#0
                     + Mul(base#0, _module.__default.eval($LS($LS($LZ)), Seq#Drop(b#0, LitInt(1)), base#0))
                   == lowDigit#0 + Mul(base#0, _module.__default.eval($LS($LS($LZ)), b'#0, base#0));
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(141,5)
                ##digits#2_3_0 := b'#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##digits#2_3_0, TSeq(TInt), $Heap);
                ##base#2_3_0 := base#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##base#2_3_0, TInt, $Heap);
                assume {:subsumption 0} LitInt(2) <= ##base#2_3_0;
                assume _module.__default.eval#canCall(b'#0, base#0);
                assume _module.__default.eval#canCall(b'#0, base#0);
                // ----- Hint3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(141,5)
                // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(149,11)
                ##digits#2_3_1 := b'#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##digits#2_3_1, TSeq(TInt), $Heap);
                ##base#2_3_1 := base#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##base#2_3_1, TInt, $Heap);
                assert {:subsumption 0} LitInt(2) <= ##base#2_3_1;
                assume _module.__default.eval#canCall(b'#0, base#0);
                ##digits#2_3_2 := a'#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##digits#2_3_2, TSeq(TInt), $Heap);
                ##base#2_3_2 := base#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##base#2_3_2, TInt, $Heap);
                assert {:subsumption 0} LitInt(2) <= ##base#2_3_2;
                assume _module.__default.eval#canCall(a'#0, base#0);
                assume _module.__default.eval#canCall(b'#0, base#0)
                   && _module.__default.eval#canCall(a'#0, base#0);
                assert {:subsumption 0} _module.__default.eval($LS($LS($LZ)), b'#0, base#0)
                   == _module.__default.eval($LS($LS($LZ)), a'#0, base#0) + 1;
                assume _module.__default.eval($LS($LZ), b'#0, base#0)
                   == _module.__default.eval($LS($LZ), a'#0, base#0) + 1;
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(141,5)
                ##digits#2_3_3 := a'#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##digits#2_3_3, TSeq(TInt), $Heap);
                ##base#2_3_3 := base#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##base#2_3_3, TInt, $Heap);
                assert {:subsumption 0} LitInt(2) <= ##base#2_3_3;
                assume _module.__default.eval#canCall(a'#0, base#0);
                assume _module.__default.eval#canCall(a'#0, base#0);
                // ----- assert line3 == line4 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(141,5)
                assert {:subsumption 0} lowDigit#0 + Mul(base#0, _module.__default.eval($LS($LS($LZ)), b'#0, base#0))
                   == lowDigit#0
                     + Mul(base#0, _module.__default.eval($LS($LS($LZ)), a'#0, base#0) + 1);
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(141,5)
                ##digits#2_2_0 := a'#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##digits#2_2_0, TSeq(TInt), $Heap);
                ##base#2_2_0 := base#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##base#2_2_0, TInt, $Heap);
                assume {:subsumption 0} LitInt(2) <= ##base#2_2_0;
                assume _module.__default.eval#canCall(a'#0, base#0);
                assume _module.__default.eval#canCall(a'#0, base#0);
                // ----- Hint4 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(141,5)
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(141,5)
                ##digits#2_2_1 := a'#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##digits#2_2_1, TSeq(TInt), $Heap);
                ##base#2_2_1 := base#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##base#2_2_1, TInt, $Heap);
                assert {:subsumption 0} LitInt(2) <= ##base#2_2_1;
                assume _module.__default.eval#canCall(a'#0, base#0);
                assume _module.__default.eval#canCall(a'#0, base#0);
                // ----- assert line4 == line5 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(141,5)
                assert {:subsumption 0} lowDigit#0
                     + Mul(base#0, _module.__default.eval($LS($LS($LZ)), a'#0, base#0) + 1)
                   == lowDigit#0
                     + Mul(base#0, _module.__default.eval($LS($LS($LZ)), a'#0, base#0))
                     + base#0;
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(141,5)
                ##digits#2_1_0 := a'#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##digits#2_1_0, TSeq(TInt), $Heap);
                ##base#2_1_0 := base#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##base#2_1_0, TInt, $Heap);
                assume {:subsumption 0} LitInt(2) <= ##base#2_1_0;
                assume _module.__default.eval#canCall(a'#0, base#0);
                assume _module.__default.eval#canCall(a'#0, base#0);
                // ----- Hint5 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(141,5)
                // ----- reveal statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(152,11)
                assume $Unbox(Seq#Index(a#0, LitInt(0))): int + 1 == lowDigit#0 + base#0;
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(141,5)
                assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
                ##digits#2_1_1 := a'#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##digits#2_1_1, TSeq(TInt), $Heap);
                ##base#2_1_1 := base#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##base#2_1_1, TInt, $Heap);
                assert {:subsumption 0} LitInt(2) <= ##base#2_1_1;
                assume _module.__default.eval#canCall(a'#0, base#0);
                assume _module.__default.eval#canCall(a'#0, base#0);
                // ----- assert line5 == line6 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(141,5)
                assert {:subsumption 0} lowDigit#0
                     + Mul(base#0, _module.__default.eval($LS($LS($LZ)), a'#0, base#0))
                     + base#0
                   == $Unbox(Seq#Index(a#0, LitInt(0))): int
                     + Mul(base#0, _module.__default.eval($LS($LS($LZ)), a'#0, base#0))
                     + 1;
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(141,5)
                assume {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
                ##digits#2_0_0 := a'#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##digits#2_0_0, TSeq(TInt), $Heap);
                ##base#2_0_0 := base#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##base#2_0_0, TInt, $Heap);
                assume {:subsumption 0} LitInt(2) <= ##base#2_0_0;
                assume _module.__default.eval#canCall(a'#0, base#0);
                assume _module.__default.eval#canCall(a'#0, base#0);
                // ----- Hint6 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(141,5)
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(141,5)
                ##digits#2_0_1 := a#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##digits#2_0_1, TSeq(TInt), $Heap);
                ##base#2_0_1 := base#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##base#2_0_1, TInt, $Heap);
                assert {:subsumption 0} LitInt(2) <= ##base#2_0_1;
                assume _module.__default.eval#canCall(a#0, base#0);
                assume _module.__default.eval#canCall(a#0, base#0);
                // ----- assert line6 == line7 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(141,5)
                assert {:subsumption 0} $Unbox(Seq#Index(a#0, LitInt(0))): int
                     + Mul(base#0, _module.__default.eval($LS($LS($LZ)), a'#0, base#0))
                     + 1
                   == _module.__default.eval($LS($LS($LZ)), a#0, base#0) + 1;
                assume false;
            }

            assume _module.__default.eval($LS($LZ), b#0, base#0)
               == _module.__default.eval($LS($LZ), a#0, base#0) + 1;
        }
    }
}



procedure CheckWellformed$$_module.__default.dec(a#0: Seq Box where $Is(a#0, TSeq(TInt)) && $IsAlloc(a#0, TSeq(TInt), $Heap), 
    lowDigit#0: int, 
    base#0: int)
   returns (b#0: Seq Box where $Is(b#0, TSeq(TInt)) && $IsAlloc(b#0, TSeq(TInt), $Heap));
  free requires 9 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.dec(a#0: Seq Box, lowDigit#0: int, base#0: int) returns (b#0: Seq Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##digits#0: Seq Box;
  var ##lowDigit#0: int;
  var ##base#0: int;
  var ##digits#1: Seq Box;
  var ##base#1: int;
  var ##digits#2: Seq Box;
  var ##lowDigit#1: int;
  var ##base#2: int;
  var ##digits#3: Seq Box;
  var ##base#3: int;
  var ##digits#4: Seq Box;
  var ##base#4: int;

    // AddMethodImpl: dec, CheckWellformed$$_module.__default.dec
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(160,13): initial state"} true;
    ##digits#0 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##digits#0, TSeq(TInt), $Heap);
    ##lowDigit#0 := lowDigit#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##lowDigit#0, TInt, $Heap);
    ##base#0 := base#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##base#0, TInt, $Heap);
    assume _module.__default.IsSkewNumber#canCall(a#0, lowDigit#0, base#0);
    assume _module.__default.IsSkewNumber(a#0, lowDigit#0, base#0);
    if (*)
    {
        ##digits#1 := a#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##digits#1, TSeq(TInt), $Heap);
        ##base#1 := base#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##base#1, TInt, $Heap);
        assert {:subsumption 0} LitInt(2) <= ##base#1;
        assume LitInt(2) <= ##base#1;
        assume _module.__default.eval#canCall(a#0, base#0);
        assume _module.__default.eval($LS($LZ), a#0, base#0) == LitInt(0);
        assume lowDigit#0 < 0;
    }
    else
    {
        assume _module.__default.eval($LS($LZ), a#0, base#0) == LitInt(0) ==> lowDigit#0 < 0;
    }

    havoc $Heap;
    assume old($Heap) == $Heap;
    havoc b#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(163,42): post-state"} true;
    ##digits#2 := b#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##digits#2, TSeq(TInt), $Heap);
    ##lowDigit#1 := lowDigit#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##lowDigit#1, TInt, $Heap);
    ##base#2 := base#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##base#2, TInt, $Heap);
    assume _module.__default.IsSkewNumber#canCall(b#0, lowDigit#0, base#0);
    assume _module.__default.IsSkewNumber(b#0, lowDigit#0, base#0);
    ##digits#3 := b#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##digits#3, TSeq(TInt), $Heap);
    ##base#3 := base#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##base#3, TInt, $Heap);
    assert {:subsumption 0} LitInt(2) <= ##base#3;
    assume LitInt(2) <= ##base#3;
    assume _module.__default.eval#canCall(b#0, base#0);
    ##digits#4 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##digits#4, TSeq(TInt), $Heap);
    ##base#4 := base#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##base#4, TInt, $Heap);
    assert {:subsumption 0} LitInt(2) <= ##base#4;
    assume LitInt(2) <= ##base#4;
    assume _module.__default.eval#canCall(a#0, base#0);
    assume _module.__default.eval($LS($LZ), b#0, base#0)
       == _module.__default.eval($LS($LZ), a#0, base#0) - 1;
}



procedure Call$$_module.__default.dec(a#0: Seq Box where $Is(a#0, TSeq(TInt)) && $IsAlloc(a#0, TSeq(TInt), $Heap), 
    lowDigit#0: int, 
    base#0: int)
   returns (b#0: Seq Box where $Is(b#0, TSeq(TInt)) && $IsAlloc(b#0, TSeq(TInt), $Heap));
  // user-defined preconditions
  requires _module.__default.IsSkewNumber#canCall(a#0, lowDigit#0, base#0)
     ==> _module.__default.IsSkewNumber(a#0, lowDigit#0, base#0) || LitInt(2) <= base#0;
  requires _module.__default.IsSkewNumber#canCall(a#0, lowDigit#0, base#0)
     ==> _module.__default.IsSkewNumber(a#0, lowDigit#0, base#0)
       || lowDigit#0 <= LitInt(0);
  requires _module.__default.IsSkewNumber#canCall(a#0, lowDigit#0, base#0)
     ==> _module.__default.IsSkewNumber(a#0, lowDigit#0, base#0)
       || 0 < lowDigit#0 + base#0;
  requires _module.__default.IsSkewNumber#canCall(a#0, lowDigit#0, base#0)
     ==> _module.__default.IsSkewNumber(a#0, lowDigit#0, base#0)
       || (forall i#0: int :: 
        { $Unbox(Seq#Index(a#0, i#0)): int } 
        true
           ==> (LitInt(0) <= i#0 && i#0 < Seq#Length(a#0)
               ==> lowDigit#0 <= $Unbox(Seq#Index(a#0, i#0)): int)
             && (LitInt(0) <= i#0 && i#0 < Seq#Length(a#0)
               ==> $Unbox(Seq#Index(a#0, i#0)): int < lowDigit#0 + base#0));
  requires _module.__default.eval($LS($LZ), a#0, base#0) == LitInt(0) ==> lowDigit#0 < 0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.IsSkewNumber#canCall(b#0, lowDigit#0, base#0)
     && (_module.__default.IsSkewNumber(b#0, lowDigit#0, base#0)
       ==> _module.__default.eval#canCall(b#0, base#0)
         && _module.__default.eval#canCall(a#0, base#0));
  free ensures _module.__default.IsSkewNumber#canCall(b#0, lowDigit#0, base#0)
     && 
    _module.__default.IsSkewNumber(b#0, lowDigit#0, base#0)
     && 
    LitInt(2) <= base#0
     && 
    lowDigit#0 <= LitInt(0)
     && 0 < lowDigit#0 + base#0
     && (forall i#1: int :: 
      { $Unbox(Seq#Index(b#0, i#1)): int } 
      true
         ==> (LitInt(0) <= i#1 && i#1 < Seq#Length(b#0)
             ==> lowDigit#0 <= $Unbox(Seq#Index(b#0, i#1)): int)
           && (LitInt(0) <= i#1 && i#1 < Seq#Length(b#0)
             ==> $Unbox(Seq#Index(b#0, i#1)): int < lowDigit#0 + base#0));
  ensures _module.__default.eval($LS($LS($LZ)), b#0, base#0)
     == _module.__default.eval($LS($LS($LZ)), a#0, base#0) - 1;
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.dec(a#0: Seq Box where $Is(a#0, TSeq(TInt)) && $IsAlloc(a#0, TSeq(TInt), $Heap), 
    lowDigit#0: int, 
    base#0: int)
   returns (b#0: Seq Box where $Is(b#0, TSeq(TInt)) && $IsAlloc(b#0, TSeq(TInt), $Heap), 
    $_reverifyPost: bool);
  free requires 9 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.__default.IsSkewNumber#canCall(a#0, lowDigit#0, base#0)
     && 
    _module.__default.IsSkewNumber(a#0, lowDigit#0, base#0)
     && 
    LitInt(2) <= base#0
     && 
    lowDigit#0 <= LitInt(0)
     && 0 < lowDigit#0 + base#0
     && (forall i#2: int :: 
      { $Unbox(Seq#Index(a#0, i#2)): int } 
      true
         ==> (LitInt(0) <= i#2 && i#2 < Seq#Length(a#0)
             ==> lowDigit#0 <= $Unbox(Seq#Index(a#0, i#2)): int)
           && (LitInt(0) <= i#2 && i#2 < Seq#Length(a#0)
             ==> $Unbox(Seq#Index(a#0, i#2)): int < lowDigit#0 + base#0));
  requires _module.__default.eval($LS($LZ), a#0, base#0) == LitInt(0) ==> lowDigit#0 < 0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.IsSkewNumber#canCall(b#0, lowDigit#0, base#0)
     && (_module.__default.IsSkewNumber(b#0, lowDigit#0, base#0)
       ==> _module.__default.eval#canCall(b#0, base#0)
         && _module.__default.eval#canCall(a#0, base#0));
  ensures _module.__default.IsSkewNumber#canCall(b#0, lowDigit#0, base#0)
     ==> _module.__default.IsSkewNumber(b#0, lowDigit#0, base#0) || LitInt(2) <= base#0;
  ensures _module.__default.IsSkewNumber#canCall(b#0, lowDigit#0, base#0)
     ==> _module.__default.IsSkewNumber(b#0, lowDigit#0, base#0)
       || lowDigit#0 <= LitInt(0);
  ensures _module.__default.IsSkewNumber#canCall(b#0, lowDigit#0, base#0)
     ==> _module.__default.IsSkewNumber(b#0, lowDigit#0, base#0)
       || 0 < lowDigit#0 + base#0;
  ensures _module.__default.IsSkewNumber#canCall(b#0, lowDigit#0, base#0)
     ==> _module.__default.IsSkewNumber(b#0, lowDigit#0, base#0)
       || (forall i#3: int :: 
        { $Unbox(Seq#Index(b#0, i#3)): int } 
        true
           ==> (LitInt(0) <= i#3 && i#3 < Seq#Length(b#0)
               ==> lowDigit#0 <= $Unbox(Seq#Index(b#0, i#3)): int)
             && (LitInt(0) <= i#3 && i#3 < Seq#Length(b#0)
               ==> $Unbox(Seq#Index(b#0, i#3)): int < lowDigit#0 + base#0));
  ensures _module.__default.eval($LS($LS($LZ)), b#0, base#0)
     == _module.__default.eval($LS($LS($LZ)), a#0, base#0) - 1;
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.dec(a#0: Seq Box, lowDigit#0: int, base#0: int)
   returns (b#0: Seq Box, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs##0: Seq Box
     where $Is($rhs##0, TSeq(TInt)) && $IsAlloc($rhs##0, TSeq(TInt), $Heap);
  var a##0: Seq Box;
  var lowDigit##0: int;
  var base##0: int;

    // AddMethodImpl: dec, Impl$$_module.__default.dec
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(164,0): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(165,3)
    assume true;
    if (Seq#Equal(a#0, Seq#Empty(): Seq Box))
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(166,7)
        assume true;
        assume true;
        b#0 := Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(-1))));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(166,13)"} true;
    }
    else
    {
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(167,10)
        assert 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
        assume true;
        if (lowDigit#0 <= $Unbox(Seq#Index(a#0, LitInt(0))): int - 1)
        {
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(168,7)
            assume true;
            assert 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
            assert 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
            assume true;
            b#0 := Seq#Update(a#0, LitInt(0), $Box($Unbox(Seq#Index(a#0, LitInt(0))): int - 1));
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(168,25)"} true;
        }
        else
        {
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(170,13)
            assume true;
            // TrCallStmt: Adding lhs with type seq<int>
            // TrCallStmt: Before ProcessCallStmt
            assert 0 <= LitInt(1) && LitInt(1) <= Seq#Length(a#0);
            assume true;
            // ProcessCallStmt: CheckSubrange
            a##0 := Seq#Drop(a#0, LitInt(1));
            assume true;
            // ProcessCallStmt: CheckSubrange
            lowDigit##0 := lowDigit#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            base##0 := base#0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0 <= lowDigit#0 || Seq#Rank(a##0) < Seq#Rank(a#0) || lowDigit##0 == lowDigit#0;
            assert 0 <= base#0
               || Seq#Rank(a##0) < Seq#Rank(a#0)
               || lowDigit##0 < lowDigit#0
               || base##0 == base#0;
            assert Seq#Rank(a##0) < Seq#Rank(a#0)
               || (Seq#Rank(a##0) == Seq#Rank(a#0)
                 && (lowDigit##0 < lowDigit#0 || (lowDigit##0 == lowDigit#0 && base##0 < base#0)));
            // ProcessCallStmt: Make the call
            call $rhs##0 := Call$$_module.__default.dec(a##0, lowDigit##0, base##0);
            // TrCallStmt: After ProcessCallStmt
            b#0 := $rhs##0;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(170,36)"} true;
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(171,7)
            assume true;
            assume true;
            b#0 := Seq#Append(Seq#Build(Seq#Empty(): Seq Box, $Box(lowDigit#0 + base#0 - 1)), b#0);
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(171,34)"} true;
        }
    }
}



// function declaration for _module._default.trim
function _module.__default.trim($ly: LayerType, digits#0: Seq Box) : Seq Box;

function _module.__default.trim#canCall(digits#0: Seq Box) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, digits#0: Seq Box :: 
  { _module.__default.trim($LS($ly), digits#0) } 
  _module.__default.trim($LS($ly), digits#0)
     == _module.__default.trim($ly, digits#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, digits#0: Seq Box :: 
  { _module.__default.trim(AsFuelBottom($ly), digits#0) } 
  _module.__default.trim($ly, digits#0) == _module.__default.trim($LZ, digits#0));

// consequence axiom for _module.__default.trim
axiom 11 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, digits#0: Seq Box :: 
    { _module.__default.trim($ly, digits#0) } 
    _module.__default.trim#canCall(digits#0)
         || (11 != $FunctionContextHeight && $Is(digits#0, TSeq(TInt)))
       ==> $Is(_module.__default.trim($ly, digits#0), TSeq(TInt)));

function _module.__default.trim#requires(LayerType, Seq Box) : bool;

// #requires axiom for _module.__default.trim
axiom (forall $ly: LayerType, digits#0: Seq Box :: 
  { _module.__default.trim#requires($ly, digits#0) } 
  $Is(digits#0, TSeq(TInt))
     ==> _module.__default.trim#requires($ly, digits#0) == true);

// definition axiom for _module.__default.trim (revealed)
axiom 11 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, digits#0: Seq Box :: 
    { _module.__default.trim($LS($ly), digits#0) } 
    _module.__default.trim#canCall(digits#0)
         || (11 != $FunctionContextHeight && $Is(digits#0, TSeq(TInt)))
       ==> (Seq#Length(digits#0) != 0
             && $Unbox(Seq#Index(digits#0, Seq#Length(digits#0) - 1)): int == LitInt(0)
           ==> _module.__default.trim#canCall(Seq#Take(digits#0, Seq#Length(digits#0) - 1)))
         && _module.__default.trim($LS($ly), digits#0)
           == (if Seq#Length(digits#0) != 0
               && $Unbox(Seq#Index(digits#0, Seq#Length(digits#0) - 1)): int == LitInt(0)
             then _module.__default.trim($ly, Seq#Take(digits#0, Seq#Length(digits#0) - 1))
             else digits#0));

// definition axiom for _module.__default.trim for all literals (revealed)
axiom 11 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, digits#0: Seq Box :: 
    {:weight 3} { _module.__default.trim($LS($ly), Lit(digits#0)) } 
    _module.__default.trim#canCall(Lit(digits#0))
         || (11 != $FunctionContextHeight && $Is(digits#0, TSeq(TInt)))
       ==> (Seq#Length(Lit(digits#0)) != 0
             && $Unbox(Seq#Index(Lit(digits#0), Seq#Length(Lit(digits#0)) - 1)): int
               == LitInt(0)
           ==> _module.__default.trim#canCall(Seq#Take(Lit(digits#0), Seq#Length(Lit(digits#0)) - 1)))
         && _module.__default.trim($LS($ly), Lit(digits#0))
           == (if Seq#Length(Lit(digits#0)) != 0
               && $Unbox(Seq#Index(Lit(digits#0), Seq#Length(Lit(digits#0)) - 1)): int
                 == LitInt(0)
             then _module.__default.trim($LS($ly), Seq#Take(Lit(digits#0), Seq#Length(Lit(digits#0)) - 1))
             else digits#0));

procedure CheckWellformed$$_module.__default.trim(digits#0: Seq Box where $Is(digits#0, TSeq(TInt)));
  free requires 11 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.trim(digits#0: Seq Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##digits#0: Seq Box;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function trim
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(180,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.trim($LS($LZ), digits#0), TSeq(TInt));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (Seq#Length(digits#0) != 0)
        {
            assert 0 <= Seq#Length(digits#0) - 1 && Seq#Length(digits#0) - 1 < Seq#Length(digits#0);
        }

        if (Seq#Length(digits#0) != 0
           && $Unbox(Seq#Index(digits#0, Seq#Length(digits#0) - 1)): int == LitInt(0))
        {
            assert 0 <= Seq#Length(digits#0) - 1
               && Seq#Length(digits#0) - 1 <= Seq#Length(digits#0);
            ##digits#0 := Seq#Take(digits#0, Seq#Length(digits#0) - 1);
            // assume allocatedness for argument to function
            assume $IsAlloc(##digits#0, TSeq(TInt), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert Seq#Rank(##digits#0) < Seq#Rank(digits#0);
            assume _module.__default.trim#canCall(Seq#Take(digits#0, Seq#Length(digits#0) - 1));
            assume _module.__default.trim($LS($LZ), digits#0)
               == _module.__default.trim($LS($LZ), Seq#Take(digits#0, Seq#Length(digits#0) - 1));
            assume _module.__default.trim#canCall(Seq#Take(digits#0, Seq#Length(digits#0) - 1));
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.trim($LS($LZ), digits#0), TSeq(TInt));
        }
        else
        {
            assume _module.__default.trim($LS($LZ), digits#0) == digits#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.trim($LS($LZ), digits#0), TSeq(TInt));
        }

        assert b$reqreads#0;
    }
}



procedure {:_induction digits#0} CheckWellformed$$_module.__default.TrimResult(digits#0: Seq Box
       where $Is(digits#0, TSeq(TInt)) && $IsAlloc(digits#0, TSeq(TInt), $Heap));
  free requires 12 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:_induction digits#0} CheckWellformed$$_module.__default.TrimResult(digits#0: Seq Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var last#Z#0: int;
  var let#0#0#0: int;
  var ##digits#0: Seq Box;
  var ##digits#1: Seq Box;

    // AddMethodImpl: TrimResult, CheckWellformed$$_module.__default.TrimResult
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(187,6): initial state"} true;
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(188,10): post-state"} true;
    havoc last#Z#0;
    assume true;
    ##digits#0 := digits#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##digits#0, TSeq(TInt), $Heap);
    assume _module.__default.trim#canCall(digits#0);
    assume let#0#0#0 == Seq#Length(_module.__default.trim($LS($LZ), digits#0)) - 1;
    assume _module.__default.trim#canCall(digits#0);
    // CheckWellformedWithResult: any expression
    assume $Is(let#0#0#0, TInt);
    assume last#Z#0 == let#0#0#0;
    if (LitInt(0) <= last#Z#0)
    {
        ##digits#1 := digits#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##digits#1, TSeq(TInt), $Heap);
        assume _module.__default.trim#canCall(digits#0);
        assert 0 <= last#Z#0
           && last#Z#0 < Seq#Length(_module.__default.trim($LS($LZ), digits#0));
    }

    assume (var last#0 := Seq#Length(_module.__default.trim($LS($LZ), digits#0)) - 1; 
      LitInt(0) <= last#0
         ==> $Unbox(Seq#Index(_module.__default.trim($LS($LZ), digits#0), last#0)): int != 0);
}



procedure {:_induction digits#0} Call$$_module.__default.TrimResult(digits#0: Seq Box
       where $Is(digits#0, TSeq(TInt)) && $IsAlloc(digits#0, TSeq(TInt), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.trim#canCall(digits#0)
     && (var last#0 := Seq#Length(_module.__default.trim($LS($LZ), digits#0)) - 1; 
      LitInt(0) <= last#0 ==> _module.__default.trim#canCall(digits#0));
  ensures (var last#0 := Seq#Length(_module.__default.trim($LS($LS($LZ)), digits#0)) - 1; 
    LitInt(0) <= last#0
       ==> $Unbox(Seq#Index(_module.__default.trim($LS($LS($LZ)), digits#0), last#0)): int
         != 0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction digits#0} Impl$$_module.__default.TrimResult(digits#0: Seq Box
       where $Is(digits#0, TSeq(TInt)) && $IsAlloc(digits#0, TSeq(TInt), $Heap))
   returns ($_reverifyPost: bool);
  free requires 12 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.trim#canCall(digits#0)
     && (var last#0 := Seq#Length(_module.__default.trim($LS($LZ), digits#0)) - 1; 
      LitInt(0) <= last#0 ==> _module.__default.trim#canCall(digits#0));
  ensures (var last#0 := Seq#Length(_module.__default.trim($LS($LS($LZ)), digits#0)) - 1; 
    LitInt(0) <= last#0
       ==> $Unbox(Seq#Index(_module.__default.trim($LS($LS($LZ)), digits#0), last#0)): int
         != 0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction digits#0} Impl$$_module.__default.TrimResult(digits#0: Seq Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;

    // AddMethodImpl: TrimResult, Impl$$_module.__default.TrimResult
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(190,0): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#digits0#0: Seq Box :: 
      $Is($ih#digits0#0, TSeq(TInt))
           && Lit(true)
           && Seq#Rank($ih#digits0#0) < Seq#Rank(digits#0)
         ==> (var last#1 := Seq#Length(_module.__default.trim($LS($LZ), $ih#digits0#0)) - 1; 
          LitInt(0) <= last#1
             ==> $Unbox(Seq#Index(_module.__default.trim($LS($LZ), $ih#digits0#0), last#1)): int
               != 0));
    $_reverifyPost := false;
}



procedure {:_induction a#0} CheckWellformed$$_module.__default.TrimProperty(a#0: Seq Box where $Is(a#0, TSeq(TInt)) && $IsAlloc(a#0, TSeq(TInt), $Heap));
  free requires 13 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:_induction a#0} CheckWellformed$$_module.__default.TrimProperty(a#0: Seq Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##digits#0: Seq Box;
  var ##digits#1: Seq Box;

    // AddMethodImpl: TrimProperty, CheckWellformed$$_module.__default.TrimProperty
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(193,6): initial state"} true;
    ##digits#0 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##digits#0, TSeq(TInt), $Heap);
    assume _module.__default.trim#canCall(a#0);
    assume Seq#Equal(a#0, _module.__default.trim($LS($LZ), a#0));
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(195,18): post-state"} true;
    if (*)
    {
        assume Seq#Equal(a#0, Seq#Empty(): Seq Box);
    }
    else
    {
        assume !Seq#Equal(a#0, Seq#Empty(): Seq Box);
        assert 0 <= LitInt(1) && LitInt(1) <= Seq#Length(a#0);
        assert 0 <= LitInt(1) && LitInt(1) <= Seq#Length(a#0);
        ##digits#1 := Seq#Drop(a#0, LitInt(1));
        // assume allocatedness for argument to function
        assume $IsAlloc(##digits#1, TSeq(TInt), $Heap);
        assume _module.__default.trim#canCall(Seq#Drop(a#0, LitInt(1)));
        assume Seq#Equal(Seq#Drop(a#0, LitInt(1)), 
          _module.__default.trim($LS($LZ), Seq#Drop(a#0, LitInt(1))));
    }
}



procedure {:_induction a#0} Call$$_module.__default.TrimProperty(a#0: Seq Box where $Is(a#0, TSeq(TInt)) && $IsAlloc(a#0, TSeq(TInt), $Heap));
  // user-defined preconditions
  requires Seq#Equal(a#0, _module.__default.trim($LS($LS($LZ)), a#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures !Seq#Equal(a#0, Seq#Empty(): Seq Box)
     ==> _module.__default.trim#canCall(Seq#Drop(a#0, LitInt(1)));
  ensures Seq#Equal(a#0, Seq#Empty(): Seq Box)
     || Seq#Equal(Seq#Drop(a#0, LitInt(1)), 
      _module.__default.trim($LS($LS($LZ)), Seq#Drop(a#0, LitInt(1))));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction a#0} Impl$$_module.__default.TrimProperty(a#0: Seq Box where $Is(a#0, TSeq(TInt)) && $IsAlloc(a#0, TSeq(TInt), $Heap))
   returns ($_reverifyPost: bool);
  free requires 13 == $FunctionContextHeight;
  // user-defined preconditions
  requires Seq#Equal(a#0, _module.__default.trim($LS($LS($LZ)), a#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures !Seq#Equal(a#0, Seq#Empty(): Seq Box)
     ==> _module.__default.trim#canCall(Seq#Drop(a#0, LitInt(1)));
  ensures Seq#Equal(a#0, Seq#Empty(): Seq Box)
     || Seq#Equal(Seq#Drop(a#0, LitInt(1)), 
      _module.__default.trim($LS($LS($LZ)), Seq#Drop(a#0, LitInt(1))));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction a#0} Impl$$_module.__default.TrimProperty(a#0: Seq Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var b#0: Seq Box;
  var ##digits#2: Seq Box;

    // AddMethodImpl: TrimProperty, Impl$$_module.__default.TrimProperty
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(196,0): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#a0#0: Seq Box :: 
      $Is($ih#a0#0, TSeq(TInt))
           && Seq#Equal($ih#a0#0, _module.__default.trim($LS($LZ), $ih#a0#0))
           && Seq#Rank($ih#a0#0) < Seq#Rank(a#0)
         ==> Seq#Equal($ih#a0#0, Seq#Empty(): Seq Box)
           || Seq#Equal(Seq#Drop($ih#a0#0, LitInt(1)), 
            _module.__default.trim($LS($LZ), Seq#Drop($ih#a0#0, LitInt(1)))));
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(197,3)
    // Begin Comprehension WF check
    havoc b#0;
    if ($Is(b#0, TSeq(TInt)))
    {
        ##digits#2 := b#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##digits#2, TSeq(TInt), $Heap);
        assume _module.__default.trim#canCall(b#0);
    }

    // End Comprehension WF check
    assume (forall b#1: Seq Box :: 
      { _module.__default.trim($LS($LZ), b#1) } 
      $Is(b#1, TSeq(TInt)) ==> _module.__default.trim#canCall(b#1));
    assert {:subsumption 0} (forall b#1: Seq Box :: 
      { _module.__default.trim($LS($LS($LZ)), b#1) } 
      $Is(b#1, TSeq(TInt))
           && (forall b$ih#0#0: Seq Box :: 
            { _module.__default.trim($LS($LZ), b$ih#0#0) } 
            $Is(b$ih#0#0, TSeq(TInt))
               ==> 
              Seq#Rank(b$ih#0#0) < Seq#Rank(b#1)
               ==> Seq#Length(_module.__default.trim($LS($LZ), b$ih#0#0)) <= Seq#Length(b$ih#0#0))
           && true
         ==> Seq#Length(_module.__default.trim($LS($LS($LZ)), b#1)) <= Seq#Length(b#1));
    assume (forall b#1: Seq Box :: 
      {:induction} {:_induction b#1} { _module.__default.trim($LS($LZ), b#1) } 
      $Is(b#1, TSeq(TInt))
         ==> Seq#Length(_module.__default.trim($LS($LZ), b#1)) <= Seq#Length(b#1));
}



procedure {:_induction digits#0, base#0} CheckWellformed$$_module.__default.TrimPreservesValue(digits#0: Seq Box
       where $Is(digits#0, TSeq(TInt)) && $IsAlloc(digits#0, TSeq(TInt), $Heap), 
    base#0: int);
  free requires 15 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:_induction digits#0, base#0} CheckWellformed$$_module.__default.TrimPreservesValue(digits#0: Seq Box, base#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##digits#0: Seq Box;
  var ##base#0: int;
  var ##digits#1: Seq Box;
  var ##digits#2: Seq Box;
  var ##base#1: int;

    // AddMethodImpl: TrimPreservesValue, CheckWellformed$$_module.__default.TrimPreservesValue
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(200,6): initial state"} true;
    assume LitInt(2) <= base#0;
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(202,29): post-state"} true;
    ##digits#0 := digits#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##digits#0, TSeq(TInt), $Heap);
    ##base#0 := base#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##base#0, TInt, $Heap);
    assert {:subsumption 0} LitInt(2) <= ##base#0;
    assume LitInt(2) <= ##base#0;
    assume _module.__default.eval#canCall(digits#0, base#0);
    ##digits#1 := digits#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##digits#1, TSeq(TInt), $Heap);
    assume _module.__default.trim#canCall(digits#0);
    ##digits#2 := _module.__default.trim($LS($LZ), digits#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##digits#2, TSeq(TInt), $Heap);
    ##base#1 := base#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##base#1, TInt, $Heap);
    assert {:subsumption 0} LitInt(2) <= ##base#1;
    assume LitInt(2) <= ##base#1;
    assume _module.__default.eval#canCall(_module.__default.trim($LS($LZ), digits#0), base#0);
    assume _module.__default.eval($LS($LZ), digits#0, base#0)
       == _module.__default.eval($LS($LZ), _module.__default.trim($LS($LZ), digits#0), base#0);
}



procedure {:_induction digits#0, base#0} Call$$_module.__default.TrimPreservesValue(digits#0: Seq Box
       where $Is(digits#0, TSeq(TInt)) && $IsAlloc(digits#0, TSeq(TInt), $Heap), 
    base#0: int);
  // user-defined preconditions
  requires LitInt(2) <= base#0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.eval#canCall(digits#0, base#0)
     && 
    _module.__default.trim#canCall(digits#0)
     && _module.__default.eval#canCall(_module.__default.trim($LS($LZ), digits#0), base#0);
  ensures _module.__default.eval($LS($LS($LZ)), digits#0, base#0)
     == _module.__default.eval($LS($LS($LZ)), _module.__default.trim($LS($LS($LZ)), digits#0), base#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction digits#0, base#0} Impl$$_module.__default.TrimPreservesValue(digits#0: Seq Box
       where $Is(digits#0, TSeq(TInt)) && $IsAlloc(digits#0, TSeq(TInt), $Heap), 
    base#0: int)
   returns ($_reverifyPost: bool);
  free requires 15 == $FunctionContextHeight;
  // user-defined preconditions
  requires LitInt(2) <= base#0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.eval#canCall(digits#0, base#0)
     && 
    _module.__default.trim#canCall(digits#0)
     && _module.__default.eval#canCall(_module.__default.trim($LS($LZ), digits#0), base#0);
  ensures _module.__default.eval($LS($LS($LZ)), digits#0, base#0)
     == _module.__default.eval($LS($LS($LZ)), _module.__default.trim($LS($LS($LZ)), digits#0), base#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction digits#0, base#0} Impl$$_module.__default.TrimPreservesValue(digits#0: Seq Box, base#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var last#0: int;
  var digits##0_0: Seq Box;
  var base##0_0: int;

    // AddMethodImpl: TrimPreservesValue, Impl$$_module.__default.TrimPreservesValue
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(203,0): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#digits0#0: Seq Box, $ih#base0#0: int :: 
      $Is($ih#digits0#0, TSeq(TInt))
           && LitInt(2) <= $ih#base0#0
           && (Seq#Rank($ih#digits0#0) < Seq#Rank(digits#0)
             || (Seq#Rank($ih#digits0#0) == Seq#Rank(digits#0)
               && 
              0 <= $ih#base0#0
               && $ih#base0#0 < base#0))
         ==> _module.__default.eval($LS($LZ), $ih#digits0#0, $ih#base0#0)
           == _module.__default.eval($LS($LZ), _module.__default.trim($LS($LZ), $ih#digits0#0), $ih#base0#0));
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(204,12)
    assume true;
    assume true;
    last#0 := Seq#Length(digits#0) - 1;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(204,26)"} true;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(205,3)
    if (Seq#Length(digits#0) != 0)
    {
        assert 0 <= last#0 && last#0 < Seq#Length(digits#0);
    }

    assume true;
    if (Seq#Length(digits#0) != 0
       && $Unbox(Seq#Index(digits#0, last#0)): int == LitInt(0))
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(206,5)
        assert {:subsumption 0} 0 <= last#0 && last#0 <= Seq#Length(digits#0);
        assume true;
        assert Seq#Equal(digits#0, 
          Seq#Append(Seq#Take(digits#0, last#0), Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0)))));
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(207,29)
        // TrCallStmt: Before ProcessCallStmt
        assert 0 <= last#0 && last#0 <= Seq#Length(digits#0);
        assume true;
        // ProcessCallStmt: CheckSubrange
        digits##0_0 := Seq#Take(digits#0, last#0);
        assume true;
        // ProcessCallStmt: CheckSubrange
        base##0_0 := base#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.LeadingZeroInsignificant(digits##0_0, base##0_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(207,50)"} true;
    }
    else
    {
    }
}



procedure {:_induction digits#0, base#0} CheckWellformed$$_module.__default.LeadingZeroInsignificant(digits#0: Seq Box
       where $Is(digits#0, TSeq(TInt)) && $IsAlloc(digits#0, TSeq(TInt), $Heap), 
    base#0: int);
  free requires 14 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:_induction digits#0, base#0} CheckWellformed$$_module.__default.LeadingZeroInsignificant(digits#0: Seq Box, base#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##digits#0: Seq Box;
  var ##base#0: int;
  var ##digits#1: Seq Box;
  var ##base#1: int;

    // AddMethodImpl: LeadingZeroInsignificant, CheckWellformed$$_module.__default.LeadingZeroInsignificant
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(211,6): initial state"} true;
    assume LitInt(2) <= base#0;
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(213,29): post-state"} true;
    ##digits#0 := digits#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##digits#0, TSeq(TInt), $Heap);
    ##base#0 := base#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##base#0, TInt, $Heap);
    assert {:subsumption 0} LitInt(2) <= ##base#0;
    assume LitInt(2) <= ##base#0;
    assume _module.__default.eval#canCall(digits#0, base#0);
    ##digits#1 := Seq#Append(digits#0, Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0))));
    // assume allocatedness for argument to function
    assume $IsAlloc(##digits#1, TSeq(TInt), $Heap);
    ##base#1 := base#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##base#1, TInt, $Heap);
    assert {:subsumption 0} LitInt(2) <= ##base#1;
    assume LitInt(2) <= ##base#1;
    assume _module.__default.eval#canCall(Seq#Append(digits#0, Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0)))), base#0);
    assume _module.__default.eval($LS($LZ), digits#0, base#0)
       == _module.__default.eval($LS($LZ), 
        Seq#Append(digits#0, Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0)))), 
        base#0);
}



procedure {:_induction digits#0, base#0} Call$$_module.__default.LeadingZeroInsignificant(digits#0: Seq Box
       where $Is(digits#0, TSeq(TInt)) && $IsAlloc(digits#0, TSeq(TInt), $Heap), 
    base#0: int);
  // user-defined preconditions
  requires LitInt(2) <= base#0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.eval#canCall(digits#0, base#0)
     && _module.__default.eval#canCall(Seq#Append(digits#0, Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0)))), base#0);
  ensures _module.__default.eval($LS($LS($LZ)), digits#0, base#0)
     == _module.__default.eval($LS($LS($LZ)), 
      Seq#Append(digits#0, Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0)))), 
      base#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction digits#0, base#0} Impl$$_module.__default.LeadingZeroInsignificant(digits#0: Seq Box
       where $Is(digits#0, TSeq(TInt)) && $IsAlloc(digits#0, TSeq(TInt), $Heap), 
    base#0: int)
   returns ($_reverifyPost: bool);
  free requires 14 == $FunctionContextHeight;
  // user-defined preconditions
  requires LitInt(2) <= base#0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.eval#canCall(digits#0, base#0)
     && _module.__default.eval#canCall(Seq#Append(digits#0, Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0)))), base#0);
  ensures _module.__default.eval($LS($LS($LZ)), digits#0, base#0)
     == _module.__default.eval($LS($LS($LZ)), 
      Seq#Append(digits#0, Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0)))), 
      base#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction digits#0, base#0} Impl$$_module.__default.LeadingZeroInsignificant(digits#0: Seq Box, base#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var d#0_0: int;
  var ##digits#0_0_0_0: Seq Box;
  var ##base#0_0_0_0: int;
  var ##digits#0_0_0_1: Seq Box;
  var ##base#0_0_0_1: int;
  var ##digits#0_0_1_0: Seq Box;
  var ##base#0_0_1_0: int;
  var ##digits#0_0_1_1: Seq Box;
  var ##base#0_0_1_1: int;
  var ##digits#0_0_2_0: Seq Box;
  var ##base#0_0_2_0: int;
  var ##digits#0_0_2_1: Seq Box;
  var ##base#0_0_2_1: int;
  var ##digits#0_0_3_0: Seq Box;
  var ##base#0_0_3_0: int;
  var digits##0_0_3_0: Seq Box;
  var base##0_0_3_0: int;
  var ##digits#0_0_3_1: Seq Box;
  var ##base#0_0_3_1: int;
  var ##digits#0_0_4_0: Seq Box;
  var ##base#0_0_4_0: int;
  var ##digits#0_0_4_1: Seq Box;
  var ##base#0_0_4_1: int;
  var ##digits#0_0_5_0: Seq Box;
  var ##base#0_0_5_0: int;
  var ##digits#0_0_5_1: Seq Box;
  var ##base#0_0_5_1: int;
  var ##digits#0_0_0: Seq Box;
  var ##base#0_0_0: int;

    // AddMethodImpl: LeadingZeroInsignificant, Impl$$_module.__default.LeadingZeroInsignificant
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(214,0): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#digits0#0: Seq Box, $ih#base0#0: int :: 
      $Is($ih#digits0#0, TSeq(TInt))
           && LitInt(2) <= $ih#base0#0
           && (Seq#Rank($ih#digits0#0) < Seq#Rank(digits#0)
             || (Seq#Rank($ih#digits0#0) == Seq#Rank(digits#0)
               && 
              0 <= $ih#base0#0
               && $ih#base0#0 < base#0))
         ==> _module.__default.eval($LS($LZ), $ih#digits0#0, $ih#base0#0)
           == _module.__default.eval($LS($LZ), 
            Seq#Append($ih#digits0#0, Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0)))), 
            $ih#base0#0));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(215,3)
    assume true;
    if (Seq#Length(digits#0) != 0)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(216,11)
        assume true;
        assert 0 <= LitInt(0) && LitInt(0) < Seq#Length(digits#0);
        assume true;
        d#0_0 := $Unbox(Seq#Index(digits#0, LitInt(0))): int;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(216,22)"} true;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(217,5)
        assert {:subsumption 0} 0 <= LitInt(1) && LitInt(1) <= Seq#Length(digits#0);
        assume true;
        assert Seq#Equal(Seq#Append(Seq#Build(Seq#Empty(): Seq Box, $Box(d#0_0)), Seq#Drop(digits#0, LitInt(1))), 
          digits#0);
        // ----- calc statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(218,5)
        // Assume Fuel Constant
        if (*)
        {
            // ----- assert wf[initial] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(218,5)
            ##digits#0_0_0 := digits#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##digits#0_0_0, TSeq(TInt), $Heap);
            ##base#0_0_0 := base#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##base#0_0_0, TInt, $Heap);
            assert {:subsumption 0} LitInt(2) <= ##base#0_0_0;
            assume _module.__default.eval#canCall(digits#0, base#0);
            assume _module.__default.eval#canCall(digits#0, base#0);
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(218,5)
            ##digits#0_0_5_0 := digits#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##digits#0_0_5_0, TSeq(TInt), $Heap);
            ##base#0_0_5_0 := base#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##base#0_0_5_0, TInt, $Heap);
            assume {:subsumption 0} LitInt(2) <= ##base#0_0_5_0;
            assume _module.__default.eval#canCall(digits#0, base#0);
            assume _module.__default.eval#canCall(digits#0, base#0);
            // ----- Hint0 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(218,5)
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(218,5)
            assert {:subsumption 0} 0 <= LitInt(1) && LitInt(1) <= Seq#Length(digits#0);
            ##digits#0_0_5_1 := Seq#Append(Seq#Build(Seq#Empty(): Seq Box, $Box(d#0_0)), Seq#Drop(digits#0, LitInt(1)));
            // assume allocatedness for argument to function
            assume $IsAlloc(##digits#0_0_5_1, TSeq(TInt), $Heap);
            ##base#0_0_5_1 := base#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##base#0_0_5_1, TInt, $Heap);
            assert {:subsumption 0} LitInt(2) <= ##base#0_0_5_1;
            assume _module.__default.eval#canCall(Seq#Append(Seq#Build(Seq#Empty(): Seq Box, $Box(d#0_0)), Seq#Drop(digits#0, LitInt(1))), 
              base#0);
            assume _module.__default.eval#canCall(Seq#Append(Seq#Build(Seq#Empty(): Seq Box, $Box(d#0_0)), Seq#Drop(digits#0, LitInt(1))), 
              base#0);
            // ----- assert line0 == line1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(218,5)
            assert {:subsumption 0} _module.__default.eval($LS($LS($LZ)), digits#0, base#0)
               == _module.__default.eval($LS($LS($LZ)), 
                Seq#Append(Seq#Build(Seq#Empty(): Seq Box, $Box(d#0_0)), Seq#Drop(digits#0, LitInt(1))), 
                base#0);
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(218,5)
            assume {:subsumption 0} 0 <= LitInt(1) && LitInt(1) <= Seq#Length(digits#0);
            ##digits#0_0_4_0 := Seq#Append(Seq#Build(Seq#Empty(): Seq Box, $Box(d#0_0)), Seq#Drop(digits#0, LitInt(1)));
            // assume allocatedness for argument to function
            assume $IsAlloc(##digits#0_0_4_0, TSeq(TInt), $Heap);
            ##base#0_0_4_0 := base#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##base#0_0_4_0, TInt, $Heap);
            assume {:subsumption 0} LitInt(2) <= ##base#0_0_4_0;
            assume _module.__default.eval#canCall(Seq#Append(Seq#Build(Seq#Empty(): Seq Box, $Box(d#0_0)), Seq#Drop(digits#0, LitInt(1))), 
              base#0);
            assume _module.__default.eval#canCall(Seq#Append(Seq#Build(Seq#Empty(): Seq Box, $Box(d#0_0)), Seq#Drop(digits#0, LitInt(1))), 
              base#0);
            // ----- Hint1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(218,5)
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(218,5)
            assert {:subsumption 0} 0 <= LitInt(1) && LitInt(1) <= Seq#Length(digits#0);
            ##digits#0_0_4_1 := Seq#Drop(digits#0, LitInt(1));
            // assume allocatedness for argument to function
            assume $IsAlloc(##digits#0_0_4_1, TSeq(TInt), $Heap);
            ##base#0_0_4_1 := base#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##base#0_0_4_1, TInt, $Heap);
            assert {:subsumption 0} LitInt(2) <= ##base#0_0_4_1;
            assume _module.__default.eval#canCall(Seq#Drop(digits#0, LitInt(1)), base#0);
            assume _module.__default.eval#canCall(Seq#Drop(digits#0, LitInt(1)), base#0);
            // ----- assert line1 == line2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(218,5)
            assert {:subsumption 0} _module.__default.eval($LS($LS($LZ)), 
                Seq#Append(Seq#Build(Seq#Empty(): Seq Box, $Box(d#0_0)), Seq#Drop(digits#0, LitInt(1))), 
                base#0)
               == d#0_0
                 + Mul(base#0, 
                  _module.__default.eval($LS($LS($LZ)), Seq#Drop(digits#0, LitInt(1)), base#0));
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(218,5)
            assume {:subsumption 0} 0 <= LitInt(1) && LitInt(1) <= Seq#Length(digits#0);
            ##digits#0_0_3_0 := Seq#Drop(digits#0, LitInt(1));
            // assume allocatedness for argument to function
            assume $IsAlloc(##digits#0_0_3_0, TSeq(TInt), $Heap);
            ##base#0_0_3_0 := base#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##base#0_0_3_0, TInt, $Heap);
            assume {:subsumption 0} LitInt(2) <= ##base#0_0_3_0;
            assume _module.__default.eval#canCall(Seq#Drop(digits#0, LitInt(1)), base#0);
            assume _module.__default.eval#canCall(Seq#Drop(digits#0, LitInt(1)), base#0);
            // ----- Hint2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(218,5)
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(222,33)
            // TrCallStmt: Before ProcessCallStmt
            assert 0 <= LitInt(1) && LitInt(1) <= Seq#Length(digits#0);
            assume true;
            // ProcessCallStmt: CheckSubrange
            digits##0_0_3_0 := Seq#Drop(digits#0, LitInt(1));
            assume true;
            // ProcessCallStmt: CheckSubrange
            base##0_0_3_0 := base#0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0 <= base#0
               || Seq#Rank(digits##0_0_3_0) < Seq#Rank(digits#0)
               || base##0_0_3_0 == base#0;
            assert Seq#Rank(digits##0_0_3_0) < Seq#Rank(digits#0)
               || (Seq#Rank(digits##0_0_3_0) == Seq#Rank(digits#0) && base##0_0_3_0 < base#0);
            // ProcessCallStmt: Make the call
            call Call$$_module.__default.LeadingZeroInsignificant(digits##0_0_3_0, base##0_0_3_0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(222,51)"} true;
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(218,5)
            assert {:subsumption 0} 0 <= LitInt(1) && LitInt(1) <= Seq#Length(digits#0);
            ##digits#0_0_3_1 := Seq#Append(Seq#Drop(digits#0, LitInt(1)), Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0))));
            // assume allocatedness for argument to function
            assume $IsAlloc(##digits#0_0_3_1, TSeq(TInt), $Heap);
            ##base#0_0_3_1 := base#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##base#0_0_3_1, TInt, $Heap);
            assert {:subsumption 0} LitInt(2) <= ##base#0_0_3_1;
            assume _module.__default.eval#canCall(Seq#Append(Seq#Drop(digits#0, LitInt(1)), Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0)))), 
              base#0);
            assume _module.__default.eval#canCall(Seq#Append(Seq#Drop(digits#0, LitInt(1)), Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0)))), 
              base#0);
            // ----- assert line2 == line3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(218,5)
            assert {:subsumption 0} d#0_0
                 + Mul(base#0, 
                  _module.__default.eval($LS($LS($LZ)), Seq#Drop(digits#0, LitInt(1)), base#0))
               == d#0_0
                 + Mul(base#0, 
                  _module.__default.eval($LS($LS($LZ)), 
                    Seq#Append(Seq#Drop(digits#0, LitInt(1)), Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0)))), 
                    base#0));
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(218,5)
            assume {:subsumption 0} 0 <= LitInt(1) && LitInt(1) <= Seq#Length(digits#0);
            ##digits#0_0_2_0 := Seq#Append(Seq#Drop(digits#0, LitInt(1)), Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0))));
            // assume allocatedness for argument to function
            assume $IsAlloc(##digits#0_0_2_0, TSeq(TInt), $Heap);
            ##base#0_0_2_0 := base#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##base#0_0_2_0, TInt, $Heap);
            assume {:subsumption 0} LitInt(2) <= ##base#0_0_2_0;
            assume _module.__default.eval#canCall(Seq#Append(Seq#Drop(digits#0, LitInt(1)), Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0)))), 
              base#0);
            assume _module.__default.eval#canCall(Seq#Append(Seq#Drop(digits#0, LitInt(1)), Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0)))), 
              base#0);
            // ----- Hint3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(218,5)
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(218,5)
            assert {:subsumption 0} 0 <= LitInt(1) && LitInt(1) <= Seq#Length(digits#0);
            ##digits#0_0_2_1 := Seq#Append(Seq#Build(Seq#Empty(): Seq Box, $Box(d#0_0)), 
              Seq#Append(Seq#Drop(digits#0, LitInt(1)), Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0)))));
            // assume allocatedness for argument to function
            assume $IsAlloc(##digits#0_0_2_1, TSeq(TInt), $Heap);
            ##base#0_0_2_1 := base#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##base#0_0_2_1, TInt, $Heap);
            assert {:subsumption 0} LitInt(2) <= ##base#0_0_2_1;
            assume _module.__default.eval#canCall(Seq#Append(Seq#Build(Seq#Empty(): Seq Box, $Box(d#0_0)), 
                Seq#Append(Seq#Drop(digits#0, LitInt(1)), Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0))))), 
              base#0);
            assume _module.__default.eval#canCall(Seq#Append(Seq#Build(Seq#Empty(): Seq Box, $Box(d#0_0)), 
                Seq#Append(Seq#Drop(digits#0, LitInt(1)), Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0))))), 
              base#0);
            // ----- assert line3 == line4 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(218,5)
            assert {:subsumption 0} d#0_0
                 + Mul(base#0, 
                  _module.__default.eval($LS($LS($LZ)), 
                    Seq#Append(Seq#Drop(digits#0, LitInt(1)), Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0)))), 
                    base#0))
               == _module.__default.eval($LS($LS($LZ)), 
                Seq#Append(Seq#Build(Seq#Empty(): Seq Box, $Box(d#0_0)), 
                  Seq#Append(Seq#Drop(digits#0, LitInt(1)), Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0))))), 
                base#0);
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(218,5)
            assume {:subsumption 0} 0 <= LitInt(1) && LitInt(1) <= Seq#Length(digits#0);
            ##digits#0_0_1_0 := Seq#Append(Seq#Build(Seq#Empty(): Seq Box, $Box(d#0_0)), 
              Seq#Append(Seq#Drop(digits#0, LitInt(1)), Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0)))));
            // assume allocatedness for argument to function
            assume $IsAlloc(##digits#0_0_1_0, TSeq(TInt), $Heap);
            ##base#0_0_1_0 := base#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##base#0_0_1_0, TInt, $Heap);
            assume {:subsumption 0} LitInt(2) <= ##base#0_0_1_0;
            assume _module.__default.eval#canCall(Seq#Append(Seq#Build(Seq#Empty(): Seq Box, $Box(d#0_0)), 
                Seq#Append(Seq#Drop(digits#0, LitInt(1)), Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0))))), 
              base#0);
            assume _module.__default.eval#canCall(Seq#Append(Seq#Build(Seq#Empty(): Seq Box, $Box(d#0_0)), 
                Seq#Append(Seq#Drop(digits#0, LitInt(1)), Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0))))), 
              base#0);
            // ----- Hint4 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(218,5)
            // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(225,9)
            assert {:subsumption 0} 0 <= LitInt(1) && LitInt(1) <= Seq#Length(digits#0);
            assert {:subsumption 0} 0 <= LitInt(1) && LitInt(1) <= Seq#Length(digits#0);
            assume true;
            assert Seq#Equal(Seq#Append(Seq#Build(Seq#Empty(): Seq Box, $Box(d#0_0)), 
                Seq#Append(Seq#Drop(digits#0, LitInt(1)), Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0))))), 
              Seq#Append(Seq#Append(Seq#Build(Seq#Empty(): Seq Box, $Box(d#0_0)), Seq#Drop(digits#0, LitInt(1))), 
                Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0)))));
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(218,5)
            assert {:subsumption 0} 0 <= LitInt(1) && LitInt(1) <= Seq#Length(digits#0);
            ##digits#0_0_1_1 := Seq#Append(Seq#Append(Seq#Build(Seq#Empty(): Seq Box, $Box(d#0_0)), Seq#Drop(digits#0, LitInt(1))), 
              Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0))));
            // assume allocatedness for argument to function
            assume $IsAlloc(##digits#0_0_1_1, TSeq(TInt), $Heap);
            ##base#0_0_1_1 := base#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##base#0_0_1_1, TInt, $Heap);
            assert {:subsumption 0} LitInt(2) <= ##base#0_0_1_1;
            assume _module.__default.eval#canCall(Seq#Append(Seq#Append(Seq#Build(Seq#Empty(): Seq Box, $Box(d#0_0)), Seq#Drop(digits#0, LitInt(1))), 
                Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0)))), 
              base#0);
            assume _module.__default.eval#canCall(Seq#Append(Seq#Append(Seq#Build(Seq#Empty(): Seq Box, $Box(d#0_0)), Seq#Drop(digits#0, LitInt(1))), 
                Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0)))), 
              base#0);
            // ----- assert line4 == line5 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(218,5)
            assert {:subsumption 0} _module.__default.eval($LS($LS($LZ)), 
                Seq#Append(Seq#Build(Seq#Empty(): Seq Box, $Box(d#0_0)), 
                  Seq#Append(Seq#Drop(digits#0, LitInt(1)), Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0))))), 
                base#0)
               == _module.__default.eval($LS($LS($LZ)), 
                Seq#Append(Seq#Append(Seq#Build(Seq#Empty(): Seq Box, $Box(d#0_0)), Seq#Drop(digits#0, LitInt(1))), 
                  Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0)))), 
                base#0);
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(218,5)
            assume {:subsumption 0} 0 <= LitInt(1) && LitInt(1) <= Seq#Length(digits#0);
            ##digits#0_0_0_0 := Seq#Append(Seq#Append(Seq#Build(Seq#Empty(): Seq Box, $Box(d#0_0)), Seq#Drop(digits#0, LitInt(1))), 
              Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0))));
            // assume allocatedness for argument to function
            assume $IsAlloc(##digits#0_0_0_0, TSeq(TInt), $Heap);
            ##base#0_0_0_0 := base#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##base#0_0_0_0, TInt, $Heap);
            assume {:subsumption 0} LitInt(2) <= ##base#0_0_0_0;
            assume _module.__default.eval#canCall(Seq#Append(Seq#Append(Seq#Build(Seq#Empty(): Seq Box, $Box(d#0_0)), Seq#Drop(digits#0, LitInt(1))), 
                Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0)))), 
              base#0);
            assume _module.__default.eval#canCall(Seq#Append(Seq#Append(Seq#Build(Seq#Empty(): Seq Box, $Box(d#0_0)), Seq#Drop(digits#0, LitInt(1))), 
                Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0)))), 
              base#0);
            // ----- Hint5 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(218,5)
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(218,5)
            ##digits#0_0_0_1 := Seq#Append(digits#0, Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0))));
            // assume allocatedness for argument to function
            assume $IsAlloc(##digits#0_0_0_1, TSeq(TInt), $Heap);
            ##base#0_0_0_1 := base#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##base#0_0_0_1, TInt, $Heap);
            assert {:subsumption 0} LitInt(2) <= ##base#0_0_0_1;
            assume _module.__default.eval#canCall(Seq#Append(digits#0, Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0)))), base#0);
            assume _module.__default.eval#canCall(Seq#Append(digits#0, Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0)))), base#0);
            // ----- assert line5 == line6 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(218,5)
            assert {:subsumption 0} _module.__default.eval($LS($LS($LZ)), 
                Seq#Append(Seq#Append(Seq#Build(Seq#Empty(): Seq Box, $Box(d#0_0)), Seq#Drop(digits#0, LitInt(1))), 
                  Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0)))), 
                base#0)
               == _module.__default.eval($LS($LS($LZ)), 
                Seq#Append(digits#0, Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0)))), 
                base#0);
            assume false;
        }

        assume _module.__default.eval($LS($LZ), digits#0, base#0)
           == _module.__default.eval($LS($LZ), 
            Seq#Append(digits#0, Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0)))), 
            base#0);
    }
    else
    {
    }
}



procedure {:_induction a#0, b#0, base#0} CheckWellformed$$_module.__default.UniqueRepresentation(a#0: Seq Box where $Is(a#0, TSeq(TInt)) && $IsAlloc(a#0, TSeq(TInt), $Heap), 
    b#0: Seq Box where $Is(b#0, TSeq(TInt)) && $IsAlloc(b#0, TSeq(TInt), $Heap), 
    lowDigit#0: int, 
    base#0: int);
  free requires 24 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:_induction a#0, b#0, base#0} CheckWellformed$$_module.__default.UniqueRepresentation(a#0: Seq Box, b#0: Seq Box, lowDigit#0: int, base#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##digits#0: Seq Box;
  var ##lowDigit#0: int;
  var ##base#0: int;
  var ##digits#1: Seq Box;
  var ##lowDigit#1: int;
  var ##base#1: int;
  var ##digits#2: Seq Box;
  var ##digits#3: Seq Box;
  var ##digits#4: Seq Box;
  var ##base#2: int;
  var ##digits#5: Seq Box;
  var ##base#3: int;

    // AddMethodImpl: UniqueRepresentation, CheckWellformed$$_module.__default.UniqueRepresentation
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(234,6): initial state"} true;
    ##digits#0 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##digits#0, TSeq(TInt), $Heap);
    ##lowDigit#0 := lowDigit#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##lowDigit#0, TInt, $Heap);
    ##base#0 := base#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##base#0, TInt, $Heap);
    assume _module.__default.IsSkewNumber#canCall(a#0, lowDigit#0, base#0);
    assume _module.__default.IsSkewNumber(a#0, lowDigit#0, base#0);
    ##digits#1 := b#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##digits#1, TSeq(TInt), $Heap);
    ##lowDigit#1 := lowDigit#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##lowDigit#1, TInt, $Heap);
    ##base#1 := base#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##base#1, TInt, $Heap);
    assume _module.__default.IsSkewNumber#canCall(b#0, lowDigit#0, base#0);
    assume _module.__default.IsSkewNumber(b#0, lowDigit#0, base#0);
    ##digits#2 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##digits#2, TSeq(TInt), $Heap);
    assume _module.__default.trim#canCall(a#0);
    assume Seq#Equal(a#0, _module.__default.trim($LS($LZ), a#0));
    ##digits#3 := b#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##digits#3, TSeq(TInt), $Heap);
    assume _module.__default.trim#canCall(b#0);
    assume Seq#Equal(b#0, _module.__default.trim($LS($LZ), b#0));
    ##digits#4 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##digits#4, TSeq(TInt), $Heap);
    ##base#2 := base#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##base#2, TInt, $Heap);
    assert {:subsumption 0} LitInt(2) <= ##base#2;
    assume LitInt(2) <= ##base#2;
    assume _module.__default.eval#canCall(a#0, base#0);
    ##digits#5 := b#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##digits#5, TSeq(TInt), $Heap);
    ##base#3 := base#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##base#3, TInt, $Heap);
    assert {:subsumption 0} LitInt(2) <= ##base#3;
    assume LitInt(2) <= ##base#3;
    assume _module.__default.eval#canCall(b#0, base#0);
    assume _module.__default.eval($LS($LZ), a#0, base#0)
       == _module.__default.eval($LS($LZ), b#0, base#0);
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(238,12): post-state"} true;
    assume Seq#Equal(a#0, b#0);
}



procedure {:_induction a#0, b#0, base#0} Call$$_module.__default.UniqueRepresentation(a#0: Seq Box where $Is(a#0, TSeq(TInt)) && $IsAlloc(a#0, TSeq(TInt), $Heap), 
    b#0: Seq Box where $Is(b#0, TSeq(TInt)) && $IsAlloc(b#0, TSeq(TInt), $Heap), 
    lowDigit#0: int, 
    base#0: int);
  // user-defined preconditions
  requires _module.__default.IsSkewNumber#canCall(a#0, lowDigit#0, base#0)
     ==> _module.__default.IsSkewNumber(a#0, lowDigit#0, base#0) || LitInt(2) <= base#0;
  requires _module.__default.IsSkewNumber#canCall(a#0, lowDigit#0, base#0)
     ==> _module.__default.IsSkewNumber(a#0, lowDigit#0, base#0)
       || lowDigit#0 <= LitInt(0);
  requires _module.__default.IsSkewNumber#canCall(a#0, lowDigit#0, base#0)
     ==> _module.__default.IsSkewNumber(a#0, lowDigit#0, base#0)
       || 0 < lowDigit#0 + base#0;
  requires _module.__default.IsSkewNumber#canCall(a#0, lowDigit#0, base#0)
     ==> _module.__default.IsSkewNumber(a#0, lowDigit#0, base#0)
       || (forall i#0: int :: 
        { $Unbox(Seq#Index(a#0, i#0)): int } 
        true
           ==> (LitInt(0) <= i#0 && i#0 < Seq#Length(a#0)
               ==> lowDigit#0 <= $Unbox(Seq#Index(a#0, i#0)): int)
             && (LitInt(0) <= i#0 && i#0 < Seq#Length(a#0)
               ==> $Unbox(Seq#Index(a#0, i#0)): int < lowDigit#0 + base#0));
  requires _module.__default.IsSkewNumber#canCall(b#0, lowDigit#0, base#0)
     ==> _module.__default.IsSkewNumber(b#0, lowDigit#0, base#0) || LitInt(2) <= base#0;
  requires _module.__default.IsSkewNumber#canCall(b#0, lowDigit#0, base#0)
     ==> _module.__default.IsSkewNumber(b#0, lowDigit#0, base#0)
       || lowDigit#0 <= LitInt(0);
  requires _module.__default.IsSkewNumber#canCall(b#0, lowDigit#0, base#0)
     ==> _module.__default.IsSkewNumber(b#0, lowDigit#0, base#0)
       || 0 < lowDigit#0 + base#0;
  requires _module.__default.IsSkewNumber#canCall(b#0, lowDigit#0, base#0)
     ==> _module.__default.IsSkewNumber(b#0, lowDigit#0, base#0)
       || (forall i#1: int :: 
        { $Unbox(Seq#Index(b#0, i#1)): int } 
        true
           ==> (LitInt(0) <= i#1 && i#1 < Seq#Length(b#0)
               ==> lowDigit#0 <= $Unbox(Seq#Index(b#0, i#1)): int)
             && (LitInt(0) <= i#1 && i#1 < Seq#Length(b#0)
               ==> $Unbox(Seq#Index(b#0, i#1)): int < lowDigit#0 + base#0));
  requires Seq#Equal(a#0, _module.__default.trim($LS($LS($LZ)), a#0));
  requires Seq#Equal(b#0, _module.__default.trim($LS($LS($LZ)), b#0));
  requires _module.__default.eval($LS($LS($LZ)), a#0, base#0)
     == _module.__default.eval($LS($LS($LZ)), b#0, base#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures Seq#Equal(a#0, b#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction a#0, b#0, base#0} Impl$$_module.__default.UniqueRepresentation(a#0: Seq Box where $Is(a#0, TSeq(TInt)) && $IsAlloc(a#0, TSeq(TInt), $Heap), 
    b#0: Seq Box where $Is(b#0, TSeq(TInt)) && $IsAlloc(b#0, TSeq(TInt), $Heap), 
    lowDigit#0: int, 
    base#0: int)
   returns ($_reverifyPost: bool);
  free requires 24 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.__default.IsSkewNumber#canCall(a#0, lowDigit#0, base#0)
     && 
    _module.__default.IsSkewNumber(a#0, lowDigit#0, base#0)
     && 
    LitInt(2) <= base#0
     && 
    lowDigit#0 <= LitInt(0)
     && 0 < lowDigit#0 + base#0
     && (forall i#2: int :: 
      { $Unbox(Seq#Index(a#0, i#2)): int } 
      true
         ==> (LitInt(0) <= i#2 && i#2 < Seq#Length(a#0)
             ==> lowDigit#0 <= $Unbox(Seq#Index(a#0, i#2)): int)
           && (LitInt(0) <= i#2 && i#2 < Seq#Length(a#0)
             ==> $Unbox(Seq#Index(a#0, i#2)): int < lowDigit#0 + base#0));
  free requires _module.__default.IsSkewNumber#canCall(b#0, lowDigit#0, base#0)
     && 
    _module.__default.IsSkewNumber(b#0, lowDigit#0, base#0)
     && 
    LitInt(2) <= base#0
     && 
    lowDigit#0 <= LitInt(0)
     && 0 < lowDigit#0 + base#0
     && (forall i#3: int :: 
      { $Unbox(Seq#Index(b#0, i#3)): int } 
      true
         ==> (LitInt(0) <= i#3 && i#3 < Seq#Length(b#0)
             ==> lowDigit#0 <= $Unbox(Seq#Index(b#0, i#3)): int)
           && (LitInt(0) <= i#3 && i#3 < Seq#Length(b#0)
             ==> $Unbox(Seq#Index(b#0, i#3)): int < lowDigit#0 + base#0));
  requires Seq#Equal(a#0, _module.__default.trim($LS($LS($LZ)), a#0));
  requires Seq#Equal(b#0, _module.__default.trim($LS($LS($LZ)), b#0));
  requires _module.__default.eval($LS($LS($LZ)), a#0, base#0)
     == _module.__default.eval($LS($LS($LZ)), b#0, base#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures Seq#Equal(a#0, b#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction a#0, b#0, base#0} Impl$$_module.__default.UniqueRepresentation(a#0: Seq Box, b#0: Seq Box, lowDigit#0: int, base#0: int)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var ##digits#6: Seq Box;
  var ##base#4: int;
  var a##0_0: Seq Box;
  var lowDigit##0_0: int;
  var base##0_0: int;
  var a##0_1: Seq Box;
  var lowDigit##0_1: int;
  var base##0_1: int;
  var aa#0: int;
  var bb#0: int;
  var $rhs#0: int;
  var ##digits#7: Seq Box;
  var ##base#5: int;
  var $rhs#1: int;
  var ##digits#8: Seq Box;
  var ##base#6: int;
  var arest#0: Seq Box
     where $Is(arest#0, TSeq(TInt)) && $IsAlloc(arest#0, TSeq(TInt), $Heap);
  var brest#0: Seq Box
     where $Is(brest#0, TSeq(TInt)) && $IsAlloc(brest#0, TSeq(TInt), $Heap);
  var $rhs#2: Seq Box where $Is($rhs#2, TSeq(TInt));
  var $rhs#3: Seq Box where $Is($rhs#3, TSeq(TInt));
  var ma#0: int;
  var mb#0: int;
  var $rhs#4: int;
  var $rhs#5: int;
  var a##0: Seq Box;
  var lowDigit##0: int;
  var base##0: int;
  var a##1: Seq Box;
  var lowDigit##1: int;
  var base##1: int;
  var y#0: int;
  var ##digits#9: Seq Box;
  var ##base#7: int;
  var ##digits#10: Seq Box;
  var ##base#8: int;
  var x##0: int;
  var a##2: int;
  var ##digits#11: Seq Box;
  var ##base#9: int;
  var b##0: int;
  var ##digits#12: Seq Box;
  var ##base#10: int;
  var y##0: int;
  var ##digits#13: Seq Box;
  var ##base#11: int;
  var ##digits#14: Seq Box;
  var ##base#12: int;
  var a##3: Seq Box;
  var a##4: Seq Box;
  var a##5: Seq Box;
  var b##1: Seq Box;
  var lowDigit##2: int;
  var base##2: int;

    // AddMethodImpl: UniqueRepresentation, Impl$$_module.__default.UniqueRepresentation
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(239,0): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#a0#0: Seq Box, $ih#b0#0: Seq Box, $ih#base0#0: int :: 
      $Is($ih#a0#0, TSeq(TInt))
           && $Is($ih#b0#0, TSeq(TInt))
           && 
          _module.__default.IsSkewNumber($ih#a0#0, lowDigit#0, $ih#base0#0)
           && _module.__default.IsSkewNumber($ih#b0#0, lowDigit#0, $ih#base0#0)
           && 
          Seq#Equal($ih#a0#0, _module.__default.trim($LS($LZ), $ih#a0#0))
           && Seq#Equal($ih#b0#0, _module.__default.trim($LS($LZ), $ih#b0#0))
           && _module.__default.eval($LS($LZ), $ih#a0#0, $ih#base0#0)
             == _module.__default.eval($LS($LZ), $ih#b0#0, $ih#base0#0)
           && (Seq#Rank($ih#a0#0) < Seq#Rank(a#0)
             || (Seq#Rank($ih#a0#0) == Seq#Rank(a#0)
               && (Seq#Rank($ih#b0#0) < Seq#Rank(b#0)
                 || (Seq#Rank($ih#b0#0) == Seq#Rank(b#0)
                   && ((0 <= lowDigit#0 && lowDigit#0 < lowDigit#0)
                     || (lowDigit#0 == lowDigit#0 && 0 <= $ih#base0#0 && $ih#base0#0 < base#0))))))
         ==> Seq#Equal($ih#a0#0, $ih#b0#0));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(240,3)
    ##digits#6 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##digits#6, TSeq(TInt), $Heap);
    ##base#4 := base#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##base#4, TInt, $Heap);
    assert {:subsumption 0} LitInt(2) <= ##base#4;
    assume LitInt(2) <= ##base#4;
    assume _module.__default.eval#canCall(a#0, base#0);
    assume _module.__default.eval#canCall(a#0, base#0);
    if (_module.__default.eval($LS($LZ), a#0, base#0) == LitInt(0))
    {
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(241,17)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        a##0_0 := a#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        lowDigit##0_0 := lowDigit#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        base##0_0 := base#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.ZeroIsUnique(a##0_0, lowDigit##0_0, base##0_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(241,35)"} true;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(242,17)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        a##0_1 := b#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        lowDigit##0_1 := lowDigit#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        base##0_1 := base#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.ZeroIsUnique(a##0_1, lowDigit##0_1, base##0_1);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(242,35)"} true;
    }
    else
    {
        // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(244,16)
        assume true;
        assume true;
        ##digits#7 := a#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##digits#7, TSeq(TInt), $Heap);
        ##base#5 := base#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##base#5, TInt, $Heap);
        assert {:subsumption 0} LitInt(2) <= ##base#5;
        assume LitInt(2) <= ##base#5;
        assume _module.__default.eval#canCall(a#0, base#0);
        assume _module.__default.eval#canCall(a#0, base#0);
        $rhs#0 := _module.__default.eval($LS($LZ), a#0, base#0);
        ##digits#8 := b#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##digits#8, TSeq(TInt), $Heap);
        ##base#6 := base#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##base#6, TInt, $Heap);
        assert {:subsumption 0} LitInt(2) <= ##base#6;
        assume LitInt(2) <= ##base#6;
        assume _module.__default.eval#canCall(b#0, base#0);
        assume _module.__default.eval#canCall(b#0, base#0);
        $rhs#1 := _module.__default.eval($LS($LZ), b#0, base#0);
        aa#0 := $rhs#0;
        bb#0 := $rhs#1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(244,46)"} true;
        // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(245,22)
        assume true;
        assume true;
        assert 0 <= LitInt(1) && LitInt(1) <= Seq#Length(a#0);
        assume true;
        $rhs#2 := Seq#Drop(a#0, LitInt(1));
        assert 0 <= LitInt(1) && LitInt(1) <= Seq#Length(b#0);
        assume true;
        $rhs#3 := Seq#Drop(b#0, LitInt(1));
        arest#0 := $rhs#2;
        brest#0 := $rhs#3;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(245,38)"} true;
        // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(246,16)
        assume true;
        assume true;
        assert base#0 != 0;
        assume true;
        $rhs#4 := Mod(aa#0, base#0);
        assert base#0 != 0;
        assume true;
        $rhs#5 := Mod(bb#0, base#0);
        ma#0 := $rhs#4;
        mb#0 := $rhs#5;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(246,38)"} true;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(248,5)
        if (LitInt(0) <= ma#0)
        {
        }

        if (LitInt(0) <= ma#0 && ma#0 < base#0)
        {
            if (LitInt(0) <= mb#0)
            {
            }
        }

        assume true;
        assert {:subsumption 0} LitInt(0) <= ma#0;
        assert {:subsumption 0} ma#0 < base#0;
        assert {:subsumption 0} LitInt(0) <= mb#0;
        assert {:subsumption 0} mb#0 < base#0;
        assume LitInt(0) <= ma#0 && ma#0 < base#0 && LitInt(0) <= mb#0 && mb#0 < base#0;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(249,37)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        a##0 := a#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        lowDigit##0 := lowDigit#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        base##0 := base#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.LeastSignificantDigitIsAlmostMod(a##0, lowDigit##0, base##0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(249,55)"} true;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(250,37)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        a##1 := b#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        lowDigit##1 := lowDigit#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        base##1 := base#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.LeastSignificantDigitIsAlmostMod(a##1, lowDigit##1, base##1);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(250,55)"} true;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(251,5)
        if (ma#0 == mb#0)
        {
            assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
            assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(b#0);
        }

        assume true;
        assert {:subsumption 0} ma#0 == mb#0;
        assert {:subsumption 0} $Unbox(Seq#Index(a#0, LitInt(0))): int == $Unbox(Seq#Index(b#0, LitInt(0))): int;
        assume ma#0 == mb#0
           && $Unbox(Seq#Index(a#0, LitInt(0))): int == $Unbox(Seq#Index(b#0, LitInt(0))): int;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(252,11)
        assume true;
        assert 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
        assume true;
        y#0 := $Unbox(Seq#Index(a#0, LitInt(0))): int;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(252,17)"} true;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(254,5)
        ##digits#9 := arest#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##digits#9, TSeq(TInt), $Heap);
        ##base#7 := base#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##base#7, TInt, $Heap);
        assert {:subsumption 0} LitInt(2) <= ##base#7;
        assume _module.__default.eval#canCall(arest#0, base#0);
        assume _module.__default.eval#canCall(arest#0, base#0);
        assert {:subsumption 0} aa#0
           == Mul(base#0, _module.__default.eval($LS($LS($LZ)), arest#0, base#0)) + y#0;
        assume aa#0 == Mul(base#0, _module.__default.eval($LS($LZ), arest#0, base#0)) + y#0;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(255,5)
        ##digits#10 := brest#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##digits#10, TSeq(TInt), $Heap);
        ##base#8 := base#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##base#8, TInt, $Heap);
        assert {:subsumption 0} LitInt(2) <= ##base#8;
        assume _module.__default.eval#canCall(brest#0, base#0);
        assume _module.__default.eval#canCall(brest#0, base#0);
        assert {:subsumption 0} bb#0
           == Mul(base#0, _module.__default.eval($LS($LS($LZ)), brest#0, base#0)) + y#0;
        assume bb#0 == Mul(base#0, _module.__default.eval($LS($LZ), brest#0, base#0)) + y#0;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(256,15)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        x##0 := base#0;
        ##digits#11 := arest#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##digits#11, TSeq(TInt), $Heap);
        ##base#9 := base#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##base#9, TInt, $Heap);
        assert {:subsumption 0} LitInt(2) <= ##base#9;
        assume LitInt(2) <= ##base#9;
        assume _module.__default.eval#canCall(arest#0, base#0);
        assume _module.__default.eval#canCall(arest#0, base#0);
        // ProcessCallStmt: CheckSubrange
        a##2 := _module.__default.eval($LS($LZ), arest#0, base#0);
        ##digits#12 := brest#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##digits#12, TSeq(TInt), $Heap);
        ##base#10 := base#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##base#10, TInt, $Heap);
        assert {:subsumption 0} LitInt(2) <= ##base#10;
        assume LitInt(2) <= ##base#10;
        assume _module.__default.eval#canCall(brest#0, base#0);
        assume _module.__default.eval#canCall(brest#0, base#0);
        // ProcessCallStmt: CheckSubrange
        b##0 := _module.__default.eval($LS($LZ), brest#0, base#0);
        assume true;
        // ProcessCallStmt: CheckSubrange
        y##0 := y#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.MulInverse(x##0, a##2, b##0, y##0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(256,61)"} true;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(257,5)
        ##digits#13 := arest#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##digits#13, TSeq(TInt), $Heap);
        ##base#11 := base#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##base#11, TInt, $Heap);
        assert {:subsumption 0} LitInt(2) <= ##base#11;
        assume _module.__default.eval#canCall(arest#0, base#0);
        ##digits#14 := brest#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##digits#14, TSeq(TInt), $Heap);
        ##base#12 := base#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##base#12, TInt, $Heap);
        assert {:subsumption 0} LitInt(2) <= ##base#12;
        assume _module.__default.eval#canCall(brest#0, base#0);
        assume _module.__default.eval#canCall(arest#0, base#0)
           && _module.__default.eval#canCall(brest#0, base#0);
        assert {:subsumption 0} _module.__default.eval($LS($LS($LZ)), arest#0, base#0)
           == _module.__default.eval($LS($LS($LZ)), brest#0, base#0);
        assume _module.__default.eval($LS($LZ), arest#0, base#0)
           == _module.__default.eval($LS($LZ), brest#0, base#0);
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(259,17)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        a##3 := a#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.TrimProperty(a##3);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(259,19)"} true;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(260,17)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        a##4 := b#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.TrimProperty(a##4);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(260,19)"} true;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(261,25)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        a##5 := arest#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        b##1 := brest#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        lowDigit##2 := lowDigit#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        base##2 := base#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assert 0 <= lowDigit#0
           || Seq#Rank(a##5) < Seq#Rank(a#0)
           || Seq#Rank(b##1) < Seq#Rank(b#0)
           || lowDigit##2 == lowDigit#0;
        assert 0 <= base#0
           || Seq#Rank(a##5) < Seq#Rank(a#0)
           || Seq#Rank(b##1) < Seq#Rank(b#0)
           || lowDigit##2 < lowDigit#0
           || base##2 == base#0;
        assert Seq#Rank(a##5) < Seq#Rank(a#0)
           || (Seq#Rank(a##5) == Seq#Rank(a#0)
             && (Seq#Rank(b##1) < Seq#Rank(b#0)
               || (Seq#Rank(b##1) == Seq#Rank(b#0)
                 && (lowDigit##2 < lowDigit#0 || (lowDigit##2 == lowDigit#0 && base##2 < base#0)))));
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.UniqueRepresentation(a##5, b##1, lowDigit##2, base##2);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(261,54)"} true;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(262,5)
        if (Seq#Equal(Seq#Append(Seq#Build(Seq#Empty(): Seq Box, $Box(y#0)), arest#0), a#0))
        {
        }

        assume true;
        assert {:subsumption 0} Seq#Equal(Seq#Append(Seq#Build(Seq#Empty(): Seq Box, $Box(y#0)), arest#0), a#0);
        assert {:subsumption 0} Seq#Equal(Seq#Append(Seq#Build(Seq#Empty(): Seq Box, $Box(y#0)), brest#0), b#0);
        assume Seq#Equal(Seq#Append(Seq#Build(Seq#Empty(): Seq Box, $Box(y#0)), arest#0), a#0)
           && Seq#Equal(Seq#Append(Seq#Build(Seq#Empty(): Seq Box, $Box(y#0)), brest#0), b#0);
    }
}



procedure {:induction false} CheckWellformed$$_module.__default.ZeroIsUnique(a#0: Seq Box where $Is(a#0, TSeq(TInt)) && $IsAlloc(a#0, TSeq(TInt), $Heap), 
    lowDigit#0: int, 
    base#0: int);
  free requires 16 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:induction false} CheckWellformed$$_module.__default.ZeroIsUnique(a#0: Seq Box, lowDigit#0: int, base#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##digits#0: Seq Box;
  var ##lowDigit#0: int;
  var ##base#0: int;
  var ##digits#1: Seq Box;
  var ##digits#2: Seq Box;
  var ##base#1: int;

    // AddMethodImpl: ZeroIsUnique, CheckWellformed$$_module.__default.ZeroIsUnique
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(266,25): initial state"} true;
    ##digits#0 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##digits#0, TSeq(TInt), $Heap);
    ##lowDigit#0 := lowDigit#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##lowDigit#0, TInt, $Heap);
    ##base#0 := base#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##base#0, TInt, $Heap);
    assume _module.__default.IsSkewNumber#canCall(a#0, lowDigit#0, base#0);
    assume _module.__default.IsSkewNumber(a#0, lowDigit#0, base#0);
    ##digits#1 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##digits#1, TSeq(TInt), $Heap);
    assume _module.__default.trim#canCall(a#0);
    assume Seq#Equal(a#0, _module.__default.trim($LS($LZ), a#0));
    ##digits#2 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##digits#2, TSeq(TInt), $Heap);
    ##base#1 := base#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##base#1, TInt, $Heap);
    assert {:subsumption 0} LitInt(2) <= ##base#1;
    assume LitInt(2) <= ##base#1;
    assume _module.__default.eval#canCall(a#0, base#0);
    assume _module.__default.eval($LS($LZ), a#0, base#0) == LitInt(0);
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(270,12): post-state"} true;
    assume Seq#Equal(a#0, Seq#Empty(): Seq Box);
}



procedure {:induction false} Call$$_module.__default.ZeroIsUnique(a#0: Seq Box where $Is(a#0, TSeq(TInt)) && $IsAlloc(a#0, TSeq(TInt), $Heap), 
    lowDigit#0: int, 
    base#0: int);
  // user-defined preconditions
  requires _module.__default.IsSkewNumber#canCall(a#0, lowDigit#0, base#0)
     ==> _module.__default.IsSkewNumber(a#0, lowDigit#0, base#0) || LitInt(2) <= base#0;
  requires _module.__default.IsSkewNumber#canCall(a#0, lowDigit#0, base#0)
     ==> _module.__default.IsSkewNumber(a#0, lowDigit#0, base#0)
       || lowDigit#0 <= LitInt(0);
  requires _module.__default.IsSkewNumber#canCall(a#0, lowDigit#0, base#0)
     ==> _module.__default.IsSkewNumber(a#0, lowDigit#0, base#0)
       || 0 < lowDigit#0 + base#0;
  requires _module.__default.IsSkewNumber#canCall(a#0, lowDigit#0, base#0)
     ==> _module.__default.IsSkewNumber(a#0, lowDigit#0, base#0)
       || (forall i#0: int :: 
        { $Unbox(Seq#Index(a#0, i#0)): int } 
        true
           ==> (LitInt(0) <= i#0 && i#0 < Seq#Length(a#0)
               ==> lowDigit#0 <= $Unbox(Seq#Index(a#0, i#0)): int)
             && (LitInt(0) <= i#0 && i#0 < Seq#Length(a#0)
               ==> $Unbox(Seq#Index(a#0, i#0)): int < lowDigit#0 + base#0));
  requires Seq#Equal(a#0, _module.__default.trim($LS($LS($LZ)), a#0));
  requires _module.__default.eval($LS($LS($LZ)), a#0, base#0) == LitInt(0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures Seq#Equal(a#0, Seq#Empty(): Seq Box);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:induction false} Impl$$_module.__default.ZeroIsUnique(a#0: Seq Box where $Is(a#0, TSeq(TInt)) && $IsAlloc(a#0, TSeq(TInt), $Heap), 
    lowDigit#0: int, 
    base#0: int)
   returns ($_reverifyPost: bool);
  free requires 16 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.__default.IsSkewNumber#canCall(a#0, lowDigit#0, base#0)
     && 
    _module.__default.IsSkewNumber(a#0, lowDigit#0, base#0)
     && 
    LitInt(2) <= base#0
     && 
    lowDigit#0 <= LitInt(0)
     && 0 < lowDigit#0 + base#0
     && (forall i#1: int :: 
      { $Unbox(Seq#Index(a#0, i#1)): int } 
      true
         ==> (LitInt(0) <= i#1 && i#1 < Seq#Length(a#0)
             ==> lowDigit#0 <= $Unbox(Seq#Index(a#0, i#1)): int)
           && (LitInt(0) <= i#1 && i#1 < Seq#Length(a#0)
             ==> $Unbox(Seq#Index(a#0, i#1)): int < lowDigit#0 + base#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures Seq#Equal(a#0, Seq#Empty(): Seq Box);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:induction false} Impl$$_module.__default.ZeroIsUnique(a#0: Seq Box, lowDigit#0: int, base#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var a1#0_0: int;
  var ##digits#0_0: Seq Box;
  var ##base#0_0: int;
  var b#0_0: int;
  var ##digits#0_1: Seq Box;
  var ##base#0_1: int;
  var $Heap_at_0_0: Heap;
  var a##0_0_5_0: int;
  var x##0_0_5_0: int;
  var y##0_0_5_0: int;
  var a##0_1_5_0: int;
  var x##0_1_5_0: int;
  var y##0_1_5_0: int;
  var ##digits#0_2_0: Seq Box;
  var ##lowDigit#0_2_0: int;
  var ##base#0_2_0: int;
  var d#0_2_0: int;
  var ##digits#0_2_1: Seq Box;
  var a##0_2_0: Seq Box;
  var a##0_2_1: Seq Box;
  var lowDigit##0_2_0: int;
  var base##0_2_0: int;
  var ##digits#0_2_1_1_0: Seq Box;
  var ##digits#0_2_1_2_0: Seq Box;
  var ##digits#0_2_1_2_1: Seq Box;
  var ##digits#0_2_1_3_0: Seq Box;
  var ##digits#0_2_1_3_1: Seq Box;
  var ##digits#0_2_1_4_0: Seq Box;
  var ##digits#0_2_1_4_1: Seq Box;
  var ##digits#0_2_1_5_0: Seq Box;
  var ##digits#0_2_1_5_1: Seq Box;
  var ##digits#0_2_1_6_0: Seq Box;

    // AddMethodImpl: ZeroIsUnique, Impl$$_module.__default.ZeroIsUnique
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(271,0): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(272,3)
    assume true;
    if (!Seq#Equal(a#0, Seq#Empty(): Seq Box))
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(273,12)
        assume true;
        assert 0 <= LitInt(1) && LitInt(1) <= Seq#Length(a#0);
        ##digits#0_0 := Seq#Drop(a#0, LitInt(1));
        // assume allocatedness for argument to function
        assume $IsAlloc(##digits#0_0, TSeq(TInt), $Heap);
        ##base#0_0 := base#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##base#0_0, TInt, $Heap);
        assert {:subsumption 0} LitInt(2) <= ##base#0_0;
        assume LitInt(2) <= ##base#0_0;
        assume _module.__default.eval#canCall(Seq#Drop(a#0, LitInt(1)), base#0);
        assume _module.__default.eval#canCall(Seq#Drop(a#0, LitInt(1)), base#0);
        a1#0_0 := _module.__default.eval($LS($LZ), Seq#Drop(a#0, LitInt(1)), base#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(273,32)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(274,11)
        assume true;
        assume true;
        b#0_0 := Mul(base#0, a1#0_0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(274,22)"} true;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(275,5)
        assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
        ##digits#0_1 := a#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##digits#0_1, TSeq(TInt), $Heap);
        ##base#0_1 := base#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##base#0_1, TInt, $Heap);
        assert {:subsumption 0} LitInt(2) <= ##base#0_1;
        assume _module.__default.eval#canCall(a#0, base#0);
        assume _module.__default.eval#canCall(a#0, base#0);
        assert {:subsumption 0} $Unbox(Seq#Index(a#0, LitInt(0))): int + b#0_0
           == _module.__default.eval($LS($LS($LZ)), a#0, base#0);
        assume $Unbox(Seq#Index(a#0, LitInt(0))): int + b#0_0
           == _module.__default.eval($LS($LZ), a#0, base#0);
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(277,5)
        if (0 - base#0 < lowDigit#0)
        {
            assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
        }

        if (0 - base#0 < lowDigit#0 && lowDigit#0 <= $Unbox(Seq#Index(a#0, LitInt(0))): int)
        {
            assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
        }

        if (0 - base#0 < lowDigit#0
           && lowDigit#0 <= $Unbox(Seq#Index(a#0, LitInt(0))): int
           && $Unbox(Seq#Index(a#0, LitInt(0))): int < lowDigit#0 + base#0)
        {
        }

        assume true;
        if (*)
        {
            // ----- assert statement proof ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(277,5)
            // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(278,7)
            assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
            assume true;
            assert Seq#Contains(a#0, Seq#Index(a#0, LitInt(0)));
            assert {:subsumption 0} 0 - base#0 < lowDigit#0;
            assert {:subsumption 0} lowDigit#0 <= $Unbox(Seq#Index(a#0, LitInt(0))): int;
            assert {:subsumption 0} $Unbox(Seq#Index(a#0, LitInt(0))): int < lowDigit#0 + base#0;
            assert {:subsumption 0} lowDigit#0 + base#0 <= base#0;
            assume false;
        }

        $Heap_at_0_0 := $Heap;
        // ----- calc statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(283,5)
        // Assume Fuel Constant
        if (*)
        {
            // ----- assert wf[initial] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(283,5)
            assume true;
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(283,5)
            assume true;
            // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(283,5)
            assume a1#0_0 <= LitInt(-1);
            // ----- Hint0 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(283,5)
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(285,25)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            a##0_0_5_0 := base#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            x##0_0_5_0 := a1#0_0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            y##0_0_5_0 := LitInt(-1);
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call Call$$_module.__default.MulIsMonotonic(a##0_0_5_0, x##0_0_5_0, y##0_0_5_0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(285,38)"} true;
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(283,5)
            assume true;
            // ----- assert line0 ==> line1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(283,5)
            assert {:subsumption 0} a1#0_0 <= LitInt(-1) ==> Mul(base#0, a1#0_0) <= Mul(base#0, LitInt(-1));
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(283,5)
            assume true;
            // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(283,5)
            assume Mul(base#0, a1#0_0) <= Mul(base#0, LitInt(-1));
            // ----- Hint1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(283,5)
            // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(287,12)
            assume true;
            assert Mul(base#0, a1#0_0) == b#0_0;
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(283,5)
            assume true;
            // ----- assert line1 ==> line2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(283,5)
            assert {:subsumption 0} Mul(base#0, a1#0_0) <= Mul(base#0, LitInt(-1))
               ==> b#0_0 <= Mul(base#0, LitInt(-1));
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(283,5)
            assume true;
            // ----- Hint2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(283,5)
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(283,5)
            assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
            assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
            assume true;
            // ----- assert line2 == line3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(283,5)
            assert {:subsumption 0} (b#0_0 <= Mul(base#0, LitInt(-1)))
               == ($Unbox(Seq#Index(a#0, LitInt(0))): int + b#0_0
                 <= $Unbox(Seq#Index(a#0, LitInt(0))): int - base#0);
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(283,5)
            assume {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
            assume {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
            assume true;
            // ----- Hint3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(283,5)
            // ----- reveal statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(291,11)
            assume _module.__default.eval($LS($LZ), a#0, base#0) == LitInt(0);
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(283,5)
            assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
            assume true;
            // ----- assert line3 == line4 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(283,5)
            assert {:subsumption 0} ($Unbox(Seq#Index(a#0, LitInt(0))): int + b#0_0
                 <= $Unbox(Seq#Index(a#0, LitInt(0))): int - base#0)
               == (LitInt(0) <= $Unbox(Seq#Index(a#0, LitInt(0))): int - base#0);
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(283,5)
            assume {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
            assume true;
            // ----- Hint4 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(283,5)
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(283,5)
            assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
            assume true;
            // ----- assert line4 == line5 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(283,5)
            assert {:subsumption 0} (LitInt(0) <= $Unbox(Seq#Index(a#0, LitInt(0))): int - base#0)
               == (base#0 <= $Unbox(Seq#Index(a#0, LitInt(0))): int);
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(283,5)
            assume {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
            assume true;
            // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(283,5)
            assume base#0 <= $Unbox(Seq#Index(a#0, LitInt(0))): int;
            // ----- Hint5 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(283,5)
            // ----- reveal statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(295,12)
            assume 0 - base#0 < lowDigit#0
               && lowDigit#0 <= $Unbox(Seq#Index(a#0, LitInt(0))): int
               && $Unbox(Seq#Index(a#0, LitInt(0))): int < lowDigit#0 + base#0
               && lowDigit#0 + base#0 <= base#0;
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(283,5)
            assume true;
            // ----- assert line5 ==> line6 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(283,5)
            assert {:subsumption 0} base#0 <= $Unbox(Seq#Index(a#0, LitInt(0))): int ==> Lit(false);
            assume false;
        }

        assume a1#0_0 <= LitInt(-1) ==> false;
        // ----- calc statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(299,5)
        // Assume Fuel Constant
        if (*)
        {
            // ----- assert wf[initial] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(299,5)
            assume true;
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(299,5)
            assume true;
            // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(299,5)
            assume LitInt(1) <= a1#0_0;
            // ----- Hint0 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(299,5)
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(301,25)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            a##0_1_5_0 := base#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            x##0_1_5_0 := LitInt(1);
            assume true;
            // ProcessCallStmt: CheckSubrange
            y##0_1_5_0 := a1#0_0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call Call$$_module.__default.MulIsMonotonic(a##0_1_5_0, x##0_1_5_0, y##0_1_5_0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(301,37)"} true;
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(299,5)
            assume true;
            // ----- assert line0 ==> line1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(299,5)
            assert {:subsumption 0} LitInt(1) <= a1#0_0 ==> Mul(base#0, LitInt(1)) <= Mul(base#0, a1#0_0);
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(299,5)
            assume true;
            // ----- Hint1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(299,5)
            // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(303,11)
            assume true;
            assert Mul(base#0, LitInt(1)) == base#0;
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(299,5)
            assume true;
            // ----- assert line1 == line2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(299,5)
            assert {:subsumption 0} (Mul(base#0, LitInt(1)) <= Mul(base#0, a1#0_0))
               == (base#0 <= Mul(base#0, a1#0_0));
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(299,5)
            assume true;
            // ----- Hint2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(299,5)
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(299,5)
            assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
            assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
            assume true;
            // ----- assert line2 == line3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(299,5)
            assert {:subsumption 0} (base#0 <= Mul(base#0, a1#0_0))
               == ($Unbox(Seq#Index(a#0, LitInt(0))): int + base#0
                 <= $Unbox(Seq#Index(a#0, LitInt(0))): int + Mul(base#0, a1#0_0));
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(299,5)
            assume {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
            assume {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
            assume true;
            // ----- Hint3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(299,5)
            // ----- reveal statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(307,11)
            assume _module.__default.eval($LS($LZ), a#0, base#0) == LitInt(0);
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(299,5)
            assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
            assume true;
            // ----- assert line3 == line4 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(299,5)
            assert {:subsumption 0} ($Unbox(Seq#Index(a#0, LitInt(0))): int + base#0
                 <= $Unbox(Seq#Index(a#0, LitInt(0))): int + Mul(base#0, a1#0_0))
               == ($Unbox(Seq#Index(a#0, LitInt(0))): int + base#0 <= LitInt(0));
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(299,5)
            assume {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
            assume true;
            // ----- Hint4 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(299,5)
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(299,5)
            assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
            assume true;
            // ----- assert line4 == line5 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(299,5)
            assert {:subsumption 0} ($Unbox(Seq#Index(a#0, LitInt(0))): int + base#0 <= LitInt(0))
               == ($Unbox(Seq#Index(a#0, LitInt(0))): int <= 0 - base#0);
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(299,5)
            assume {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
            assume true;
            // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(299,5)
            assume $Unbox(Seq#Index(a#0, LitInt(0))): int <= 0 - base#0;
            // ----- Hint5 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(299,5)
            // ----- reveal statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(311,12)
            assume 0 - base#0 < lowDigit#0
               && lowDigit#0 <= $Unbox(Seq#Index(a#0, LitInt(0))): int
               && $Unbox(Seq#Index(a#0, LitInt(0))): int < lowDigit#0 + base#0
               && lowDigit#0 + base#0 <= base#0;
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(299,5)
            assume true;
            // ----- assert line5 ==> line6 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(299,5)
            assert {:subsumption 0} $Unbox(Seq#Index(a#0, LitInt(0))): int <= 0 - base#0 ==> Lit(false);
            assume false;
        }

        assume LitInt(1) <= a1#0_0 ==> false;
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(315,5)
        assume true;
        if (a1#0_0 == LitInt(0))
        {
            // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(316,7)
            assume true;
            if (*)
            {
                // ----- assert statement proof ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(316,7)
                // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(317,9)
                assert {:subsumption 0} 0 <= LitInt(1) && LitInt(1) <= Seq#Length(a#0);
                ##digits#0_2_0 := Seq#Drop(a#0, LitInt(1));
                // assume allocatedness for argument to function
                assume $IsAlloc(##digits#0_2_0, TSeq(TInt), $Heap);
                ##lowDigit#0_2_0 := lowDigit#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##lowDigit#0_2_0, TInt, $Heap);
                ##base#0_2_0 := base#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##base#0_2_0, TInt, $Heap);
                assume _module.__default.IsSkewNumber#canCall(Seq#Drop(a#0, LitInt(1)), lowDigit#0, base#0);
                assume _module.__default.IsSkewNumber#canCall(Seq#Drop(a#0, LitInt(1)), lowDigit#0, base#0);
                if (*)
                {
                    // ----- assert statement proof ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(317,9)
                    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(318,11)
                    // Begin Comprehension WF check
                    havoc d#0_2_0;
                    if (true)
                    {
                        assert {:subsumption 0} 0 <= LitInt(1) && LitInt(1) <= Seq#Length(a#0);
                        if (Seq#Contains(Seq#Drop(a#0, LitInt(1)), $Box(d#0_2_0)))
                        {
                        }
                    }

                    // End Comprehension WF check
                    assume true;
                    assert (forall d#0_2_1: int :: 
                      { Seq#Contains(a#0, $Box(d#0_2_1)) } 
                        { Seq#Contains(Seq#Drop(a#0, 1), $Box(d#0_2_1)) } 
                      true
                         ==> 
                        Seq#Contains(Seq#Drop(a#0, LitInt(1)), $Box(d#0_2_1))
                         ==> Seq#Contains(a#0, $Box(d#0_2_1)));
                    assert {:subsumption 0} _module.__default.IsSkewNumber#canCall(Seq#Drop(a#0, LitInt(1)), lowDigit#0, base#0)
                       ==> _module.__default.IsSkewNumber(Seq#Drop(a#0, LitInt(1)), lowDigit#0, base#0)
                         || LitInt(2) <= base#0;
                    assert {:subsumption 0} _module.__default.IsSkewNumber#canCall(Seq#Drop(a#0, LitInt(1)), lowDigit#0, base#0)
                       ==> _module.__default.IsSkewNumber(Seq#Drop(a#0, LitInt(1)), lowDigit#0, base#0)
                         || lowDigit#0 <= LitInt(0);
                    assert {:subsumption 0} _module.__default.IsSkewNumber#canCall(Seq#Drop(a#0, LitInt(1)), lowDigit#0, base#0)
                       ==> _module.__default.IsSkewNumber(Seq#Drop(a#0, LitInt(1)), lowDigit#0, base#0)
                         || 0 < lowDigit#0 + base#0;
                    assert {:subsumption 0} _module.__default.IsSkewNumber#canCall(Seq#Drop(a#0, LitInt(1)), lowDigit#0, base#0)
                       ==> _module.__default.IsSkewNumber(Seq#Drop(a#0, LitInt(1)), lowDigit#0, base#0)
                         || (forall i#0_2_0: int :: 
                          { $Unbox(Seq#Index(Seq#Drop(a#0, 1), i#0_2_0)): int } 
                          true
                             ==> (LitInt(0) <= i#0_2_0 && i#0_2_0 < Seq#Length(Seq#Drop(a#0, LitInt(1)))
                                 ==> lowDigit#0 <= $Unbox(Seq#Index(Seq#Drop(a#0, LitInt(1)), i#0_2_0)): int)
                               && (LitInt(0) <= i#0_2_0 && i#0_2_0 < Seq#Length(Seq#Drop(a#0, LitInt(1)))
                                 ==> $Unbox(Seq#Index(Seq#Drop(a#0, LitInt(1)), i#0_2_0)): int < lowDigit#0 + base#0));
                    assume false;
                }

                assume _module.__default.IsSkewNumber(Seq#Drop(a#0, LitInt(1)), lowDigit#0, base#0);
                // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(320,9)
                assert {:subsumption 0} 0 <= LitInt(1) && LitInt(1) <= Seq#Length(a#0);
                assert {:subsumption 0} 0 <= LitInt(1) && LitInt(1) <= Seq#Length(a#0);
                ##digits#0_2_1 := Seq#Drop(a#0, LitInt(1));
                // assume allocatedness for argument to function
                assume $IsAlloc(##digits#0_2_1, TSeq(TInt), $Heap);
                assume _module.__default.trim#canCall(Seq#Drop(a#0, LitInt(1)));
                assume _module.__default.trim#canCall(Seq#Drop(a#0, LitInt(1)));
                if (*)
                {
                    // ----- assert statement proof ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(320,9)
                    // ----- reveal statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(321,11)
                    assume Seq#Equal(a#0, _module.__default.trim($LS($LZ), a#0));
                    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(322,23)
                    // TrCallStmt: Before ProcessCallStmt
                    assume true;
                    // ProcessCallStmt: CheckSubrange
                    a##0_2_0 := a#0;
                    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                    // ProcessCallStmt: Make the call
                    call Call$$_module.__default.TrimProperty(a##0_2_0);
                    // TrCallStmt: After ProcessCallStmt
                    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(322,25)"} true;
                    assert {:subsumption 0} Seq#Equal(Seq#Drop(a#0, LitInt(1)), 
                      _module.__default.trim($LS($LS($LZ)), Seq#Drop(a#0, LitInt(1))));
                    assume false;
                }

                assume Seq#Equal(Seq#Drop(a#0, LitInt(1)), 
                  _module.__default.trim($LS($LZ), Seq#Drop(a#0, LitInt(1))));
                // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(324,21)
                // TrCallStmt: Before ProcessCallStmt
                assert 0 <= LitInt(1) && LitInt(1) <= Seq#Length(a#0);
                assume true;
                // ProcessCallStmt: CheckSubrange
                a##0_2_1 := Seq#Drop(a#0, LitInt(1));
                assume true;
                // ProcessCallStmt: CheckSubrange
                lowDigit##0_2_0 := lowDigit#0;
                assume true;
                // ProcessCallStmt: CheckSubrange
                base##0_2_0 := base#0;
                assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assert 0 <= lowDigit#0
                   || Seq#Rank(a##0_2_1) < Seq#Rank(a#0)
                   || lowDigit##0_2_0 == lowDigit#0;
                assert 0 <= base#0
                   || Seq#Rank(a##0_2_1) < Seq#Rank(a#0)
                   || lowDigit##0_2_0 < lowDigit#0
                   || base##0_2_0 == base#0;
                assert Seq#Rank(a##0_2_1) < Seq#Rank(a#0)
                   || (Seq#Rank(a##0_2_1) == Seq#Rank(a#0)
                     && (lowDigit##0_2_0 < lowDigit#0
                       || (lowDigit##0_2_0 == lowDigit#0 && base##0_2_0 < base#0)));
                // ProcessCallStmt: Make the call
                call Call$$_module.__default.ZeroIsUnique(a##0_2_1, lowDigit##0_2_0, base##0_2_0);
                // TrCallStmt: After ProcessCallStmt
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(324,44)"} true;
                assert Seq#Length(a#0) == LitInt(1);
                assume false;
            }

            assume Seq#Length(a#0) == LitInt(1);
            // ----- calc statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(327,7)
            // Assume Fuel Constant
            if (*)
            {
                // ----- assert wf[initial] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(327,7)
                assume true;
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(327,7)
                assume true;
                // ----- Hint0 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(327,7)
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(327,7)
                assume true;
                // ----- assert line0 == line1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(327,7)
                assert {:subsumption 0} Lit(true) == (a1#0_0 == LitInt(0));
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(327,7)
                assume true;
                // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(327,7)
                assume a1#0_0 == LitInt(0);
                // ----- Hint1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(327,7)
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(327,7)
                assume true;
                // ----- assert line1 ==> line2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(327,7)
                assert {:subsumption 0} a1#0_0 == LitInt(0) ==> Mul(base#0, a1#0_0) == LitInt(0);
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(327,7)
                assume true;
                // ----- Hint2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(327,7)
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(327,7)
                assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
                assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
                assume true;
                // ----- assert line2 == line3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(327,7)
                assert {:subsumption 0} (Mul(base#0, a1#0_0)
                   == LitInt(0))
                   == 
                  ($Unbox(Seq#Index(a#0, LitInt(0))): int + Mul(base#0, a1#0_0)
                   == $Unbox(Seq#Index(a#0, LitInt(0))): int);
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(327,7)
                assume {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
                assume {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
                assume true;
                // ----- Hint3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(327,7)
                // ----- reveal statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(335,13)
                assume _module.__default.eval($LS($LZ), a#0, base#0) == LitInt(0);
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(327,7)
                assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
                assume true;
                // ----- assert line3 == line4 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(327,7)
                assert {:subsumption 0} ($Unbox(Seq#Index(a#0, LitInt(0))): int + Mul(base#0, a1#0_0)
                   == $Unbox(Seq#Index(a#0, LitInt(0))): int)
                   == 
                  (LitInt(0)
                   == $Unbox(Seq#Index(a#0, LitInt(0))): int);
                assume false;
            }

            assume true ==> LitInt(0) == $Unbox(Seq#Index(a#0, LitInt(0))): int;
            // ----- calc statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(339,7)
            // Assume Fuel Constant
            if (*)
            {
                // ----- assert wf[initial] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(339,7)
                assume true;
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(339,7)
                assume true;
                // ----- Hint0 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(339,7)
                // ----- reveal statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(341,13)
                assume Seq#Equal(a#0, _module.__default.trim($LS($LZ), a#0));
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(339,7)
                ##digits#0_2_1_6_0 := a#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##digits#0_2_1_6_0, TSeq(TInt), $Heap);
                assume _module.__default.trim#canCall(a#0);
                assume _module.__default.trim#canCall(a#0);
                // ----- assert line0 == line1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(339,7)
                assert {:subsumption 0} Seq#Equal(a#0, _module.__default.trim($LS($LS($LZ)), a#0));
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(339,7)
                ##digits#0_2_1_5_0 := a#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##digits#0_2_1_5_0, TSeq(TInt), $Heap);
                assume _module.__default.trim#canCall(a#0);
                assume _module.__default.trim#canCall(a#0);
                // ----- Hint1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(339,7)
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(339,7)
                if (Seq#Length(a#0) != 0)
                {
                    assert {:subsumption 0} 0 <= Seq#Length(a#0) - 1 && Seq#Length(a#0) - 1 < Seq#Length(a#0);
                }

                if (Seq#Length(a#0) != 0
                   && $Unbox(Seq#Index(a#0, Seq#Length(a#0) - 1)): int == LitInt(0))
                {
                    assert {:subsumption 0} 0 <= Seq#Length(a#0) - 1 && Seq#Length(a#0) - 1 <= Seq#Length(a#0);
                    ##digits#0_2_1_5_1 := Seq#Take(a#0, Seq#Length(a#0) - 1);
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##digits#0_2_1_5_1, TSeq(TInt), $Heap);
                    assume _module.__default.trim#canCall(Seq#Take(a#0, Seq#Length(a#0) - 1));
                }
                else
                {
                }

                assume Seq#Length(a#0) != 0
                     && $Unbox(Seq#Index(a#0, Seq#Length(a#0) - 1)): int == LitInt(0)
                   ==> _module.__default.trim#canCall(Seq#Take(a#0, Seq#Length(a#0) - 1));
                // ----- assert line1 == line2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(339,7)
                assert {:subsumption 0} Seq#Equal(_module.__default.trim($LS($LS($LZ)), a#0), 
                  (if Seq#Length(a#0) != 0
                       && $Unbox(Seq#Index(a#0, Seq#Length(a#0) - 1)): int == LitInt(0)
                     then _module.__default.trim($LS($LS($LZ)), Seq#Take(a#0, Seq#Length(a#0) - 1))
                     else a#0));
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(339,7)
                if (Seq#Length(a#0) != 0)
                {
                    assume {:subsumption 0} 0 <= Seq#Length(a#0) - 1 && Seq#Length(a#0) - 1 < Seq#Length(a#0);
                }

                if (Seq#Length(a#0) != 0
                   && $Unbox(Seq#Index(a#0, Seq#Length(a#0) - 1)): int == LitInt(0))
                {
                    assume {:subsumption 0} 0 <= Seq#Length(a#0) - 1 && Seq#Length(a#0) - 1 <= Seq#Length(a#0);
                    ##digits#0_2_1_4_0 := Seq#Take(a#0, Seq#Length(a#0) - 1);
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##digits#0_2_1_4_0, TSeq(TInt), $Heap);
                    assume _module.__default.trim#canCall(Seq#Take(a#0, Seq#Length(a#0) - 1));
                }
                else
                {
                }

                assume Seq#Length(a#0) != 0
                     && $Unbox(Seq#Index(a#0, Seq#Length(a#0) - 1)): int == LitInt(0)
                   ==> _module.__default.trim#canCall(Seq#Take(a#0, Seq#Length(a#0) - 1));
                // ----- Hint2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(339,7)
                // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(345,13)
                assume true;
                assert Seq#Length(a#0) == LitInt(1);
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(339,7)
                assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
                if ($Unbox(Seq#Index(a#0, LitInt(0))): int == LitInt(0))
                {
                    assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) <= Seq#Length(a#0);
                    ##digits#0_2_1_4_1 := Seq#Take(a#0, LitInt(0));
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##digits#0_2_1_4_1, TSeq(TInt), $Heap);
                    assume _module.__default.trim#canCall(Seq#Take(a#0, LitInt(0)));
                }
                else
                {
                }

                assume $Unbox(Seq#Index(a#0, LitInt(0))): int == LitInt(0)
                   ==> _module.__default.trim#canCall(Seq#Take(a#0, LitInt(0)));
                // ----- assert line2 == line3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(339,7)
                assert {:subsumption 0} Seq#Equal((if Seq#Length(a#0) != 0
                       && $Unbox(Seq#Index(a#0, Seq#Length(a#0) - 1)): int == LitInt(0)
                     then _module.__default.trim($LS($LS($LZ)), Seq#Take(a#0, Seq#Length(a#0) - 1))
                     else a#0), 
                  (if $Unbox(Seq#Index(a#0, LitInt(0))): int == LitInt(0)
                     then _module.__default.trim($LS($LS($LZ)), Seq#Take(a#0, LitInt(0)))
                     else a#0));
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(339,7)
                assume {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
                if ($Unbox(Seq#Index(a#0, LitInt(0))): int == LitInt(0))
                {
                    assume {:subsumption 0} 0 <= LitInt(0) && LitInt(0) <= Seq#Length(a#0);
                    ##digits#0_2_1_3_0 := Seq#Take(a#0, LitInt(0));
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##digits#0_2_1_3_0, TSeq(TInt), $Heap);
                    assume _module.__default.trim#canCall(Seq#Take(a#0, LitInt(0)));
                }
                else
                {
                }

                assume $Unbox(Seq#Index(a#0, LitInt(0))): int == LitInt(0)
                   ==> _module.__default.trim#canCall(Seq#Take(a#0, LitInt(0)));
                // ----- Hint3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(339,7)
                // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(347,13)
                assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
                assume true;
                assert $Unbox(Seq#Index(a#0, LitInt(0))): int == LitInt(0);
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(339,7)
                assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) <= Seq#Length(a#0);
                ##digits#0_2_1_3_1 := Seq#Take(a#0, LitInt(0));
                // assume allocatedness for argument to function
                assume $IsAlloc(##digits#0_2_1_3_1, TSeq(TInt), $Heap);
                assume _module.__default.trim#canCall(Seq#Take(a#0, LitInt(0)));
                assume _module.__default.trim#canCall(Seq#Take(a#0, LitInt(0)));
                // ----- assert line3 == line4 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(339,7)
                assert {:subsumption 0} Seq#Equal((if $Unbox(Seq#Index(a#0, LitInt(0))): int == LitInt(0)
                     then _module.__default.trim($LS($LS($LZ)), Seq#Take(a#0, LitInt(0)))
                     else a#0), 
                  _module.__default.trim($LS($LS($LZ)), Seq#Take(a#0, LitInt(0))));
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(339,7)
                assume {:subsumption 0} 0 <= LitInt(0) && LitInt(0) <= Seq#Length(a#0);
                ##digits#0_2_1_2_0 := Seq#Take(a#0, LitInt(0));
                // assume allocatedness for argument to function
                assume $IsAlloc(##digits#0_2_1_2_0, TSeq(TInt), $Heap);
                assume _module.__default.trim#canCall(Seq#Take(a#0, LitInt(0)));
                assume _module.__default.trim#canCall(Seq#Take(a#0, LitInt(0)));
                // ----- Hint4 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(339,7)
                // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(349,13)
                assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) <= Seq#Length(a#0);
                assume true;
                assert Seq#Equal(Seq#Take(a#0, LitInt(0)), Seq#Empty(): Seq Box);
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(339,7)
                ##digits#0_2_1_2_1 := Lit(Seq#Empty(): Seq Box);
                // assume allocatedness for argument to function
                assume $IsAlloc(##digits#0_2_1_2_1, TSeq(TInt), $Heap);
                assume _module.__default.trim#canCall(Lit(Seq#Empty(): Seq Box));
                assume _module.__default.trim#canCall(Lit(Seq#Empty(): Seq Box));
                // ----- assert line4 == line5 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(339,7)
                assert {:subsumption 0} Seq#Equal(_module.__default.trim($LS($LS($LZ)), Seq#Take(a#0, LitInt(0))), 
                  _module.__default.trim($LS($LS($LZ)), Lit(Seq#Empty(): Seq Box)));
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(339,7)
                ##digits#0_2_1_1_0 := Lit(Seq#Empty(): Seq Box);
                // assume allocatedness for argument to function
                assume $IsAlloc(##digits#0_2_1_1_0, TSeq(TInt), $Heap);
                assume _module.__default.trim#canCall(Lit(Seq#Empty(): Seq Box));
                assume _module.__default.trim#canCall(Lit(Seq#Empty(): Seq Box));
                // ----- Hint5 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(339,7)
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(339,7)
                assume true;
                // ----- assert line5 == line6 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(339,7)
                assert {:subsumption 0} Seq#Equal(_module.__default.trim($LS($LS($LZ)), Lit(Seq#Empty(): Seq Box)), 
                  Seq#Empty(): Seq Box);
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(339,7)
                assume true;
                // ----- Hint6 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(339,7)
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(339,7)
                assume true;
                // ----- assert line6 != line7 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(339,7)
                assert {:subsumption 0} !Seq#Equal(Seq#Empty(): Seq Box, a#0);
                assume false;
            }

            assume !Seq#Equal(a#0, a#0);
        }
        else
        {
        }
    }
    else
    {
    }
}



procedure {:_induction a#0, base#0} CheckWellformed$$_module.__default.LeastSignificantDigitIsAlmostMod(a#0: Seq Box where $Is(a#0, TSeq(TInt)) && $IsAlloc(a#0, TSeq(TInt), $Heap), 
    lowDigit#0: int, 
    base#0: int);
  free requires 22 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:_induction a#0, base#0} CheckWellformed$$_module.__default.LeastSignificantDigitIsAlmostMod(a#0: Seq Box, lowDigit#0: int, base#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##digits#0: Seq Box;
  var ##lowDigit#0: int;
  var ##base#0: int;
  var mod#Z#0: int;
  var let#0#0#0: int;
  var ##digits#1: Seq Box;
  var ##base#1: int;

    // AddMethodImpl: LeastSignificantDigitIsAlmostMod, CheckWellformed$$_module.__default.LeastSignificantDigitIsAlmostMod
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(360,6): initial state"} true;
    ##digits#0 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##digits#0, TSeq(TInt), $Heap);
    ##lowDigit#0 := lowDigit#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##lowDigit#0, TInt, $Heap);
    ##base#0 := base#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##base#0, TInt, $Heap);
    assume _module.__default.IsSkewNumber#canCall(a#0, lowDigit#0, base#0);
    assume _module.__default.IsSkewNumber(a#0, lowDigit#0, base#0);
    assume !Seq#Equal(a#0, Seq#Empty(): Seq Box);
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(363,10): post-state"} true;
    havoc mod#Z#0;
    assume true;
    ##digits#1 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##digits#1, TSeq(TInt), $Heap);
    ##base#1 := base#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##base#1, TInt, $Heap);
    assert {:subsumption 0} LitInt(2) <= ##base#1;
    assume LitInt(2) <= ##base#1;
    assume _module.__default.eval#canCall(a#0, base#0);
    assert base#0 != 0;
    assume let#0#0#0 == Mod(_module.__default.eval($LS($LZ), a#0, base#0), base#0);
    assume _module.__default.eval#canCall(a#0, base#0);
    // CheckWellformedWithResult: any expression
    assume $Is(let#0#0#0, TInt);
    assume mod#Z#0 == let#0#0#0;
    assert 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
    if ($Unbox(Seq#Index(a#0, LitInt(0))): int != mod#Z#0)
    {
        assert 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
    }

    assume (var mod#0 := Mod(_module.__default.eval($LS($LZ), a#0, base#0), base#0); 
      $Unbox(Seq#Index(a#0, LitInt(0))): int == mod#0
         || $Unbox(Seq#Index(a#0, LitInt(0))): int == mod#0 - base#0);
}



procedure {:_induction a#0, base#0} Call$$_module.__default.LeastSignificantDigitIsAlmostMod(a#0: Seq Box where $Is(a#0, TSeq(TInt)) && $IsAlloc(a#0, TSeq(TInt), $Heap), 
    lowDigit#0: int, 
    base#0: int);
  // user-defined preconditions
  requires _module.__default.IsSkewNumber#canCall(a#0, lowDigit#0, base#0)
     ==> _module.__default.IsSkewNumber(a#0, lowDigit#0, base#0) || LitInt(2) <= base#0;
  requires _module.__default.IsSkewNumber#canCall(a#0, lowDigit#0, base#0)
     ==> _module.__default.IsSkewNumber(a#0, lowDigit#0, base#0)
       || lowDigit#0 <= LitInt(0);
  requires _module.__default.IsSkewNumber#canCall(a#0, lowDigit#0, base#0)
     ==> _module.__default.IsSkewNumber(a#0, lowDigit#0, base#0)
       || 0 < lowDigit#0 + base#0;
  requires _module.__default.IsSkewNumber#canCall(a#0, lowDigit#0, base#0)
     ==> _module.__default.IsSkewNumber(a#0, lowDigit#0, base#0)
       || (forall i#0: int :: 
        { $Unbox(Seq#Index(a#0, i#0)): int } 
        true
           ==> (LitInt(0) <= i#0 && i#0 < Seq#Length(a#0)
               ==> lowDigit#0 <= $Unbox(Seq#Index(a#0, i#0)): int)
             && (LitInt(0) <= i#0 && i#0 < Seq#Length(a#0)
               ==> $Unbox(Seq#Index(a#0, i#0)): int < lowDigit#0 + base#0));
  requires !Seq#Equal(a#0, Seq#Empty(): Seq Box);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.eval#canCall(a#0, base#0);
  ensures (var mod#0 := Mod(_module.__default.eval($LS($LS($LZ)), a#0, base#0), base#0); 
    $Unbox(Seq#Index(a#0, LitInt(0))): int == mod#0
       || $Unbox(Seq#Index(a#0, LitInt(0))): int == mod#0 - base#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction a#0, base#0} Impl$$_module.__default.LeastSignificantDigitIsAlmostMod(a#0: Seq Box where $Is(a#0, TSeq(TInt)) && $IsAlloc(a#0, TSeq(TInt), $Heap), 
    lowDigit#0: int, 
    base#0: int)
   returns ($_reverifyPost: bool);
  free requires 22 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.__default.IsSkewNumber#canCall(a#0, lowDigit#0, base#0)
     && 
    _module.__default.IsSkewNumber(a#0, lowDigit#0, base#0)
     && 
    LitInt(2) <= base#0
     && 
    lowDigit#0 <= LitInt(0)
     && 0 < lowDigit#0 + base#0
     && (forall i#1: int :: 
      { $Unbox(Seq#Index(a#0, i#1)): int } 
      true
         ==> (LitInt(0) <= i#1 && i#1 < Seq#Length(a#0)
             ==> lowDigit#0 <= $Unbox(Seq#Index(a#0, i#1)): int)
           && (LitInt(0) <= i#1 && i#1 < Seq#Length(a#0)
             ==> $Unbox(Seq#Index(a#0, i#1)): int < lowDigit#0 + base#0));
  requires !Seq#Equal(a#0, Seq#Empty(): Seq Box);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.eval#canCall(a#0, base#0);
  ensures (var mod#0 := Mod(_module.__default.eval($LS($LS($LZ)), a#0, base#0), base#0); 
    $Unbox(Seq#Index(a#0, LitInt(0))): int == mod#0
       || $Unbox(Seq#Index(a#0, LitInt(0))): int == mod#0 - base#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction a#0, base#0} Impl$$_module.__default.LeastSignificantDigitIsAlmostMod(a#0: Seq Box, lowDigit#0: int, base#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var a##0_0: Seq Box;
  var lowDigit##0_0: int;
  var base##0_0: int;
  var a##0: Seq Box;
  var lowDigit##0: int;
  var base##0: int;

    // AddMethodImpl: LeastSignificantDigitIsAlmostMod, Impl$$_module.__default.LeastSignificantDigitIsAlmostMod
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(365,0): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#a0#0: Seq Box, $ih#base0#0: int :: 
      $Is($ih#a0#0, TSeq(TInt))
           && 
          _module.__default.IsSkewNumber($ih#a0#0, lowDigit#0, $ih#base0#0)
           && !Seq#Equal($ih#a0#0, Seq#Empty(): Seq Box)
           && (Seq#Rank($ih#a0#0) < Seq#Rank(a#0)
             || (Seq#Rank($ih#a0#0) == Seq#Rank(a#0)
               && ((0 <= lowDigit#0 && lowDigit#0 < lowDigit#0)
                 || (lowDigit#0 == lowDigit#0 && 0 <= $ih#base0#0 && $ih#base0#0 < base#0))))
         ==> (var mod#1 := Mod(_module.__default.eval($LS($LZ), $ih#a0#0, $ih#base0#0), $ih#base0#0); 
          $Unbox(Seq#Index($ih#a0#0, LitInt(0))): int == mod#1
             || $Unbox(Seq#Index($ih#a0#0, LitInt(0))): int == mod#1 - $ih#base0#0));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(366,3)
    assert 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
    assume true;
    if (LitInt(0) <= $Unbox(Seq#Index(a#0, LitInt(0))): int)
    {
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(367,41)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        a##0_0 := a#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        lowDigit##0_0 := lowDigit#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        base##0_0 := base#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.LeastSignificantDigitIsAlmostMod__Pos(a##0_0, lowDigit##0_0, base##0_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(367,59)"} true;
    }
    else
    {
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(369,41)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        a##0 := a#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        lowDigit##0 := lowDigit#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        base##0 := base#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.LeastSignificantDigitIsAlmostMod__Neg(a##0, lowDigit##0, base##0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(369,59)"} true;
    }
}



procedure {:_induction a#0, base#0} CheckWellformed$$_module.__default.LeastSignificantDigitIsAlmostMod__Pos(a#0: Seq Box where $Is(a#0, TSeq(TInt)) && $IsAlloc(a#0, TSeq(TInt), $Heap), 
    lowDigit#0: int, 
    base#0: int);
  free requires 20 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:_induction a#0, base#0} CheckWellformed$$_module.__default.LeastSignificantDigitIsAlmostMod__Pos(a#0: Seq Box, lowDigit#0: int, base#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##digits#0: Seq Box;
  var ##lowDigit#0: int;
  var ##base#0: int;
  var ##digits#1: Seq Box;
  var ##base#1: int;

    // AddMethodImpl: LeastSignificantDigitIsAlmostMod_Pos, CheckWellformed$$_module.__default.LeastSignificantDigitIsAlmostMod__Pos
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(373,6): initial state"} true;
    ##digits#0 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##digits#0, TSeq(TInt), $Heap);
    ##lowDigit#0 := lowDigit#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##lowDigit#0, TInt, $Heap);
    ##base#0 := base#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##base#0, TInt, $Heap);
    assume _module.__default.IsSkewNumber#canCall(a#0, lowDigit#0, base#0);
    assume _module.__default.IsSkewNumber(a#0, lowDigit#0, base#0);
    assume !Seq#Equal(a#0, Seq#Empty(): Seq Box);
    assert 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
    assume LitInt(0) <= $Unbox(Seq#Index(a#0, LitInt(0))): int;
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(376,31): post-state"} true;
    ##digits#1 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##digits#1, TSeq(TInt), $Heap);
    ##base#1 := base#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##base#1, TInt, $Heap);
    assert {:subsumption 0} LitInt(2) <= ##base#1;
    assume LitInt(2) <= ##base#1;
    assume _module.__default.eval#canCall(a#0, base#0);
    assert base#0 != 0;
    assert 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
    assume Mod(_module.__default.eval($LS($LZ), a#0, base#0), base#0)
       == $Unbox(Seq#Index(a#0, LitInt(0))): int;
}



procedure {:_induction a#0, base#0} Call$$_module.__default.LeastSignificantDigitIsAlmostMod__Pos(a#0: Seq Box where $Is(a#0, TSeq(TInt)) && $IsAlloc(a#0, TSeq(TInt), $Heap), 
    lowDigit#0: int, 
    base#0: int);
  // user-defined preconditions
  requires _module.__default.IsSkewNumber#canCall(a#0, lowDigit#0, base#0)
     ==> _module.__default.IsSkewNumber(a#0, lowDigit#0, base#0) || LitInt(2) <= base#0;
  requires _module.__default.IsSkewNumber#canCall(a#0, lowDigit#0, base#0)
     ==> _module.__default.IsSkewNumber(a#0, lowDigit#0, base#0)
       || lowDigit#0 <= LitInt(0);
  requires _module.__default.IsSkewNumber#canCall(a#0, lowDigit#0, base#0)
     ==> _module.__default.IsSkewNumber(a#0, lowDigit#0, base#0)
       || 0 < lowDigit#0 + base#0;
  requires _module.__default.IsSkewNumber#canCall(a#0, lowDigit#0, base#0)
     ==> _module.__default.IsSkewNumber(a#0, lowDigit#0, base#0)
       || (forall i#0: int :: 
        { $Unbox(Seq#Index(a#0, i#0)): int } 
        true
           ==> (LitInt(0) <= i#0 && i#0 < Seq#Length(a#0)
               ==> lowDigit#0 <= $Unbox(Seq#Index(a#0, i#0)): int)
             && (LitInt(0) <= i#0 && i#0 < Seq#Length(a#0)
               ==> $Unbox(Seq#Index(a#0, i#0)): int < lowDigit#0 + base#0));
  requires !Seq#Equal(a#0, Seq#Empty(): Seq Box);
  requires LitInt(0) <= $Unbox(Seq#Index(a#0, LitInt(0))): int;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.eval#canCall(a#0, base#0);
  ensures Mod(_module.__default.eval($LS($LS($LZ)), a#0, base#0), base#0)
     == $Unbox(Seq#Index(a#0, LitInt(0))): int;
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction a#0, base#0} Impl$$_module.__default.LeastSignificantDigitIsAlmostMod__Pos(a#0: Seq Box where $Is(a#0, TSeq(TInt)) && $IsAlloc(a#0, TSeq(TInt), $Heap), 
    lowDigit#0: int, 
    base#0: int)
   returns ($_reverifyPost: bool);
  free requires 20 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.__default.IsSkewNumber#canCall(a#0, lowDigit#0, base#0)
     && 
    _module.__default.IsSkewNumber(a#0, lowDigit#0, base#0)
     && 
    LitInt(2) <= base#0
     && 
    lowDigit#0 <= LitInt(0)
     && 0 < lowDigit#0 + base#0
     && (forall i#1: int :: 
      { $Unbox(Seq#Index(a#0, i#1)): int } 
      true
         ==> (LitInt(0) <= i#1 && i#1 < Seq#Length(a#0)
             ==> lowDigit#0 <= $Unbox(Seq#Index(a#0, i#1)): int)
           && (LitInt(0) <= i#1 && i#1 < Seq#Length(a#0)
             ==> $Unbox(Seq#Index(a#0, i#1)): int < lowDigit#0 + base#0));
  requires !Seq#Equal(a#0, Seq#Empty(): Seq Box);
  requires LitInt(0) <= $Unbox(Seq#Index(a#0, LitInt(0))): int;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.eval#canCall(a#0, base#0);
  ensures Mod(_module.__default.eval($LS($LS($LZ)), a#0, base#0), base#0)
     == $Unbox(Seq#Index(a#0, LitInt(0))): int;
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction a#0, base#0} Impl$$_module.__default.LeastSignificantDigitIsAlmostMod__Pos(a#0: Seq Box, lowDigit#0: int, base#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var n#0: int;
  var ##digits#2: Seq Box;
  var ##base#2: int;
  var a1#0: int;
  var ##digits#3: Seq Box;
  var ##base#3: int;
  var b#0: int;
  var a##0_0_0: int;
  var b##0_0_0: int;
  var n##0_1_0: int;
  var k##0_1_0: int;
  var base##0_1_0: int;

    // AddMethodImpl: LeastSignificantDigitIsAlmostMod_Pos, Impl$$_module.__default.LeastSignificantDigitIsAlmostMod__Pos
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(377,0): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#a0#0: Seq Box, $ih#base0#0: int :: 
      $Is($ih#a0#0, TSeq(TInt))
           && 
          _module.__default.IsSkewNumber($ih#a0#0, lowDigit#0, $ih#base0#0)
           && 
          !Seq#Equal($ih#a0#0, Seq#Empty(): Seq Box)
           && LitInt(0) <= $Unbox(Seq#Index($ih#a0#0, LitInt(0))): int
           && (Seq#Rank($ih#a0#0) < Seq#Rank(a#0)
             || (Seq#Rank($ih#a0#0) == Seq#Rank(a#0)
               && ((0 <= lowDigit#0 && lowDigit#0 < lowDigit#0)
                 || (lowDigit#0 == lowDigit#0 && 0 <= $ih#base0#0 && $ih#base0#0 < base#0))))
         ==> Mod(_module.__default.eval($LS($LZ), $ih#a0#0, $ih#base0#0), $ih#base0#0)
           == $Unbox(Seq#Index($ih#a0#0, LitInt(0))): int);
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(378,9)
    assume true;
    ##digits#2 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##digits#2, TSeq(TInt), $Heap);
    ##base#2 := base#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##base#2, TInt, $Heap);
    assert {:subsumption 0} LitInt(2) <= ##base#2;
    assume LitInt(2) <= ##base#2;
    assume _module.__default.eval#canCall(a#0, base#0);
    assume _module.__default.eval#canCall(a#0, base#0);
    n#0 := _module.__default.eval($LS($LZ), a#0, base#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(378,24)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(379,10)
    assume true;
    assert 0 <= LitInt(1) && LitInt(1) <= Seq#Length(a#0);
    ##digits#3 := Seq#Drop(a#0, LitInt(1));
    // assume allocatedness for argument to function
    assume $IsAlloc(##digits#3, TSeq(TInt), $Heap);
    ##base#3 := base#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##base#3, TInt, $Heap);
    assert {:subsumption 0} LitInt(2) <= ##base#3;
    assume LitInt(2) <= ##base#3;
    assume _module.__default.eval#canCall(Seq#Drop(a#0, LitInt(1)), base#0);
    assume _module.__default.eval#canCall(Seq#Drop(a#0, LitInt(1)), base#0);
    a1#0 := _module.__default.eval($LS($LZ), Seq#Drop(a#0, LitInt(1)), base#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(379,30)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(380,9)
    assume true;
    assume true;
    b#0 := Mul(base#0, a1#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(380,20)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(381,3)
    assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
    assume true;
    assert $Unbox(Seq#Index(a#0, LitInt(0))): int + b#0 == n#0;
    // ----- calc statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(383,3)
    // Assume Fuel Constant
    if (*)
    {
        // ----- assert wf[initial] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(383,3)
        assert {:subsumption 0} base#0 != 0;
        assume true;
        assume false;
    }
    else if (*)
    {
        // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(383,3)
        assume {:subsumption 0} base#0 != 0;
        assume true;
        // ----- Hint0 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(383,3)
        // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(383,3)
        assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
        assert {:subsumption 0} base#0 != 0;
        assume true;
        // ----- assert line0 == line1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(383,3)
        assert {:subsumption 0} Mod(n#0, base#0)
           == Mod($Unbox(Seq#Index(a#0, LitInt(0))): int + Mul(base#0, a1#0), base#0);
        assume false;
    }
    else if (*)
    {
        // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(383,3)
        assume {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
        assume {:subsumption 0} base#0 != 0;
        assume true;
        // ----- Hint1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(383,3)
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(387,20)
        // TrCallStmt: Before ProcessCallStmt
        assert 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
        assume true;
        // ProcessCallStmt: CheckSubrange
        n##0_1_0 := $Unbox(Seq#Index(a#0, LitInt(0))): int;
        assume true;
        // ProcessCallStmt: CheckSubrange
        k##0_1_0 := a1#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        base##0_1_0 := base#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.ModProperty(n##0_1_0, k##0_1_0, base##0_1_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(387,35)"} true;
        // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(383,3)
        assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
        assert {:subsumption 0} base#0 != 0;
        assume true;
        // ----- assert line1 == line2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(383,3)
        assert {:subsumption 0} Mod($Unbox(Seq#Index(a#0, LitInt(0))): int + Mul(base#0, a1#0), base#0)
           == Mod($Unbox(Seq#Index(a#0, LitInt(0))): int, base#0);
        assume false;
    }
    else if (*)
    {
        // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(383,3)
        assume {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
        assume {:subsumption 0} base#0 != 0;
        assume true;
        // ----- Hint2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(383,3)
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(389,9)
        assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
        assume true;
        assert Seq#Contains(a#0, Seq#Index(a#0, LitInt(0)));
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(389,34)
        // TrCallStmt: Before ProcessCallStmt
        assert 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
        assume true;
        // ProcessCallStmt: CheckSubrange
        a##0_0_0 := $Unbox(Seq#Index(a#0, LitInt(0))): int;
        assume true;
        // ProcessCallStmt: CheckSubrange
        b##0_0_0 := base#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.ModNoop(a##0_0_0, b##0_0_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(389,45)"} true;
        // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(383,3)
        assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
        assume true;
        // ----- assert line2 == line3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(383,3)
        assert {:subsumption 0} Mod($Unbox(Seq#Index(a#0, LitInt(0))): int, base#0)
           == $Unbox(Seq#Index(a#0, LitInt(0))): int;
        assume false;
    }

    assume Mod(n#0, base#0) == $Unbox(Seq#Index(a#0, LitInt(0))): int;
}



procedure {:_induction a#0, base#0} CheckWellformed$$_module.__default.LeastSignificantDigitIsAlmostMod__Neg(a#0: Seq Box where $Is(a#0, TSeq(TInt)) && $IsAlloc(a#0, TSeq(TInt), $Heap), 
    lowDigit#0: int, 
    base#0: int);
  free requires 21 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:_induction a#0, base#0} CheckWellformed$$_module.__default.LeastSignificantDigitIsAlmostMod__Neg(a#0: Seq Box, lowDigit#0: int, base#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##digits#0: Seq Box;
  var ##lowDigit#0: int;
  var ##base#0: int;
  var ##digits#1: Seq Box;
  var ##base#1: int;

    // AddMethodImpl: LeastSignificantDigitIsAlmostMod_Neg, CheckWellformed$$_module.__default.LeastSignificantDigitIsAlmostMod__Neg
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(394,6): initial state"} true;
    ##digits#0 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##digits#0, TSeq(TInt), $Heap);
    ##lowDigit#0 := lowDigit#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##lowDigit#0, TInt, $Heap);
    ##base#0 := base#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##base#0, TInt, $Heap);
    assume _module.__default.IsSkewNumber#canCall(a#0, lowDigit#0, base#0);
    assume _module.__default.IsSkewNumber(a#0, lowDigit#0, base#0);
    assume !Seq#Equal(a#0, Seq#Empty(): Seq Box);
    assert 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
    assume $Unbox(Seq#Index(a#0, LitInt(0))): int < 0;
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(397,31): post-state"} true;
    ##digits#1 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##digits#1, TSeq(TInt), $Heap);
    ##base#1 := base#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##base#1, TInt, $Heap);
    assert {:subsumption 0} LitInt(2) <= ##base#1;
    assume LitInt(2) <= ##base#1;
    assume _module.__default.eval#canCall(a#0, base#0);
    assert base#0 != 0;
    assert 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
    assume Mod(_module.__default.eval($LS($LZ), a#0, base#0), base#0)
       == $Unbox(Seq#Index(a#0, LitInt(0))): int + base#0;
}



procedure {:_induction a#0, base#0} Call$$_module.__default.LeastSignificantDigitIsAlmostMod__Neg(a#0: Seq Box where $Is(a#0, TSeq(TInt)) && $IsAlloc(a#0, TSeq(TInt), $Heap), 
    lowDigit#0: int, 
    base#0: int);
  // user-defined preconditions
  requires _module.__default.IsSkewNumber#canCall(a#0, lowDigit#0, base#0)
     ==> _module.__default.IsSkewNumber(a#0, lowDigit#0, base#0) || LitInt(2) <= base#0;
  requires _module.__default.IsSkewNumber#canCall(a#0, lowDigit#0, base#0)
     ==> _module.__default.IsSkewNumber(a#0, lowDigit#0, base#0)
       || lowDigit#0 <= LitInt(0);
  requires _module.__default.IsSkewNumber#canCall(a#0, lowDigit#0, base#0)
     ==> _module.__default.IsSkewNumber(a#0, lowDigit#0, base#0)
       || 0 < lowDigit#0 + base#0;
  requires _module.__default.IsSkewNumber#canCall(a#0, lowDigit#0, base#0)
     ==> _module.__default.IsSkewNumber(a#0, lowDigit#0, base#0)
       || (forall i#0: int :: 
        { $Unbox(Seq#Index(a#0, i#0)): int } 
        true
           ==> (LitInt(0) <= i#0 && i#0 < Seq#Length(a#0)
               ==> lowDigit#0 <= $Unbox(Seq#Index(a#0, i#0)): int)
             && (LitInt(0) <= i#0 && i#0 < Seq#Length(a#0)
               ==> $Unbox(Seq#Index(a#0, i#0)): int < lowDigit#0 + base#0));
  requires !Seq#Equal(a#0, Seq#Empty(): Seq Box);
  requires $Unbox(Seq#Index(a#0, LitInt(0))): int < 0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.eval#canCall(a#0, base#0);
  ensures Mod(_module.__default.eval($LS($LS($LZ)), a#0, base#0), base#0)
     == $Unbox(Seq#Index(a#0, LitInt(0))): int + base#0;
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction a#0, base#0} Impl$$_module.__default.LeastSignificantDigitIsAlmostMod__Neg(a#0: Seq Box where $Is(a#0, TSeq(TInt)) && $IsAlloc(a#0, TSeq(TInt), $Heap), 
    lowDigit#0: int, 
    base#0: int)
   returns ($_reverifyPost: bool);
  free requires 21 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.__default.IsSkewNumber#canCall(a#0, lowDigit#0, base#0)
     && 
    _module.__default.IsSkewNumber(a#0, lowDigit#0, base#0)
     && 
    LitInt(2) <= base#0
     && 
    lowDigit#0 <= LitInt(0)
     && 0 < lowDigit#0 + base#0
     && (forall i#1: int :: 
      { $Unbox(Seq#Index(a#0, i#1)): int } 
      true
         ==> (LitInt(0) <= i#1 && i#1 < Seq#Length(a#0)
             ==> lowDigit#0 <= $Unbox(Seq#Index(a#0, i#1)): int)
           && (LitInt(0) <= i#1 && i#1 < Seq#Length(a#0)
             ==> $Unbox(Seq#Index(a#0, i#1)): int < lowDigit#0 + base#0));
  requires !Seq#Equal(a#0, Seq#Empty(): Seq Box);
  requires $Unbox(Seq#Index(a#0, LitInt(0))): int < 0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.eval#canCall(a#0, base#0);
  ensures Mod(_module.__default.eval($LS($LS($LZ)), a#0, base#0), base#0)
     == $Unbox(Seq#Index(a#0, LitInt(0))): int + base#0;
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction a#0, base#0} Impl$$_module.__default.LeastSignificantDigitIsAlmostMod__Neg(a#0: Seq Box, lowDigit#0: int, base#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var n#0: int;
  var ##digits#2: Seq Box;
  var ##base#2: int;
  var a1#0: int;
  var ##digits#3: Seq Box;
  var ##base#3: int;
  var b#0: int;
  var aPlus#0: int;
  var a1minus#0: int;
  var $rhs#0: int;
  var $rhs#1: int;
  var a##0_0_0: int;
  var b##0_0_0: int;
  var n##0_1_0: int;
  var k##0_1_0: int;
  var base##0_1_0: int;

    // AddMethodImpl: LeastSignificantDigitIsAlmostMod_Neg, Impl$$_module.__default.LeastSignificantDigitIsAlmostMod__Neg
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(398,0): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#a0#0: Seq Box, $ih#base0#0: int :: 
      $Is($ih#a0#0, TSeq(TInt))
           && 
          _module.__default.IsSkewNumber($ih#a0#0, lowDigit#0, $ih#base0#0)
           && 
          !Seq#Equal($ih#a0#0, Seq#Empty(): Seq Box)
           && $Unbox(Seq#Index($ih#a0#0, LitInt(0))): int < 0
           && (Seq#Rank($ih#a0#0) < Seq#Rank(a#0)
             || (Seq#Rank($ih#a0#0) == Seq#Rank(a#0)
               && ((0 <= lowDigit#0 && lowDigit#0 < lowDigit#0)
                 || (lowDigit#0 == lowDigit#0 && 0 <= $ih#base0#0 && $ih#base0#0 < base#0))))
         ==> Mod(_module.__default.eval($LS($LZ), $ih#a0#0, $ih#base0#0), $ih#base0#0)
           == $Unbox(Seq#Index($ih#a0#0, LitInt(0))): int + $ih#base0#0);
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(399,9)
    assume true;
    ##digits#2 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##digits#2, TSeq(TInt), $Heap);
    ##base#2 := base#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##base#2, TInt, $Heap);
    assert {:subsumption 0} LitInt(2) <= ##base#2;
    assume LitInt(2) <= ##base#2;
    assume _module.__default.eval#canCall(a#0, base#0);
    assume _module.__default.eval#canCall(a#0, base#0);
    n#0 := _module.__default.eval($LS($LZ), a#0, base#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(399,24)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(400,10)
    assume true;
    assert 0 <= LitInt(1) && LitInt(1) <= Seq#Length(a#0);
    ##digits#3 := Seq#Drop(a#0, LitInt(1));
    // assume allocatedness for argument to function
    assume $IsAlloc(##digits#3, TSeq(TInt), $Heap);
    ##base#3 := base#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##base#3, TInt, $Heap);
    assert {:subsumption 0} LitInt(2) <= ##base#3;
    assume LitInt(2) <= ##base#3;
    assume _module.__default.eval#canCall(Seq#Drop(a#0, LitInt(1)), base#0);
    assume _module.__default.eval#canCall(Seq#Drop(a#0, LitInt(1)), base#0);
    a1#0 := _module.__default.eval($LS($LZ), Seq#Drop(a#0, LitInt(1)), base#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(400,30)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(401,9)
    assume true;
    assume true;
    b#0 := Mul(base#0, a1#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(401,20)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(402,3)
    assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
    assume true;
    assert $Unbox(Seq#Index(a#0, LitInt(0))): int + b#0 == n#0;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(404,22)
    assume true;
    assume true;
    assert 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
    assume true;
    $rhs#0 := $Unbox(Seq#Index(a#0, LitInt(0))): int + base#0;
    assume true;
    $rhs#1 := a1#0 - 1;
    aPlus#0 := $rhs#0;
    a1minus#0 := $rhs#1;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(404,43)"} true;
    // ----- calc statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(405,3)
    // Assume Fuel Constant
    if (*)
    {
        // ----- assert wf[initial] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(405,3)
        assert {:subsumption 0} base#0 != 0;
        assume true;
        assume false;
    }
    else if (*)
    {
        // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(405,3)
        assume {:subsumption 0} base#0 != 0;
        assume true;
        // ----- Hint0 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(405,3)
        // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(405,3)
        assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
        assert {:subsumption 0} base#0 != 0;
        assume true;
        // ----- assert line0 == line1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(405,3)
        assert {:subsumption 0} Mod(n#0, base#0)
           == Mod($Unbox(Seq#Index(a#0, LitInt(0))): int + Mul(base#0, a1#0), base#0);
        assume false;
    }
    else if (*)
    {
        // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(405,3)
        assume {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
        assume {:subsumption 0} base#0 != 0;
        assume true;
        // ----- Hint1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(405,3)
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(409,9)
        assume true;
        assert Mul(base#0, a1#0) == base#0 + Mul(base#0, a1minus#0);
        // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(405,3)
        assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
        assert {:subsumption 0} base#0 != 0;
        assume true;
        // ----- assert line1 == line2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(405,3)
        assert {:subsumption 0} Mod($Unbox(Seq#Index(a#0, LitInt(0))): int + Mul(base#0, a1#0), base#0)
           == Mod($Unbox(Seq#Index(a#0, LitInt(0))): int + base#0 + Mul(base#0, a1minus#0), base#0);
        assume false;
    }
    else if (*)
    {
        // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(405,3)
        assume {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
        assume {:subsumption 0} base#0 != 0;
        assume true;
        // ----- Hint2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(405,3)
        // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(405,3)
        assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
        assert {:subsumption 0} base#0 != 0;
        assume true;
        // ----- assert line2 == line3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(405,3)
        assert {:subsumption 0} Mod($Unbox(Seq#Index(a#0, LitInt(0))): int + base#0 + Mul(base#0, a1minus#0), base#0)
           == Mod($Unbox(Seq#Index(a#0, LitInt(0))): int + base#0 + Mul(base#0, a1minus#0), base#0);
        assume false;
    }
    else if (*)
    {
        // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(405,3)
        assume {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
        assume {:subsumption 0} base#0 != 0;
        assume true;
        // ----- Hint3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(405,3)
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(413,20)
        // TrCallStmt: Before ProcessCallStmt
        assert 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
        assume true;
        // ProcessCallStmt: CheckSubrange
        n##0_1_0 := $Unbox(Seq#Index(a#0, LitInt(0))): int + base#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        k##0_1_0 := a1minus#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        base##0_1_0 := base#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.ModProperty(n##0_1_0, k##0_1_0, base##0_1_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(413,47)"} true;
        // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(405,3)
        assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
        assert {:subsumption 0} base#0 != 0;
        assume true;
        // ----- assert line3 == line4 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(405,3)
        assert {:subsumption 0} Mod($Unbox(Seq#Index(a#0, LitInt(0))): int + base#0 + Mul(base#0, a1minus#0), base#0)
           == Mod($Unbox(Seq#Index(a#0, LitInt(0))): int + base#0, base#0);
        assume false;
    }
    else if (*)
    {
        // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(405,3)
        assume {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
        assume {:subsumption 0} base#0 != 0;
        assume true;
        // ----- Hint4 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(405,3)
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(415,9)
        assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
        assume true;
        assert Seq#Contains(a#0, Seq#Index(a#0, LitInt(0)));
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(415,34)
        // TrCallStmt: Before ProcessCallStmt
        assert 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
        assume true;
        // ProcessCallStmt: CheckSubrange
        a##0_0_0 := $Unbox(Seq#Index(a#0, LitInt(0))): int + base#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        b##0_0_0 := base#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.ModNoop(a##0_0_0, b##0_0_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(415,52)"} true;
        // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(405,3)
        assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(a#0);
        assume true;
        // ----- assert line4 == line5 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(405,3)
        assert {:subsumption 0} Mod($Unbox(Seq#Index(a#0, LitInt(0))): int + base#0, base#0)
           == $Unbox(Seq#Index(a#0, LitInt(0))): int + base#0;
        assume false;
    }

    assume Mod(n#0, base#0) == $Unbox(Seq#Index(a#0, LitInt(0))): int + base#0;
}



procedure CheckWellformed$$_module.__default.ModProperty(n#0: int, k#0: int, base#0: int);
  free requires 18 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.ModProperty(n#0: int, k#0: int, base#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: ModProperty, CheckWellformed$$_module.__default.ModProperty
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(421,6): initial state"} true;
    assume LitInt(2) <= base#0;
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(423,32): post-state"} true;
    assert base#0 != 0;
    assert base#0 != 0;
    assume Mod(n#0 + Mul(base#0, k#0), base#0) == Mod(n#0, base#0);
}



procedure Call$$_module.__default.ModProperty(n#0: int, k#0: int, base#0: int);
  // user-defined preconditions
  requires LitInt(2) <= base#0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures Mod(n#0 + Mul(base#0, k#0), base#0) == Mod(n#0, base#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.ModProperty(n#0: int, k#0: int, base#0: int) returns ($_reverifyPost: bool);
  free requires 18 == $FunctionContextHeight;
  // user-defined preconditions
  requires LitInt(2) <= base#0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures Mod(n#0 + Mul(base#0, k#0), base#0) == Mod(n#0, base#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.ModProperty(n#0: int, k#0: int, base#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var d#0: int;
  var m#0: int;
  var $rhs#0: int;
  var $rhs#1: int;
  var $Heap_at_0: Heap;
  var ##$Heap_at_0#m#0: int;
  var n'#0: int;
  var d'#0: int;
  var m'#0: int;
  var $rhs#2: int;
  var $rhs#3: int;
  var $Heap_at_1: Heap;
  var ##$Heap_at_1#m'#0: int;
  var y#0: int;
  var p#0: int;
  var $rhs##0: int;
  var k##0: int;
  var a##0: int;
  var x##0: int;
  var b##0: int;
  var y##0: int;
  var pk#0: int;
  var a##2_0: int;
  var x##2_0: int;
  var y##2_0: int;
  var a##3_0: int;
  var x##3_0: int;
  var y##3_0: int;

    // AddMethodImpl: ModProperty, Impl$$_module.__default.ModProperty
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(424,0): initial state"} true;
    $_reverifyPost := false;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(425,12)
    assume true;
    assume true;
    assert base#0 != 0;
    assume true;
    $rhs#0 := Div(n#0, base#0);
    assert base#0 != 0;
    assume true;
    $rhs#1 := Mod(n#0, base#0);
    d#0 := $rhs#0;
    m#0 := $rhs#1;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(425,32)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(426,3)
    assume true;
    assert Mul(base#0, d#0) + m#0 == n#0;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(427,3)
    if (LitInt(0) <= m#0)
    {
    }

    assume true;
    if (*)
    {
        // ----- assert statement proof ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(427,3)
        assert {:subsumption 0} LitInt(0) <= m#0;
        assert {:subsumption 0} m#0 < base#0;
        assume false;
    }

    $Heap_at_0 := $Heap;
    ##$Heap_at_0#m#0 := m#0;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(429,10)
    assume true;
    assume true;
    n'#0 := n#0 + Mul(base#0, k#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(429,24)"} true;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(430,14)
    assume true;
    assume true;
    assert base#0 != 0;
    assume true;
    $rhs#2 := Div(n'#0, base#0);
    assert base#0 != 0;
    assume true;
    $rhs#3 := Mod(n'#0, base#0);
    d'#0 := $rhs#2;
    m'#0 := $rhs#3;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(430,36)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(431,3)
    assume true;
    assert Mul(base#0, d'#0) + m'#0 == n'#0;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(432,3)
    if (LitInt(0) <= m'#0)
    {
    }

    assume true;
    if (*)
    {
        // ----- assert statement proof ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(432,3)
        assert {:subsumption 0} LitInt(0) <= m'#0;
        assert {:subsumption 0} m'#0 < base#0;
        assume false;
    }

    $Heap_at_1 := $Heap;
    ##$Heap_at_1#m'#0 := m'#0;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(434,3)
    if (0 - base#0 < m'#0 - m#0)
    {
    }

    assume true;
    if (*)
    {
        // ----- assert statement proof ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(434,3)
        // ----- reveal statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(435,5)
        assume LitInt(0) <= ##$Heap_at_0#m#0 && ##$Heap_at_0#m#0 < base#0;
        assume LitInt(0) <= ##$Heap_at_1#m'#0 && ##$Heap_at_1#m'#0 < base#0;
        assert {:subsumption 0} 0 - base#0 < m'#0 - m#0;
        assert {:subsumption 0} m'#0 - m#0 < base#0;
        assume false;
    }

    assume 0 - base#0 < m'#0 - m#0 && m'#0 - m#0 < base#0;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(438,9)
    assume true;
    assume true;
    y#0 := m'#0 - Mul(base#0, k#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(438,24)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(439,23)
    assume true;
    // TrCallStmt: Adding lhs with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    k##0 := base#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##0 := d#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##0 := m#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    b##0 := d'#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    y##0 := y#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0 := Call$$_module.__default.MulProperty(k##0, a##0, x##0, b##0, y##0);
    // TrCallStmt: After ProcessCallStmt
    p#0 := $rhs##0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(439,41)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(440,10)
    assume true;
    assume true;
    pk#0 := p#0 + k#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(440,17)"} true;
    // ----- calc statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(441,3)
    // Assume Fuel Constant
    if (*)
    {
        // ----- assert wf[initial] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(441,3)
        assume true;
        assume false;
    }
    else if (*)
    {
        // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(441,3)
        assume true;
        // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(441,3)
        assume true;
        // ----- Hint0 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(441,3)
        // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(441,3)
        assume true;
        // ----- assert line0 ==> line1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(441,3)
        assert {:subsumption 0} Lit(true) ==> y#0 - m#0 == Mul(base#0, p#0);
        assume false;
    }
    else if (*)
    {
        // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(441,3)
        assume true;
        // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(441,3)
        assume y#0 - m#0 == Mul(base#0, p#0);
        // ----- Hint1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(441,3)
        // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(441,3)
        assume true;
        // ----- assert line1 ==> line2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(441,3)
        assert {:subsumption 0} y#0 - m#0 == Mul(base#0, p#0)
           ==> m'#0 - Mul(base#0, k#0) - m#0 == Mul(base#0, p#0);
        assume false;
    }
    else if (*)
    {
        // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(441,3)
        assume true;
        // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(441,3)
        assume m'#0 - Mul(base#0, k#0) - m#0 == Mul(base#0, p#0);
        // ----- Hint2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(441,3)
        // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(441,3)
        assume true;
        // ----- assert line2 ==> line3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(441,3)
        assert {:subsumption 0} m'#0 - Mul(base#0, k#0) - m#0 == Mul(base#0, p#0)
           ==> m'#0 - m#0 == Mul(base#0, p#0) + Mul(base#0, k#0);
        assume false;
    }
    else if (*)
    {
        // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(441,3)
        assume true;
        // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(441,3)
        assume m'#0 - m#0 == Mul(base#0, p#0) + Mul(base#0, k#0);
        // ----- Hint3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(441,3)
        // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(441,3)
        assume true;
        // ----- assert line3 ==> line4 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(441,3)
        assert {:subsumption 0} m'#0 - m#0 == Mul(base#0, p#0) + Mul(base#0, k#0)
           ==> m'#0 - m#0 == Mul(base#0, pk#0);
        assume false;
    }

    assume true ==> m'#0 - m#0 == Mul(base#0, pk#0);
    // ----- alternative statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(452,3)
    if (*)
    {
        assume true;
        assume pk#0 < 0;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(454,19)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        a##3_0 := base#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        x##3_0 := pk#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        y##3_0 := LitInt(-1);
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.MulIsMonotonic(a##3_0, x##3_0, y##3_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(454,32)"} true;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(455,5)
        assume true;
        assert Mul(base#0, pk#0) <= 0 - base#0;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(456,5)
        assume true;
        assert false;
    }
    else if (*)
    {
        assume true;
        assume 0 < pk#0;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(458,19)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        a##2_0 := base#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        x##2_0 := LitInt(1);
        assume true;
        // ProcessCallStmt: CheckSubrange
        y##2_0 := pk#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.MulIsMonotonic(a##2_0, x##2_0, y##2_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(458,31)"} true;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(459,5)
        assume true;
        assert base#0 <= Mul(base#0, pk#0);
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(460,5)
        assume true;
        assert false;
    }
    else if (*)
    {
        assume true;
        assume pk#0 == LitInt(0);
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(462,5)
        assume true;
        assert Mul(base#0, pk#0) == LitInt(0);
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(463,5)
        assume true;
        assert m'#0 == m#0;
    }
    else
    {
        assume true;
        assume true;
        assume true;
        assume 0 <= pk#0 && pk#0 <= 0 && pk#0 != LitInt(0);
        assert false;
    }
}



procedure CheckWellformed$$_module.__default.MulIsMonotonic(a#0: int, x#0: int, y#0: int);
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.MulIsMonotonic(a#0: int, x#0: int, y#0: int);
  // user-defined preconditions
  requires LitInt(0) <= a#0;
  requires x#0 <= y#0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures Mul(a#0, x#0) <= Mul(a#0, y#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.MulIsMonotonic(a#0: int, x#0: int, y#0: int) returns ($_reverifyPost: bool);
  free requires 3 == $FunctionContextHeight;
  // user-defined preconditions
  requires LitInt(0) <= a#0;
  requires x#0 <= y#0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures Mul(a#0, x#0) <= Mul(a#0, y#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.MulIsMonotonic(a#0: int, x#0: int, y#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: MulIsMonotonic, Impl$$_module.__default.MulIsMonotonic
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(469,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.ModNoop(a#0: int, b#0: int);
  free requires 19 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.ModNoop(a#0: int, b#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: ModNoop, CheckWellformed$$_module.__default.ModNoop
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(473,6): initial state"} true;
    if (LitInt(0) <= a#0)
    {
    }

    assume LitInt(0) <= a#0 && a#0 < b#0;
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(475,16): post-state"} true;
    assert b#0 != 0;
    assume Mod(a#0, b#0) == a#0;
}



procedure Call$$_module.__default.ModNoop(a#0: int, b#0: int);
  // user-defined preconditions
  requires LitInt(0) <= a#0;
  requires a#0 < b#0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures Mod(a#0, b#0) == a#0;
  // frame condition
  free ensures old($Heap) == $Heap;



procedure CheckWellformed$$_module.__default.MulProperty(k#0: int, a#0: int, x#0: int, b#0: int, y#0: int) returns (p#0: int);
  free requires 17 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.MulProperty(k#0: int, a#0: int, x#0: int, b#0: int, y#0: int) returns (p#0: int);
  // user-defined preconditions
  requires 0 < k#0;
  requires Mul(k#0, a#0) + x#0 == Mul(k#0, b#0) + y#0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures y#0 - x#0 == Mul(k#0, p#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.MulProperty(k#0: int, a#0: int, x#0: int, b#0: int, y#0: int)
   returns (p#0: int, $_reverifyPost: bool);
  free requires 17 == $FunctionContextHeight;
  // user-defined preconditions
  requires 0 < k#0;
  requires Mul(k#0, a#0) + x#0 == Mul(k#0, b#0) + y#0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures y#0 - x#0 == Mul(k#0, p#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.MulProperty(k#0: int, a#0: int, x#0: int, b#0: int, y#0: int)
   returns (p#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: MulProperty, Impl$$_module.__default.MulProperty
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(481,0): initial state"} true;
    $_reverifyPost := false;
    // ----- calc statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(482,3)
    // Assume Fuel Constant
    if (*)
    {
        // ----- assert wf[initial] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(482,3)
        assume true;
        assume false;
    }
    else if (*)
    {
        // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(482,3)
        assume true;
        // ----- Hint0 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(482,3)
        // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(482,3)
        assume true;
        // ----- assert line0 == line1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(482,3)
        assert {:subsumption 0} (Mul(k#0, a#0) + x#0
           == Mul(k#0, b#0) + y#0)
           == 
          (Mul(k#0, a#0) - Mul(k#0, b#0)
           == y#0 - x#0);
        assume false;
    }
    else if (*)
    {
        // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(482,3)
        assume true;
        // ----- Hint1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(482,3)
        // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(482,3)
        assume true;
        // ----- assert line1 == line2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(482,3)
        assert {:subsumption 0} (Mul(k#0, a#0) - Mul(k#0, b#0)
           == y#0 - x#0)
           == 
          (Mul(k#0, a#0 - b#0)
           == y#0 - x#0);
        assume false;
    }

    assume (Mul(k#0, a#0) + x#0
       == Mul(k#0, b#0) + y#0)
       == 
      (Mul(k#0, a#0 - b#0)
       == y#0 - x#0);
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(487,5)
    assume true;
    assume true;
    p#0 := a#0 - b#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(487,12)"} true;
}



procedure CheckWellformed$$_module.__default.MulInverse(x#0: int, a#0: int, b#0: int, y#0: int);
  free requires 23 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.MulInverse(x#0: int, a#0: int, b#0: int, y#0: int);
  // user-defined preconditions
  requires x#0 != 0;
  requires Mul(x#0, a#0) + y#0 == Mul(x#0, b#0) + y#0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures a#0 == b#0;
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.MulInverse(x#0: int, a#0: int, b#0: int, y#0: int) returns ($_reverifyPost: bool);
  free requires 23 == $FunctionContextHeight;
  // user-defined preconditions
  requires x#0 != 0;
  requires Mul(x#0, a#0) + y#0 == Mul(x#0, b#0) + y#0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures a#0 == b#0;
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.MulInverse(x#0: int, a#0: int, b#0: int, y#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: MulInverse, Impl$$_module.__default.MulInverse
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NumberRepresentations.dfy(493,0): initial state"} true;
    $_reverifyPost := false;
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

const unique tytagFamily$_default: TyTagFamily;
