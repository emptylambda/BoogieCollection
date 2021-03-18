// Dafny 3.0.0.30204
// Command Line Options: -compile:0 -noVerify /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy -print:./Maps.bpl

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

// Box/unbox axiom for bv3
axiom (forall bx: Box :: 
  { $IsBox(bx, TBitvector(3)) } 
  $IsBox(bx, TBitvector(3))
     ==> $Box($Unbox(bx): bv3) == bx && $Is($Unbox(bx): bv3, TBitvector(3)));

axiom (forall v: bv3 :: { $Is(v, TBitvector(3)) } $Is(v, TBitvector(3)));

axiom (forall v: bv3, heap: Heap :: 
  { $IsAlloc(v, TBitvector(3), heap) } 
  $IsAlloc(v, TBitvector(3), heap));

function {:bvbuiltin "bvand"} and_bv3(bv3, bv3) : bv3;

function {:bvbuiltin "bvor"} or_bv3(bv3, bv3) : bv3;

function {:bvbuiltin "bvxor"} xor_bv3(bv3, bv3) : bv3;

function {:bvbuiltin "bvnot"} not_bv3(bv3) : bv3;

function {:bvbuiltin "bvadd"} add_bv3(bv3, bv3) : bv3;

function {:bvbuiltin "bvsub"} sub_bv3(bv3, bv3) : bv3;

function {:bvbuiltin "bvmul"} mul_bv3(bv3, bv3) : bv3;

function {:bvbuiltin "bvudiv"} div_bv3(bv3, bv3) : bv3;

function {:bvbuiltin "bvurem"} mod_bv3(bv3, bv3) : bv3;

function {:bvbuiltin "bvult"} lt_bv3(bv3, bv3) : bool;

function {:bvbuiltin "bvule"} le_bv3(bv3, bv3) : bool;

function {:bvbuiltin "bvuge"} ge_bv3(bv3, bv3) : bool;

function {:bvbuiltin "bvugt"} gt_bv3(bv3, bv3) : bool;

function {:bvbuiltin "bvshl"} LeftShift_bv3(bv3, bv3) : bv3;

function {:bvbuiltin "bvlshr"} RightShift_bv3(bv3, bv3) : bv3;

function {:bvbuiltin "ext_rotate_left"} LeftRotate_bv3(bv3, bv3) : bv3;

function {:bvbuiltin "ext_rotate_right"} RightRotate_bv3(bv3, bv3) : bv3;

function {:bvbuiltin "(_ int2bv 3)"} nat_to_bv3(int) : bv3;

function {:bvbuiltin "bv2int"} smt_nat_from_bv3(bv3) : int;

function nat_from_bv3(bv3) : int;

axiom (forall b: bv3 :: 
  { nat_from_bv3(b) } 
  0 <= nat_from_bv3(b)
     && nat_from_bv3(b) < 8
     && nat_from_bv3(b) == smt_nat_from_bv3(b));

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

const unique class._module.A?: ClassName;

function Tclass._module.A?() : Ty;

const unique Tagclass._module.A?: TyTag;

// Tclass._module.A? Tag
axiom Tag(Tclass._module.A?()) == Tagclass._module.A?
   && TagFamily(Tclass._module.A?()) == tytagFamily$A;

// Box/unbox axiom for Tclass._module.A?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.A?()) } 
  $IsBox(bx, Tclass._module.A?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.A?()));

// A: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.A?()) } 
  $Is($o, Tclass._module.A?()) <==> $o == null || dtype($o) == Tclass._module.A?());

// A: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.A?(), $h) } 
  $IsAlloc($o, Tclass._module.A?(), $h) <==> $o == null || read($h, $o, alloc));

axiom FDim(_module.A.x) == 0
   && FieldOfDecl(class._module.A?, field$x) == _module.A.x
   && !$IsGhostField(_module.A.x);

const _module.A.x: Field int;

// A.x: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.A.x) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.A?()
     ==> $Is(read($h, $o, _module.A.x), TInt));

// A.x: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.A.x) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.A?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.A.x), TInt, $h));

function Tclass._module.A() : Ty;

const unique Tagclass._module.A: TyTag;

// Tclass._module.A Tag
axiom Tag(Tclass._module.A()) == Tagclass._module.A
   && TagFamily(Tclass._module.A()) == tytagFamily$A;

// Box/unbox axiom for Tclass._module.A
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.A()) } 
  $IsBox(bx, Tclass._module.A())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.A()));

// _module.A: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.A()) } 
  $Is(c#0, Tclass._module.A()) <==> $Is(c#0, Tclass._module.A?()) && c#0 != null);

// _module.A: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.A(), $h) } 
  $IsAlloc(c#0, Tclass._module.A(), $h)
     <==> $IsAlloc(c#0, Tclass._module.A?(), $h));

const unique class._module.Elem?: ClassName;

function Tclass._module.Elem?() : Ty;

const unique Tagclass._module.Elem?: TyTag;

// Tclass._module.Elem? Tag
axiom Tag(Tclass._module.Elem?()) == Tagclass._module.Elem?
   && TagFamily(Tclass._module.Elem?()) == tytagFamily$Elem;

// Box/unbox axiom for Tclass._module.Elem?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Elem?()) } 
  $IsBox(bx, Tclass._module.Elem?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Elem?()));

// Elem: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.Elem?()) } 
  $Is($o, Tclass._module.Elem?())
     <==> $o == null || dtype($o) == Tclass._module.Elem?());

// Elem: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.Elem?(), $h) } 
  $IsAlloc($o, Tclass._module.Elem?(), $h) <==> $o == null || read($h, $o, alloc));

function Tclass._module.Elem() : Ty;

const unique Tagclass._module.Elem: TyTag;

// Tclass._module.Elem Tag
axiom Tag(Tclass._module.Elem()) == Tagclass._module.Elem
   && TagFamily(Tclass._module.Elem()) == tytagFamily$Elem;

// Box/unbox axiom for Tclass._module.Elem
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Elem()) } 
  $IsBox(bx, Tclass._module.Elem())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Elem()));

// _module.Elem: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.Elem()) } 
  $Is(c#0, Tclass._module.Elem())
     <==> $Is(c#0, Tclass._module.Elem?()) && c#0 != null);

// _module.Elem: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.Elem(), $h) } 
  $IsAlloc(c#0, Tclass._module.Elem(), $h)
     <==> $IsAlloc(c#0, Tclass._module.Elem?(), $h));

const unique class._module.MyClass?: ClassName;

function Tclass._module.MyClass?() : Ty;

const unique Tagclass._module.MyClass?: TyTag;

// Tclass._module.MyClass? Tag
axiom Tag(Tclass._module.MyClass?()) == Tagclass._module.MyClass?
   && TagFamily(Tclass._module.MyClass?()) == tytagFamily$MyClass;

// Box/unbox axiom for Tclass._module.MyClass?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.MyClass?()) } 
  $IsBox(bx, Tclass._module.MyClass?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.MyClass?()));

// MyClass: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.MyClass?()) } 
  $Is($o, Tclass._module.MyClass?())
     <==> $o == null || dtype($o) == Tclass._module.MyClass?());

// MyClass: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.MyClass?(), $h) } 
  $IsAlloc($o, Tclass._module.MyClass?(), $h)
     <==> $o == null || read($h, $o, alloc));

function Tclass._module.MyClass() : Ty;

const unique Tagclass._module.MyClass: TyTag;

// Tclass._module.MyClass Tag
axiom Tag(Tclass._module.MyClass()) == Tagclass._module.MyClass
   && TagFamily(Tclass._module.MyClass()) == tytagFamily$MyClass;

// Box/unbox axiom for Tclass._module.MyClass
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.MyClass()) } 
  $IsBox(bx, Tclass._module.MyClass())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.MyClass()));

// _module.MyClass: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.MyClass()) } 
  $Is(c#0, Tclass._module.MyClass())
     <==> $Is(c#0, Tclass._module.MyClass?()) && c#0 != null);

// _module.MyClass: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.MyClass(), $h) } 
  $IsAlloc(c#0, Tclass._module.MyClass(), $h)
     <==> $IsAlloc(c#0, Tclass._module.MyClass?(), $h));

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
  free requires 55 == $FunctionContextHeight;
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
  free requires 55 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default._default_Main() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var m#0: Map Box Box
     where $Is(m#0, TMap(TInt, TInt)) && $IsAlloc(m#0, TMap(TInt, TInt), $Heap);

    // AddMethodImpl: Main, Impl$$_module.__default._default_Main
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(6,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(7,10)
    assume true;
    assume true;
    m#0 := Lit(Map#Build(Map#Empty(): Map Box Box, $Box(LitInt(2)), $Box(LitInt(3))));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(7,21)"} true;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(9,4)
    assume true;
    if (Map#Domain(m#0)[$Box(2)])
    {
        // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(11,7)
        assume true;
    }
    else
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(14,6)
        assume true;
        assert false;
    }

    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(16,4)
    assume true;
    if (!Map#Domain(m#0)[$Box(3)])
    {
        // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(18,7)
        assume true;
    }
    else
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(21,6)
        assume true;
        assert false;
    }

    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(23,4)
    assert Map#Domain(m#0)[$Box(LitInt(2))];
    assume true;
    if ($Unbox(Map#Elements(m#0)[$Box(LitInt(2))]): int == LitInt(3))
    {
        // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(25,7)
        assume true;
    }
    else
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(28,6)
        assume true;
        assert false;
    }

    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(30,4)
    assume true;
    if (Set#Disjoint(Map#Domain(m#0), 
      Map#Domain(Lit(Map#Build(Map#Empty(): Map Box Box, $Box(LitInt(3)), $Box(LitInt(3)))))))
    {
        // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(32,7)
        assume true;
    }
    else
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(35,6)
        assume true;
        assert false;
    }

    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(37,4)
    assume true;
    if (Map#Equal(Map#Build(m#0, $Box(LitInt(2)), $Box(LitInt(4))), 
      Map#Build(Map#Empty(): Map Box Box, $Box(LitInt(2)), $Box(LitInt(4)))))
    {
        // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(39,7)
        assume true;
    }
    else
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(42,6)
        assume true;
        assert false;
    }

    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(44,4)
    assume true;
    if (Map#Equal(Map#Build(m#0, $Box(LitInt(7)), $Box(LitInt(1))), 
      Map#Build(Map#Build(Map#Empty(): Map Box Box, $Box(LitInt(2)), $Box(LitInt(3))), 
        $Box(LitInt(7)), 
        $Box(LitInt(1)))))
    {
        // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(46,7)
        assume true;
    }
    else
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(49,6)
        assume true;
        assert false;
    }

    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(51,4)
    assume true;
    if (Map#Equal(m#0, Map#Build(Map#Empty(): Map Box Box, $Box(LitInt(2)), $Box(LitInt(3)))))
    {
        // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(53,7)
        assume true;
    }
    else
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(56,6)
        assume true;
        assert false;
    }
}



procedure CheckWellformed$$_module.__default.m();
  free requires 29 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.m();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.m() returns ($_reverifyPost: bool);
  free requires 29 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.m() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var a#0: Map Box Box
     where $Is(a#0, TMap(TInt, TInt)) && $IsAlloc(a#0, TMap(TInt, TInt), $Heap);
  var b#0: Map Box Box
     where $Is(b#0, TMap(TInt, TInt)) && $IsAlloc(b#0, TMap(TInt, TInt), $Heap);

    // AddMethodImpl: m, Impl$$_module.__default.m
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(61,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(62,10)
    assume true;
    assume true;
    a#0 := Lit(Map#Build(Map#Empty(): Map Box Box, $Box(LitInt(2)), $Box(LitInt(3))));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(62,21)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(62,30)
    assume true;
    assume true;
    b#0 := Lit(Map#Build(Map#Empty(): Map Box Box, $Box(LitInt(3)), $Box(LitInt(2))));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(62,41)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(63,4)
    assert {:subsumption 0} Map#Domain(b#0)[$Box(LitInt(3))];
    assert {:subsumption 0} Map#Domain(a#0)[Map#Elements(b#0)[$Box(LitInt(3))]];
    assume true;
    assert $Unbox(Map#Elements(a#0)[Map#Elements(b#0)[$Box(LitInt(3))]]): int == LitInt(3);
}



procedure CheckWellformed$$_module.__default.m2(a#0: Map Box Box
       where $Is(a#0, TMap(TInt, TBool)) && $IsAlloc(a#0, TMap(TInt, TBool), $Heap), 
    b#0: Map Box Box
       where $Is(b#0, TMap(TInt, TBool)) && $IsAlloc(b#0, TMap(TInt, TBool), $Heap));
  free requires 56 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.m2(a#0: Map Box Box, b#0: Map Box Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var i#0: int;

    // AddMethodImpl: m2, CheckWellformed$$_module.__default.m2
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(65,7): initial state"} true;
    havoc i#0;
    assume true;
    if (*)
    {
        assume LitInt(0) <= i#0;
        assume i#0 < 100;
        assume Map#Domain(a#0)[$Box(i#0)];
        assume Map#Domain(b#0)[$Box(i#0)];
        assert Map#Domain(a#0)[$Box(i#0)];
        assert Map#Domain(b#0)[$Box(i#0)];
        assume $Unbox(Map#Elements(a#0)[$Box(i#0)]): bool
           != $Unbox(Map#Elements(b#0)[$Box(i#0)]): bool;
    }
    else
    {
        assume LitInt(0) <= i#0 && i#0 < 100
           ==> Map#Domain(a#0)[$Box(i#0)]
             && Map#Domain(b#0)[$Box(i#0)]
             && $Unbox(Map#Elements(a#0)[$Box(i#0)]): bool
               != $Unbox(Map#Elements(b#0)[$Box(i#0)]): bool;
    }

    assume (forall i#1: int :: 
      { $Unbox(Map#Elements(b#0)[$Box(i#1)]): bool } 
        { $Unbox(Map#Elements(a#0)[$Box(i#1)]): bool } 
        { Map#Domain(b#0)[$Box(i#1)] } 
        { Map#Domain(a#0)[$Box(i#1)] } 
      LitInt(0) <= i#1 && i#1 < 100
         ==> Map#Domain(a#0)[$Box(i#1)]
           && Map#Domain(b#0)[$Box(i#1)]
           && $Unbox(Map#Elements(a#0)[$Box(i#1)]): bool
             != $Unbox(Map#Elements(b#0)[$Box(i#1)]): bool);
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
    assume $HeapSucc(old($Heap), $Heap);
}



procedure Call$$_module.__default.m2(a#0: Map Box Box
       where $Is(a#0, TMap(TInt, TBool)) && $IsAlloc(a#0, TMap(TInt, TBool), $Heap), 
    b#0: Map Box Box
       where $Is(b#0, TMap(TInt, TBool)) && $IsAlloc(b#0, TMap(TInt, TBool), $Heap));
  // user-defined preconditions
  requires (forall i#1: int :: 
    { $Unbox(Map#Elements(b#0)[$Box(i#1)]): bool } 
      { $Unbox(Map#Elements(a#0)[$Box(i#1)]): bool } 
      { Map#Domain(b#0)[$Box(i#1)] } 
      { Map#Domain(a#0)[$Box(i#1)] } 
    LitInt(0) <= i#1 && i#1 < 100
       ==> Map#Domain(a#0)[$Box(i#1)]
         && Map#Domain(b#0)[$Box(i#1)]
         && $Unbox(Map#Elements(a#0)[$Box(i#1)]): bool
           != $Unbox(Map#Elements(b#0)[$Box(i#1)]): bool);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.m2(a#0: Map Box Box
       where $Is(a#0, TMap(TInt, TBool)) && $IsAlloc(a#0, TMap(TInt, TBool), $Heap), 
    b#0: Map Box Box
       where $Is(b#0, TMap(TInt, TBool)) && $IsAlloc(b#0, TMap(TInt, TBool), $Heap))
   returns ($_reverifyPost: bool);
  free requires 56 == $FunctionContextHeight;
  // user-defined preconditions
  requires (forall i#1: int :: 
    { $Unbox(Map#Elements(b#0)[$Box(i#1)]): bool } 
      { $Unbox(Map#Elements(a#0)[$Box(i#1)]): bool } 
      { Map#Domain(b#0)[$Box(i#1)] } 
      { Map#Domain(a#0)[$Box(i#1)] } 
    LitInt(0) <= i#1 && i#1 < 100
       ==> Map#Domain(a#0)[$Box(i#1)]
         && Map#Domain(b#0)[$Box(i#1)]
         && $Unbox(Map#Elements(a#0)[$Box(i#1)]): bool
           != $Unbox(Map#Elements(b#0)[$Box(i#1)]): bool);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.m2(a#0: Map Box Box, b#0: Map Box Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var i#2: int;

    // AddMethodImpl: m2, Impl$$_module.__default.m2
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(67,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(68,4)
    // Begin Comprehension WF check
    havoc i#2;
    if (true)
    {
        if (LitInt(0) <= i#2)
        {
        }

        if (LitInt(0) <= i#2 && i#2 < 100)
        {
            assert {:subsumption 0} Map#Domain(a#0)[$Box(i#2)];
            if (!$Unbox(Map#Elements(a#0)[$Box(i#2)]): bool)
            {
                assert {:subsumption 0} Map#Domain(b#0)[$Box(i#2)];
            }
        }
    }

    // End Comprehension WF check
    assume true;
    assert (forall i#3: int :: 
      { $Unbox(Map#Elements(b#0)[$Box(i#3)]): bool } 
        { $Unbox(Map#Elements(a#0)[$Box(i#3)]): bool } 
      LitInt(0) <= i#3 && i#3 < 100
         ==> $Unbox(Map#Elements(a#0)[$Box(i#3)]): bool
           || $Unbox(Map#Elements(b#0)[$Box(i#3)]): bool);
}



procedure CheckWellformed$$_module.__default.m3(a#0: Map Box Box
       where $Is(a#0, TMap(TInt, TInt)) && $IsAlloc(a#0, TMap(TInt, TInt), $Heap));
  free requires 31 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.m3(a#0: Map Box Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var i#0: int;

    // AddMethodImpl: m3, CheckWellformed$$_module.__default.m3
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(70,7): initial state"} true;
    havoc i#0;
    assume true;
    if (*)
    {
        assume LitInt(0) <= i#0;
        assume i#0 < 100;
        assume Map#Domain(a#0)[$Box(i#0)];
        assert Map#Domain(a#0)[$Box(i#0)];
        assume $Unbox(Map#Elements(a#0)[$Box(i#0)]): int == Mul(i#0, i#0);
    }
    else
    {
        assume LitInt(0) <= i#0 && i#0 < 100
           ==> Map#Domain(a#0)[$Box(i#0)]
             && $Unbox(Map#Elements(a#0)[$Box(i#0)]): int == Mul(i#0, i#0);
    }

    assume (forall i#1: int :: 
      { $Unbox(Map#Elements(a#0)[$Box(i#1)]): int } { Map#Domain(a#0)[$Box(i#1)] } 
      LitInt(0) <= i#1 && i#1 < 100
         ==> Map#Domain(a#0)[$Box(i#1)]
           && $Unbox(Map#Elements(a#0)[$Box(i#1)]): int == Mul(i#1, i#1));
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
    assume $HeapSucc(old($Heap), $Heap);
}



procedure Call$$_module.__default.m3(a#0: Map Box Box
       where $Is(a#0, TMap(TInt, TInt)) && $IsAlloc(a#0, TMap(TInt, TInt), $Heap));
  // user-defined preconditions
  requires (forall i#1: int :: 
    { $Unbox(Map#Elements(a#0)[$Box(i#1)]): int } { Map#Domain(a#0)[$Box(i#1)] } 
    LitInt(0) <= i#1 && i#1 < 100
       ==> Map#Domain(a#0)[$Box(i#1)]
         && $Unbox(Map#Elements(a#0)[$Box(i#1)]): int == Mul(i#1, i#1));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.m3(a#0: Map Box Box
       where $Is(a#0, TMap(TInt, TInt)) && $IsAlloc(a#0, TMap(TInt, TInt), $Heap))
   returns ($_reverifyPost: bool);
  free requires 31 == $FunctionContextHeight;
  // user-defined preconditions
  requires (forall i#1: int :: 
    { $Unbox(Map#Elements(a#0)[$Box(i#1)]): int } { Map#Domain(a#0)[$Box(i#1)] } 
    LitInt(0) <= i#1 && i#1 < 100
       ==> Map#Domain(a#0)[$Box(i#1)]
         && $Unbox(Map#Elements(a#0)[$Box(i#1)]): int == Mul(i#1, i#1));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.m3(a#0: Map Box Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: m3, Impl$$_module.__default.m3
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(72,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(73,4)
    assert {:subsumption 0} Map#Domain(a#0)[$Box(LitInt(20))];
    assume true;
    assert $Unbox(Map#Elements(a#0)[$Box(LitInt(20))]): int == LitInt(400);
}



procedure CheckWellformed$$_module.__default.m4();
  free requires 30 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.m4();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.m4() returns ($_reverifyPost: bool);
  free requires 30 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.m4() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var a#0: Map Box Box
     where $Is(a#0, TMap(TInt, TInt)) && $IsAlloc(a#0, TMap(TInt, TInt), $Heap);

    // AddMethodImpl: m4, Impl$$_module.__default.m4
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(76,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(77,10)
    assume true;
    assume true;
    a#0 := Lit(Map#Build(Map#Empty(): Map Box Box, $Box(LitInt(3)), $Box(LitInt(9))));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(77,23)"} true;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(78,4)
    assert Map#Domain(a#0)[$Box(LitInt(4))];
    assume true;
    if ($Unbox(Map#Elements(a#0)[$Box(LitInt(4))]): int == LitInt(4))
    {
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(80,8)
        // TrCallStmt: Before ProcessCallStmt
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.m();
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(80,9)"} true;
    }
    else
    {
    }
}



procedure CheckWellformed$$_module.__default.m5(a#0: Map Box Box
       where $Is(a#0, TMap(TInt, TInt)) && $IsAlloc(a#0, TMap(TInt, TInt), $Heap));
  free requires 57 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.m5(a#0: Map Box Box
       where $Is(a#0, TMap(TInt, TInt)) && $IsAlloc(a#0, TMap(TInt, TInt), $Heap));
  // user-defined preconditions
  requires Map#Domain(a#0)[$Box(20)];
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.m5(a#0: Map Box Box
       where $Is(a#0, TMap(TInt, TInt)) && $IsAlloc(a#0, TMap(TInt, TInt), $Heap))
   returns ($_reverifyPost: bool);
  free requires 57 == $FunctionContextHeight;
  // user-defined preconditions
  requires Map#Domain(a#0)[$Box(20)];
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.m5(a#0: Map Box Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: m5, Impl$$_module.__default.m5
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(86,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(87,4)
    assert {:subsumption 0} Map#Domain(a#0)[$Box(LitInt(20))];
    if (LitInt(0) < $Unbox(Map#Elements(a#0)[$Box(LitInt(20))]): int)
    {
        assert {:subsumption 0} Map#Domain(a#0)[$Box(LitInt(20))];
    }

    assume true;
    assert $Unbox(Map#Elements(a#0)[$Box(LitInt(20))]): int <= LitInt(0)
       || 0 < $Unbox(Map#Elements(a#0)[$Box(LitInt(20))]): int;
}



procedure CheckWellformed$$_module.__default.m6();
  free requires 58 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.m6();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.m6() returns ($_reverifyPost: bool);
  free requires 58 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.m6() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var a#0: Map Box Box
     where $Is(a#0, TMap(TInt, TInt)) && $IsAlloc(a#0, TMap(TInt, TInt), $Heap);

    // AddMethodImpl: m6, Impl$$_module.__default.m6
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(90,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(91,10)
    assume true;
    assume true;
    a#0 := Lit(Map#Build(Map#Empty(): Map Box Box, $Box(LitInt(3)), $Box(LitInt(9))));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(91,23)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(92,4)
    assume true;
    assert Map#Equal(Map#Build(a#0, $Box(LitInt(3)), $Box(LitInt(5))), 
      Map#Build(Map#Empty(): Map Box Box, $Box(LitInt(3)), $Box(LitInt(5))));
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(93,4)
    assume true;
    assert Map#Equal(Map#Build(a#0, $Box(LitInt(2)), $Box(LitInt(5))), 
      Map#Build(Map#Build(Map#Empty(): Map Box Box, $Box(LitInt(2)), $Box(LitInt(5))), 
        $Box(LitInt(3)), 
        $Box(LitInt(9))));
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(94,4)
    assume true;
    assert Map#Equal(Map#Build(a#0, $Box(LitInt(2)), $Box(LitInt(5))), 
      Map#Build(Map#Build(Map#Build(Map#Empty(): Map Box Box, $Box(LitInt(2)), $Box(LitInt(6))), 
          $Box(LitInt(3)), 
          $Box(LitInt(9))), 
        $Box(LitInt(2)), 
        $Box(LitInt(5))));
}



procedure CheckWellformed$$_module.__default.m7();
  free requires 59 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.m7();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.m7() returns ($_reverifyPost: bool);
  free requires 59 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.m7() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var a#0: Map Box Box
     where $Is(a#0, TMap(TInt, TInt)) && $IsAlloc(a#0, TMap(TInt, TInt), $Heap);
  var i#0: int;
  var i#2: int;

    // AddMethodImpl: m7, Impl$$_module.__default.m7
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(97,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(98,10)
    assume true;
    assume true;
    a#0 := Lit(Map#Build(Map#Build(Map#Build(Map#Empty(): Map Box Box, $Box(LitInt(1)), $Box(LitInt(1))), 
          $Box(LitInt(2)), 
          $Box(LitInt(4))), 
        $Box(LitInt(3)), 
        $Box(LitInt(9))));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(98,33)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(99,4)
    // Begin Comprehension WF check
    havoc i#0;
    if (true)
    {
        if (Map#Domain(a#0)[$Box(i#0)])
        {
            assert {:subsumption 0} Map#Domain(a#0)[$Box(i#0)];
        }
    }

    // End Comprehension WF check
    assume true;
    assert (forall i#1: int :: 
      { $Unbox(Map#Elements(a#0)[$Box(i#1)]): int } { Map#Domain(a#0)[$Box(i#1)] } 
      Map#Domain(a#0)[$Box(i#1)]
         ==> $Unbox(Map#Elements(a#0)[$Box(i#1)]): int == Mul(i#1, i#1));
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(100,4)
    assume true;
    assert !Map#Domain(a#0)[$Box(0)];
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(101,4)
    assume true;
    assert Map#Domain(a#0)[$Box(1)];
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(102,4)
    assume true;
    assert Map#Domain(a#0)[$Box(2)];
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(103,4)
    assume true;
    assert Map#Domain(a#0)[$Box(3)];
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(104,4)
    // Begin Comprehension WF check
    havoc i#2;
    if (true)
    {
        if (1 <= i#2)
        {
        }

        if (i#2 < 1 || i#2 > 3)
        {
        }
    }

    // End Comprehension WF check
    assume true;
    assert (forall i#3: int :: 
      { Map#Domain(a#0)[$Box(i#3)] } 
      i#3 < 1 || i#3 > 3 ==> !Map#Domain(a#0)[$Box(i#3)]);
}



procedure CheckWellformed$$_module.__default.m8();
  free requires 32 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.m8();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.m8() returns ($_reverifyPost: bool);
  free requires 32 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.m8() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var a#0: Map Box Box
     where $Is(a#0, TMap(TInt, TInt)) && $IsAlloc(a#0, TMap(TInt, TInt), $Heap);
  var i#0: int;
  var i#2: int;
  var n#0: int;
  var $rhs#0: int;
  var $rhs#1: int;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var i#3: int;
  var k#0: int;
  var $decr$loop#00: int;
  var a##0: Map Box Box;

    // AddMethodImpl: m8, Impl$$_module.__default.m8
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(107,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(108,24)
    assume true;
    assume true;
    a#0 := Lit(Map#Empty(): Map Box Box);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(108,31)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(109,4)
    // Begin Comprehension WF check
    havoc i#0;
    if (true)
    {
    }

    // End Comprehension WF check
    assume true;
    assert (forall i#1: int :: 
      { Map#Domain(a#0)[$Box(i#1)] } 
      true ==> !Map#Domain(a#0)[$Box(i#1)]);
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(110,12)
    assume true;
    assume true;
    assume true;
    $rhs#0 := LitInt(0);
    assume true;
    $rhs#1 := LitInt(100);
    i#2 := $rhs#0;
    n#0 := $rhs#1;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(110,20)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(111,4)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := n#0 - i#2;
    havoc $w$loop#0;
    while (true)
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> LitInt(0) <= i#2;
      invariant $w$loop#0 ==> i#2 <= n#0;
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0
         ==> (forall i#4: int :: 
          { $Unbox(Map#Elements(a#0)[$Box(i#4)]): int } { Map#Domain(a#0)[$Box(i#4)] } 
          Map#Domain(a#0)[$Box(i#4)]
             ==> $Unbox(Map#Elements(a#0)[$Box(i#4)]): int == Mul(i#4, i#4));
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0
         ==> (forall k#1: int :: 
          { Map#Domain(a#0)[$Box(k#1)] } 
          true ==> (LitInt(0) <= k#1 && k#1 < i#2 <==> Map#Domain(a#0)[$Box(k#1)]));
      free invariant (forall $o: ref :: 
        { $Heap[$o] } 
        $o != null && read(old($Heap), $o, alloc)
           ==> $Heap[$o] == $PreLoopHeap$loop#0[$o]);
      free invariant $HeapSucc($PreLoopHeap$loop#0, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
        { read($Heap, $o, $f) } 
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
      free invariant n#0 - i#2 <= $decr_init$loop#00 && (n#0 - i#2 == $decr_init$loop#00 ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(111,3): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            if (LitInt(0) <= i#2)
            {
            }

            assume true;
            assume LitInt(0) <= i#2 && i#2 <= n#0;
            // Begin Comprehension WF check
            havoc i#3;
            if (true)
            {
                if (Map#Domain(a#0)[$Box(i#3)])
                {
                    assert {:subsumption 0} Map#Domain(a#0)[$Box(i#3)];
                }
            }

            // End Comprehension WF check
            assume true;
            assume (forall i#4: int :: 
              { $Unbox(Map#Elements(a#0)[$Box(i#4)]): int } { Map#Domain(a#0)[$Box(i#4)] } 
              Map#Domain(a#0)[$Box(i#4)]
                 ==> $Unbox(Map#Elements(a#0)[$Box(i#4)]): int == Mul(i#4, i#4));
            // Begin Comprehension WF check
            havoc k#0;
            if (true)
            {
                if (LitInt(0) <= k#0)
                {
                }
            }

            // End Comprehension WF check
            assume true;
            assume (forall k#1: int :: 
              { Map#Domain(a#0)[$Box(k#1)] } 
              true ==> (LitInt(0) <= k#1 && k#1 < i#2 <==> Map#Domain(a#0)[$Box(k#1)]));
            assume true;
            assume false;
        }

        assume true;
        if (n#0 <= i#2)
        {
            break;
        }

        $decr$loop#00 := n#0 - i#2;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(116,9)
        assume true;
        assume true;
        a#0 := Map#Build(a#0, $Box(i#2), $Box(Mul(i#2, i#2)));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(116,24)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(117,9)
        assume true;
        assume true;
        i#2 := i#2 + 1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(117,16)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(111,4)
        assert 0 <= $decr$loop#00 || n#0 - i#2 == $decr$loop#00;
        assert n#0 - i#2 < $decr$loop#00;
        assume true;
        assume true;
        assume true;
    }

    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(119,4)
    assume true;
    assert Set#Disjoint(Map#Domain(a#0), 
      Map#Domain(Lit(Map#Build(Map#Empty(): Map Box Box, $Box(LitInt(-1)), $Box(LitInt(2))))));
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(120,6)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##0 := a#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.m3(a##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(120,8)"} true;
}



procedure CheckWellformed$$_module.__default.m9();
  free requires 60 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.m9();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.m9() returns ($_reverifyPost: bool);
  free requires 60 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.m9() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var a#0: Map Box Box
     where $Is(a#0, TMap(TInt, TInt)) && $IsAlloc(a#0, TMap(TInt, TInt), $Heap);
  var b#0: Map Box Box
     where $Is(b#0, TMap(TInt, TInt)) && $IsAlloc(b#0, TMap(TInt, TInt), $Heap);
  var $rhs#0: Map Box Box where $Is($rhs#0, TMap(TInt, TInt));
  var $rhs#1: Map Box Box where $Is($rhs#1, TMap(TInt, TInt));

    // AddMethodImpl: m9, Impl$$_module.__default.m9
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(123,0): initial state"} true;
    $_reverifyPost := false;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(124,27)
    assume true;
    assume true;
    assume true;
    $rhs#0 := Lit(Map#Empty(): Map Box Box);
    assume true;
    $rhs#1 := Lit(Map#Empty(): Map Box Box);
    a#0 := $rhs#0;
    b#0 := $rhs#1;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(124,41)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(125,4)
    assume true;
    assert Set#Disjoint(Map#Domain(a#0), Map#Domain(b#0));
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(126,6)
    assume true;
    assume true;
    b#0 := Lit(Map#Build(Map#Build(Map#Build(Map#Build(Map#Empty(): Map Box Box, $Box(LitInt(2)), $Box(LitInt(3))), 
            $Box(LitInt(4)), 
            $Box(LitInt(2))), 
          $Box(LitInt(5)), 
          $Box(LitInt(-6))), 
        $Box(LitInt(6)), 
        $Box(LitInt(7))));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(126,33)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(127,4)
    assume true;
    assert Set#Disjoint(Map#Domain(a#0), Map#Domain(b#0));
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(128,4)
    assume true;
    assert Set#Disjoint(Map#Domain(b#0), 
      Map#Domain(Lit(Map#Build(Map#Empty(): Map Box Box, $Box(LitInt(6)), $Box(LitInt(3))))));
}



procedure CheckWellformed$$_module.__default.m10();
  free requires 61 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.m10();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.m10() returns ($_reverifyPost: bool);
  free requires 61 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.m10() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var a#0: Map Box Box
     where $Is(a#0, TMap(TInt, TInt)) && $IsAlloc(a#0, TMap(TInt, TInt), $Heap);
  var b#0: Map Box Box
     where $Is(b#0, TMap(TInt, TInt)) && $IsAlloc(b#0, TMap(TInt, TInt), $Heap);
  var $rhs#0: Map Box Box where $Is($rhs#0, TMap(TInt, TInt));
  var $rhs#1: Map Box Box where $Is($rhs#1, TMap(TInt, TInt));

    // AddMethodImpl: m10, Impl$$_module.__default.m10
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(131,0): initial state"} true;
    $_reverifyPost := false;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(132,13)
    assume true;
    assume true;
    assume true;
    $rhs#0 := Lit(Map#Empty(): Map Box Box);
    assume true;
    $rhs#1 := Lit(Map#Empty(): Map Box Box);
    a#0 := $rhs#0;
    b#0 := $rhs#1;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(132,27)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(133,4)
    assume true;
    assert Set#Disjoint(Map#Domain(a#0), Map#Domain(b#0));
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(134,6)
    assume true;
    assume true;
    b#0 := Lit(Map#Build(Map#Build(Map#Build(Map#Build(Map#Empty(): Map Box Box, $Box(LitInt(2)), $Box(LitInt(3))), 
            $Box(LitInt(4)), 
            $Box(LitInt(2))), 
          $Box(LitInt(5)), 
          $Box(LitInt(-6))), 
        $Box(LitInt(6)), 
        $Box(LitInt(7))));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(134,33)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(135,4)
    assume true;
    assert Set#Disjoint(Map#Domain(a#0), Map#Domain(b#0));
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(136,6)
    assume true;
    assume true;
    a#0 := Lit(Map#Build(Map#Build(Map#Build(Map#Build(Map#Empty(): Map Box Box, $Box(LitInt(3)), $Box(LitInt(3))), 
            $Box(LitInt(1)), 
            $Box(LitInt(2))), 
          $Box(LitInt(9)), 
          $Box(LitInt(-6))), 
        $Box(LitInt(8)), 
        $Box(LitInt(7))));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(136,33)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(137,4)
    assume true;
    assert Set#Disjoint(Map#Domain(a#0), Map#Domain(b#0));
}



procedure CheckWellformed$$_module.__default.m11(_module._default.m11$U: Ty, 
    _module._default.m11$V: Ty, 
    a#0: Map Box Box
       where $Is(a#0, TMap(_module._default.m11$U, _module._default.m11$V))
         && $IsAlloc(a#0, TMap(_module._default.m11$U, _module._default.m11$V), $Heap), 
    b#0: Map Box Box
       where $Is(b#0, TMap(_module._default.m11$U, _module._default.m11$V))
         && $IsAlloc(b#0, TMap(_module._default.m11$U, _module._default.m11$V), $Heap));
  free requires 62 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.m11(_module._default.m11$U: Ty, 
    _module._default.m11$V: Ty, 
    a#0: Map Box Box
       where $Is(a#0, TMap(_module._default.m11$U, _module._default.m11$V))
         && $IsAlloc(a#0, TMap(_module._default.m11$U, _module._default.m11$V), $Heap), 
    b#0: Map Box Box
       where $Is(b#0, TMap(_module._default.m11$U, _module._default.m11$V))
         && $IsAlloc(b#0, TMap(_module._default.m11$U, _module._default.m11$V), $Heap));
  // user-defined preconditions
  requires (forall i#1: Box :: 
    { Map#Domain(b#0)[i#1] } { Map#Domain(a#0)[i#1] } 
    $IsBox(i#1, _module._default.m11$U)
       ==> !(Map#Domain(a#0)[i#1] && Map#Domain(b#0)[i#1]));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.m11(_module._default.m11$U: Ty, 
    _module._default.m11$V: Ty, 
    a#0: Map Box Box
       where $Is(a#0, TMap(_module._default.m11$U, _module._default.m11$V))
         && $IsAlloc(a#0, TMap(_module._default.m11$U, _module._default.m11$V), $Heap), 
    b#0: Map Box Box
       where $Is(b#0, TMap(_module._default.m11$U, _module._default.m11$V))
         && $IsAlloc(b#0, TMap(_module._default.m11$U, _module._default.m11$V), $Heap))
   returns ($_reverifyPost: bool);
  free requires 62 == $FunctionContextHeight;
  // user-defined preconditions
  requires (forall i#1: Box :: 
    { Map#Domain(b#0)[i#1] } { Map#Domain(a#0)[i#1] } 
    $IsBox(i#1, _module._default.m11$U)
       ==> !(Map#Domain(a#0)[i#1] && Map#Domain(b#0)[i#1]));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.m11(_module._default.m11$U: Ty, 
    _module._default.m11$V: Ty, 
    a#0: Map Box Box, 
    b#0: Map Box Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: m11, Impl$$_module.__default.m11
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(141,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(142,4)
    assume true;
    assert Set#Disjoint(Map#Domain(a#0), Map#Domain(b#0));
}



procedure CheckWellformed$$_module.__default.m12();
  free requires 63 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.m12();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.m12() returns ($_reverifyPost: bool);
  free requires 63 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.m12() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var x#0: Map Box Box
     where $Is(x#0, TMap(TInt, TInt)) && $IsAlloc(x#0, TMap(TInt, TInt), $Heap);
  var i#0: int;

    // AddMethodImpl: m12, Impl$$_module.__default.m12
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(146,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(147,10)
    assume true;
    // Begin Comprehension WF check
    havoc i#0;
    if (true)
    {
        if (LitInt(0) <= i#0)
        {
        }

        if (LitInt(0) <= i#0 && i#0 < 10)
        {
        }
    }

    // End Comprehension WF check
    assume true;
    x#0 := Map#Glue((lambda $w#0: Box :: LitInt(0) <= $Unbox($w#0): int && $Unbox($w#0): int < 10), 
      (lambda $w#0: Box :: $Box(Mul($Unbox($w#0): int, LitInt(2)))), 
      TMap(TInt, TInt));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(147,40)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(148,4)
    assume true;
    assert Map#Domain(x#0)[$Box(0)];
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(149,4)
    assume true;
    assert Map#Domain(x#0)[$Box(1)];
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(150,4)
    assume true;
    assert !Map#Domain(x#0)[$Box(10)];
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(151,4)
    assert {:subsumption 0} Map#Domain(x#0)[$Box(LitInt(0))];
    if ($Unbox(Map#Elements(x#0)[$Box(LitInt(0))]): int == LitInt(0))
    {
        assert {:subsumption 0} Map#Domain(x#0)[$Box(LitInt(2))];
    }

    assume true;
    assert {:subsumption 0} $Unbox(Map#Elements(x#0)[$Box(LitInt(0))]): int == LitInt(0);
    assert {:subsumption 0} $Unbox(Map#Elements(x#0)[$Box(LitInt(2))]): int == LitInt(4);
    assume $Unbox(Map#Elements(x#0)[$Box(LitInt(0))]): int == LitInt(0)
       && $Unbox(Map#Elements(x#0)[$Box(LitInt(2))]): int == LitInt(4);
}



// function declaration for _module._default.domain
function _module.__default.domain(_module._default.domain$U: Ty, _module._default.domain$V: Ty, m#0: Map Box Box)
   : Set Box;

function _module.__default.domain#canCall(_module._default.domain$U: Ty, _module._default.domain$V: Ty, m#0: Map Box Box)
   : bool;

// consequence axiom for _module.__default.domain
axiom 33 <= $FunctionContextHeight
   ==> (forall _module._default.domain$U: Ty, _module._default.domain$V: Ty, m#0: Map Box Box :: 
    { _module.__default.domain(_module._default.domain$U, _module._default.domain$V, m#0) } 
    _module.__default.domain#canCall(_module._default.domain$U, _module._default.domain$V, m#0)
         || (33 != $FunctionContextHeight
           && $Is(m#0, TMap(_module._default.domain$U, _module._default.domain$V)))
       ==> (forall i#0: Box :: 
          { Map#Domain(m#0)[i#0] } 
            { _module.__default.domain(_module._default.domain$U, _module._default.domain$V, m#0)[i#0] } 
          $IsBox(i#0, _module._default.domain$U)
             ==> 
            _module.__default.domain(_module._default.domain$U, _module._default.domain$V, m#0)[i#0]
             ==> Map#Domain(m#0)[i#0])
         && (forall i#1: Box :: 
          { _module.__default.domain(_module._default.domain$U, _module._default.domain$V, m#0)[i#1] } 
            { Map#Domain(m#0)[i#1] } 
          $IsBox(i#1, _module._default.domain$U)
             ==> 
            Map#Domain(m#0)[i#1]
             ==> _module.__default.domain(_module._default.domain$U, _module._default.domain$V, m#0)[i#1])
         && $Is(_module.__default.domain(_module._default.domain$U, _module._default.domain$V, m#0), 
          TSet(_module._default.domain$U)));

function _module.__default.domain#requires(Ty, Ty, Map Box Box) : bool;

// #requires axiom for _module.__default.domain
axiom (forall _module._default.domain$U: Ty, _module._default.domain$V: Ty, m#0: Map Box Box :: 
  { _module.__default.domain#requires(_module._default.domain$U, _module._default.domain$V, m#0) } 
  $Is(m#0, TMap(_module._default.domain$U, _module._default.domain$V))
     ==> _module.__default.domain#requires(_module._default.domain$U, _module._default.domain$V, m#0)
       == true);

// definition axiom for _module.__default.domain (revealed)
axiom 33 <= $FunctionContextHeight
   ==> (forall _module._default.domain$U: Ty, _module._default.domain$V: Ty, m#0: Map Box Box :: 
    { _module.__default.domain(_module._default.domain$U, _module._default.domain$V, m#0) } 
    _module.__default.domain#canCall(_module._default.domain$U, _module._default.domain$V, m#0)
         || (33 != $FunctionContextHeight
           && $Is(m#0, TMap(_module._default.domain$U, _module._default.domain$V)))
       ==> _module.__default.domain(_module._default.domain$U, _module._default.domain$V, m#0)
         == (lambda $y#0: Box :: 
          $IsBox($y#0, _module._default.domain$U) && Map#Domain(m#0)[$y#0]));

// definition axiom for _module.__default.domain for all literals (revealed)
axiom 33 <= $FunctionContextHeight
   ==> (forall _module._default.domain$U: Ty, _module._default.domain$V: Ty, m#0: Map Box Box :: 
    {:weight 3} { _module.__default.domain(_module._default.domain$U, _module._default.domain$V, Lit(m#0)) } 
    _module.__default.domain#canCall(_module._default.domain$U, _module._default.domain$V, Lit(m#0))
         || (33 != $FunctionContextHeight
           && $Is(m#0, TMap(_module._default.domain$U, _module._default.domain$V)))
       ==> _module.__default.domain(_module._default.domain$U, _module._default.domain$V, Lit(m#0))
         == (lambda $y#1: Box :: 
          $IsBox($y#1, _module._default.domain$U) && Map#Domain(m#0)[$y#1]));

procedure CheckWellformed$$_module.__default.domain(_module._default.domain$U: Ty, 
    _module._default.domain$V: Ty, 
    m#0: Map Box Box
       where $Is(m#0, TMap(_module._default.domain$U, _module._default.domain$V)));
  free requires 33 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures (forall i#2: Box :: 
    { Map#Domain(m#0)[i#2] } 
      { _module.__default.domain(_module._default.domain$U, _module._default.domain$V, m#0)[i#2] } 
    $IsBox(i#2, _module._default.domain$U)
       ==> 
      _module.__default.domain(_module._default.domain$U, _module._default.domain$V, m#0)[i#2]
       ==> Map#Domain(m#0)[i#2]);
  ensures (forall i#3: Box :: 
    { _module.__default.domain(_module._default.domain$U, _module._default.domain$V, m#0)[i#3] } 
      { Map#Domain(m#0)[i#3] } 
    $IsBox(i#3, _module._default.domain$U)
       ==> 
      Map#Domain(m#0)[i#3]
       ==> _module.__default.domain(_module._default.domain$U, _module._default.domain$V, m#0)[i#3]);



implementation CheckWellformed$$_module.__default.domain(_module._default.domain$U: Ty, _module._default.domain$V: Ty, m#0: Map Box Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var i#4: Box;
  var ##m#0: Map Box Box;
  var i#5: Box;
  var ##m#1: Map Box Box;
  var s#2: Box;


    // AddWellformednessCheck for function domain
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(154,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.domain(_module._default.domain$U, _module._default.domain$V, m#0), 
          TSet(_module._default.domain$U));
        havoc i#4;
        assume $IsBox(i#4, _module._default.domain$U);
        if (*)
        {
            ##m#0 := m#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#0, TMap(_module._default.domain$U, _module._default.domain$V), $Heap);
            assert m#0 == m#0
               || (Set#Subset(Map#Domain(##m#0), Map#Domain(m#0))
                 && !Set#Subset(Map#Domain(m#0), Map#Domain(##m#0)));
            assume m#0 == m#0
               || _module.__default.domain#canCall(_module._default.domain$U, _module._default.domain$V, m#0);
            assume _module.__default.domain(_module._default.domain$U, _module._default.domain$V, m#0)[i#4];
            assume Map#Domain(m#0)[i#4];
        }
        else
        {
            assume _module.__default.domain(_module._default.domain$U, _module._default.domain$V, m#0)[i#4]
               ==> Map#Domain(m#0)[i#4];
        }

        assume (forall i#2: Box :: 
          { Map#Domain(m#0)[i#2] } 
            { _module.__default.domain(_module._default.domain$U, _module._default.domain$V, m#0)[i#2] } 
          $IsBox(i#2, _module._default.domain$U)
             ==> 
            _module.__default.domain(_module._default.domain$U, _module._default.domain$V, m#0)[i#2]
             ==> Map#Domain(m#0)[i#2]);
        havoc i#5;
        assume $IsBox(i#5, _module._default.domain$U);
        if (*)
        {
            assume Map#Domain(m#0)[i#5];
            ##m#1 := m#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#1, TMap(_module._default.domain$U, _module._default.domain$V), $Heap);
            assert m#0 == m#0
               || (Set#Subset(Map#Domain(##m#1), Map#Domain(m#0))
                 && !Set#Subset(Map#Domain(m#0), Map#Domain(##m#1)));
            assume m#0 == m#0
               || _module.__default.domain#canCall(_module._default.domain$U, _module._default.domain$V, m#0);
            assume _module.__default.domain(_module._default.domain$U, _module._default.domain$V, m#0)[i#5];
        }
        else
        {
            assume Map#Domain(m#0)[i#5]
               ==> _module.__default.domain(_module._default.domain$U, _module._default.domain$V, m#0)[i#5];
        }

        assume (forall i#3: Box :: 
          { _module.__default.domain(_module._default.domain$U, _module._default.domain$V, m#0)[i#3] } 
            { Map#Domain(m#0)[i#3] } 
          $IsBox(i#3, _module._default.domain$U)
             ==> 
            Map#Domain(m#0)[i#3]
             ==> _module.__default.domain(_module._default.domain$U, _module._default.domain$V, m#0)[i#3]);
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        // Begin Comprehension WF check
        havoc s#2;
        if ($IsBox(s#2, _module._default.domain$U))
        {
            if (Map#Domain(m#0)[s#2])
            {
            }
        }

        // End Comprehension WF check
        assume _module.__default.domain(_module._default.domain$U, _module._default.domain$V, m#0)
           == (lambda $y#2: Box :: 
            $IsBox($y#2, _module._default.domain$U) && Map#Domain(m#0)[$y#2]);
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.domain(_module._default.domain$U, _module._default.domain$V, m#0), 
          TSet(_module._default.domain$U));
    }
}



procedure CheckWellformed$$_module.__default.m13();
  free requires 34 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.m13();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.m13() returns ($_reverifyPost: bool);
  free requires 34 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.m13() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var s#0: Set Box where $Is(s#0, TSet(TInt)) && $IsAlloc(s#0, TSet(TInt), $Heap);
  var x#0: Map Box Box
     where $Is(x#0, TMap(TInt, TInt)) && $IsAlloc(x#0, TMap(TInt, TInt), $Heap);
  var i#0: int;
  var i#2: int;
  var ##m#0: Map Box Box;

    // AddMethodImpl: m13, Impl$$_module.__default.m13
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(162,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(163,10)
    assume true;
    assume true;
    s#0 := Lit(Set#UnionOne(Set#UnionOne(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(LitInt(0))), $Box(LitInt(1))), 
          $Box(LitInt(3))), 
        $Box(LitInt(4))));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(163,24)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(164,10)
    assume true;
    // Begin Comprehension WF check
    havoc i#0;
    if (true)
    {
        if (s#0[$Box(i#0)])
        {
        }
    }

    // End Comprehension WF check
    assume true;
    x#0 := Map#Glue((lambda $w#0: Box :: s#0[$w#0]), (lambda $w#0: Box :: $w#0), TMap(TInt, TInt));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(164,31)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(165,4)
    // Begin Comprehension WF check
    havoc i#2;
    if (true)
    {
        if (Map#Domain(x#0)[$Box(i#2)])
        {
            assert {:subsumption 0} Map#Domain(x#0)[$Box(i#2)];
        }
    }

    // End Comprehension WF check
    assume true;
    assert (forall i#3: int :: 
      { $Unbox(Map#Elements(x#0)[$Box(i#3)]): int } { Map#Domain(x#0)[$Box(i#3)] } 
      Map#Domain(x#0)[$Box(i#3)] ==> $Unbox(Map#Elements(x#0)[$Box(i#3)]): int == i#3);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(166,4)
    ##m#0 := x#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##m#0, TMap(TInt, TInt), $Heap);
    assume _module.__default.domain#canCall(TInt, TInt, x#0);
    assume _module.__default.domain#canCall(TInt, TInt, x#0);
    assert Set#Equal(_module.__default.domain(TInt, TInt, x#0), s#0);
}



// function declaration for _module._default.union
function _module.__default.union(_module._default.union$U: Ty, 
    _module._default.union$V: Ty, 
    m#0: Map Box Box, 
    m'#0: Map Box Box)
   : Map Box Box;

function _module.__default.union#canCall(_module._default.union$U: Ty, 
    _module._default.union$V: Ty, 
    m#0: Map Box Box, 
    m'#0: Map Box Box)
   : bool;

// consequence axiom for _module.__default.union
axiom 35 <= $FunctionContextHeight
   ==> (forall _module._default.union$U: Ty, 
      _module._default.union$V: Ty, 
      m#0: Map Box Box, 
      m'#0: Map Box Box :: 
    { _module.__default.union(_module._default.union$U, _module._default.union$V, m#0, m'#0) } 
    _module.__default.union#canCall(_module._default.union$U, _module._default.union$V, m#0, m'#0)
         || (35 != $FunctionContextHeight
           && 
          $Is(m#0, TMap(_module._default.union$U, _module._default.union$V))
           && $Is(m'#0, TMap(_module._default.union$U, _module._default.union$V))
           && Set#Disjoint(Map#Domain(m#0), Map#Domain(m'#0)))
       ==> (forall i#0: Box :: 
          { Map#Domain(_module.__default.union(_module._default.union$U, _module._default.union$V, m#0, m'#0))[i#0] } 
          $IsBox(i#0, _module._default.union$U)
             ==> 
            Map#Domain(_module.__default.union(_module._default.union$U, _module._default.union$V, m#0, m'#0))[i#0]
             ==> Map#Domain(m#0)[i#0] || Map#Domain(m'#0)[i#0])
         && (forall i#1: Box :: 
          { Map#Domain(_module.__default.union(_module._default.union$U, _module._default.union$V, m#0, m'#0))[i#1] } 
          $IsBox(i#1, _module._default.union$U)
             ==> 
            Map#Domain(m#0)[i#1] || Map#Domain(m'#0)[i#1]
             ==> Map#Domain(_module.__default.union(_module._default.union$U, _module._default.union$V, m#0, m'#0))[i#1])
         && (forall i#2: Box :: 
          { Map#Elements(m#0)[i#2] } 
            { Map#Elements(_module.__default.union(_module._default.union$U, _module._default.union$V, m#0, m'#0))[i#2] } 
            { Map#Domain(m#0)[i#2] } 
          $IsBox(i#2, _module._default.union$U)
             ==> 
            Map#Domain(m#0)[i#2]
             ==> Map#Elements(_module.__default.union(_module._default.union$U, _module._default.union$V, m#0, m'#0))[i#2]
               == Map#Elements(m#0)[i#2])
         && (forall i#3: Box :: 
          { Map#Elements(m'#0)[i#3] } 
            { Map#Elements(_module.__default.union(_module._default.union$U, _module._default.union$V, m#0, m'#0))[i#3] } 
            { Map#Domain(m'#0)[i#3] } 
          $IsBox(i#3, _module._default.union$U)
             ==> 
            Map#Domain(m'#0)[i#3]
             ==> Map#Elements(_module.__default.union(_module._default.union$U, _module._default.union$V, m#0, m'#0))[i#3]
               == Map#Elements(m'#0)[i#3])
         && $Is(_module.__default.union(_module._default.union$U, _module._default.union$V, m#0, m'#0), 
          TMap(_module._default.union$U, _module._default.union$V)));

function _module.__default.union#requires(Ty, Ty, Map Box Box, Map Box Box) : bool;

// #requires axiom for _module.__default.union
axiom (forall _module._default.union$U: Ty, 
    _module._default.union$V: Ty, 
    m#0: Map Box Box, 
    m'#0: Map Box Box :: 
  { _module.__default.union#requires(_module._default.union$U, _module._default.union$V, m#0, m'#0) } 
  $Is(m#0, TMap(_module._default.union$U, _module._default.union$V))
       && $Is(m'#0, TMap(_module._default.union$U, _module._default.union$V))
     ==> _module.__default.union#requires(_module._default.union$U, _module._default.union$V, m#0, m'#0)
       == Set#Disjoint(Map#Domain(m#0), Map#Domain(m'#0)));

// definition axiom for _module.__default.union (revealed)
axiom 35 <= $FunctionContextHeight
   ==> (forall _module._default.union$U: Ty, 
      _module._default.union$V: Ty, 
      m#0: Map Box Box, 
      m'#0: Map Box Box :: 
    { _module.__default.union(_module._default.union$U, _module._default.union$V, m#0, m'#0) } 
    _module.__default.union#canCall(_module._default.union$U, _module._default.union$V, m#0, m'#0)
         || (35 != $FunctionContextHeight
           && 
          $Is(m#0, TMap(_module._default.union$U, _module._default.union$V))
           && $Is(m'#0, TMap(_module._default.union$U, _module._default.union$V))
           && Set#Disjoint(Map#Domain(m#0), Map#Domain(m'#0)))
       ==> _module.__default.domain#canCall(_module._default.union$U, _module._default.union$V, m#0)
         && _module.__default.domain#canCall(_module._default.union$U, _module._default.union$V, m'#0)
         && _module.__default.union(_module._default.union$U, _module._default.union$V, m#0, m'#0)
           == Map#Glue((lambda $w#0: Box :: 
              $IsBox($w#0, _module._default.union$U)
                 && (_module.__default.domain(_module._default.union$U, _module._default.union$V, m#0)[$w#0]
                   || _module.__default.domain(_module._default.union$U, _module._default.union$V, m'#0)[$w#0])), 
            (lambda $w#0: Box :: 
              (if Map#Domain(m#0)[$w#0]
                 then Map#Elements(m#0)[$w#0]
                 else Map#Elements(m'#0)[$w#0])), 
            TMap(_module._default.union$U, _module._default.union$V)));

// definition axiom for _module.__default.union for all literals (revealed)
axiom 35 <= $FunctionContextHeight
   ==> (forall _module._default.union$U: Ty, 
      _module._default.union$V: Ty, 
      m#0: Map Box Box, 
      m'#0: Map Box Box :: 
    {:weight 3} { _module.__default.union(_module._default.union$U, _module._default.union$V, Lit(m#0), Lit(m'#0)) } 
    _module.__default.union#canCall(_module._default.union$U, _module._default.union$V, Lit(m#0), Lit(m'#0))
         || (35 != $FunctionContextHeight
           && 
          $Is(m#0, TMap(_module._default.union$U, _module._default.union$V))
           && $Is(m'#0, TMap(_module._default.union$U, _module._default.union$V))
           && Set#Disjoint(Map#Domain(Lit(m#0)), Map#Domain(Lit(m'#0))))
       ==> _module.__default.domain#canCall(_module._default.union$U, _module._default.union$V, Lit(m#0))
         && _module.__default.domain#canCall(_module._default.union$U, _module._default.union$V, Lit(m'#0))
         && _module.__default.union(_module._default.union$U, _module._default.union$V, Lit(m#0), Lit(m'#0))
           == Map#Glue((lambda $w#1: Box :: 
              $IsBox($w#1, _module._default.union$U)
                 && (Lit(_module.__default.domain(_module._default.union$U, _module._default.union$V, Lit(m#0)))[$w#1]
                   || Lit(_module.__default.domain(_module._default.union$U, _module._default.union$V, Lit(m'#0)))[$w#1])), 
            (lambda $w#1: Box :: 
              (if Map#Domain(m#0)[$w#1]
                 then Map#Elements(Lit(m#0))[$w#1]
                 else Map#Elements(Lit(m'#0))[$w#1])), 
            TMap(_module._default.union$U, _module._default.union$V)));

procedure CheckWellformed$$_module.__default.union(_module._default.union$U: Ty, 
    _module._default.union$V: Ty, 
    m#0: Map Box Box
       where $Is(m#0, TMap(_module._default.union$U, _module._default.union$V)), 
    m'#0: Map Box Box
       where $Is(m'#0, TMap(_module._default.union$U, _module._default.union$V)));
  free requires 35 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures (forall i#5: Box :: 
    { Map#Domain(_module.__default.union(_module._default.union$U, _module._default.union$V, m#0, m'#0))[i#5] } 
    $IsBox(i#5, _module._default.union$U)
       ==> 
      Map#Domain(_module.__default.union(_module._default.union$U, _module._default.union$V, m#0, m'#0))[i#5]
       ==> Map#Domain(m#0)[i#5] || Map#Domain(m'#0)[i#5]);
  ensures (forall i#6: Box :: 
    { Map#Domain(_module.__default.union(_module._default.union$U, _module._default.union$V, m#0, m'#0))[i#6] } 
    $IsBox(i#6, _module._default.union$U)
       ==> 
      Map#Domain(m#0)[i#6] || Map#Domain(m'#0)[i#6]
       ==> Map#Domain(_module.__default.union(_module._default.union$U, _module._default.union$V, m#0, m'#0))[i#6]);
  ensures (forall i#7: Box :: 
    { Map#Elements(m#0)[i#7] } 
      { Map#Elements(_module.__default.union(_module._default.union$U, _module._default.union$V, m#0, m'#0))[i#7] } 
      { Map#Domain(m#0)[i#7] } 
    $IsBox(i#7, _module._default.union$U)
       ==> 
      Map#Domain(m#0)[i#7]
       ==> Map#Elements(_module.__default.union(_module._default.union$U, _module._default.union$V, m#0, m'#0))[i#7]
         == Map#Elements(m#0)[i#7]);
  ensures (forall i#8: Box :: 
    { Map#Elements(m'#0)[i#8] } 
      { Map#Elements(_module.__default.union(_module._default.union$U, _module._default.union$V, m#0, m'#0))[i#8] } 
      { Map#Domain(m'#0)[i#8] } 
    $IsBox(i#8, _module._default.union$U)
       ==> 
      Map#Domain(m'#0)[i#8]
       ==> Map#Elements(_module.__default.union(_module._default.union$U, _module._default.union$V, m#0, m'#0))[i#8]
         == Map#Elements(m'#0)[i#8]);



implementation CheckWellformed$$_module.__default.union(_module._default.union$U: Ty, 
    _module._default.union$V: Ty, 
    m#0: Map Box Box, 
    m'#0: Map Box Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var i#9: Box;
  var ##m#0: Map Box Box;
  var ##m'#0: Map Box Box;
  var i#10: Box;
  var ##m#1: Map Box Box;
  var ##m'#1: Map Box Box;
  var i#11: Box;
  var ##m#2: Map Box Box;
  var ##m'#2: Map Box Box;
  var i#12: Box;
  var ##m#3: Map Box Box;
  var ##m'#3: Map Box Box;
  var i#13: Box;
  var ##m#4: Map Box Box;
  var ##m#5: Map Box Box;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function union
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(169,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume Set#Disjoint(Map#Domain(m#0), Map#Domain(m'#0));
    if (*)
    {
        assume $Is(_module.__default.union(_module._default.union$U, _module._default.union$V, m#0, m'#0), 
          TMap(_module._default.union$U, _module._default.union$V));
        havoc i#9;
        assume $IsBox(i#9, _module._default.union$U);
        if (*)
        {
            ##m#0 := m#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#0, TMap(_module._default.union$U, _module._default.union$V), $Heap);
            ##m'#0 := m'#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##m'#0, TMap(_module._default.union$U, _module._default.union$V), $Heap);
            assert {:subsumption 0} Set#Disjoint(Map#Domain(##m#0), Map#Domain(##m'#0));
            assume Set#Disjoint(Map#Domain(##m#0), Map#Domain(##m'#0));
            assert (m#0 == m#0 && m'#0 == m'#0)
               || 
              (Set#Subset(Map#Domain(##m#0), Map#Domain(m#0))
                 && !Set#Subset(Map#Domain(m#0), Map#Domain(##m#0)))
               || (Set#Equal(Map#Domain(##m#0), Map#Domain(m#0))
                 && 
                Set#Subset(Map#Domain(##m'#0), Map#Domain(m'#0))
                 && !Set#Subset(Map#Domain(m'#0), Map#Domain(##m'#0)));
            assume (m#0 == m#0 && m'#0 == m'#0)
               || _module.__default.union#canCall(_module._default.union$U, _module._default.union$V, m#0, m'#0);
            assume Map#Domain(_module.__default.union(_module._default.union$U, _module._default.union$V, m#0, m'#0))[i#9];
            assume Map#Domain(m#0)[i#9] || Map#Domain(m'#0)[i#9];
        }
        else
        {
            assume Map#Domain(_module.__default.union(_module._default.union$U, _module._default.union$V, m#0, m'#0))[i#9]
               ==> Map#Domain(m#0)[i#9] || Map#Domain(m'#0)[i#9];
        }

        assume (forall i#5: Box :: 
          { Map#Domain(_module.__default.union(_module._default.union$U, _module._default.union$V, m#0, m'#0))[i#5] } 
          $IsBox(i#5, _module._default.union$U)
             ==> 
            Map#Domain(_module.__default.union(_module._default.union$U, _module._default.union$V, m#0, m'#0))[i#5]
             ==> Map#Domain(m#0)[i#5] || Map#Domain(m'#0)[i#5]);
        havoc i#10;
        assume $IsBox(i#10, _module._default.union$U);
        if (*)
        {
            assume Map#Domain(m#0)[i#10] || Map#Domain(m'#0)[i#10];
            ##m#1 := m#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#1, TMap(_module._default.union$U, _module._default.union$V), $Heap);
            ##m'#1 := m'#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##m'#1, TMap(_module._default.union$U, _module._default.union$V), $Heap);
            assert {:subsumption 0} Set#Disjoint(Map#Domain(##m#1), Map#Domain(##m'#1));
            assume Set#Disjoint(Map#Domain(##m#1), Map#Domain(##m'#1));
            assert (m#0 == m#0 && m'#0 == m'#0)
               || 
              (Set#Subset(Map#Domain(##m#1), Map#Domain(m#0))
                 && !Set#Subset(Map#Domain(m#0), Map#Domain(##m#1)))
               || (Set#Equal(Map#Domain(##m#1), Map#Domain(m#0))
                 && 
                Set#Subset(Map#Domain(##m'#1), Map#Domain(m'#0))
                 && !Set#Subset(Map#Domain(m'#0), Map#Domain(##m'#1)));
            assume (m#0 == m#0 && m'#0 == m'#0)
               || _module.__default.union#canCall(_module._default.union$U, _module._default.union$V, m#0, m'#0);
            assume Map#Domain(_module.__default.union(_module._default.union$U, _module._default.union$V, m#0, m'#0))[i#10];
        }
        else
        {
            assume Map#Domain(m#0)[i#10] || Map#Domain(m'#0)[i#10]
               ==> Map#Domain(_module.__default.union(_module._default.union$U, _module._default.union$V, m#0, m'#0))[i#10];
        }

        assume (forall i#6: Box :: 
          { Map#Domain(_module.__default.union(_module._default.union$U, _module._default.union$V, m#0, m'#0))[i#6] } 
          $IsBox(i#6, _module._default.union$U)
             ==> 
            Map#Domain(m#0)[i#6] || Map#Domain(m'#0)[i#6]
             ==> Map#Domain(_module.__default.union(_module._default.union$U, _module._default.union$V, m#0, m'#0))[i#6]);
        havoc i#11;
        assume $IsBox(i#11, _module._default.union$U);
        if (*)
        {
            assume Map#Domain(m#0)[i#11];
            ##m#2 := m#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#2, TMap(_module._default.union$U, _module._default.union$V), $Heap);
            ##m'#2 := m'#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##m'#2, TMap(_module._default.union$U, _module._default.union$V), $Heap);
            assert {:subsumption 0} Set#Disjoint(Map#Domain(##m#2), Map#Domain(##m'#2));
            assume Set#Disjoint(Map#Domain(##m#2), Map#Domain(##m'#2));
            assert (m#0 == m#0 && m'#0 == m'#0)
               || 
              (Set#Subset(Map#Domain(##m#2), Map#Domain(m#0))
                 && !Set#Subset(Map#Domain(m#0), Map#Domain(##m#2)))
               || (Set#Equal(Map#Domain(##m#2), Map#Domain(m#0))
                 && 
                Set#Subset(Map#Domain(##m'#2), Map#Domain(m'#0))
                 && !Set#Subset(Map#Domain(m'#0), Map#Domain(##m'#2)));
            assume (m#0 == m#0 && m'#0 == m'#0)
               || _module.__default.union#canCall(_module._default.union$U, _module._default.union$V, m#0, m'#0);
            assert Map#Domain(_module.__default.union(_module._default.union$U, _module._default.union$V, m#0, m'#0))[i#11];
            assert Map#Domain(m#0)[i#11];
            assume Map#Elements(_module.__default.union(_module._default.union$U, _module._default.union$V, m#0, m'#0))[i#11]
               == Map#Elements(m#0)[i#11];
        }
        else
        {
            assume Map#Domain(m#0)[i#11]
               ==> Map#Elements(_module.__default.union(_module._default.union$U, _module._default.union$V, m#0, m'#0))[i#11]
                 == Map#Elements(m#0)[i#11];
        }

        assume (forall i#7: Box :: 
          { Map#Elements(m#0)[i#7] } 
            { Map#Elements(_module.__default.union(_module._default.union$U, _module._default.union$V, m#0, m'#0))[i#7] } 
            { Map#Domain(m#0)[i#7] } 
          $IsBox(i#7, _module._default.union$U)
             ==> 
            Map#Domain(m#0)[i#7]
             ==> Map#Elements(_module.__default.union(_module._default.union$U, _module._default.union$V, m#0, m'#0))[i#7]
               == Map#Elements(m#0)[i#7]);
        havoc i#12;
        assume $IsBox(i#12, _module._default.union$U);
        if (*)
        {
            assume Map#Domain(m'#0)[i#12];
            ##m#3 := m#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#3, TMap(_module._default.union$U, _module._default.union$V), $Heap);
            ##m'#3 := m'#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##m'#3, TMap(_module._default.union$U, _module._default.union$V), $Heap);
            assert {:subsumption 0} Set#Disjoint(Map#Domain(##m#3), Map#Domain(##m'#3));
            assume Set#Disjoint(Map#Domain(##m#3), Map#Domain(##m'#3));
            assert (m#0 == m#0 && m'#0 == m'#0)
               || 
              (Set#Subset(Map#Domain(##m#3), Map#Domain(m#0))
                 && !Set#Subset(Map#Domain(m#0), Map#Domain(##m#3)))
               || (Set#Equal(Map#Domain(##m#3), Map#Domain(m#0))
                 && 
                Set#Subset(Map#Domain(##m'#3), Map#Domain(m'#0))
                 && !Set#Subset(Map#Domain(m'#0), Map#Domain(##m'#3)));
            assume (m#0 == m#0 && m'#0 == m'#0)
               || _module.__default.union#canCall(_module._default.union$U, _module._default.union$V, m#0, m'#0);
            assert Map#Domain(_module.__default.union(_module._default.union$U, _module._default.union$V, m#0, m'#0))[i#12];
            assert Map#Domain(m'#0)[i#12];
            assume Map#Elements(_module.__default.union(_module._default.union$U, _module._default.union$V, m#0, m'#0))[i#12]
               == Map#Elements(m'#0)[i#12];
        }
        else
        {
            assume Map#Domain(m'#0)[i#12]
               ==> Map#Elements(_module.__default.union(_module._default.union$U, _module._default.union$V, m#0, m'#0))[i#12]
                 == Map#Elements(m'#0)[i#12];
        }

        assume (forall i#8: Box :: 
          { Map#Elements(m'#0)[i#8] } 
            { Map#Elements(_module.__default.union(_module._default.union$U, _module._default.union$V, m#0, m'#0))[i#8] } 
            { Map#Domain(m'#0)[i#8] } 
          $IsBox(i#8, _module._default.union$U)
             ==> 
            Map#Domain(m'#0)[i#8]
             ==> Map#Elements(_module.__default.union(_module._default.union$U, _module._default.union$V, m#0, m'#0))[i#8]
               == Map#Elements(m'#0)[i#8]);
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        // Begin Comprehension WF check
        havoc i#13;
        if ($IsBox(i#13, _module._default.union$U))
        {
            ##m#4 := m#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#4, TMap(_module._default.union$U, _module._default.union$V), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.domain#canCall(_module._default.union$U, _module._default.union$V, m#0);
            ##m#5 := m'#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#5, TMap(_module._default.union$U, _module._default.union$V), $Heap);
            b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.domain#canCall(_module._default.union$U, _module._default.union$V, m'#0);
            if (_module.__default.domain(_module._default.union$U, _module._default.union$V, m#0)[i#13]
               || _module.__default.domain(_module._default.union$U, _module._default.union$V, m'#0)[i#13])
            {
                if (Map#Domain(m#0)[i#13])
                {
                    assert Map#Domain(m#0)[i#13];
                }
                else
                {
                    assert Map#Domain(m'#0)[i#13];
                }
            }
        }

        // End Comprehension WF check
        assume _module.__default.union(_module._default.union$U, _module._default.union$V, m#0, m'#0)
           == Map#Glue((lambda $w#2: Box :: 
              $IsBox($w#2, _module._default.union$U)
                 && (_module.__default.domain(_module._default.union$U, _module._default.union$V, m#0)[$w#2]
                   || _module.__default.domain(_module._default.union$U, _module._default.union$V, m'#0)[$w#2])), 
            (lambda $w#2: Box :: 
              (if Map#Domain(m#0)[$w#2]
                 then Map#Elements(m#0)[$w#2]
                 else Map#Elements(m'#0)[$w#2])), 
            TMap(_module._default.union$U, _module._default.union$V));
        assume _module.__default.domain#canCall(_module._default.union$U, _module._default.union$V, m#0)
           && _module.__default.domain#canCall(_module._default.union$U, _module._default.union$V, m'#0);
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.union(_module._default.union$U, _module._default.union$V, m#0, m'#0), 
          TMap(_module._default.union$U, _module._default.union$V));
        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



procedure CheckWellformed$$_module.__default.m14();
  free requires 36 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.m14();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.m14() returns ($_reverifyPost: bool);
  free requires 36 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.m14() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var s#0: Set Box where $Is(s#0, TSet(TInt)) && $IsAlloc(s#0, TSet(TInt), $Heap);
  var t#0: Set Box where $Is(t#0, TSet(TInt)) && $IsAlloc(t#0, TSet(TInt), $Heap);
  var $rhs#0: Set Box where $Is($rhs#0, TSet(TInt));
  var $rhs#1: Set Box where $Is($rhs#1, TSet(TInt));
  var x#0: Map Box Box
     where $Is(x#0, TMap(TInt, TInt)) && $IsAlloc(x#0, TMap(TInt, TInt), $Heap);
  var y#0: Map Box Box
     where $Is(y#0, TMap(TInt, TInt)) && $IsAlloc(y#0, TMap(TInt, TInt), $Heap);
  var $rhs#2: Map Box Box where $Is($rhs#2, TMap(TInt, TInt));
  var i#0: int;
  var $rhs#3: Map Box Box where $Is($rhs#3, TMap(TInt, TInt));
  var i#2: int;
  var u#0: Map Box Box
     where $Is(u#0, TMap(TInt, TInt)) && $IsAlloc(u#0, TMap(TInt, TInt), $Heap);
  var ##m#0: Map Box Box;
  var ##m'#0: Map Box Box;
  var ##m#1: Map Box Box;

    // AddMethodImpl: m14, Impl$$_module.__default.m14
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(181,0): initial state"} true;
    $_reverifyPost := false;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(182,13)
    assume true;
    assume true;
    assume true;
    $rhs#0 := Lit(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(LitInt(0))), $Box(LitInt(1))));
    assume true;
    $rhs#1 := Lit(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(LitInt(3))), $Box(LitInt(4))));
    s#0 := $rhs#0;
    t#0 := $rhs#1;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(182,29)"} true;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(183,12)
    assume true;
    assume true;
    // Begin Comprehension WF check
    havoc i#0;
    if (true)
    {
        if (s#0[$Box(i#0)])
        {
        }
    }

    // End Comprehension WF check
    assume true;
    $rhs#2 := Map#Glue((lambda $w#0: Box :: s#0[$w#0]), (lambda $w#0: Box :: $w#0), TMap(TInt, TInt));
    // Begin Comprehension WF check
    havoc i#2;
    if (true)
    {
        if (t#0[$Box(i#2)])
        {
        }
    }

    // End Comprehension WF check
    assume true;
    $rhs#3 := Map#Glue((lambda $w#1: Box :: t#0[$w#1]), 
      (lambda $w#1: Box :: $Box(1 + $Unbox($w#1): int)), 
      TMap(TInt, TInt));
    x#0 := $rhs#2;
    y#0 := $rhs#3;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(183,56)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(184,16)
    assume true;
    ##m#0 := x#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##m#0, TMap(TInt, TInt), $Heap);
    ##m'#0 := y#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##m'#0, TMap(TInt, TInt), $Heap);
    assert {:subsumption 0} Set#Disjoint(Map#Domain(##m#0), Map#Domain(##m'#0));
    assume Set#Disjoint(Map#Domain(##m#0), Map#Domain(##m'#0));
    assume _module.__default.union#canCall(TInt, TInt, x#0, y#0);
    assume _module.__default.union#canCall(TInt, TInt, x#0, y#0);
    u#0 := _module.__default.union(TInt, TInt, x#0, y#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(184,28)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(185,4)
    assert {:subsumption 0} Map#Domain(u#0)[$Box(LitInt(1))];
    if ($Unbox(Map#Elements(u#0)[$Box(LitInt(1))]): int == LitInt(1))
    {
        assert {:subsumption 0} Map#Domain(u#0)[$Box(LitInt(3))];
    }

    assume true;
    assert {:subsumption 0} $Unbox(Map#Elements(u#0)[$Box(LitInt(1))]): int == LitInt(1);
    assert {:subsumption 0} $Unbox(Map#Elements(u#0)[$Box(LitInt(3))]): int == LitInt(4);
    assume $Unbox(Map#Elements(u#0)[$Box(LitInt(1))]): int == LitInt(1)
       && $Unbox(Map#Elements(u#0)[$Box(LitInt(3))]): int == LitInt(4);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(186,4)
    ##m#1 := u#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##m#1, TMap(TInt, TInt), $Heap);
    assume _module.__default.domain#canCall(TInt, TInt, u#0);
    assume _module.__default.domain#canCall(TInt, TInt, u#0);
    assert Set#Equal(_module.__default.domain(TInt, TInt, u#0), 
      Set#UnionOne(Set#UnionOne(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(LitInt(0))), $Box(LitInt(1))), 
          $Box(LitInt(3))), 
        $Box(LitInt(4))));
}



procedure CheckWellformed$$_module.__default.m15(b#0: Set Box
       where $Is(b#0, TSet(Tclass._module.A()))
         && $IsAlloc(b#0, TSet(Tclass._module.A()), $Heap));
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.m15(b#0: Set Box
       where $Is(b#0, TSet(Tclass._module.A()))
         && $IsAlloc(b#0, TSet(Tclass._module.A()), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.m15(b#0: Set Box
       where $Is(b#0, TSet(Tclass._module.A()))
         && $IsAlloc(b#0, TSet(Tclass._module.A()), $Heap))
   returns ($_reverifyPost: bool);
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.m15(b#0: Set Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var m#0: Map Box Box
     where $Is(m#0, TMap(Tclass._module.A(), TInt))
       && $IsAlloc(m#0, TMap(Tclass._module.A(), TInt), $Heap);
  var a#0: ref;
  var aa#0: ref
     where $Is(aa#0, Tclass._module.A()) && $IsAlloc(aa#0, Tclass._module.A(), $Heap);
  var $nw: ref;

    // AddMethodImpl: m15, Impl$$_module.__default.m15
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(192,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(193,9)
    assume true;
    // Begin Comprehension WF check
    havoc a#0;
    if ($Is(a#0, Tclass._module.A()))
    {
        if (b#0[$Box(a#0)])
        {
            assert a#0 != null;
        }
    }

    // End Comprehension WF check
    assume true;
    m#0 := Map#Glue((lambda $w#0: Box :: $Is($Unbox($w#0): ref, Tclass._module.A()) && b#0[$w#0]), 
      (lambda $w#0: Box :: $Box(read($Heap, $Unbox($w#0): ref, _module.A.x))), 
      TMap(Tclass._module.A(), TInt));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(193,32)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(194,10)
    assume true;
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._module.A?();
    assume !read($Heap, $nw, alloc);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    aa#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(194,17)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(195,3)
    assume true;
    assert !Map#Domain(m#0)[$Box(aa#0)];
}



// function declaration for _module._default.Plus
function _module.__default.Plus(x#0: int, y#0: int) : int;

function _module.__default.Plus#canCall(x#0: int, y#0: int) : bool;

// consequence axiom for _module.__default.Plus
axiom 37 <= $FunctionContextHeight
   ==> (forall x#0: int, y#0: int :: 
    { _module.__default.Plus(x#0, y#0) } 
    _module.__default.Plus#canCall(x#0, y#0) || 37 != $FunctionContextHeight
       ==> true);

function _module.__default.Plus#requires(int, int) : bool;

// #requires axiom for _module.__default.Plus
axiom (forall x#0: int, y#0: int :: 
  { _module.__default.Plus#requires(x#0, y#0) } 
  _module.__default.Plus#requires(x#0, y#0) == true);

// definition axiom for _module.__default.Plus (revealed)
axiom 37 <= $FunctionContextHeight
   ==> (forall x#0: int, y#0: int :: 
    { _module.__default.Plus(x#0, y#0) } 
    _module.__default.Plus#canCall(x#0, y#0) || 37 != $FunctionContextHeight
       ==> _module.__default.Plus(x#0, y#0) == x#0 + y#0);

// definition axiom for _module.__default.Plus for all literals (revealed)
axiom 37 <= $FunctionContextHeight
   ==> (forall x#0: int, y#0: int :: 
    {:weight 3} { _module.__default.Plus(LitInt(x#0), LitInt(y#0)) } 
    _module.__default.Plus#canCall(LitInt(x#0), LitInt(y#0))
         || 37 != $FunctionContextHeight
       ==> _module.__default.Plus(LitInt(x#0), LitInt(y#0)) == LitInt(x#0 + y#0));

procedure CheckWellformed$$_module.__default.Plus(x#0: int, y#0: int);
  free requires 37 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure CheckWellformed$$_module.__default.GeneralMaps0();
  free requires 38 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.GeneralMaps0();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.GeneralMaps0() returns ($_reverifyPost: bool);
  free requires 38 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



function map$project$0#0#y#0(int) : int;

implementation Impl$$_module.__default.GeneralMaps0() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var m#0: Map Box Box
     where $Is(m#0, TMap(TInt, TInt)) && $IsAlloc(m#0, TMap(TInt, TInt), $Heap);
  var x#0: int;
  var y#0: int;
  var y#prime#0: int;
  var ##x#0: int;
  var ##y#0: int;
  var ##x#1: int;
  var ##y#1: int;

    // AddMethodImpl: GeneralMaps0, Impl$$_module.__default.GeneralMaps0
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(199,22): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(200,9)
    assume true;
    // Begin Comprehension WF check
    havoc x#0;
    if (true)
    {
        if (LitInt(2) <= x#0)
        {
        }

        if (LitInt(2) <= x#0 && x#0 < 6)
        {
        }
    }

    // End Comprehension WF check
    assume true;
    m#0 := Map#Glue((lambda $w#0: Box :: LitInt(2) <= $Unbox($w#0): int && $Unbox($w#0): int < 6), 
      (lambda $w#0: Box :: $Box($Unbox($w#0): int + 1)), 
      TMap(TInt, TInt));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(200,36)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(201,3)
    assume true;
    assert Map#Domain(m#0)[$Box(LitInt(5))];
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(202,3)
    assume true;
    assert !Map#Domain(m#0)[$Box(LitInt(6))];
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(203,3)
    assert {:subsumption 0} Map#Domain(m#0)[$Box(LitInt(5))];
    assume true;
    assert $Unbox(Map#Elements(m#0)[$Box(LitInt(5))]): int == LitInt(6);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(204,3)
    assume true;
    assert Map#Values(m#0)[$Box(LitInt(6))];
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(205,3)
    assume true;
    assert Map#Items(m#0)[$Box(Lit(#_System._tuple#2._#Make2($Box(LitInt(5)), $Box(LitInt(6)))))];
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(206,5)
    assume true;
    // Begin Comprehension WF check
    havoc y#0;
    if (true)
    {
        havoc y#prime#0;
        assume true;
        if (LitInt(2) <= y#0)
        {
        }

        if (LitInt(2) <= y#0 && y#0 < 6)
        {
            ##x#0 := y#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##x#0, TInt, $Heap);
            ##y#0 := LitInt(1);
            // assume allocatedness for argument to function
            assume $IsAlloc(##y#0, TInt, $Heap);
            assume _module.__default.Plus#canCall(y#0, LitInt(1));
        }

        if (LitInt(2) <= y#0 && y#0 < 6)
        {
        }

        if (LitInt(2) <= y#0 && y#0 < 6 && LitInt(2) <= y#prime#0 && y#prime#0 < 6)
        {
            assert _module.__default.Plus(y#0, LitInt(1))
                 != _module.__default.Plus(y#prime#0, LitInt(1))
               || y#0 + 3 == y#prime#0 + 3;
        }
    }

    // End Comprehension WF check
    assume (forall y#1: int :: 
      { _module.__default.Plus(y#1, 1) } 
      _module.__default.Plus#canCall(y#1, LitInt(1))
         && (forall a#0#0#0: int :: 
          { _module.__default.Plus(a#0#0#0, 1) } 
          LitInt(2) <= a#0#0#0 && a#0#0#0 < 6
             ==> LitInt(2) <= map$project$0#0#y#0(_module.__default.Plus(a#0#0#0, LitInt(1)))
               && map$project$0#0#y#0(_module.__default.Plus(a#0#0#0, LitInt(1))) < 6
               && _module.__default.Plus(a#0#0#0, LitInt(1))
                 == _module.__default.Plus(map$project$0#0#y#0(_module.__default.Plus(a#0#0#0, LitInt(1))), LitInt(1))));
    m#0 := Map#Glue((lambda $w#1: Box :: 
        (exists a#1#0#0: int :: 
          LitInt(2) <= a#1#0#0
             && a#1#0#0 < 6
             && $Unbox($w#1): int == _module.__default.Plus(a#1#0#0, LitInt(1)))), 
      (lambda $w#1: Box :: $Box(map$project$0#0#y#0($Unbox($w#1): int) + 3)), 
      TMap(TInt, TInt));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(206,48)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(207,3)
    ##x#1 := LitInt(5);
    // assume allocatedness for argument to function
    assume $IsAlloc(##x#1, TInt, $Heap);
    ##y#1 := LitInt(1);
    // assume allocatedness for argument to function
    assume $IsAlloc(##y#1, TInt, $Heap);
    assume _module.__default.Plus#canCall(LitInt(5), LitInt(1));
    assume _module.__default.Plus#canCall(LitInt(5), LitInt(1));
    assert Map#Domain(m#0)[$Box(LitInt(_module.__default.Plus(LitInt(5), LitInt(1))))];
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(208,3)
    assume true;
    assert !Map#Domain(m#0)[$Box(LitInt(7))];
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(209,3)
    assert {:subsumption 0} Map#Domain(m#0)[$Box(LitInt(6))];
    assume true;
    assert $Unbox(Map#Elements(m#0)[$Box(LitInt(6))]): int == LitInt(8);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(210,3)
    assume true;
    assert Map#Values(m#0)[$Box(LitInt(8))];
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(211,3)
    assume true;
    assert Map#Items(m#0)[$Box(Lit(#_System._tuple#2._#Make2($Box(LitInt(6)), $Box(LitInt(8)))))];
}



// function declaration for _module._default.f
function _module.__default.f(x#0: int) : int;

function _module.__default.f#canCall(x#0: int) : bool;

// consequence axiom for _module.__default.f
axiom 39 <= $FunctionContextHeight
   ==> (forall x#0: int :: 
    { _module.__default.f(x#0) } 
    _module.__default.f#canCall(x#0)
         || (39 != $FunctionContextHeight && LitInt(0) <= x#0)
       ==> true);

function _module.__default.f#requires(int) : bool;

// #requires axiom for _module.__default.f
axiom (forall x#0: int :: 
  { _module.__default.f#requires(x#0) } 
  _module.__default.f#requires(x#0) == (LitInt(0) <= x#0));

procedure CheckWellformed$$_module.__default.f(x#0: int);
  free requires 39 == $FunctionContextHeight;
  modifies $Heap, $Tick;



// function declaration for _module._default.g
function _module.__default.g(x#0: int) : int;

function _module.__default.g#canCall(x#0: int) : bool;

// consequence axiom for _module.__default.g
axiom 41 <= $FunctionContextHeight
   ==> (forall x#0: int :: 
    { _module.__default.g(x#0) } 
    _module.__default.g#canCall(x#0) || 41 != $FunctionContextHeight ==> true);

function _module.__default.g#requires(int) : bool;

// #requires axiom for _module.__default.g
axiom (forall x#0: int :: 
  { _module.__default.g#requires(x#0) } 
  _module.__default.g#requires(x#0) == true);

procedure CheckWellformed$$_module.__default.g(x#0: int);
  free requires 41 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure CheckWellformed$$_module.__default.GeneralMaps1();
  free requires 40 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.GeneralMaps1();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.GeneralMaps1() returns ($_reverifyPost: bool);
  free requires 40 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



function map$project$1#0_0#z#0(int) : int;

function map$project$2#1_0#z#0(int) : int;

function map$project$3#2_0#z#0(int) : int;

function map$project$4#3_0#z#0(int) : int;

implementation Impl$$_module.__default.GeneralMaps1() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var m#0_0: Map Box Box
     where $Is(m#0_0, TMap(TInt, TInt)) && $IsAlloc(m#0_0, TMap(TInt, TInt), $Heap);
  var z#0_0: int;
  var z#prime#0_0: int;
  var m#1_0: Map Box Box
     where $Is(m#1_0, TMap(TInt, TInt)) && $IsAlloc(m#1_0, TMap(TInt, TInt), $Heap);
  var z#1_0: int;
  var z#prime#1_0: int;
  var m#2_0: Map Box Box
     where $Is(m#2_0, TMap(TInt, TInt)) && $IsAlloc(m#2_0, TMap(TInt, TInt), $Heap);
  var z#2_0: int;
  var z#prime#2_0: int;
  var ##x#2_0: int;
  var m#3_0: Map Box Box
     where $Is(m#3_0, TMap(TInt, TInt)) && $IsAlloc(m#3_0, TMap(TInt, TInt), $Heap);
  var z#3_0: int;
  var z#prime#3_0: int;
  var ##x#3_0: int;

    // AddMethodImpl: GeneralMaps1, Impl$$_module.__default.GeneralMaps1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(218,22): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(219,3)
    if (*)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(220,11)
        assume true;
        // Begin Comprehension WF check
        havoc z#0_0;
        if (true)
        {
            havoc z#prime#0_0;
            assume true;
            if (LitInt(2) <= z#0_0)
            {
            }

            if (LitInt(2) <= z#0_0 && z#0_0 < 6)
            {
                assert LitInt(2) != 0;
            }

            if (LitInt(2) <= z#0_0 && z#0_0 < 6)
            {
            }

            if (LitInt(2) <= z#0_0 && z#0_0 < 6 && LitInt(2) <= z#prime#0_0 && z#prime#0_0 < 6)
            {
                assert Div(z#0_0, LitInt(2)) != Div(z#prime#0_0, LitInt(2)) || z#0_0 == z#prime#0_0;
            }
        }

        // End Comprehension WF check
        assume (forall a#0_0#0#0: int :: 
          { Div(a#0_0#0#0, 2) } 
          LitInt(2) <= a#0_0#0#0 && a#0_0#0#0 < 6
             ==> LitInt(2) <= map$project$1#0_0#z#0(Div(a#0_0#0#0, LitInt(2)))
               && map$project$1#0_0#z#0(Div(a#0_0#0#0, LitInt(2))) < 6
               && Div(a#0_0#0#0, LitInt(2))
                 == Div(map$project$1#0_0#z#0(Div(a#0_0#0#0, LitInt(2))), LitInt(2)));
        m#0_0 := Map#Glue((lambda $w#0_0: Box :: 
            (exists a#0_1#0#0: int :: 
              LitInt(2) <= a#0_1#0#0
                 && a#0_1#0#0 < 6
                 && $Unbox($w#0_0): int == Div(a#0_1#0#0, LitInt(2)))), 
          (lambda $w#0_0: Box :: $Box(map$project$1#0_0#z#0($Unbox($w#0_0): int))), 
          TMap(TInt, TInt));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(220,43)"} true;
    }
    else
    {
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(221,10)
        if (*)
        {
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(222,11)
            assume true;
            // Begin Comprehension WF check
            havoc z#1_0;
            if (true)
            {
                havoc z#prime#1_0;
                assume true;
                if (LitInt(2) <= z#1_0)
                {
                }

                if (LitInt(2) <= z#1_0 && z#1_0 < 6)
                {
                    assert LitInt(2) != 0;
                }

                if (LitInt(2) <= z#1_0 && z#1_0 < 6)
                {
                    assert LitInt(2) != 0;
                }

                if (LitInt(2) <= z#1_0 && z#1_0 < 6 && LitInt(2) <= z#prime#1_0 && z#prime#1_0 < 6)
                {
                    assert Div(z#1_0, LitInt(2)) != Div(z#prime#1_0, LitInt(2))
                       || Div(z#1_0, LitInt(2)) + 3 == Div(z#prime#1_0, LitInt(2)) + 3;
                }
            }

            // End Comprehension WF check
            assume (forall a#1_0#0#0: int :: 
              { Div(a#1_0#0#0, 2) } 
              LitInt(2) <= a#1_0#0#0 && a#1_0#0#0 < 6
                 ==> LitInt(2) <= map$project$2#1_0#z#0(Div(a#1_0#0#0, LitInt(2)))
                   && map$project$2#1_0#z#0(Div(a#1_0#0#0, LitInt(2))) < 6
                   && Div(a#1_0#0#0, LitInt(2))
                     == Div(map$project$2#1_0#z#0(Div(a#1_0#0#0, LitInt(2))), LitInt(2)));
            m#1_0 := Map#Glue((lambda $w#1_0: Box :: 
                (exists a#1_1#0#0: int :: 
                  LitInt(2) <= a#1_1#0#0
                     && a#1_1#0#0 < 6
                     && $Unbox($w#1_0): int == Div(a#1_1#0#0, LitInt(2)))), 
              (lambda $w#1_0: Box :: 
                $Box(Div(map$project$2#1_0#z#0($Unbox($w#1_0): int), LitInt(2)) + 3)), 
              TMap(TInt, TInt));
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(222,49)"} true;
        }
        else
        {
            // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(223,10)
            if (*)
            {
                // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(224,11)
                assume true;
                // Begin Comprehension WF check
                havoc z#2_0;
                if (true)
                {
                    havoc z#prime#2_0;
                    assume true;
                    if (LitInt(2) <= z#2_0)
                    {
                    }

                    if (LitInt(2) <= z#2_0 && z#2_0 < 6)
                    {
                        ##x#2_0 := z#2_0;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##x#2_0, TInt, $Heap);
                        assert {:subsumption 0} LitInt(0) <= ##x#2_0;
                        assume LitInt(0) <= ##x#2_0;
                        assume _module.__default.f#canCall(z#2_0);
                    }

                    if (LitInt(2) <= z#2_0 && z#2_0 < 6)
                    {
                    }

                    if (LitInt(2) <= z#2_0 && z#2_0 < 6 && LitInt(2) <= z#prime#2_0 && z#prime#2_0 < 6)
                    {
                        assert _module.__default.f(z#2_0) != _module.__default.f(z#prime#2_0)
                           || LitInt(20) == LitInt(20);
                    }
                }

                // End Comprehension WF check
                assume (forall z#2_1: int :: 
                  { _module.__default.f(z#2_1) } 
                  _module.__default.f#canCall(z#2_1)
                     && (forall a#2_0#0#0: int :: 
                      { _module.__default.f(a#2_0#0#0) } 
                      LitInt(2) <= a#2_0#0#0 && a#2_0#0#0 < 6
                         ==> LitInt(2) <= map$project$3#2_0#z#0(_module.__default.f(a#2_0#0#0))
                           && map$project$3#2_0#z#0(_module.__default.f(a#2_0#0#0)) < 6
                           && _module.__default.f(a#2_0#0#0)
                             == _module.__default.f(map$project$3#2_0#z#0(_module.__default.f(a#2_0#0#0)))));
                m#2_0 := Map#Glue((lambda $w#2_0: Box :: 
                    (exists a#2_1#0#0: int :: 
                      LitInt(2) <= a#2_1#0#0
                         && a#2_1#0#0 < 6
                         && $Unbox($w#2_0): int == _module.__default.f(a#2_1#0#0))), 
                  (lambda $w#2_0: Box :: $Box(LitInt(20))), 
                  TMap(TInt, TInt));
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(224,45)"} true;
            }
            else
            {
                // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(225,10)
                if (*)
                {
                    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(226,11)
                    assume true;
                    // Begin Comprehension WF check
                    havoc z#3_0;
                    if (true)
                    {
                        havoc z#prime#3_0;
                        assume true;
                        if (LitInt(2) <= z#3_0)
                        {
                        }

                        if (LitInt(2) <= z#3_0 && z#3_0 < 6)
                        {
                            ##x#3_0 := z#3_0;
                            // assume allocatedness for argument to function
                            assume $IsAlloc(##x#3_0, TInt, $Heap);
                            assert {:subsumption 0} LitInt(0) <= ##x#3_0;
                            assume LitInt(0) <= ##x#3_0;
                            assume _module.__default.f#canCall(z#3_0);
                        }

                        if (LitInt(2) <= z#3_0 && z#3_0 < 6)
                        {
                        }

                        if (LitInt(2) <= z#3_0 && z#3_0 < 6 && LitInt(2) <= z#prime#3_0 && z#prime#3_0 < 6)
                        {
                            assert _module.__default.f(z#3_0) != _module.__default.f(z#prime#3_0)
                               || z#3_0 == z#prime#3_0;
                        }
                    }

                    // End Comprehension WF check
                    assume (forall z#3_1: int :: 
                      { _module.__default.f(z#3_1) } 
                      _module.__default.f#canCall(z#3_1)
                         && (forall a#3_0#0#0: int :: 
                          { _module.__default.f(a#3_0#0#0) } 
                          LitInt(2) <= a#3_0#0#0 && a#3_0#0#0 < 6
                             ==> LitInt(2) <= map$project$4#3_0#z#0(_module.__default.f(a#3_0#0#0))
                               && map$project$4#3_0#z#0(_module.__default.f(a#3_0#0#0)) < 6
                               && _module.__default.f(a#3_0#0#0)
                                 == _module.__default.f(map$project$4#3_0#z#0(_module.__default.f(a#3_0#0#0)))));
                    m#3_0 := Map#Glue((lambda $w#3_0: Box :: 
                        (exists a#3_1#0#0: int :: 
                          LitInt(2) <= a#3_1#0#0
                             && a#3_1#0#0 < 6
                             && $Unbox($w#3_0): int == _module.__default.f(a#3_1#0#0))), 
                      (lambda $w#3_0: Box :: $Box(map$project$4#3_0#z#0($Unbox($w#3_0): int))), 
                      TMap(TInt, TInt));
                    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(226,44)"} true;
                }
                else
                {
                }
            }
        }
    }
}



procedure CheckWellformed$$_module.__default.GeneralMaps2();
  free requires 42 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.GeneralMaps2();
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.GeneralMaps2() returns ($_reverifyPost: bool);
  free requires 42 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;



function map$project$5#0_0#z#0(int) : int;

function map$project$6#0#z#0(int) : int;

implementation Impl$$_module.__default.GeneralMaps2() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var m#0_0: IMap Box Box
     where $Is(m#0_0, TIMap(TInt, TInt)) && $IsAlloc(m#0_0, TIMap(TInt, TInt), $Heap);
  var z#0_0: int;
  var z#prime#0_0: int;
  var ##x#0_0: int;
  var m#0: IMap Box Box
     where $Is(m#0, TIMap(TInt, TInt)) && $IsAlloc(m#0, TIMap(TInt, TInt), $Heap);
  var z#0: int;
  var z#prime#0: int;
  var ##x#0: int;

    // AddMethodImpl: GeneralMaps2, Impl$$_module.__default.GeneralMaps2
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(230,28): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(231,3)
    if (*)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(232,11)
        assume true;
        // Begin Comprehension WF check
        havoc z#0_0;
        if (true)
        {
            havoc z#prime#0_0;
            assume true;
            if (LitInt(2) <= z#0_0)
            {
            }

            if (LitInt(2) <= z#0_0 && z#0_0 < 6)
            {
                ##x#0_0 := z#0_0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##x#0_0, TInt, $Heap);
                assume _module.__default.g#canCall(z#0_0);
            }

            if (LitInt(2) <= z#0_0 && z#0_0 < 6)
            {
            }

            if (LitInt(2) <= z#0_0 && z#0_0 < 6 && LitInt(2) <= z#prime#0_0 && z#prime#0_0 < 6)
            {
                assert _module.__default.g(z#0_0) != _module.__default.g(z#prime#0_0)
                   || z#0_0 == z#prime#0_0;
            }
        }

        // End Comprehension WF check
        assume (forall z#0_1: int :: 
          { _module.__default.g(z#0_1) } 
          _module.__default.g#canCall(z#0_1)
             && (forall a#0_0#0#0: int :: 
              { _module.__default.g(a#0_0#0#0) } 
              LitInt(2) <= a#0_0#0#0 && a#0_0#0#0 < 6
                 ==> LitInt(2) <= map$project$5#0_0#z#0(_module.__default.g(a#0_0#0#0))
                   && map$project$5#0_0#z#0(_module.__default.g(a#0_0#0#0)) < 6
                   && _module.__default.g(a#0_0#0#0)
                     == _module.__default.g(map$project$5#0_0#z#0(_module.__default.g(a#0_0#0#0)))));
        m#0_0 := IMap#Glue((lambda $w#0_0: Box :: 
            (exists a#0_1#0#0: int :: 
              LitInt(2) <= a#0_1#0#0
                 && a#0_1#0#0 < 6
                 && $Unbox($w#0_0): int == _module.__default.g(a#0_1#0#0))), 
          (lambda $w#0_0: Box :: $Box(map$project$5#0_0#z#0($Unbox($w#0_0): int))), 
          TIMap(TInt, TInt));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(232,45)"} true;
    }
    else
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(234,11)
        assume true;
        // Begin Comprehension WF check
        havoc z#0;
        if (true)
        {
            havoc z#prime#0;
            assume true;
            if (Lit(true))
            {
                ##x#0 := z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##x#0, TInt, $Heap);
                assume _module.__default.g#canCall(z#0);
            }

            if (Lit(true))
            {
            }

            if (Lit(true) && Lit(true))
            {
                assert _module.__default.g(z#0) != _module.__default.g(z#prime#0) || z#0 == z#prime#0;
            }
        }

        // End Comprehension WF check
        assume (forall z#1: int :: 
          { _module.__default.g(z#1) } 
          _module.__default.g#canCall(z#1)
             && (forall a#0#0#0: int :: 
              { _module.__default.g(a#0#0#0) } 
              Lit(true)
                 ==> Lit(true)
                   && _module.__default.g(a#0#0#0)
                     == _module.__default.g(map$project$6#0#z#0(_module.__default.g(a#0#0#0)))));
        m#0 := IMap#Glue((lambda $w#0: Box :: 
            (exists a#1#0#0: int :: 
              Lit(true) && $Unbox($w#0): int == _module.__default.g(a#1#0#0))), 
          (lambda $w#0: Box :: $Box(map$project$6#0#z#0($Unbox($w#0): int))), 
          TIMap(TInt, TInt));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(234,32)"} true;
    }
}



procedure CheckWellformed$$_module.__default.GeneralMaps3();
  free requires 43 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.GeneralMaps3();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.GeneralMaps3() returns ($_reverifyPost: bool);
  free requires 43 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



function map$project$7#1_0#u#0(int) : int;

implementation Impl$$_module.__default.GeneralMaps3() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var m#0_0: Map Box Box
     where $Is(m#0_0, TMap(TInt, TInt)) && $IsAlloc(m#0_0, TMap(TInt, TInt), $Heap);
  var u#0_0: int;
  var ##x#0_0: int;
  var m#1_0: Map Box Box
     where $Is(m#1_0, TMap(TInt, TInt)) && $IsAlloc(m#1_0, TMap(TInt, TInt), $Heap);
  var u#1_0: int;
  var u#prime#1_0: int;
  var ##x#1_0: int;

    // AddMethodImpl: GeneralMaps3, Impl$$_module.__default.GeneralMaps3
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(238,22): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(240,3)
    if (*)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(241,11)
        assume true;
        // Begin Comprehension WF check
        havoc u#0_0;
        if (true)
        {
            if (LitInt(-2) <= u#0_0)
            {
            }

            if (LitInt(-2) <= u#0_0 && u#0_0 < 6)
            {
                ##x#0_0 := u#0_0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##x#0_0, TInt, $Heap);
                assert {:subsumption 0} LitInt(0) <= ##x#0_0;
                assume LitInt(0) <= ##x#0_0;
                assume _module.__default.f#canCall(u#0_0);
            }
        }

        // End Comprehension WF check
        assume (forall u#0_1: int :: 
          { _module.__default.f(u#0_1) } 
          LitInt(-2) <= u#0_1 && u#0_1 < 6 ==> _module.__default.f#canCall(u#0_1));
        m#0_0 := Map#Glue((lambda $w#0_0: Box :: 
            LitInt(-2) <= $Unbox($w#0_0): int && $Unbox($w#0_0): int < 6), 
          (lambda $w#0_0: Box :: $Box(_module.__default.f($Unbox($w#0_0): int))), 
          TMap(TInt, TInt));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(241,45)"} true;
    }
    else
    {
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(242,10)
        if (*)
        {
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(243,11)
            assume true;
            // Begin Comprehension WF check
            havoc u#1_0;
            if (true)
            {
                havoc u#prime#1_0;
                assume true;
                if (LitInt(-2) <= u#1_0)
                {
                }

                if (LitInt(-2) <= u#1_0 && u#1_0 < 6)
                {
                    ##x#1_0 := u#1_0;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##x#1_0, TInt, $Heap);
                    assert {:subsumption 0} LitInt(0) <= ##x#1_0;
                    assume LitInt(0) <= ##x#1_0;
                    assume _module.__default.f#canCall(u#1_0);
                }

                if (LitInt(-2) <= u#1_0 && u#1_0 < 6)
                {
                }

                if (LitInt(-2) <= u#1_0 && u#1_0 < 6 && LitInt(-2) <= u#prime#1_0 && u#prime#1_0 < 6)
                {
                    assert _module.__default.f(u#1_0) != _module.__default.f(u#prime#1_0)
                       || u#1_0 == u#prime#1_0;
                }
            }

            // End Comprehension WF check
            assume (forall u#1_1: int :: 
              { _module.__default.f(u#1_1) } 
              _module.__default.f#canCall(u#1_1)
                 && (forall a#1_0#0#0: int :: 
                  { _module.__default.f(a#1_0#0#0) } 
                  LitInt(-2) <= a#1_0#0#0 && a#1_0#0#0 < 6
                     ==> LitInt(-2) <= map$project$7#1_0#u#0(_module.__default.f(a#1_0#0#0))
                       && map$project$7#1_0#u#0(_module.__default.f(a#1_0#0#0)) < 6
                       && _module.__default.f(a#1_0#0#0)
                         == _module.__default.f(map$project$7#1_0#u#0(_module.__default.f(a#1_0#0#0)))));
            m#1_0 := Map#Glue((lambda $w#1_0: Box :: 
                (exists a#1_1#0#0: int :: 
                  LitInt(-2) <= a#1_1#0#0
                     && a#1_1#0#0 < 6
                     && $Unbox($w#1_0): int == _module.__default.f(a#1_1#0#0))), 
              (lambda $w#1_0: Box :: $Box(map$project$7#1_0#u#0($Unbox($w#1_0): int))), 
              TMap(TInt, TInt));
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(243,45)"} true;
        }
        else
        {
        }
    }
}



// function declaration for _module._default.UnboxTest
function _module.__default.UnboxTest(s#0: Seq Box) : Map Box Box;

function _module.__default.UnboxTest#canCall(s#0: Seq Box) : bool;

// consequence axiom for _module.__default.UnboxTest
axiom 64 <= $FunctionContextHeight
   ==> (forall s#0: Seq Box :: 
    { _module.__default.UnboxTest(s#0) } 
    _module.__default.UnboxTest#canCall(s#0)
         || (64 != $FunctionContextHeight && $Is(s#0, TSeq(TSeq(TInt))))
       ==> $Is(_module.__default.UnboxTest(s#0), TMap(TSeq(TInt), TSeq(TInt))));

function _module.__default.UnboxTest#requires(Seq Box) : bool;

// #requires axiom for _module.__default.UnboxTest
axiom (forall s#0: Seq Box :: 
  { _module.__default.UnboxTest#requires(s#0) } 
  $Is(s#0, TSeq(TSeq(TInt))) ==> _module.__default.UnboxTest#requires(s#0) == true);

function map$project$8#0#i#0(Seq Box) : int;

// definition axiom for _module.__default.UnboxTest (revealed)
axiom 64 <= $FunctionContextHeight
   ==> (forall s#0: Seq Box :: 
    { _module.__default.UnboxTest(s#0) } 
    _module.__default.UnboxTest#canCall(s#0)
         || (64 != $FunctionContextHeight && $Is(s#0, TSeq(TSeq(TInt))))
       ==> (forall a#1#0#0: int :: 
          { $Unbox(Seq#Index(s#0, a#1#0#0)): Seq Box } 
          LitInt(0) <= a#1#0#0 && a#1#0#0 < Seq#Length(s#0)
             ==> LitInt(0) <= map$project$8#0#i#0($Unbox(Seq#Index(s#0, a#1#0#0)): Seq Box)
               && map$project$8#0#i#0($Unbox(Seq#Index(s#0, a#1#0#0)): Seq Box) < Seq#Length(s#0)
               && $Unbox(Seq#Index(s#0, a#1#0#0)): Seq Box
                 == $Unbox(Seq#Index(s#0, map$project$8#0#i#0($Unbox(Seq#Index(s#0, a#1#0#0)): Seq Box))): Seq Box)
         && _module.__default.UnboxTest(s#0)
           == Map#Glue((lambda $w#0: Box :: 
              $Is($Unbox($w#0): Seq Box, TSeq(TInt))
                 && (exists a#0#0#0: int :: 
                  LitInt(0) <= a#0#0#0
                     && a#0#0#0 < Seq#Length(s#0)
                     && $Unbox($w#0): Seq Box == $Unbox(Seq#Index(s#0, a#0#0#0)): Seq Box)), 
            (lambda $w#0: Box :: Seq#Index(s#0, map$project$8#0#i#0($Unbox($w#0): Seq Box))), 
            TMap(TSeq(TInt), TSeq(TInt))));

function map$project$9#0#i#0(Seq Box) : int;

// definition axiom for _module.__default.UnboxTest for all literals (revealed)
axiom 64 <= $FunctionContextHeight
   ==> (forall s#0: Seq Box :: 
    {:weight 3} { _module.__default.UnboxTest(Lit(s#0)) } 
    _module.__default.UnboxTest#canCall(Lit(s#0))
         || (64 != $FunctionContextHeight && $Is(s#0, TSeq(TSeq(TInt))))
       ==> (forall a#3#0#0: int :: 
          { $Unbox(Seq#Index(s#0, a#3#0#0)): Seq Box } 
          LitInt(0) <= a#3#0#0 && a#3#0#0 < Seq#Length(Lit(s#0))
             ==> LitInt(0) <= map$project$9#0#i#0($Unbox(Seq#Index(Lit(s#0), a#3#0#0)): Seq Box)
               && map$project$9#0#i#0($Unbox(Seq#Index(Lit(s#0), a#3#0#0)): Seq Box)
                 < Seq#Length(Lit(s#0))
               && $Unbox(Seq#Index(Lit(s#0), a#3#0#0)): Seq Box
                 == $Unbox(Seq#Index(Lit(s#0), map$project$9#0#i#0($Unbox(Seq#Index(Lit(s#0), a#3#0#0)): Seq Box))): Seq Box)
         && _module.__default.UnboxTest(Lit(s#0))
           == Map#Glue((lambda $w#1: Box :: 
              $Is($Unbox($w#1): Seq Box, TSeq(TInt))
                 && (exists a#2#0#0: int :: 
                  LitInt(0) <= a#2#0#0
                     && a#2#0#0 < Seq#Length(Lit(s#0))
                     && $Unbox($w#1): Seq Box == $Unbox(Seq#Index(Lit(s#0), a#2#0#0)): Seq Box)), 
            (lambda $w#1: Box :: 
              Seq#Index(Lit(s#0), map$project$9#0#i#0($Unbox($w#1): Seq Box))), 
            TMap(TSeq(TInt), TSeq(TInt))));

procedure CheckWellformed$$_module.__default.UnboxTest(s#0: Seq Box where $Is(s#0, TSeq(TSeq(TInt))));
  free requires 64 == $FunctionContextHeight;
  modifies $Heap, $Tick;



function map$project$10#0#i#0(Seq Box) : int;

implementation CheckWellformed$$_module.__default.UnboxTest(s#0: Seq Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var i#1: int;
  var i#prime#0: int;


    // AddWellformednessCheck for function UnboxTest
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(247,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.UnboxTest(s#0), TMap(TSeq(TInt), TSeq(TInt)));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        // Begin Comprehension WF check
        havoc i#1;
        if (true)
        {
            havoc i#prime#0;
            assume true;
            if (LitInt(0) <= i#1)
            {
            }

            if (LitInt(0) <= i#1 && i#1 < Seq#Length(s#0))
            {
                assert 0 <= i#1 && i#1 < Seq#Length(s#0);
            }

            if (LitInt(0) <= i#1 && i#1 < Seq#Length(s#0))
            {
                assert 0 <= i#1 && i#1 < Seq#Length(s#0);
            }

            if (LitInt(0) <= i#1
               && i#1 < Seq#Length(s#0)
               && 
              LitInt(0) <= i#prime#0
               && i#prime#0 < Seq#Length(s#0))
            {
                assert $Unbox(Seq#Index(s#0, i#1)): Seq Box
                     != $Unbox(Seq#Index(s#0, i#prime#0)): Seq Box
                   || $Unbox(Seq#Index(s#0, i#1)): Seq Box
                     == $Unbox(Seq#Index(s#0, i#prime#0)): Seq Box;
            }
        }

        // End Comprehension WF check
        assume _module.__default.UnboxTest(s#0)
           == Map#Glue((lambda $w#2: Box :: 
              $Is($Unbox($w#2): Seq Box, TSeq(TInt))
                 && (exists a#4#0#0: int :: 
                  LitInt(0) <= a#4#0#0
                     && a#4#0#0 < Seq#Length(s#0)
                     && $Unbox($w#2): Seq Box == $Unbox(Seq#Index(s#0, a#4#0#0)): Seq Box)), 
            (lambda $w#2: Box :: 
              Seq#Index(s#0, map$project$10#0#i#0($Unbox($w#2): Seq Box))), 
            TMap(TSeq(TInt), TSeq(TInt)));
        assume (forall a#5#0#0: int :: 
          { $Unbox(Seq#Index(s#0, a#5#0#0)): Seq Box } 
          LitInt(0) <= a#5#0#0 && a#5#0#0 < Seq#Length(s#0)
             ==> LitInt(0) <= map$project$10#0#i#0($Unbox(Seq#Index(s#0, a#5#0#0)): Seq Box)
               && map$project$10#0#i#0($Unbox(Seq#Index(s#0, a#5#0#0)): Seq Box) < Seq#Length(s#0)
               && $Unbox(Seq#Index(s#0, a#5#0#0)): Seq Box
                 == $Unbox(Seq#Index(s#0, map$project$10#0#i#0($Unbox(Seq#Index(s#0, a#5#0#0)): Seq Box))): Seq Box);
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.UnboxTest(s#0), TMap(TSeq(TInt), TSeq(TInt)));
    }
}



procedure CheckWellformed$$_module.__default.GeneralMaps4(s#0: Set Box where $Is(s#0, TSet(TReal)) && $IsAlloc(s#0, TSet(TReal), $Heap), 
    twelve#0: real);
  free requires 65 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.GeneralMaps4(s#0: Set Box where $Is(s#0, TSet(TReal)) && $IsAlloc(s#0, TSet(TReal), $Heap), 
    twelve#0: real);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.GeneralMaps4(s#0: Set Box where $Is(s#0, TSet(TReal)) && $IsAlloc(s#0, TSet(TReal), $Heap), 
    twelve#0: real)
   returns ($_reverifyPost: bool);
  free requires 65 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



function map$project$11#0#n#0(real) : real;

function map$project$11#0#p#0(real) : real;

implementation Impl$$_module.__default.GeneralMaps4(s#0: Set Box, twelve#0: real) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var c0#0: Map Box Box
     where $Is(c0#0, TMap(TReal, TReal)) && $IsAlloc(c0#0, TMap(TReal, TReal), $Heap);
  var n#0: real;
  var p#0: real;
  var n#prime#0: real;
  var p#prime#0: real;

    // AddMethodImpl: GeneralMaps4, Impl$$_module.__default.GeneralMaps4
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(254,48): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(255,10)
    assume true;
    // Begin Comprehension WF check
    havoc n#0;
    havoc p#0;
    if (true)
    {
        havoc n#prime#0;
        havoc p#prime#0;
        assume true;
        if (s#0[$Box(n#0)])
        {
        }

        if (s#0[$Box(n#0)] && s#0[$Box(p#0)])
        {
        }

        if (s#0[$Box(n#0)] && s#0[$Box(p#0)])
        {
        }

        if (s#0[$Box(n#0)] && s#0[$Box(p#0)] && s#0[$Box(n#prime#0)] && s#0[$Box(p#prime#0)])
        {
            assert n#0 != n#prime#0 || twelve#0 == twelve#0;
        }
    }

    // End Comprehension WF check
    assume (forall a#0#0#0: real, a#0#1#0: real :: 
      { s#0[$Box(a#0#1#0)], s#0[$Box(a#0#0#0)] } 
      s#0[$Box(a#0#0#0)] && s#0[$Box(a#0#1#0)]
         ==> s#0[$Box(map$project$11#0#n#0(a#0#0#0))]
           && s#0[$Box(map$project$11#0#p#0(a#0#0#0))]
           && a#0#0#0 == map$project$11#0#n#0(a#0#0#0));
    c0#0 := Map#Glue((lambda $w#0: Box :: 
        (exists a#1#0#0: real, a#1#1#0: real :: 
          s#0[$Box(a#1#0#0)] && s#0[$Box(a#1#1#0)] && $Unbox($w#0): real == a#1#0#0)), 
      (lambda $w#0: Box :: $Box(twelve#0)), 
      TMap(TReal, TReal));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(255,53)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(256,3)
    if (s#0[$Box(LitReal(2e0))])
    {
        assert {:subsumption 0} Map#Domain(c0#0)[$Box(LitReal(2e0))];
    }

    assume true;
    assert {:subsumption 0} s#0[$Box(LitReal(2e0))]
       ==> $Unbox(Map#Elements(c0#0)[$Box(LitReal(2e0))]): real == twelve#0;
    assume s#0[$Box(LitReal(2e0))]
       ==> $Unbox(Map#Elements(c0#0)[$Box(LitReal(2e0))]): real == twelve#0;
}



procedure CheckWellformed$$_module.__default.GeneralMaps5(u#0: Seq Box where $Is(u#0, TSeq(TInt)) && $IsAlloc(u#0, TSeq(TInt), $Heap));
  free requires 66 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.GeneralMaps5(u#0: Seq Box where $Is(u#0, TSeq(TInt)) && $IsAlloc(u#0, TSeq(TInt), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.GeneralMaps5(u#0: Seq Box where $Is(u#0, TSeq(TInt)) && $IsAlloc(u#0, TSeq(TInt), $Heap))
   returns ($_reverifyPost: bool);
  free requires 66 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



function map$project$12#0#i#0(int) : int;

implementation Impl$$_module.__default.GeneralMaps5(u#0: Seq Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var c1#0: Map Box Box
     where $Is(c1#0, TMap(TInt, TInt)) && $IsAlloc(c1#0, TMap(TInt, TInt), $Heap);
  var i#0: int;
  var i#prime#0: int;

    // AddMethodImpl: GeneralMaps5, Impl$$_module.__default.GeneralMaps5
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(259,33): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(260,10)
    assume true;
    // Begin Comprehension WF check
    havoc i#0;
    if (true)
    {
        havoc i#prime#0;
        assume true;
        if (LitInt(0) <= i#0)
        {
        }

        if (LitInt(0) <= i#0 && i#0 < Seq#Length(u#0))
        {
            assert 0 <= i#0 && i#0 < Seq#Length(u#0);
        }

        if (LitInt(0) <= i#0 && i#0 < Seq#Length(u#0))
        {
            assert 0 <= i#0 && i#0 < Seq#Length(u#0);
        }

        if (LitInt(0) <= i#0
           && i#0 < Seq#Length(u#0)
           && 
          LitInt(0) <= i#prime#0
           && i#prime#0 < Seq#Length(u#0))
        {
            assert $Unbox(Seq#Index(u#0, i#0)): int != $Unbox(Seq#Index(u#0, i#prime#0)): int
               || $Unbox(Seq#Index(u#0, i#0)): int + 100
                 == $Unbox(Seq#Index(u#0, i#prime#0)): int + 100;
        }
    }

    // End Comprehension WF check
    assume (forall a#0#0#0: int :: 
      { $Unbox(Seq#Index(u#0, a#0#0#0)): int } 
      LitInt(0) <= a#0#0#0 && a#0#0#0 < Seq#Length(u#0)
         ==> LitInt(0) <= map$project$12#0#i#0($Unbox(Seq#Index(u#0, a#0#0#0)): int)
           && map$project$12#0#i#0($Unbox(Seq#Index(u#0, a#0#0#0)): int) < Seq#Length(u#0)
           && $Unbox(Seq#Index(u#0, a#0#0#0)): int
             == $Unbox(Seq#Index(u#0, map$project$12#0#i#0($Unbox(Seq#Index(u#0, a#0#0#0)): int))): int);
    c1#0 := Map#Glue((lambda $w#0: Box :: 
        (exists a#1#0#0: int :: 
          LitInt(0) <= a#1#0#0
             && a#1#0#0 < Seq#Length(u#0)
             && $Unbox($w#0): int == $Unbox(Seq#Index(u#0, a#1#0#0)): int)), 
      (lambda $w#0: Box :: 
        $Box($Unbox(Seq#Index(u#0, map$project$12#0#i#0($Unbox($w#0): int))): int + 100)), 
      TMap(TInt, TInt));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(260,59)"} true;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(261,3)
    if (*)
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(262,5)
        if (7 < Seq#Length(u#0))
        {
            assert {:subsumption 0} 0 <= LitInt(7) && LitInt(7) < Seq#Length(u#0);
            if (101 < $Unbox(Seq#Index(u#0, LitInt(7))): int)
            {
                assert {:subsumption 0} 0 <= LitInt(7) && LitInt(7) < Seq#Length(u#0);
            }
        }

        if (7 < Seq#Length(u#0)
           && 
          101 < $Unbox(Seq#Index(u#0, LitInt(7))): int
           && $Unbox(Seq#Index(u#0, LitInt(7))): int < 103)
        {
            assert {:subsumption 0} Map#Domain(c1#0)[$Box(LitInt(102))];
        }

        assume true;
        assert {:subsumption 0} 7 < Seq#Length(u#0)
             && 
            101 < $Unbox(Seq#Index(u#0, LitInt(7))): int
             && $Unbox(Seq#Index(u#0, LitInt(7))): int < 103
           ==> $Unbox(Map#Elements(c1#0)[$Box(LitInt(102))]): int == LitInt(202);
        assume 7 < Seq#Length(u#0)
             && 
            101 < $Unbox(Seq#Index(u#0, LitInt(7))): int
             && $Unbox(Seq#Index(u#0, LitInt(7))): int < 103
           ==> $Unbox(Map#Elements(c1#0)[$Box(LitInt(102))]): int == LitInt(202);
    }
    else
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(264,5)
        if (7 < Seq#Length(u#0))
        {
            assert {:subsumption 0} 0 <= LitInt(7) && LitInt(7) < Seq#Length(u#0);
            if (2101 < $Unbox(Seq#Index(u#0, LitInt(7))): int)
            {
                assert {:subsumption 0} 0 <= LitInt(7) && LitInt(7) < Seq#Length(u#0);
            }
        }

        if (7 < Seq#Length(u#0)
           && 
          2101 < $Unbox(Seq#Index(u#0, LitInt(7))): int
           && $Unbox(Seq#Index(u#0, LitInt(7))): int < 2103)
        {
            assert {:subsumption 0} Map#Domain(c1#0)[$Box(LitInt(2102))];
        }

        assume true;
        assert {:subsumption 0} 7 < Seq#Length(u#0)
             && 
            2101 < $Unbox(Seq#Index(u#0, LitInt(7))): int
             && $Unbox(Seq#Index(u#0, LitInt(7))): int < 2103
           ==> $Unbox(Map#Elements(c1#0)[$Box(LitInt(2102))]): int == LitInt(2200);
        assume 7 < Seq#Length(u#0)
             && 
            2101 < $Unbox(Seq#Index(u#0, LitInt(7))): int
             && $Unbox(Seq#Index(u#0, LitInt(7))): int < 2103
           ==> $Unbox(Map#Elements(c1#0)[$Box(LitInt(2102))]): int == LitInt(2200);
    }
}



// function declaration for _module._default.Thirteen
function _module.__default.Thirteen(x#0: int) : bool;

function _module.__default.Thirteen#canCall(x#0: int) : bool;

// consequence axiom for _module.__default.Thirteen
axiom 44 <= $FunctionContextHeight
   ==> (forall x#0: int :: 
    { _module.__default.Thirteen(x#0) } 
    _module.__default.Thirteen#canCall(x#0) || 44 != $FunctionContextHeight ==> true);

function _module.__default.Thirteen#requires(int) : bool;

// #requires axiom for _module.__default.Thirteen
axiom (forall x#0: int :: 
  { _module.__default.Thirteen#requires(x#0) } 
  _module.__default.Thirteen#requires(x#0) == true);

// definition axiom for _module.__default.Thirteen (revealed)
axiom 44 <= $FunctionContextHeight
   ==> (forall x#0: int :: 
    { _module.__default.Thirteen(x#0) } 
    _module.__default.Thirteen#canCall(x#0) || 44 != $FunctionContextHeight
       ==> _module.__default.Thirteen(x#0) == (x#0 == LitInt(13)));

// definition axiom for _module.__default.Thirteen for all literals (revealed)
axiom 44 <= $FunctionContextHeight
   ==> (forall x#0: int :: 
    {:weight 3} { _module.__default.Thirteen(LitInt(x#0)) } 
    _module.__default.Thirteen#canCall(LitInt(x#0)) || 44 != $FunctionContextHeight
       ==> _module.__default.Thirteen(LitInt(x#0)) == (LitInt(x#0) == LitInt(13)));

procedure CheckWellformed$$_module.__default.Thirteen(x#0: int);
  free requires 44 == $FunctionContextHeight;
  modifies $Heap, $Tick;



// function declaration for _module._default.Odd
function _module.__default.Odd(y#0: int) : bool;

function _module.__default.Odd#canCall(y#0: int) : bool;

// consequence axiom for _module.__default.Odd
axiom 45 <= $FunctionContextHeight
   ==> (forall y#0: int :: 
    { _module.__default.Odd(y#0) } 
    _module.__default.Odd#canCall(y#0) || 45 != $FunctionContextHeight ==> true);

function _module.__default.Odd#requires(int) : bool;

// #requires axiom for _module.__default.Odd
axiom (forall y#0: int :: 
  { _module.__default.Odd#requires(y#0) } 
  _module.__default.Odd#requires(y#0) == true);

// definition axiom for _module.__default.Odd (revealed)
axiom 45 <= $FunctionContextHeight
   ==> (forall y#0: int :: 
    { _module.__default.Odd(y#0) } 
    _module.__default.Odd#canCall(y#0) || 45 != $FunctionContextHeight
       ==> _module.__default.Odd(y#0) == (Mod(y#0, LitInt(2)) == LitInt(1)));

// definition axiom for _module.__default.Odd for all literals (revealed)
axiom 45 <= $FunctionContextHeight
   ==> (forall y#0: int :: 
    {:weight 3} { _module.__default.Odd(LitInt(y#0)) } 
    _module.__default.Odd#canCall(LitInt(y#0)) || 45 != $FunctionContextHeight
       ==> _module.__default.Odd(LitInt(y#0)) == (LitInt(Mod(y#0, LitInt(2))) == LitInt(1)));

procedure CheckWellformed$$_module.__default.Odd(y#0: int);
  free requires 45 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Odd(y#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;


    // AddWellformednessCheck for function Odd
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(269,17): initial state"} true;
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
        assert LitInt(2) != 0;
        assume _module.__default.Odd(y#0) == (Mod(y#0, LitInt(2)) == LitInt(1));
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.Odd(y#0), TBool);
    }
}



procedure CheckWellformed$$_module.__default.GeneralMaps6();
  free requires 46 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.GeneralMaps6();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.GeneralMaps6() returns ($_reverifyPost: bool);
  free requires 46 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



function map$project$13#0#x#0(int) : int;

function map$project$13#0#y#0(int) : int;

implementation Impl$$_module.__default.GeneralMaps6() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var c2#0: Map Box Box
     where $Is(c2#0, TMap(TInt, TInt)) && $IsAlloc(c2#0, TMap(TInt, TInt), $Heap);
  var x#0: int;
  var y#0: int;
  var x#prime#0: int;
  var y#prime#0: int;
  var ##x#0: int;
  var ##y#0: int;
  var ##x#1: int;
  var ##y#1: int;

    // AddMethodImpl: GeneralMaps6, Impl$$_module.__default.GeneralMaps6
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(271,22): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(272,10)
    assume true;
    // Begin Comprehension WF check
    havoc x#0;
    havoc y#0;
    if (true)
    {
        havoc x#prime#0;
        havoc y#prime#0;
        assume true;
        if (LitInt(12) <= x#0)
        {
        }

        if (LitInt(12) <= x#0 && x#0 < y#0)
        {
        }

        if (LitInt(12) <= x#0 && x#0 < y#0 && y#0 < 17)
        {
            ##x#0 := x#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##x#0, TInt, $Heap);
            assume _module.__default.Thirteen#canCall(x#0);
        }

        if (LitInt(12) <= x#0 && x#0 < y#0 && y#0 < 17 && _module.__default.Thirteen(x#0))
        {
            ##y#0 := y#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##y#0, TInt, $Heap);
            assume _module.__default.Odd#canCall(y#0);
        }

        if (LitInt(12) <= x#0
           && x#0 < y#0
           && y#0 < 17
           && _module.__default.Thirteen(x#0)
           && _module.__default.Odd(y#0))
        {
        }

        if (LitInt(12) <= x#0
           && x#0 < y#0
           && y#0 < 17
           && _module.__default.Thirteen(x#0)
           && _module.__default.Odd(y#0))
        {
        }

        if (LitInt(12) <= x#0
           && x#0 < y#0
           && y#0 < 17
           && _module.__default.Thirteen(x#0)
           && _module.__default.Odd(y#0)
           && 
          LitInt(12) <= x#prime#0
           && x#prime#0 < y#prime#0
           && y#prime#0 < 17
           && _module.__default.Thirteen(x#prime#0)
           && _module.__default.Odd(y#prime#0))
        {
            assert x#0 != x#prime#0 || y#0 == y#prime#0;
        }
    }

    // End Comprehension WF check
    assume (forall x#1: int, y#1: int :: 
      { _module.__default.Odd(y#1), _module.__default.Thirteen(x#1) } 
      (LitInt(12) <= x#1 && x#1 < y#1 && y#1 < 17
           ==> _module.__default.Thirteen#canCall(x#1)
             && (_module.__default.Thirteen(x#1) ==> _module.__default.Odd#canCall(y#1)))
         && (forall a#0#0#0: int, a#0#1#0: int :: 
          { _module.__default.Odd(a#0#1#0), _module.__default.Thirteen(a#0#0#0) } 
          LitInt(12) <= a#0#0#0
               && a#0#0#0 < a#0#1#0
               && a#0#1#0 < 17
               && _module.__default.Thirteen(a#0#0#0)
               && _module.__default.Odd(a#0#1#0)
             ==> LitInt(12) <= map$project$13#0#x#0(a#0#0#0)
               && map$project$13#0#x#0(a#0#0#0) < map$project$13#0#y#0(a#0#0#0)
               && map$project$13#0#y#0(a#0#0#0) < 17
               && _module.__default.Thirteen(map$project$13#0#x#0(a#0#0#0))
               && _module.__default.Odd(map$project$13#0#y#0(a#0#0#0))
               && a#0#0#0 == map$project$13#0#x#0(a#0#0#0)));
    c2#0 := Map#Glue((lambda $w#0: Box :: 
        (exists a#1#0#0: int, a#1#1#0: int :: 
          LitInt(12) <= a#1#0#0
             && a#1#0#0 < a#1#1#0
             && a#1#1#0 < 17
             && _module.__default.Thirteen(a#1#0#0)
             && _module.__default.Odd(a#1#1#0)
             && $Unbox($w#0): int == a#1#0#0)), 
      (lambda $w#0: Box :: $Box(map$project$13#0#y#0($Unbox($w#0): int))), 
      TMap(TInt, TInt));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(272,73)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(273,3)
    ##x#1 := LitInt(13);
    // assume allocatedness for argument to function
    assume $IsAlloc(##x#1, TInt, $Heap);
    assume _module.__default.Thirteen#canCall(LitInt(13));
    if (Lit(_module.__default.Thirteen(LitInt(13))))
    {
        ##y#1 := LitInt(15);
        // assume allocatedness for argument to function
        assume $IsAlloc(##y#1, TInt, $Heap);
        assume _module.__default.Odd#canCall(LitInt(15));
    }

    assume _module.__default.Thirteen#canCall(LitInt(13))
       && (Lit(_module.__default.Thirteen(LitInt(13)))
         ==> _module.__default.Odd#canCall(LitInt(15)));
    assert {:subsumption 0} _module.__default.Thirteen#canCall(LitInt(13))
       ==> Lit(_module.__default.Thirteen(LitInt(13))) || LitInt(13) == LitInt(13);
    assert {:subsumption 0} _module.__default.Odd#canCall(LitInt(15))
       ==> Lit(_module.__default.Odd(LitInt(15)))
         || LitInt(Mod(15, LitInt(2))) == LitInt(1);
    assume _module.__default.Thirteen(LitInt(13)) && _module.__default.Odd(LitInt(15));
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(274,3)
    assert {:subsumption 0} Map#Domain(c2#0)[$Box(LitInt(13))];
    assume true;
    assert $Unbox(Map#Elements(c2#0)[$Box(LitInt(13))]): int == LitInt(15);
}



procedure CheckWellformed$$_module.__default.GeneralMaps7();
  free requires 47 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.GeneralMaps7();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.GeneralMaps7() returns ($_reverifyPost: bool);
  free requires 47 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



function map$project$14#0#i#0(int) : int;

implementation Impl$$_module.__default.GeneralMaps7() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var c3#0: Map Box Box
     where $Is(c3#0, TMap(TInt, TInt)) && $IsAlloc(c3#0, TMap(TInt, TInt), $Heap);
  var i#0: int;
  var i#prime#0: int;
  var ##x#0: int;
  var ##x#1: int;

    // AddMethodImpl: GeneralMaps7, Impl$$_module.__default.GeneralMaps7
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(277,22): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(278,10)
    assume true;
    // Begin Comprehension WF check
    havoc i#0;
    if (true)
    {
        havoc i#prime#0;
        assume true;
        if (LitInt(0) <= i#0)
        {
        }

        if (LitInt(0) <= i#0 && i#0 < 100)
        {
            ##x#0 := i#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##x#0, TInt, $Heap);
            assume _module.__default.Thirteen#canCall(i#0);
        }

        if (LitInt(0) <= i#0 && i#0 < 100 && _module.__default.Thirteen(i#0))
        {
        }

        if (LitInt(0) <= i#0 && i#0 < 100 && _module.__default.Thirteen(i#0))
        {
        }

        if (LitInt(0) <= i#0
           && i#0 < 100
           && _module.__default.Thirteen(i#0)
           && 
          LitInt(0) <= i#prime#0
           && i#prime#0 < 100
           && _module.__default.Thirteen(i#prime#0))
        {
            assert LitInt(5) != LitInt(5) || i#0 == i#prime#0;
        }
    }

    // End Comprehension WF check
    assume (forall i#1: int :: 
      { _module.__default.Thirteen(i#1) } 
      (LitInt(0) <= i#1 && i#1 < 100 ==> _module.__default.Thirteen#canCall(i#1))
         && (forall a#0#0#0: int :: 
          { _module.__default.Thirteen(a#0#0#0) } 
          LitInt(0) <= a#0#0#0 && a#0#0#0 < 100 && _module.__default.Thirteen(a#0#0#0)
             ==> LitInt(0) <= map$project$14#0#i#0(LitInt(5))
               && map$project$14#0#i#0(LitInt(5)) < 100
               && _module.__default.Thirteen(map$project$14#0#i#0(LitInt(5)))
               && LitInt(5) == LitInt(5)));
    c3#0 := Map#Glue((lambda $w#0: Box :: 
        (exists a#1#0#0: int :: 
          LitInt(0) <= a#1#0#0
             && a#1#0#0 < 100
             && _module.__default.Thirteen(a#1#0#0)
             && $Unbox($w#0): int == LitInt(5))), 
      (lambda $w#0: Box :: $Box(map$project$14#0#i#0($Unbox($w#0): int))), 
      TMap(TInt, TInt));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(278,62)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(279,3)
    ##x#1 := LitInt(13);
    // assume allocatedness for argument to function
    assume $IsAlloc(##x#1, TInt, $Heap);
    assume _module.__default.Thirteen#canCall(LitInt(13));
    assume _module.__default.Thirteen#canCall(LitInt(13));
    assert {:subsumption 0} _module.__default.Thirteen#canCall(LitInt(13))
       ==> Lit(_module.__default.Thirteen(LitInt(13))) || LitInt(13) == LitInt(13);
    assume _module.__default.Thirteen(LitInt(13));
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(280,3)
    assert {:subsumption 0} Map#Domain(c3#0)[$Box(LitInt(5))];
    assume true;
    assert $Unbox(Map#Elements(c3#0)[$Box(LitInt(5))]): int == LitInt(13);
}



// function declaration for _module._default.P8
function _module.__default.P8(x#0: int) : bool;

function _module.__default.P8#canCall(x#0: int) : bool;

// consequence axiom for _module.__default.P8
axiom 48 <= $FunctionContextHeight
   ==> (forall x#0: int :: 
    { _module.__default.P8(x#0) } 
    _module.__default.P8#canCall(x#0) || 48 != $FunctionContextHeight ==> true);

function _module.__default.P8#requires(int) : bool;

// #requires axiom for _module.__default.P8
axiom (forall x#0: int :: 
  { _module.__default.P8#requires(x#0) } 
  _module.__default.P8#requires(x#0) == true);

// definition axiom for _module.__default.P8 (revealed)
axiom 48 <= $FunctionContextHeight
   ==> (forall x#0: int :: 
    { _module.__default.P8(x#0) } 
    _module.__default.P8#canCall(x#0) || 48 != $FunctionContextHeight
       ==> _module.__default.P8(x#0) == Lit(true));

// definition axiom for _module.__default.P8 for all literals (revealed)
axiom 48 <= $FunctionContextHeight
   ==> (forall x#0: int :: 
    {:weight 3} { _module.__default.P8(LitInt(x#0)) } 
    _module.__default.P8#canCall(LitInt(x#0)) || 48 != $FunctionContextHeight
       ==> _module.__default.P8(LitInt(x#0)) == Lit(true));

procedure CheckWellformed$$_module.__default.P8(x#0: int);
  free requires 48 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure CheckWellformed$$_module.__default.GeneralMaps8();
  free requires 49 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.GeneralMaps8();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.GeneralMaps8() returns ($_reverifyPost: bool);
  free requires 49 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



function map$project$15#0#x#0(bool) : int;

implementation Impl$$_module.__default.GeneralMaps8() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var c4#0: Map Box Box
     where $Is(c4#0, TMap(TBool, TInt)) && $IsAlloc(c4#0, TMap(TBool, TInt), $Heap);
  var x#0: int;
  var x#prime#0: int;
  var ##x#0: int;
  var ##x#1: int;

    // AddMethodImpl: GeneralMaps8, Impl$$_module.__default.GeneralMaps8
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(285,22): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(286,16)
    assume true;
    // Begin Comprehension WF check
    havoc x#0;
    if (true)
    {
        havoc x#prime#0;
        assume true;
        if (Lit(true))
        {
            ##x#0 := x#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##x#0, TInt, $Heap);
            assume _module.__default.P8#canCall(x#0);
        }

        if (Lit(true))
        {
        }

        if (Lit(true) && Lit(true))
        {
            assert _module.__default.P8(x#0) != _module.__default.P8(x#prime#0)
               || LitInt(6) == LitInt(6);
        }
    }

    // End Comprehension WF check
    assume (forall x#1: int :: 
      { _module.__default.P8(x#1) } 
      _module.__default.P8#canCall(x#1)
         && (forall a#0#0#0: int :: 
          { _module.__default.P8(a#0#0#0) } 
          Lit(true)
             ==> Lit(true)
               && _module.__default.P8(a#0#0#0)
                 == _module.__default.P8(map$project$15#0#x#0(_module.__default.P8(a#0#0#0)))));
    c4#0 := Map#Glue((lambda $w#0: Box :: 
        (exists a#1#0#0: int :: 
          Lit(true) && $Unbox($w#0): bool == _module.__default.P8(a#1#0#0))), 
      (lambda $w#0: Box :: $Box(LitInt(6))), 
      TMap(TBool, TInt));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(286,49)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(287,3)
    ##x#1 := LitInt(177);
    // assume allocatedness for argument to function
    assume $IsAlloc(##x#1, TInt, $Heap);
    assume _module.__default.P8#canCall(LitInt(177));
    assume _module.__default.P8#canCall(LitInt(177));
    assert {:subsumption 0} _module.__default.P8#canCall(LitInt(177))
       ==> Lit(_module.__default.P8(LitInt(177))) || Lit(true);
    assume _module.__default.P8(LitInt(177));
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(288,3)
    assert {:subsumption 0} Map#Domain(c4#0)[$Box(Lit(true))];
    assume true;
    assert $Unbox(Map#Elements(c4#0)[$Box(Lit(true))]): int == LitInt(6);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(289,3)
    assume true;
    assert !Map#Domain(c4#0)[$Box(Lit(false))];
}



procedure CheckWellformed$$_module.__default.GeneralMaps8_k();
  free requires 50 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.GeneralMaps8_k();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.GeneralMaps8_k() returns ($_reverifyPost: bool);
  free requires 50 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



function map$project$16#0#x#0(bool) : int;

implementation Impl$$_module.__default.GeneralMaps8_k() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var c4#0: Map Box Box
     where $Is(c4#0, TMap(TBool, TInt)) && $IsAlloc(c4#0, TMap(TBool, TInt), $Heap);
  var x#0: int;
  var x#prime#0: int;
  var ##x#0: int;
  var ##x#1: int;

    // AddMethodImpl: GeneralMaps8', Impl$$_module.__default.GeneralMaps8_k
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(292,23): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(293,16)
    assume true;
    // Begin Comprehension WF check
    havoc x#0;
    if (true)
    {
        havoc x#prime#0;
        assume true;
        ##x#0 := x#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##x#0, TInt, $Heap);
        assume _module.__default.P8#canCall(x#0);
        if (_module.__default.P8(x#0))
        {
        }

        if (_module.__default.P8(x#0))
        {
        }

        if (_module.__default.P8(x#0) && _module.__default.P8(x#prime#0))
        {
            assert Lit(true) != Lit(true) || LitInt(6) == LitInt(6);
        }
    }

    // End Comprehension WF check
    assume (forall x#1: int :: 
      { _module.__default.P8(x#1) } 
      _module.__default.P8#canCall(x#1)
         && (forall a#0#0#0: int :: 
          { _module.__default.P8(a#0#0#0) } 
          _module.__default.P8(a#0#0#0)
             ==> _module.__default.P8(map$project$16#0#x#0(Lit(true))) && Lit(true) == Lit(true)));
    c4#0 := Map#Glue((lambda $w#0: Box :: 
        (exists a#1#0#0: int :: 
          _module.__default.P8(a#1#0#0) && $Unbox($w#0): bool == Lit(true))), 
      (lambda $w#0: Box :: $Box(LitInt(6))), 
      TMap(TBool, TInt));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(293,49)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(294,3)
    ##x#1 := LitInt(177);
    // assume allocatedness for argument to function
    assume $IsAlloc(##x#1, TInt, $Heap);
    assume _module.__default.P8#canCall(LitInt(177));
    assume _module.__default.P8#canCall(LitInt(177));
    assert {:subsumption 0} _module.__default.P8#canCall(LitInt(177))
       ==> Lit(_module.__default.P8(LitInt(177))) || Lit(true);
    assume _module.__default.P8(LitInt(177));
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(295,3)
    assert {:subsumption 0} Map#Domain(c4#0)[$Box(Lit(true))];
    assume true;
    assert $Unbox(Map#Elements(c4#0)[$Box(Lit(true))]): int == LitInt(6);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(296,3)
    assume true;
    assert !Map#Domain(c4#0)[$Box(Lit(false))];
}



procedure CheckWellformed$$_module.__default.GeneralMaps8_k_k();
  free requires 51 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.GeneralMaps8_k_k();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.GeneralMaps8_k_k() returns ($_reverifyPost: bool);
  free requires 51 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



function map$project$17#0#x#0(bool) : int;

implementation Impl$$_module.__default.GeneralMaps8_k_k() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var c4#0: Map Box Box
     where $Is(c4#0, TMap(TBool, TInt)) && $IsAlloc(c4#0, TMap(TBool, TInt), $Heap);
  var x#0: int;
  var x#prime#0: int;
  var ##x#0: int;

    // AddMethodImpl: GeneralMaps8'', Impl$$_module.__default.GeneralMaps8_k_k
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(299,24): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(300,16)
    assume true;
    // Begin Comprehension WF check
    havoc x#0;
    if (true)
    {
        havoc x#prime#0;
        assume true;
        if (LitInt(0) <= x#0)
        {
        }

        if (LitInt(0) <= x#0 && x#0 < 10)
        {
            ##x#0 := x#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##x#0, TInt, $Heap);
            assume _module.__default.Thirteen#canCall(x#0);
        }

        if (LitInt(0) <= x#0 && x#0 < 10 && _module.__default.Thirteen(x#0))
        {
        }

        if (LitInt(0) <= x#0 && x#0 < 10 && _module.__default.Thirteen(x#0))
        {
        }

        if (LitInt(0) <= x#0
           && x#0 < 10
           && _module.__default.Thirteen(x#0)
           && 
          LitInt(0) <= x#prime#0
           && x#prime#0 < 10
           && _module.__default.Thirteen(x#prime#0))
        {
            assert Lit(true) != Lit(true) || LitInt(6) == LitInt(6);
        }
    }

    // End Comprehension WF check
    assume (forall x#1: int :: 
      { _module.__default.Thirteen(x#1) } 
      (LitInt(0) <= x#1 && x#1 < 10 ==> _module.__default.Thirteen#canCall(x#1))
         && (forall a#0#0#0: int :: 
          { _module.__default.Thirteen(a#0#0#0) } 
          LitInt(0) <= a#0#0#0 && a#0#0#0 < 10 && _module.__default.Thirteen(a#0#0#0)
             ==> LitInt(0) <= map$project$17#0#x#0(Lit(true))
               && map$project$17#0#x#0(Lit(true)) < 10
               && _module.__default.Thirteen(map$project$17#0#x#0(Lit(true)))
               && Lit(true) == Lit(true)));
    c4#0 := Map#Glue((lambda $w#0: Box :: 
        (exists a#1#0#0: int :: 
          LitInt(0) <= a#1#0#0
             && a#1#0#0 < 10
             && _module.__default.Thirteen(a#1#0#0)
             && $Unbox($w#0): bool == Lit(true))), 
      (lambda $w#0: Box :: $Box(LitInt(6))), 
      TMap(TBool, TInt));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(300,70)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(301,3)
    assume true;
    assert Map#Equal(c4#0, Map#Empty(): Map Box Box);
}



procedure CheckWellformed$$_module.__default.UpdateValiditySeq();
  free requires 52 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.UpdateValiditySeq();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.UpdateValiditySeq() returns ($_reverifyPost: bool);
  free requires 52 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.UpdateValiditySeq() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var s#0: Seq Box
     where $Is(s#0, TSeq(Tclass._System.nat()))
       && $IsAlloc(s#0, TSeq(Tclass._System.nat()), $Heap);

    // AddMethodImpl: UpdateValiditySeq, Impl$$_module.__default.UpdateValiditySeq
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(306,27): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(307,19)
    assume true;
    assert $Is(LitInt(4), Tclass._System.nat());
    assert $Is(LitInt(4), Tclass._System.nat());
    assert $Is(LitInt(4), Tclass._System.nat());
    assert $Is(LitInt(4), Tclass._System.nat());
    assert $Is(LitInt(4), Tclass._System.nat());
    assume true;
    s#0 := Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(4))), $Box(LitInt(4))), 
            $Box(LitInt(4))), 
          $Box(LitInt(4))), 
        $Box(LitInt(4))));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(307,36)"} true;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(308,3)
    if (*)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(309,7)
        assume true;
        assert 0 <= LitInt(10) && LitInt(10) < Seq#Length(s#0);
        assert $Is(LitInt(4), Tclass._System.nat());
        assume true;
        s#0 := Seq#Update(s#0, LitInt(10), $Box(LitInt(4)));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(309,19)"} true;
    }
    else
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(311,7)
        assume true;
        assert 0 <= LitInt(1) && LitInt(1) < Seq#Length(s#0);
        assert $Is(LitInt(-5), Tclass._System.nat());
        assume true;
        s#0 := Seq#Update(s#0, LitInt(1), $Box(LitInt(-5)));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(311,19)"} true;
    }
}



procedure CheckWellformed$$_module.__default.UpdateValidityMultiset();
  free requires 53 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.UpdateValidityMultiset();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.UpdateValidityMultiset() returns ($_reverifyPost: bool);
  free requires 53 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.UpdateValidityMultiset() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var s#0: MultiSet Box
     where $Is(s#0, TMultiSet(Tclass._System.nat()))
       && $IsAlloc(s#0, TMultiSet(Tclass._System.nat()), $Heap);

    // AddMethodImpl: UpdateValidityMultiset, Impl$$_module.__default.UpdateValidityMultiset
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(314,32): initial state"} true;
    $_reverifyPost := false;
    havoc s#0 /* where $Is(s#0, TMultiSet(Tclass._System.nat()))
       && $IsAlloc(s#0, TMultiSet(Tclass._System.nat()), $Heap) */;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(316,3)
    if (*)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(317,7)
        assume true;
        assert $Is(LitInt(-2), Tclass._System.nat());
        assert 0 <= LitInt(5);
        assume true;
        s#0 := s#0[$Box(LitInt(-2)) := LitInt(5)];
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(317,19)"} true;
    }
    else
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(319,7)
        assume true;
        assert $Is(LitInt(2), Tclass._System.nat());
        assert 0 <= LitInt(-5);
        assume true;
        s#0 := s#0[$Box(LitInt(2)) := LitInt(-5)];
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(319,19)"} true;
    }
}



procedure CheckWellformed$$_module.__default.UpdateValidityMap(mm#0: Map Box Box
       where $Is(mm#0, TMap(TInt, TInt)) && $IsAlloc(mm#0, TMap(TInt, TInt), $Heap));
  free requires 54 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.UpdateValidityMap(mm#0: Map Box Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var k#0: int;
  var k#2: int;

    // AddMethodImpl: UpdateValidityMap, CheckWellformed$$_module.__default.UpdateValidityMap
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(322,7): initial state"} true;
    havoc k#0;
    assume true;
    if (*)
    {
        assume Map#Domain(mm#0)[$Box(k#0)];
        assume LitInt(0) <= k#0;
    }
    else
    {
        assume Map#Domain(mm#0)[$Box(k#0)] ==> LitInt(0) <= k#0;
    }

    assume (forall k#1: int :: 
      { Map#Domain(mm#0)[$Box(k#1)] } 
      true ==> Map#Domain(mm#0)[$Box(k#1)] ==> LitInt(0) <= k#1);
    havoc k#2;
    assume true;
    if (*)
    {
        assume Map#Domain(mm#0)[$Box(k#2)];
        assert Map#Domain(mm#0)[$Box(k#2)];
        assume LitInt(0) <= $Unbox(Map#Elements(mm#0)[$Box(k#2)]): int;
    }
    else
    {
        assume Map#Domain(mm#0)[$Box(k#2)]
           ==> LitInt(0) <= $Unbox(Map#Elements(mm#0)[$Box(k#2)]): int;
    }

    assume (forall k#3: int :: 
      { $Unbox(Map#Elements(mm#0)[$Box(k#3)]): int } { Map#Domain(mm#0)[$Box(k#3)] } 
      true
         ==> 
        Map#Domain(mm#0)[$Box(k#3)]
         ==> LitInt(0) <= $Unbox(Map#Elements(mm#0)[$Box(k#3)]): int);
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
    assume $HeapSucc(old($Heap), $Heap);
}



procedure Call$$_module.__default.UpdateValidityMap(mm#0: Map Box Box
       where $Is(mm#0, TMap(TInt, TInt)) && $IsAlloc(mm#0, TMap(TInt, TInt), $Heap));
  // user-defined preconditions
  requires (forall k#1: int :: 
    { Map#Domain(mm#0)[$Box(k#1)] } 
    true ==> Map#Domain(mm#0)[$Box(k#1)] ==> LitInt(0) <= k#1);
  requires (forall k#3: int :: 
    { $Unbox(Map#Elements(mm#0)[$Box(k#3)]): int } { Map#Domain(mm#0)[$Box(k#3)] } 
    true
       ==> 
      Map#Domain(mm#0)[$Box(k#3)]
       ==> LitInt(0) <= $Unbox(Map#Elements(mm#0)[$Box(k#3)]): int);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.UpdateValidityMap(mm#0: Map Box Box
       where $Is(mm#0, TMap(TInt, TInt)) && $IsAlloc(mm#0, TMap(TInt, TInt), $Heap))
   returns ($_reverifyPost: bool);
  free requires 54 == $FunctionContextHeight;
  // user-defined preconditions
  requires (forall k#1: int :: 
    { Map#Domain(mm#0)[$Box(k#1)] } 
    true ==> Map#Domain(mm#0)[$Box(k#1)] ==> LitInt(0) <= k#1);
  requires (forall k#3: int :: 
    { $Unbox(Map#Elements(mm#0)[$Box(k#3)]): int } { Map#Domain(mm#0)[$Box(k#3)] } 
    true
       ==> 
      Map#Domain(mm#0)[$Box(k#3)]
       ==> LitInt(0) <= $Unbox(Map#Elements(mm#0)[$Box(k#3)]): int);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.UpdateValidityMap(mm#0: Map Box Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var m#0: Map Box Box
     where $Is(m#0, TMap(Tclass._System.nat(), Tclass._System.nat()))
       && $IsAlloc(m#0, TMap(Tclass._System.nat(), Tclass._System.nat()), $Heap);

    // AddMethodImpl: UpdateValidityMap, Impl$$_module.__default.UpdateValidityMap
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(325,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(326,24)
    assume true;
    assume true;
    assert $Is(mm#0, TMap(Tclass._System.nat(), Tclass._System.nat()));
    m#0 := mm#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(326,28)"} true;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(327,3)
    if (*)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(328,7)
        assume true;
        assert $Is(LitInt(-2), Tclass._System.nat());
        assert $Is(LitInt(10), Tclass._System.nat());
        assume true;
        m#0 := Map#Build(m#0, $Box(LitInt(-2)), $Box(LitInt(10)));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(328,20)"} true;
    }
    else
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(330,7)
        assume true;
        assert $Is(LitInt(10), Tclass._System.nat());
        assert $Is(LitInt(-2), Tclass._System.nat());
        assume true;
        m#0 := Map#Build(m#0, $Box(LitInt(10)), $Box(LitInt(-2)));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(330,20)"} true;
    }
}



procedure CheckWellformed$$_module.__default.UpdateValiditySeqNull(d#0: ref
       where $Is(d#0, Tclass._module.Elem?()) && $IsAlloc(d#0, Tclass._module.Elem?(), $Heap), 
    e#0: ref
       where $Is(e#0, Tclass._module.Elem()) && $IsAlloc(e#0, Tclass._module.Elem(), $Heap));
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.UpdateValiditySeqNull(d#0: ref
       where $Is(d#0, Tclass._module.Elem?()) && $IsAlloc(d#0, Tclass._module.Elem?(), $Heap), 
    e#0: ref
       where $Is(e#0, Tclass._module.Elem()) && $IsAlloc(e#0, Tclass._module.Elem(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.UpdateValiditySeqNull(d#0: ref
       where $Is(d#0, Tclass._module.Elem?()) && $IsAlloc(d#0, Tclass._module.Elem?(), $Heap), 
    e#0: ref
       where $Is(e#0, Tclass._module.Elem()) && $IsAlloc(e#0, Tclass._module.Elem(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.UpdateValiditySeqNull(d#0: ref, e#0: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var s#0: Seq Box
     where $Is(s#0, TSeq(Tclass._module.Elem()))
       && $IsAlloc(s#0, TSeq(Tclass._module.Elem()), $Heap);

    // AddMethodImpl: UpdateValiditySeqNull, Impl$$_module.__default.UpdateValiditySeqNull
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(336,48): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(337,20)
    assume true;
    assume true;
    s#0 := Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(e#0)), $Box(e#0)), $Box(e#0)), 
        $Box(e#0)), 
      $Box(e#0));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(337,37)"} true;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(338,3)
    if (*)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(339,7)
        assume true;
        assert 0 <= LitInt(10) && LitInt(10) < Seq#Length(s#0);
        assume true;
        s#0 := Seq#Update(s#0, LitInt(10), $Box(e#0));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(339,19)"} true;
    }
    else
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(341,7)
        assume true;
        assert 0 <= LitInt(1) && LitInt(1) < Seq#Length(s#0);
        assert $Is(d#0, Tclass._module.Elem());
        assume true;
        s#0 := Seq#Update(s#0, LitInt(1), $Box(d#0));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(341,18)"} true;
    }
}



procedure CheckWellformed$$_module.__default.UpdateValidityMultisetNull(d#0: ref
       where $Is(d#0, Tclass._module.Elem?()) && $IsAlloc(d#0, Tclass._module.Elem?(), $Heap), 
    e#0: ref
       where $Is(e#0, Tclass._module.Elem()) && $IsAlloc(e#0, Tclass._module.Elem(), $Heap));
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.UpdateValidityMultisetNull(d#0: ref
       where $Is(d#0, Tclass._module.Elem?()) && $IsAlloc(d#0, Tclass._module.Elem?(), $Heap), 
    e#0: ref
       where $Is(e#0, Tclass._module.Elem()) && $IsAlloc(e#0, Tclass._module.Elem(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.UpdateValidityMultisetNull(d#0: ref
       where $Is(d#0, Tclass._module.Elem?()) && $IsAlloc(d#0, Tclass._module.Elem?(), $Heap), 
    e#0: ref
       where $Is(e#0, Tclass._module.Elem()) && $IsAlloc(e#0, Tclass._module.Elem(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.UpdateValidityMultisetNull(d#0: ref, e#0: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var s#0: MultiSet Box
     where $Is(s#0, TMultiSet(Tclass._module.Elem()))
       && $IsAlloc(s#0, TMultiSet(Tclass._module.Elem()), $Heap);

    // AddMethodImpl: UpdateValidityMultisetNull, Impl$$_module.__default.UpdateValidityMultisetNull
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(344,53): initial state"} true;
    $_reverifyPost := false;
    havoc s#0 /* where $Is(s#0, TMultiSet(Tclass._module.Elem()))
       && $IsAlloc(s#0, TMultiSet(Tclass._module.Elem()), $Heap) */;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(346,3)
    if (*)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(347,7)
        assume true;
        assert $Is(d#0, Tclass._module.Elem());
        assert 0 <= LitInt(5);
        assume true;
        s#0 := s#0[$Box(d#0) := LitInt(5)];
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(347,18)"} true;
    }
    else
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(349,7)
        assume true;
        assert 0 <= LitInt(-5);
        assume true;
        s#0 := s#0[$Box(e#0) := LitInt(-5)];
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(349,19)"} true;
    }
}



procedure CheckWellformed$$_module.__default.UpdateValidityMapNull(mm#0: Map Box Box
       where $Is(mm#0, TMap(Tclass._module.Elem?(), Tclass._module.Elem?()))
         && $IsAlloc(mm#0, TMap(Tclass._module.Elem?(), Tclass._module.Elem?()), $Heap), 
    d#0: ref
       where $Is(d#0, Tclass._module.Elem?()) && $IsAlloc(d#0, Tclass._module.Elem?(), $Heap), 
    e#0: ref
       where $Is(e#0, Tclass._module.Elem()) && $IsAlloc(e#0, Tclass._module.Elem(), $Heap));
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.UpdateValidityMapNull(mm#0: Map Box Box, d#0: ref, e#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var k#0: ref;
  var k#2: ref;

    // AddMethodImpl: UpdateValidityMapNull, CheckWellformed$$_module.__default.UpdateValidityMapNull
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(352,7): initial state"} true;
    havoc k#0;
    assume $Is(k#0, Tclass._module.Elem?());
    if (*)
    {
        assume Map#Domain(mm#0)[$Box(k#0)];
        assume k#0 != null;
    }
    else
    {
        assume Map#Domain(mm#0)[$Box(k#0)] ==> k#0 != null;
    }

    assume (forall k#1: ref :: 
      { Map#Domain(mm#0)[$Box(k#1)] } 
      $Is(k#1, Tclass._module.Elem?()) ==> Map#Domain(mm#0)[$Box(k#1)] ==> k#1 != null);
    havoc k#2;
    assume $Is(k#2, Tclass._module.Elem?());
    if (*)
    {
        assume Map#Domain(mm#0)[$Box(k#2)];
        assert Map#Domain(mm#0)[$Box(k#2)];
        assume $Unbox(Map#Elements(mm#0)[$Box(k#2)]): ref != null;
    }
    else
    {
        assume Map#Domain(mm#0)[$Box(k#2)]
           ==> $Unbox(Map#Elements(mm#0)[$Box(k#2)]): ref != null;
    }

    assume (forall k#3: ref :: 
      { $Unbox(Map#Elements(mm#0)[$Box(k#3)]): ref } { Map#Domain(mm#0)[$Box(k#3)] } 
      $Is(k#3, Tclass._module.Elem?())
         ==> 
        Map#Domain(mm#0)[$Box(k#3)]
         ==> $Unbox(Map#Elements(mm#0)[$Box(k#3)]): ref != null);
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
    assume $HeapSucc(old($Heap), $Heap);
}



procedure Call$$_module.__default.UpdateValidityMapNull(mm#0: Map Box Box
       where $Is(mm#0, TMap(Tclass._module.Elem?(), Tclass._module.Elem?()))
         && $IsAlloc(mm#0, TMap(Tclass._module.Elem?(), Tclass._module.Elem?()), $Heap), 
    d#0: ref
       where $Is(d#0, Tclass._module.Elem?()) && $IsAlloc(d#0, Tclass._module.Elem?(), $Heap), 
    e#0: ref
       where $Is(e#0, Tclass._module.Elem()) && $IsAlloc(e#0, Tclass._module.Elem(), $Heap));
  // user-defined preconditions
  requires (forall k#1: ref :: 
    { Map#Domain(mm#0)[$Box(k#1)] } 
    $Is(k#1, Tclass._module.Elem?()) ==> Map#Domain(mm#0)[$Box(k#1)] ==> k#1 != null);
  requires (forall k#3: ref :: 
    { $Unbox(Map#Elements(mm#0)[$Box(k#3)]): ref } { Map#Domain(mm#0)[$Box(k#3)] } 
    $Is(k#3, Tclass._module.Elem?())
       ==> 
      Map#Domain(mm#0)[$Box(k#3)]
       ==> $Unbox(Map#Elements(mm#0)[$Box(k#3)]): ref != null);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.UpdateValidityMapNull(mm#0: Map Box Box
       where $Is(mm#0, TMap(Tclass._module.Elem?(), Tclass._module.Elem?()))
         && $IsAlloc(mm#0, TMap(Tclass._module.Elem?(), Tclass._module.Elem?()), $Heap), 
    d#0: ref
       where $Is(d#0, Tclass._module.Elem?()) && $IsAlloc(d#0, Tclass._module.Elem?(), $Heap), 
    e#0: ref
       where $Is(e#0, Tclass._module.Elem()) && $IsAlloc(e#0, Tclass._module.Elem(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 5 == $FunctionContextHeight;
  // user-defined preconditions
  requires (forall k#1: ref :: 
    { Map#Domain(mm#0)[$Box(k#1)] } 
    $Is(k#1, Tclass._module.Elem?()) ==> Map#Domain(mm#0)[$Box(k#1)] ==> k#1 != null);
  requires (forall k#3: ref :: 
    { $Unbox(Map#Elements(mm#0)[$Box(k#3)]): ref } { Map#Domain(mm#0)[$Box(k#3)] } 
    $Is(k#3, Tclass._module.Elem?())
       ==> 
      Map#Domain(mm#0)[$Box(k#3)]
       ==> $Unbox(Map#Elements(mm#0)[$Box(k#3)]): ref != null);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.UpdateValidityMapNull(mm#0: Map Box Box, d#0: ref, e#0: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var m#0: Map Box Box
     where $Is(m#0, TMap(Tclass._module.Elem(), Tclass._module.Elem()))
       && $IsAlloc(m#0, TMap(Tclass._module.Elem(), Tclass._module.Elem()), $Heap);

    // AddMethodImpl: UpdateValidityMapNull, Impl$$_module.__default.UpdateValidityMapNull
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(355,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(356,26)
    assume true;
    assume true;
    assert $Is(mm#0, TMap(Tclass._module.Elem(), Tclass._module.Elem()));
    m#0 := mm#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(356,30)"} true;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(357,3)
    if (*)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(358,7)
        assume true;
        assert $Is(d#0, Tclass._module.Elem());
        assume true;
        m#0 := Map#Build(m#0, $Box(d#0), $Box(e#0));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(358,18)"} true;
    }
    else
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(360,7)
        assume true;
        assert $Is(d#0, Tclass._module.Elem());
        assume true;
        m#0 := Map#Build(m#0, $Box(e#0), $Box(d#0));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(360,18)"} true;
    }
}



procedure CheckWellformed$$_module.__default.TestMapSubtraction(m#0: Map Box Box
       where $Is(m#0, TMap(TInt, TReal)) && $IsAlloc(m#0, TMap(TInt, TReal), $Heap), 
    s#0: Set Box where $Is(s#0, TSet(TInt)) && $IsAlloc(s#0, TSet(TInt), $Heap), 
    x#0: int, 
    y#0: int);
  free requires 67 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.TestMapSubtraction(m#0: Map Box Box
       where $Is(m#0, TMap(TInt, TReal)) && $IsAlloc(m#0, TMap(TInt, TReal), $Heap), 
    s#0: Set Box where $Is(s#0, TSet(TInt)) && $IsAlloc(s#0, TSet(TInt), $Heap), 
    x#0: int, 
    y#0: int);
  // user-defined preconditions
  requires Map#Domain(m#0)[$Box(x#0)];
  requires s#0[$Box(x#0)];
  requires Map#Domain(m#0)[$Box(y#0)];
  requires !s#0[$Box(y#0)];
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.TestMapSubtraction(m#0: Map Box Box
       where $Is(m#0, TMap(TInt, TReal)) && $IsAlloc(m#0, TMap(TInt, TReal), $Heap), 
    s#0: Set Box where $Is(s#0, TSet(TInt)) && $IsAlloc(s#0, TSet(TInt), $Heap), 
    x#0: int, 
    y#0: int)
   returns ($_reverifyPost: bool);
  free requires 67 == $FunctionContextHeight;
  // user-defined preconditions
  requires Map#Domain(m#0)[$Box(x#0)];
  requires s#0[$Box(x#0)];
  requires Map#Domain(m#0)[$Box(y#0)];
  requires !s#0[$Box(y#0)];
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.TestMapSubtraction(m#0: Map Box Box, s#0: Set Box, x#0: int, y#0: int)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var xx#0: real;
  var yy#0: real;
  var $rhs#0: real;
  var $rhs#1: real;
  var m'#0: Map Box Box
     where $Is(m'#0, TMap(TInt, TReal)) && $IsAlloc(m'#0, TMap(TInt, TReal), $Heap);

    // AddMethodImpl: TestMapSubtraction, Impl$$_module.__default.TestMapSubtraction
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(369,0): initial state"} true;
    $_reverifyPost := false;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(370,14)
    assume true;
    assume true;
    assert Map#Domain(m#0)[$Box(x#0)];
    assume true;
    $rhs#0 := $Unbox(Map#Elements(m#0)[$Box(x#0)]): real;
    assert Map#Domain(m#0)[$Box(y#0)];
    assume true;
    $rhs#1 := $Unbox(Map#Elements(m#0)[$Box(y#0)]): real;
    xx#0 := $rhs#0;
    yy#0 := $rhs#1;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(370,26)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(371,10)
    assume true;
    assume true;
    m'#0 := Map#Subtract(m#0, s#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(371,17)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(372,3)
    assume true;
    assert !Map#Domain(m'#0)[$Box(x#0)];
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(373,3)
    assume true;
    assert Map#Domain(m'#0)[$Box(y#0)];
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(374,3)
    assert {:subsumption 0} Map#Domain(m'#0)[$Box(y#0)];
    assume true;
    assert $Unbox(Map#Elements(m'#0)[$Box(y#0)]): real == yy#0;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(375,3)
    assume true;
    assert Set#Subset(Map#Domain(m'#0), Map#Domain(m#0));
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(376,3)
    assume true;
    assert Set#Equal(Map#Domain(m'#0), Set#Difference(Map#Domain(m#0), s#0));
}



procedure CheckWellformed$$_module.__default.TestIMapSubtraction(m#0: IMap Box Box
       where $Is(m#0, TIMap(TInt, TReal)) && $IsAlloc(m#0, TIMap(TInt, TReal), $Heap), 
    s#0: Set Box where $Is(s#0, TSet(TInt)) && $IsAlloc(s#0, TSet(TInt), $Heap), 
    x#0: int, 
    y#0: int);
  free requires 68 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.TestIMapSubtraction(m#0: IMap Box Box
       where $Is(m#0, TIMap(TInt, TReal)) && $IsAlloc(m#0, TIMap(TInt, TReal), $Heap), 
    s#0: Set Box where $Is(s#0, TSet(TInt)) && $IsAlloc(s#0, TSet(TInt), $Heap), 
    x#0: int, 
    y#0: int);
  // user-defined preconditions
  requires IMap#Domain(m#0)[$Box(x#0)];
  requires s#0[$Box(x#0)];
  requires IMap#Domain(m#0)[$Box(y#0)];
  requires !s#0[$Box(y#0)];
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.TestIMapSubtraction(m#0: IMap Box Box
       where $Is(m#0, TIMap(TInt, TReal)) && $IsAlloc(m#0, TIMap(TInt, TReal), $Heap), 
    s#0: Set Box where $Is(s#0, TSet(TInt)) && $IsAlloc(s#0, TSet(TInt), $Heap), 
    x#0: int, 
    y#0: int)
   returns ($_reverifyPost: bool);
  free requires 68 == $FunctionContextHeight;
  // user-defined preconditions
  requires IMap#Domain(m#0)[$Box(x#0)];
  requires s#0[$Box(x#0)];
  requires IMap#Domain(m#0)[$Box(y#0)];
  requires !s#0[$Box(y#0)];
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.TestIMapSubtraction(m#0: IMap Box Box, s#0: Set Box, x#0: int, y#0: int)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var xx#0: real;
  var yy#0: real;
  var $rhs#0: real;
  var $rhs#1: real;
  var m'#0: IMap Box Box
     where $Is(m'#0, TIMap(TInt, TReal)) && $IsAlloc(m'#0, TIMap(TInt, TReal), $Heap);
  var u#0: int;

    // AddMethodImpl: TestIMapSubtraction, Impl$$_module.__default.TestIMapSubtraction
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(382,0): initial state"} true;
    $_reverifyPost := false;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(383,14)
    assume true;
    assume true;
    assert IMap#Domain(m#0)[$Box(x#0)];
    assume true;
    $rhs#0 := $Unbox(IMap#Elements(m#0)[$Box(x#0)]): real;
    assert IMap#Domain(m#0)[$Box(y#0)];
    assume true;
    $rhs#1 := $Unbox(IMap#Elements(m#0)[$Box(y#0)]): real;
    xx#0 := $rhs#0;
    yy#0 := $rhs#1;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(383,26)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(384,10)
    assume true;
    assume true;
    m'#0 := IMap#Subtract(m#0, s#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(384,17)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(385,3)
    assume true;
    assert !IMap#Domain(m'#0)[$Box(x#0)];
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(386,3)
    assume true;
    assert IMap#Domain(m'#0)[$Box(y#0)];
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(387,3)
    assert {:subsumption 0} IMap#Domain(m'#0)[$Box(y#0)];
    assume true;
    assert $Unbox(IMap#Elements(m'#0)[$Box(y#0)]): real == yy#0;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(388,3)
    assume true;
    assert ISet#Subset(IMap#Domain(m'#0), IMap#Domain(m#0));
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(389,3)
    // Begin Comprehension WF check
    havoc u#0;
    if (true)
    {
        if (s#0[$Box(u#0)])
        {
        }
    }

    // End Comprehension WF check
    assume true;
    assert ISet#Equal(IMap#Domain(m'#0), 
      ISet#Difference(IMap#Domain(m#0), (lambda $y#1: Box :: $IsBox($y#1, TInt) && s#0[$y#1])));
}



procedure CheckWellformed$$_module.__default.TestMapUnion(m0#0: Map Box Box
       where $Is(m0#0, TMap(TInt, TReal)) && $IsAlloc(m0#0, TMap(TInt, TReal), $Heap), 
    m1#0: Map Box Box
       where $Is(m1#0, TMap(TInt, TReal)) && $IsAlloc(m1#0, TMap(TInt, TReal), $Heap), 
    m2#0: Map Box Box
       where $Is(m2#0, TMap(TInt, TReal)) && $IsAlloc(m2#0, TMap(TInt, TReal), $Heap), 
    x#0: int, 
    y#0: int, 
    z#0: int);
  free requires 69 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.TestMapUnion(m0#0: Map Box Box
       where $Is(m0#0, TMap(TInt, TReal)) && $IsAlloc(m0#0, TMap(TInt, TReal), $Heap), 
    m1#0: Map Box Box
       where $Is(m1#0, TMap(TInt, TReal)) && $IsAlloc(m1#0, TMap(TInt, TReal), $Heap), 
    m2#0: Map Box Box
       where $Is(m2#0, TMap(TInt, TReal)) && $IsAlloc(m2#0, TMap(TInt, TReal), $Heap), 
    x#0: int, 
    y#0: int, 
    z#0: int);
  // user-defined preconditions
  requires Map#Domain(m0#0)[$Box(x#0)];
  requires Map#Domain(m1#0)[$Box(y#0)];
  requires Map#Domain(m2#0)[$Box(z#0)];
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.TestMapUnion(m0#0: Map Box Box
       where $Is(m0#0, TMap(TInt, TReal)) && $IsAlloc(m0#0, TMap(TInt, TReal), $Heap), 
    m1#0: Map Box Box
       where $Is(m1#0, TMap(TInt, TReal)) && $IsAlloc(m1#0, TMap(TInt, TReal), $Heap), 
    m2#0: Map Box Box
       where $Is(m2#0, TMap(TInt, TReal)) && $IsAlloc(m2#0, TMap(TInt, TReal), $Heap), 
    x#0: int, 
    y#0: int, 
    z#0: int)
   returns ($_reverifyPost: bool);
  free requires 69 == $FunctionContextHeight;
  // user-defined preconditions
  requires Map#Domain(m0#0)[$Box(x#0)];
  requires Map#Domain(m1#0)[$Box(y#0)];
  requires Map#Domain(m2#0)[$Box(z#0)];
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.TestMapUnion(m0#0: Map Box Box, 
    m1#0: Map Box Box, 
    m2#0: Map Box Box, 
    x#0: int, 
    y#0: int, 
    z#0: int)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var xx#0: real;
  var yy#0: real;
  var zz#0: real;
  var $rhs#0: real;
  var $rhs#1: real;
  var $rhs#2: real;
  var m#0: Map Box Box
     where $Is(m#0, TMap(TInt, TReal)) && $IsAlloc(m#0, TMap(TInt, TReal), $Heap);
  var u#0: int;

    // AddMethodImpl: TestMapUnion, Impl$$_module.__default.TestMapUnion
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(394,0): initial state"} true;
    $_reverifyPost := false;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(395,18)
    assume true;
    assume true;
    assume true;
    assert Map#Domain(m0#0)[$Box(x#0)];
    assume true;
    $rhs#0 := $Unbox(Map#Elements(m0#0)[$Box(x#0)]): real;
    assert Map#Domain(m1#0)[$Box(y#0)];
    assume true;
    $rhs#1 := $Unbox(Map#Elements(m1#0)[$Box(y#0)]): real;
    assert Map#Domain(m2#0)[$Box(z#0)];
    assume true;
    $rhs#2 := $Unbox(Map#Elements(m2#0)[$Box(z#0)]): real;
    xx#0 := $rhs#0;
    yy#0 := $rhs#1;
    zz#0 := $rhs#2;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(395,39)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(396,9)
    assume true;
    assume true;
    m#0 := Map#Merge(Map#Merge(m0#0, m1#0), m2#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(396,23)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(397,3)
    if (Map#Domain(m#0)[$Box(x#0)])
    {
    }

    if (Map#Domain(m#0)[$Box(x#0)] && Map#Domain(m#0)[$Box(y#0)])
    {
    }

    assume true;
    assert {:subsumption 0} Map#Domain(m#0)[$Box(x#0)];
    assert {:subsumption 0} Map#Domain(m#0)[$Box(y#0)];
    assert {:subsumption 0} Map#Domain(m#0)[$Box(z#0)];
    assume Map#Domain(m#0)[$Box(x#0)]
       && Map#Domain(m#0)[$Box(y#0)]
       && Map#Domain(m#0)[$Box(z#0)];
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(398,3)
    assert {:subsumption 0} Map#Domain(m#0)[$Box(x#0)];
    if ($Unbox(Map#Elements(m#0)[$Box(x#0)]): real != xx#0)
    {
    }

    if (!($Unbox(Map#Elements(m#0)[$Box(x#0)]): real == xx#0
       || Map#Domain(m1#0)[$Box(x#0)]))
    {
    }

    assume true;
    assert $Unbox(Map#Elements(m#0)[$Box(x#0)]): real == xx#0
       || Map#Domain(m1#0)[$Box(x#0)]
       || Map#Domain(m2#0)[$Box(x#0)];
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(399,3)
    assert {:subsumption 0} Map#Domain(m#0)[$Box(y#0)];
    if ($Unbox(Map#Elements(m#0)[$Box(y#0)]): real != yy#0)
    {
    }

    assume true;
    assert $Unbox(Map#Elements(m#0)[$Box(y#0)]): real == yy#0
       || Map#Domain(m2#0)[$Box(y#0)];
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(400,3)
    assert {:subsumption 0} Map#Domain(m#0)[$Box(z#0)];
    assume true;
    assert $Unbox(Map#Elements(m#0)[$Box(z#0)]): real == zz#0;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(401,3)
    // Begin Comprehension WF check
    havoc u#0;
    if (true)
    {
    }

    // End Comprehension WF check
    assume true;
    assert (forall u#1: int :: 
      { Map#Domain(m#0)[$Box(u#1)] } 
      true
         ==> (Map#Domain(m#0)[$Box(u#1)]
           <==> Map#Domain(m0#0)[$Box(u#1)]
             || Map#Domain(m1#0)[$Box(u#1)]
             || Map#Domain(m2#0)[$Box(u#1)]));
}



procedure CheckWellformed$$_module.__default.TestIMapUnion(m0#0: IMap Box Box
       where $Is(m0#0, TIMap(TInt, TReal)) && $IsAlloc(m0#0, TIMap(TInt, TReal), $Heap), 
    m1#0: IMap Box Box
       where $Is(m1#0, TIMap(TInt, TReal)) && $IsAlloc(m1#0, TIMap(TInt, TReal), $Heap), 
    m2#0: IMap Box Box
       where $Is(m2#0, TIMap(TInt, TReal)) && $IsAlloc(m2#0, TIMap(TInt, TReal), $Heap), 
    x#0: int, 
    y#0: int, 
    z#0: int);
  free requires 70 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.TestIMapUnion(m0#0: IMap Box Box
       where $Is(m0#0, TIMap(TInt, TReal)) && $IsAlloc(m0#0, TIMap(TInt, TReal), $Heap), 
    m1#0: IMap Box Box
       where $Is(m1#0, TIMap(TInt, TReal)) && $IsAlloc(m1#0, TIMap(TInt, TReal), $Heap), 
    m2#0: IMap Box Box
       where $Is(m2#0, TIMap(TInt, TReal)) && $IsAlloc(m2#0, TIMap(TInt, TReal), $Heap), 
    x#0: int, 
    y#0: int, 
    z#0: int);
  // user-defined preconditions
  requires IMap#Domain(m0#0)[$Box(x#0)];
  requires IMap#Domain(m1#0)[$Box(y#0)];
  requires IMap#Domain(m2#0)[$Box(z#0)];
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.TestIMapUnion(m0#0: IMap Box Box
       where $Is(m0#0, TIMap(TInt, TReal)) && $IsAlloc(m0#0, TIMap(TInt, TReal), $Heap), 
    m1#0: IMap Box Box
       where $Is(m1#0, TIMap(TInt, TReal)) && $IsAlloc(m1#0, TIMap(TInt, TReal), $Heap), 
    m2#0: IMap Box Box
       where $Is(m2#0, TIMap(TInt, TReal)) && $IsAlloc(m2#0, TIMap(TInt, TReal), $Heap), 
    x#0: int, 
    y#0: int, 
    z#0: int)
   returns ($_reverifyPost: bool);
  free requires 70 == $FunctionContextHeight;
  // user-defined preconditions
  requires IMap#Domain(m0#0)[$Box(x#0)];
  requires IMap#Domain(m1#0)[$Box(y#0)];
  requires IMap#Domain(m2#0)[$Box(z#0)];
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.TestIMapUnion(m0#0: IMap Box Box, 
    m1#0: IMap Box Box, 
    m2#0: IMap Box Box, 
    x#0: int, 
    y#0: int, 
    z#0: int)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var xx#0: real;
  var yy#0: real;
  var zz#0: real;
  var $rhs#0: real;
  var $rhs#1: real;
  var $rhs#2: real;
  var m#0: IMap Box Box
     where $Is(m#0, TIMap(TInt, TReal)) && $IsAlloc(m#0, TIMap(TInt, TReal), $Heap);
  var u#0: int;

    // AddMethodImpl: TestIMapUnion, Impl$$_module.__default.TestIMapUnion
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(406,0): initial state"} true;
    $_reverifyPost := false;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(407,18)
    assume true;
    assume true;
    assume true;
    assert IMap#Domain(m0#0)[$Box(x#0)];
    assume true;
    $rhs#0 := $Unbox(IMap#Elements(m0#0)[$Box(x#0)]): real;
    assert IMap#Domain(m1#0)[$Box(y#0)];
    assume true;
    $rhs#1 := $Unbox(IMap#Elements(m1#0)[$Box(y#0)]): real;
    assert IMap#Domain(m2#0)[$Box(z#0)];
    assume true;
    $rhs#2 := $Unbox(IMap#Elements(m2#0)[$Box(z#0)]): real;
    xx#0 := $rhs#0;
    yy#0 := $rhs#1;
    zz#0 := $rhs#2;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(407,39)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(408,9)
    assume true;
    assume true;
    m#0 := IMap#Merge(IMap#Merge(m0#0, m1#0), m2#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(408,23)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(409,3)
    if (IMap#Domain(m#0)[$Box(x#0)])
    {
    }

    if (IMap#Domain(m#0)[$Box(x#0)] && IMap#Domain(m#0)[$Box(y#0)])
    {
    }

    assume true;
    assert {:subsumption 0} IMap#Domain(m#0)[$Box(x#0)];
    assert {:subsumption 0} IMap#Domain(m#0)[$Box(y#0)];
    assert {:subsumption 0} IMap#Domain(m#0)[$Box(z#0)];
    assume IMap#Domain(m#0)[$Box(x#0)]
       && IMap#Domain(m#0)[$Box(y#0)]
       && IMap#Domain(m#0)[$Box(z#0)];
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(410,3)
    assert {:subsumption 0} IMap#Domain(m#0)[$Box(x#0)];
    if ($Unbox(IMap#Elements(m#0)[$Box(x#0)]): real != xx#0)
    {
    }

    if (!($Unbox(IMap#Elements(m#0)[$Box(x#0)]): real == xx#0
       || IMap#Domain(m1#0)[$Box(x#0)]))
    {
    }

    assume true;
    assert $Unbox(IMap#Elements(m#0)[$Box(x#0)]): real == xx#0
       || IMap#Domain(m1#0)[$Box(x#0)]
       || IMap#Domain(m2#0)[$Box(x#0)];
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(411,3)
    assert {:subsumption 0} IMap#Domain(m#0)[$Box(y#0)];
    if ($Unbox(IMap#Elements(m#0)[$Box(y#0)]): real != yy#0)
    {
    }

    assume true;
    assert $Unbox(IMap#Elements(m#0)[$Box(y#0)]): real == yy#0
       || IMap#Domain(m2#0)[$Box(y#0)];
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(412,3)
    assert {:subsumption 0} IMap#Domain(m#0)[$Box(z#0)];
    assume true;
    assert $Unbox(IMap#Elements(m#0)[$Box(z#0)]): real == zz#0;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(413,3)
    // Begin Comprehension WF check
    havoc u#0;
    if (true)
    {
    }

    // End Comprehension WF check
    assume true;
    assert (forall u#1: int :: 
      { IMap#Domain(m#0)[$Box(u#1)] } 
      true
         ==> (IMap#Domain(m#0)[$Box(u#1)]
           <==> IMap#Domain(m0#0)[$Box(u#1)]
             || IMap#Domain(m1#0)[$Box(u#1)]
             || IMap#Domain(m2#0)[$Box(u#1)]));
}



procedure CheckWellformed$$_module.__default.FailingMapOperations(m#0: Map Box Box
       where $Is(m#0, TMap(TInt, TReal)) && $IsAlloc(m#0, TMap(TInt, TReal), $Heap), 
    n#0: Map Box Box
       where $Is(n#0, TMap(TInt, TReal)) && $IsAlloc(n#0, TMap(TInt, TReal), $Heap), 
    s#0: Set Box where $Is(s#0, TSet(TInt)) && $IsAlloc(s#0, TSet(TInt), $Heap), 
    x#0: int, 
    y#0: int);
  free requires 71 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.FailingMapOperations(m#0: Map Box Box
       where $Is(m#0, TMap(TInt, TReal)) && $IsAlloc(m#0, TMap(TInt, TReal), $Heap), 
    n#0: Map Box Box
       where $Is(n#0, TMap(TInt, TReal)) && $IsAlloc(n#0, TMap(TInt, TReal), $Heap), 
    s#0: Set Box where $Is(s#0, TSet(TInt)) && $IsAlloc(s#0, TSet(TInt), $Heap), 
    x#0: int, 
    y#0: int);
  // user-defined preconditions
  requires Map#Domain(m#0)[$Box(x#0)];
  requires Map#Domain(n#0)[$Box(y#0)];
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.FailingMapOperations(m#0: Map Box Box
       where $Is(m#0, TMap(TInt, TReal)) && $IsAlloc(m#0, TMap(TInt, TReal), $Heap), 
    n#0: Map Box Box
       where $Is(n#0, TMap(TInt, TReal)) && $IsAlloc(n#0, TMap(TInt, TReal), $Heap), 
    s#0: Set Box where $Is(s#0, TSet(TInt)) && $IsAlloc(s#0, TSet(TInt), $Heap), 
    x#0: int, 
    y#0: int)
   returns ($_reverifyPost: bool);
  free requires 71 == $FunctionContextHeight;
  // user-defined preconditions
  requires Map#Domain(m#0)[$Box(x#0)];
  requires Map#Domain(n#0)[$Box(y#0)];
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.FailingMapOperations(m#0: Map Box Box, n#0: Map Box Box, s#0: Set Box, x#0: int, y#0: int)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var xx#0: real;
  var yy#0: real;
  var $rhs#0: real;
  var $rhs#1: real;
  var m'#0_0: Map Box Box
     where $Is(m'#0_0, TMap(TInt, TReal)) && $IsAlloc(m'#0_0, TMap(TInt, TReal), $Heap);
  var m'#0: Map Box Box
     where $Is(m'#0, TMap(TInt, TReal)) && $IsAlloc(m'#0, TMap(TInt, TReal), $Heap);

    // AddMethodImpl: FailingMapOperations, Impl$$_module.__default.FailingMapOperations
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(418,0): initial state"} true;
    $_reverifyPost := false;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(419,14)
    assume true;
    assume true;
    assert Map#Domain(m#0)[$Box(x#0)];
    assume true;
    $rhs#0 := $Unbox(Map#Elements(m#0)[$Box(x#0)]): real;
    assert Map#Domain(n#0)[$Box(y#0)];
    assume true;
    $rhs#1 := $Unbox(Map#Elements(n#0)[$Box(y#0)]): real;
    xx#0 := $rhs#0;
    yy#0 := $rhs#1;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(419,26)"} true;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(420,3)
    if (*)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(421,12)
        assume true;
        assume true;
        m'#0_0 := Map#Subtract(m#0, s#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(421,19)"} true;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(422,5)
        if (Map#Domain(m'#0_0)[$Box(x#0)])
        {
            assert {:subsumption 0} Map#Domain(m'#0_0)[$Box(x#0)];
        }

        assume true;
        assert {:subsumption 0} Map#Domain(m'#0_0)[$Box(x#0)]
           ==> $Unbox(Map#Elements(m'#0_0)[$Box(x#0)]): real == xx#0;
        assume Map#Domain(m'#0_0)[$Box(x#0)]
           ==> $Unbox(Map#Elements(m'#0_0)[$Box(x#0)]): real == xx#0;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(423,5)
        if (!Map#Domain(m'#0_0)[$Box(x#0)])
        {
        }

        assume true;
        assert {:subsumption 0} !Map#Domain(m'#0_0)[$Box(x#0)] ==> s#0[$Box(x#0)];
        assume !Map#Domain(m'#0_0)[$Box(x#0)] ==> s#0[$Box(x#0)];
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(424,5)
        assume true;
        assert Map#Domain(m'#0_0)[$Box(x#0)];
    }
    else
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(426,12)
        assume true;
        assume true;
        m'#0 := Map#Merge(m#0, n#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(426,19)"} true;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(427,5)
        assert {:subsumption 0} Map#Domain(m'#0)[$Box(y#0)];
        assert {:subsumption 0} Map#Domain(n#0)[$Box(y#0)];
        assume true;
        assert $Unbox(Map#Elements(m'#0)[$Box(y#0)]): real
           == $Unbox(Map#Elements(n#0)[$Box(y#0)]): real;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(428,5)
        if (!Map#Domain(n#0)[$Box(x#0)])
        {
            assert {:subsumption 0} Map#Domain(m'#0)[$Box(x#0)];
            assert {:subsumption 0} Map#Domain(m#0)[$Box(x#0)];
        }

        assume true;
        assert {:subsumption 0} !Map#Domain(n#0)[$Box(x#0)]
           ==> $Unbox(Map#Elements(m'#0)[$Box(x#0)]): real
             == $Unbox(Map#Elements(m#0)[$Box(x#0)]): real;
        assume !Map#Domain(n#0)[$Box(x#0)]
           ==> $Unbox(Map#Elements(m'#0)[$Box(x#0)]): real
             == $Unbox(Map#Elements(m#0)[$Box(x#0)]): real;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(429,5)
        assert {:subsumption 0} Map#Domain(m'#0)[$Box(x#0)];
        assert {:subsumption 0} Map#Domain(m#0)[$Box(x#0)];
        assume true;
        assert $Unbox(Map#Elements(m'#0)[$Box(x#0)]): real
           == $Unbox(Map#Elements(m#0)[$Box(x#0)]): real;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(430,5)
        assume true;
        assert Map#Domain(m#0)[$Box(y#0)];
    }
}



procedure CheckWellformed$$_module.__default.FailingIMapOperations(m#0: IMap Box Box
       where $Is(m#0, TIMap(TInt, TReal)) && $IsAlloc(m#0, TIMap(TInt, TReal), $Heap), 
    n#0: IMap Box Box
       where $Is(n#0, TIMap(TInt, TReal)) && $IsAlloc(n#0, TIMap(TInt, TReal), $Heap), 
    s#0: Set Box where $Is(s#0, TSet(TInt)) && $IsAlloc(s#0, TSet(TInt), $Heap), 
    x#0: int, 
    y#0: int);
  free requires 72 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.FailingIMapOperations(m#0: IMap Box Box
       where $Is(m#0, TIMap(TInt, TReal)) && $IsAlloc(m#0, TIMap(TInt, TReal), $Heap), 
    n#0: IMap Box Box
       where $Is(n#0, TIMap(TInt, TReal)) && $IsAlloc(n#0, TIMap(TInt, TReal), $Heap), 
    s#0: Set Box where $Is(s#0, TSet(TInt)) && $IsAlloc(s#0, TSet(TInt), $Heap), 
    x#0: int, 
    y#0: int);
  // user-defined preconditions
  requires IMap#Domain(m#0)[$Box(x#0)];
  requires IMap#Domain(n#0)[$Box(y#0)];
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.FailingIMapOperations(m#0: IMap Box Box
       where $Is(m#0, TIMap(TInt, TReal)) && $IsAlloc(m#0, TIMap(TInt, TReal), $Heap), 
    n#0: IMap Box Box
       where $Is(n#0, TIMap(TInt, TReal)) && $IsAlloc(n#0, TIMap(TInt, TReal), $Heap), 
    s#0: Set Box where $Is(s#0, TSet(TInt)) && $IsAlloc(s#0, TSet(TInt), $Heap), 
    x#0: int, 
    y#0: int)
   returns ($_reverifyPost: bool);
  free requires 72 == $FunctionContextHeight;
  // user-defined preconditions
  requires IMap#Domain(m#0)[$Box(x#0)];
  requires IMap#Domain(n#0)[$Box(y#0)];
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.FailingIMapOperations(m#0: IMap Box Box, n#0: IMap Box Box, s#0: Set Box, x#0: int, y#0: int)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var xx#0: real;
  var yy#0: real;
  var $rhs#0: real;
  var $rhs#1: real;
  var m'#0_0: IMap Box Box
     where $Is(m'#0_0, TIMap(TInt, TReal)) && $IsAlloc(m'#0_0, TIMap(TInt, TReal), $Heap);
  var m'#0: IMap Box Box
     where $Is(m'#0, TIMap(TInt, TReal)) && $IsAlloc(m'#0, TIMap(TInt, TReal), $Heap);

    // AddMethodImpl: FailingIMapOperations, Impl$$_module.__default.FailingIMapOperations
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(436,0): initial state"} true;
    $_reverifyPost := false;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(437,14)
    assume true;
    assume true;
    assert IMap#Domain(m#0)[$Box(x#0)];
    assume true;
    $rhs#0 := $Unbox(IMap#Elements(m#0)[$Box(x#0)]): real;
    assert IMap#Domain(n#0)[$Box(y#0)];
    assume true;
    $rhs#1 := $Unbox(IMap#Elements(n#0)[$Box(y#0)]): real;
    xx#0 := $rhs#0;
    yy#0 := $rhs#1;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(437,26)"} true;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(438,3)
    if (*)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(439,12)
        assume true;
        assume true;
        m'#0_0 := IMap#Subtract(m#0, s#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(439,19)"} true;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(440,5)
        if (IMap#Domain(m'#0_0)[$Box(x#0)])
        {
            assert {:subsumption 0} IMap#Domain(m'#0_0)[$Box(x#0)];
        }

        assume true;
        assert {:subsumption 0} IMap#Domain(m'#0_0)[$Box(x#0)]
           ==> $Unbox(IMap#Elements(m'#0_0)[$Box(x#0)]): real == xx#0;
        assume IMap#Domain(m'#0_0)[$Box(x#0)]
           ==> $Unbox(IMap#Elements(m'#0_0)[$Box(x#0)]): real == xx#0;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(441,5)
        if (!IMap#Domain(m'#0_0)[$Box(x#0)])
        {
        }

        assume true;
        assert {:subsumption 0} !IMap#Domain(m'#0_0)[$Box(x#0)] ==> s#0[$Box(x#0)];
        assume !IMap#Domain(m'#0_0)[$Box(x#0)] ==> s#0[$Box(x#0)];
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(442,5)
        assume true;
        assert IMap#Domain(m'#0_0)[$Box(x#0)];
    }
    else
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(444,12)
        assume true;
        assume true;
        m'#0 := IMap#Merge(m#0, n#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(444,19)"} true;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(445,5)
        assert {:subsumption 0} IMap#Domain(m'#0)[$Box(y#0)];
        assert {:subsumption 0} IMap#Domain(n#0)[$Box(y#0)];
        assume true;
        assert $Unbox(IMap#Elements(m'#0)[$Box(y#0)]): real
           == $Unbox(IMap#Elements(n#0)[$Box(y#0)]): real;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(446,5)
        if (!IMap#Domain(n#0)[$Box(x#0)])
        {
            assert {:subsumption 0} IMap#Domain(m'#0)[$Box(x#0)];
            assert {:subsumption 0} IMap#Domain(m#0)[$Box(x#0)];
        }

        assume true;
        assert {:subsumption 0} !IMap#Domain(n#0)[$Box(x#0)]
           ==> $Unbox(IMap#Elements(m'#0)[$Box(x#0)]): real
             == $Unbox(IMap#Elements(m#0)[$Box(x#0)]): real;
        assume !IMap#Domain(n#0)[$Box(x#0)]
           ==> $Unbox(IMap#Elements(m'#0)[$Box(x#0)]): real
             == $Unbox(IMap#Elements(m#0)[$Box(x#0)]): real;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(447,5)
        assert {:subsumption 0} IMap#Domain(m'#0)[$Box(x#0)];
        assert {:subsumption 0} IMap#Domain(m#0)[$Box(x#0)];
        assume true;
        assert $Unbox(IMap#Elements(m'#0)[$Box(x#0)]): real
           == $Unbox(IMap#Elements(m#0)[$Box(x#0)]): real;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(448,5)
        assume true;
        assert IMap#Domain(m#0)[$Box(y#0)];
    }
}



procedure CheckWellformed$$_module.__default.CommonUseCase0(m#0: Map Box Box
       where $Is(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)), $Heap))
   returns (s#0: int where LitInt(0) <= s#0);
  free requires 9 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.CommonUseCase0(m#0: Map Box Box
       where $Is(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)), $Heap))
   returns (s#0: int where LitInt(0) <= s#0);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.CommonUseCase0(m#0: Map Box Box
       where $Is(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)), $Heap))
   returns (s#0: int where LitInt(0) <= s#0, $_reverifyPost: bool);
  free requires 9 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.CommonUseCase0(m#0: Map Box Box) returns (s#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var m#1: Map Box Box
     where $Is(m#1, TMap(Tclass._module.MyClass(), TBitvector(3)))
       && $IsAlloc(m#1, TMap(Tclass._module.MyClass(), TBitvector(3)), $Heap);
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: Set Box;
  var $w$loop#0: bool;
  var $decr$loop#00: Set Box;
  var defass#k#0_0: bool;
  var k#0_0: ref
     where defass#k#0_0
       ==> $Is(k#0_0, Tclass._module.MyClass())
         && $IsAlloc(k#0_0, Tclass._module.MyClass(), $Heap);
  var k#0_1: ref;
  var v#0_0: bv3;

    // AddMethodImpl: CommonUseCase0, Impl$$_module.__default.CommonUseCase0
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(456,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(457,5)
    assume true;
    assume true;
    assert $Is(LitInt(0), Tclass._System.nat());
    s#0 := LitInt(0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(457,8)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(458,9)
    assume true;
    assume true;
    m#1 := m#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(458,12)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(459,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := Map#Domain(m#1);
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
      free invariant Set#Subset(Map#Domain(m#1), $decr_init$loop#00)
         && (Set#Equal(Map#Domain(m#1), $decr_init$loop#00) ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(459,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assume true;
            assume false;
        }

        assume true;
        if (Map#Equal(m#1, Map#Empty(): Map Box Box))
        {
            break;
        }

        $decr$loop#00 := Map#Domain(m#1);
        // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(462,11)
        havoc k#0_1;
        if ($Is(k#0_1, Tclass._module.MyClass())
           && $IsAlloc(k#0_1, Tclass._module.MyClass(), $Heap))
        {
            assume true;
        }

        assert ($Is(null, Tclass._module.MyClass()) && Map#Domain(m#1)[$Box(null)])
           || (exists $as#k0_0#0_0: ref :: 
            $Is($as#k0_0#0_0, Tclass._module.MyClass())
               && Map#Domain(m#1)[$Box($as#k0_0#0_0)]);
        defass#k#0_0 := true;
        havoc k#0_0;
        assume Map#Domain(m#1)[$Box(k#0_0)];
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(462,24)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(463,11)
        assume true;
        assert defass#k#0_0;
        assert Map#Domain(m#1)[$Box(k#0_0)];
        assume true;
        v#0_0 := $Unbox(Map#Elements(m#1)[$Box(k#0_0)]): bv3;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(463,17)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(464,7)
        assume true;
        assume true;
        assert $Is(s#0 + nat_from_bv3(v#0_0), Tclass._System.nat());
        s#0 := s#0 + nat_from_bv3(v#0_0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(464,21)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(465,7)
        assume true;
        assert defass#k#0_0;
        assume true;
        m#1 := Map#Subtract(m#1, Set#UnionOne(Set#Empty(): Set Box, $Box(k#0_0)));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(465,16)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(459,3)
        assert Set#Subset(Map#Domain(m#1), $decr$loop#00)
           && !Set#Subset($decr$loop#00, Map#Domain(m#1));
    }
}



procedure CheckWellformed$$_module.__default.CommonUseCase1(m#0: Map Box Box
       where $Is(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)), $Heap))
   returns (s#0: int where LitInt(0) <= s#0);
  free requires 10 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.CommonUseCase1(m#0: Map Box Box
       where $Is(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)), $Heap))
   returns (s#0: int where LitInt(0) <= s#0);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.CommonUseCase1(m#0: Map Box Box
       where $Is(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)), $Heap))
   returns (s#0: int where LitInt(0) <= s#0, $_reverifyPost: bool);
  free requires 10 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.CommonUseCase1(m#0: Map Box Box) returns (s#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var m#1: Map Box Box
     where $Is(m#1, TMap(Tclass._module.MyClass(), TBitvector(3)))
       && $IsAlloc(m#1, TMap(Tclass._module.MyClass(), TBitvector(3)), $Heap);
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: Set Box;
  var $w$loop#0: bool;
  var $decr$loop#00: Set Box;
  var defass#kv#0_0: bool;
  var kv#0_0: DatatypeType
     where defass#kv#0_0
       ==> $Is(kv#0_0, Tclass._System.Tuple2(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(kv#0_0, Tclass._System.Tuple2(Tclass._module.MyClass(), TBitvector(3)), $Heap);
  var kv#0_1: DatatypeType;
  var k#0_0: ref;
  var v#0_0: bv3;
  var let#0_0#0#0: DatatypeType;

    // AddMethodImpl: CommonUseCase1, Impl$$_module.__default.CommonUseCase1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(470,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(471,5)
    assume true;
    assume true;
    assert $Is(LitInt(0), Tclass._System.nat());
    s#0 := LitInt(0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(471,8)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(472,9)
    assume true;
    assume true;
    m#1 := m#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(472,12)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(473,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := Map#Domain(m#1);
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
      free invariant Set#Subset(Map#Domain(m#1), $decr_init$loop#00)
         && (Set#Equal(Map#Domain(m#1), $decr_init$loop#00) ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(473,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assume true;
            assume false;
        }

        assume true;
        if (Map#Equal(m#1, Map#Empty(): Map Box Box))
        {
            break;
        }

        $decr$loop#00 := Map#Domain(m#1);
        // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(476,12)
        havoc kv#0_1;
        if ($Is(kv#0_1, Tclass._System.Tuple2(Tclass._module.MyClass(), TBitvector(3)))
           && $IsAlloc(kv#0_1, Tclass._System.Tuple2(Tclass._module.MyClass(), TBitvector(3)), $Heap))
        {
            assume true;
        }

        assert (exists $as#kv0_0#0_0: DatatypeType :: 
          $Is($as#kv0_0#0_0, Tclass._System.Tuple2(Tclass._module.MyClass(), TBitvector(3)))
             && Map#Items(m#1)[$Box($as#kv0_0#0_0)]);
        defass#kv#0_0 := true;
        havoc kv#0_0;
        assume Map#Items(m#1)[$Box(kv#0_0)];
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(476,27)"} true;
        havoc k#0_0;
        assume $Is(k#0_0, Tclass._module.MyClass())
           && $IsAlloc(k#0_0, Tclass._module.MyClass(), $Heap);
        havoc v#0_0;
        assert defass#kv#0_0;
        assume let#0_0#0#0 == kv#0_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_0#0#0, Tclass._System.Tuple2(Tclass._module.MyClass(), TBitvector(3)));
        assume _System.Tuple2.___hMake2_q(let#0_0#0#0);
        assume #_System._tuple#2._#Make2($Box(k#0_0), $Box(v#0_0)) == let#0_0#0#0;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(478,7)
        assume true;
        assume true;
        assert $Is(s#0 + nat_from_bv3(v#0_0), Tclass._System.nat());
        s#0 := s#0 + nat_from_bv3(v#0_0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(478,21)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(479,7)
        assume true;
        assume true;
        m#1 := Map#Subtract(m#1, Set#UnionOne(Set#Empty(): Set Box, $Box(k#0_0)));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(479,16)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(473,3)
        assert Set#Subset(Map#Domain(m#1), $decr$loop#00)
           && !Set#Subset($decr$loop#00, Map#Domain(m#1));
    }
}



procedure CheckWellformed$$_module.__default.CommonUseCase2(m#0: Map Box Box
       where $Is(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)), $Heap))
   returns (s#0: int where LitInt(0) <= s#0);
  free requires 11 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.CommonUseCase2(m#0: Map Box Box
       where $Is(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)), $Heap))
   returns (s#0: int where LitInt(0) <= s#0);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.CommonUseCase2(m#0: Map Box Box
       where $Is(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)), $Heap))
   returns (s#0: int where LitInt(0) <= s#0, $_reverifyPost: bool);
  free requires 11 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.CommonUseCase2(m#0: Map Box Box) returns (s#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var m#1: Map Box Box
     where $Is(m#1, TMap(Tclass._module.MyClass(), TBitvector(3)))
       && $IsAlloc(m#1, TMap(Tclass._module.MyClass(), TBitvector(3)), $Heap);
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: Set Box;
  var $w$loop#0: bool;
  var $decr$loop#00: Set Box;
  var defass#k#0_0: bool;
  var k#0_0: ref
     where defass#k#0_0
       ==> $Is(k#0_0, Tclass._module.MyClass())
         && $IsAlloc(k#0_0, Tclass._module.MyClass(), $Heap);
  var v#0_0: bv3;
  var k#0_1: ref;
  var v#0_1: bv3;

    // AddMethodImpl: CommonUseCase2, Impl$$_module.__default.CommonUseCase2
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(484,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(485,5)
    assume true;
    assume true;
    assert $Is(LitInt(0), Tclass._System.nat());
    s#0 := LitInt(0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(485,8)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(486,9)
    assume true;
    assume true;
    m#1 := m#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(486,12)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(487,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := Map#Domain(m#1);
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
      free invariant Set#Subset(Map#Domain(m#1), $decr_init$loop#00)
         && (Set#Equal(Map#Domain(m#1), $decr_init$loop#00) ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(487,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assume true;
            assume false;
        }

        assume true;
        if (Map#Equal(m#1, Map#Empty(): Map Box Box))
        {
            break;
        }

        $decr$loop#00 := Map#Domain(m#1);
        // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(490,14)
        havoc k#0_1;
        havoc v#0_1;
        if ($Is(k#0_1, Tclass._module.MyClass())
           && $IsAlloc(k#0_1, Tclass._module.MyClass(), $Heap))
        {
            assume true;
        }

        assert (exists $as#v0_0#0_0: bv3 :: 
            $Is(null, Tclass._module.MyClass())
               && Map#Items(m#1)[$Box(#_System._tuple#2._#Make2($Box(null), $Box($as#v0_0#0_0)))])
           || (exists $as#k0_0#0_0: ref, $as#v0_0#0_0: bv3 :: 
            $Is($as#k0_0#0_0, Tclass._module.MyClass())
               && Map#Items(m#1)[$Box(#_System._tuple#2._#Make2($Box($as#k0_0#0_0), $Box($as#v0_0#0_0)))]);
        defass#k#0_0 := true;
        havoc k#0_0, v#0_0;
        assume Map#Items(m#1)[$Box(#_System._tuple#2._#Make2($Box(k#0_0), $Box(v#0_0)))];
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(490,33)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(491,7)
        assume true;
        assume true;
        assert $Is(s#0 + nat_from_bv3(v#0_0), Tclass._System.nat());
        s#0 := s#0 + nat_from_bv3(v#0_0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(491,21)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(492,7)
        assume true;
        assert defass#k#0_0;
        assume true;
        m#1 := Map#Subtract(m#1, Set#UnionOne(Set#Empty(): Set Box, $Box(k#0_0)));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(492,16)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(487,3)
        assert Set#Subset(Map#Domain(m#1), $decr$loop#00)
           && !Set#Subset($decr$loop#00, Map#Domain(m#1));
    }
}



procedure CheckWellformed$$_module.__default.TestMapPropertyNonempty(m#0: Map Box Box
       where $Is(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)), $Heap));
  free requires 12 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.TestMapPropertyNonempty(m#0: Map Box Box
       where $Is(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)), $Heap));
  // user-defined preconditions
  requires !Map#Equal(m#0, Map#Empty(): Map Box Box);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.TestMapPropertyNonempty(m#0: Map Box Box
       where $Is(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)), $Heap))
   returns ($_reverifyPost: bool);
  free requires 12 == $FunctionContextHeight;
  // user-defined preconditions
  requires !Map#Equal(m#0, Map#Empty(): Map Box Box);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.TestMapPropertyNonempty(m#0: Map Box Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: TestMapPropertyNonempty, Impl$$_module.__default.TestMapPropertyNonempty
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(502,0): initial state"} true;
    $_reverifyPost := false;
    // ----- alternative statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(503,3)
    if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(505,5)
        assume true;
        assert Map#Card(m#0) != 0;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(507,5)
        assume true;
        assert !Set#Equal(Map#Domain(m#0), Set#Empty(): Set Box);
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(509,5)
        assume true;
        assert !Set#Equal(Map#Values(m#0), Set#Empty(): Set Box);
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(511,5)
        assume true;
        assert !Set#Equal(Map#Items(m#0), Set#Empty(): Set Box);
    }
    else
    {
        assume true;
        assume true;
        assume true;
        assume true;
        assume !Lit(true) && !Lit(true) && !Lit(true) && !Lit(true);
        assert false;
    }
}



procedure CheckWellformed$$_module.__default.TestMapPropertyCardinality0(m#0: Map Box Box
       where $Is(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)), $Heap));
  free requires 13 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.TestMapPropertyCardinality0(m#0: Map Box Box
       where $Is(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.TestMapPropertyCardinality0(m#0: Map Box Box
       where $Is(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)), $Heap))
   returns ($_reverifyPost: bool);
  free requires 13 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.TestMapPropertyCardinality0(m#0: Map Box Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: TestMapPropertyCardinality0, Impl$$_module.__default.TestMapPropertyCardinality0
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(514,59): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(515,3)
    assume true;
    assert Map#Card(m#0) == Set#Card(Map#Domain(m#0));
}



procedure CheckWellformed$$_module.__default.TestMapPropertyCardinality1(m#0: Map Box Box
       where $Is(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)), $Heap));
  free requires 14 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.TestMapPropertyCardinality1(m#0: Map Box Box
       where $Is(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.TestMapPropertyCardinality1(m#0: Map Box Box
       where $Is(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)), $Heap))
   returns ($_reverifyPost: bool);
  free requires 14 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.TestMapPropertyCardinality1(m#0: Map Box Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: TestMapPropertyCardinality1, Impl$$_module.__default.TestMapPropertyCardinality1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(518,59): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(519,3)
    assume true;
    assert Set#Card(Map#Values(m#0)) <= Set#Card(Map#Domain(m#0));
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(520,3)
    assume true;
    assert Set#Card(Map#Domain(m#0)) == Set#Card(Map#Values(m#0));
}



procedure CheckWellformed$$_module.__default.TestMapPropertyCardinality2(m#0: Map Box Box
       where $Is(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)), $Heap));
  free requires 15 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.TestMapPropertyCardinality2(m#0: Map Box Box
       where $Is(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.TestMapPropertyCardinality2(m#0: Map Box Box
       where $Is(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)), $Heap))
   returns ($_reverifyPost: bool);
  free requires 15 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.TestMapPropertyCardinality2(m#0: Map Box Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: TestMapPropertyCardinality2, Impl$$_module.__default.TestMapPropertyCardinality2
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(523,59): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(524,3)
    assume true;
    assert Set#Card(Map#Values(m#0)) <= Set#Card(Map#Items(m#0));
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(525,3)
    assume true;
    assert Set#Card(Map#Values(m#0)) == Set#Card(Map#Items(m#0));
}



procedure CheckWellformed$$_module.__default.TestMapPropertyCardinality3(m#0: Map Box Box
       where $Is(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)), $Heap));
  free requires 16 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.TestMapPropertyCardinality3(m#0: Map Box Box
       where $Is(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.TestMapPropertyCardinality3(m#0: Map Box Box
       where $Is(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)), $Heap))
   returns ($_reverifyPost: bool);
  free requires 16 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.TestMapPropertyCardinality3(m#0: Map Box Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: TestMapPropertyCardinality3, Impl$$_module.__default.TestMapPropertyCardinality3
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(528,59): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(529,3)
    assume true;
    assert Set#Card(Map#Items(m#0)) == Map#Card(m#0);
}



procedure CheckWellformed$$_module.__default.TestMapPropertyMembership0(m#0: Map Box Box
       where $Is(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)), $Heap));
  free requires 17 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.TestMapPropertyMembership0(m#0: Map Box Box
       where $Is(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)), $Heap));
  // user-defined preconditions
  requires Set#Card(Map#Values(m#0)) != 0 || Set#Card(Map#Items(m#0)) != 0;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.TestMapPropertyMembership0(m#0: Map Box Box
       where $Is(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)), $Heap))
   returns ($_reverifyPost: bool);
  free requires 17 == $FunctionContextHeight;
  // user-defined preconditions
  requires Set#Card(Map#Values(m#0)) != 0 || Set#Card(Map#Items(m#0)) != 0;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.TestMapPropertyMembership0(m#0: Map Box Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var k#0: ref;

    // AddMethodImpl: TestMapPropertyMembership0, Impl$$_module.__default.TestMapPropertyMembership0
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(534,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(535,3)
    // Begin Comprehension WF check
    havoc k#0;
    if ($Is(k#0, Tclass._module.MyClass()))
    {
    }

    // End Comprehension WF check
    assume true;
    assert (exists k#1: ref :: 
      { Map#Domain(m#0)[$Box(k#1)] } 
      $Is(k#1, Tclass._module.MyClass()) && Map#Domain(m#0)[$Box(k#1)]);
}



procedure CheckWellformed$$_module.__default.TestMapPropertyMembership1(m#0: Map Box Box
       where $Is(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)), $Heap));
  free requires 18 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.TestMapPropertyMembership1(m#0: Map Box Box
       where $Is(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)), $Heap));
  // user-defined preconditions
  requires Set#Card(Map#Items(m#0)) != 0 || Set#Card(Map#Domain(m#0)) != 0;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.TestMapPropertyMembership1(m#0: Map Box Box
       where $Is(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)), $Heap))
   returns ($_reverifyPost: bool);
  free requires 18 == $FunctionContextHeight;
  // user-defined preconditions
  requires Set#Card(Map#Items(m#0)) != 0 || Set#Card(Map#Domain(m#0)) != 0;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.TestMapPropertyMembership1(m#0: Map Box Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var v#0: bv3;

    // AddMethodImpl: TestMapPropertyMembership1, Impl$$_module.__default.TestMapPropertyMembership1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(540,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(540,2)
    assume true;
    assert !Set#Equal(Map#Values(m#0), Set#Empty(): Set Box);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(541,3)
    // Begin Comprehension WF check
    havoc v#0;
    if (true)
    {
    }

    // End Comprehension WF check
    assume true;
    assert (exists v#1: bv3 :: { Map#Values(m#0)[$Box(v#1)] } Map#Values(m#0)[$Box(v#1)]);
}



procedure CheckWellformed$$_module.__default.TestMapPropertyMembership2(m#0: Map Box Box
       where $Is(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)), $Heap));
  free requires 19 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.TestMapPropertyMembership2(m#0: Map Box Box
       where $Is(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)), $Heap));
  // user-defined preconditions
  requires Set#Card(Map#Domain(m#0)) != 0 || Set#Card(Map#Values(m#0)) != 0;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.TestMapPropertyMembership2(m#0: Map Box Box
       where $Is(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)), $Heap))
   returns ($_reverifyPost: bool);
  free requires 19 == $FunctionContextHeight;
  // user-defined preconditions
  requires Set#Card(Map#Domain(m#0)) != 0 || Set#Card(Map#Values(m#0)) != 0;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.TestMapPropertyMembership2(m#0: Map Box Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var kv#0: DatatypeType;

    // AddMethodImpl: TestMapPropertyMembership2, Impl$$_module.__default.TestMapPropertyMembership2
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(546,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(547,3)
    // Begin Comprehension WF check
    havoc kv#0;
    if ($Is(kv#0, Tclass._System.Tuple2(Tclass._module.MyClass(), TBitvector(3))))
    {
    }

    // End Comprehension WF check
    assume true;
    assert (exists kv#1: DatatypeType :: 
      { Map#Items(m#0)[$Box(kv#1)] } 
      $Is(kv#1, Tclass._System.Tuple2(Tclass._module.MyClass(), TBitvector(3)))
         && Map#Items(m#0)[$Box(kv#1)]);
}



procedure CheckWellformed$$_module.__default.TestMapPropertyMembership3(m#0: Map Box Box
       where $Is(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)), $Heap));
  free requires 20 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.TestMapPropertyMembership3(m#0: Map Box Box
       where $Is(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)), $Heap));
  // user-defined preconditions
  requires Set#Card(Map#Domain(m#0)) != 0 || Set#Card(Map#Values(m#0)) != 0;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.TestMapPropertyMembership3(m#0: Map Box Box
       where $Is(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TMap(Tclass._module.MyClass(), TBitvector(3)), $Heap))
   returns ($_reverifyPost: bool);
  free requires 20 == $FunctionContextHeight;
  // user-defined preconditions
  requires Set#Card(Map#Domain(m#0)) != 0 || Set#Card(Map#Values(m#0)) != 0;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.TestMapPropertyMembership3(m#0: Map Box Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var v#0: bv3;
  var k#0: ref;

    // AddMethodImpl: TestMapPropertyMembership3, Impl$$_module.__default.TestMapPropertyMembership3
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(552,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(553,3)
    // Begin Comprehension WF check
    havoc v#0;
    havoc k#0;
    if ($Is(k#0, Tclass._module.MyClass()))
    {
    }

    // End Comprehension WF check
    assume true;
    assert (exists v#1: bv3, k#1: ref :: 
      { #_System._tuple#2._#Make2($Box(k#1), $Box(v#1)) } 
      $Is(k#1, Tclass._module.MyClass())
         && Map#Items(m#0)[$Box(#_System._tuple#2._#Make2($Box(k#1), $Box(v#1)))]);
}



procedure CheckWellformed$$_module.__default.IMapCommonUseCase0(m#0: IMap Box Box
       where $Is(m#0, TIMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TIMap(Tclass._module.MyClass(), TBitvector(3)), $Heap))
   returns (s#0: int where LitInt(0) <= s#0);
  free requires 21 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.IMapCommonUseCase0(m#0: IMap Box Box
       where $Is(m#0, TIMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TIMap(Tclass._module.MyClass(), TBitvector(3)), $Heap))
   returns (s#0: int where LitInt(0) <= s#0);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.IMapCommonUseCase0(m#0: IMap Box Box
       where $Is(m#0, TIMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TIMap(Tclass._module.MyClass(), TBitvector(3)), $Heap))
   returns (s#0: int where LitInt(0) <= s#0, $_reverifyPost: bool);
  free requires 21 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.IMapCommonUseCase0(m#0: IMap Box Box) returns (s#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var m#1: IMap Box Box
     where $Is(m#1, TIMap(Tclass._module.MyClass(), TBitvector(3)))
       && $IsAlloc(m#1, TIMap(Tclass._module.MyClass(), TBitvector(3)), $Heap);
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: ISet Box;
  var $w$loop#0: bool;
  var $decr$loop#00: ISet Box;
  var defass#k#0_0: bool;
  var k#0_0: ref
     where defass#k#0_0
       ==> $Is(k#0_0, Tclass._module.MyClass())
         && $IsAlloc(k#0_0, Tclass._module.MyClass(), $Heap);
  var k#0_1: ref;
  var v#0_0: bv3;

    // AddMethodImpl: IMapCommonUseCase0, Impl$$_module.__default.IMapCommonUseCase0
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(559,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(560,5)
    assume true;
    assume true;
    assert $Is(LitInt(0), Tclass._System.nat());
    s#0 := LitInt(0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(560,8)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(561,9)
    assume true;
    assume true;
    m#1 := m#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(561,12)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(562,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := IMap#Domain(m#1);
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
      free invariant ISet#Equal(IMap#Domain(m#1), $decr_init$loop#00)
         && (ISet#Equal(IMap#Domain(m#1), $decr_init$loop#00) ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(562,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assume true;
            assume false;
        }

        assume true;
        if (IMap#Equal(m#1, IMap#Empty(): IMap Box Box))
        {
            break;
        }

        $decr$loop#00 := IMap#Domain(m#1);
        // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(565,11)
        havoc k#0_1;
        if ($Is(k#0_1, Tclass._module.MyClass())
           && $IsAlloc(k#0_1, Tclass._module.MyClass(), $Heap))
        {
            assume true;
        }

        assert ($Is(null, Tclass._module.MyClass()) && IMap#Domain(m#1)[$Box(null)])
           || (exists $as#k0_0#0_0: ref :: 
            $Is($as#k0_0#0_0, Tclass._module.MyClass())
               && IMap#Domain(m#1)[$Box($as#k0_0#0_0)]);
        defass#k#0_0 := true;
        havoc k#0_0;
        assume IMap#Domain(m#1)[$Box(k#0_0)];
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(565,24)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(566,11)
        assume true;
        assert defass#k#0_0;
        assert IMap#Domain(m#1)[$Box(k#0_0)];
        assume true;
        v#0_0 := $Unbox(IMap#Elements(m#1)[$Box(k#0_0)]): bv3;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(566,17)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(567,7)
        assume true;
        assume true;
        assert $Is(s#0 + nat_from_bv3(v#0_0), Tclass._System.nat());
        s#0 := s#0 + nat_from_bv3(v#0_0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(567,21)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(568,7)
        assume true;
        assert defass#k#0_0;
        assume true;
        m#1 := IMap#Subtract(m#1, Set#UnionOne(Set#Empty(): Set Box, $Box(k#0_0)));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(568,16)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(562,3)
        assert false;
    }
}



procedure CheckWellformed$$_module.__default.IMapCommonUseCase1(m#0: IMap Box Box
       where $Is(m#0, TIMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TIMap(Tclass._module.MyClass(), TBitvector(3)), $Heap))
   returns (s#0: int where LitInt(0) <= s#0);
  free requires 22 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.IMapCommonUseCase1(m#0: IMap Box Box
       where $Is(m#0, TIMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TIMap(Tclass._module.MyClass(), TBitvector(3)), $Heap))
   returns (s#0: int where LitInt(0) <= s#0);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.IMapCommonUseCase1(m#0: IMap Box Box
       where $Is(m#0, TIMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TIMap(Tclass._module.MyClass(), TBitvector(3)), $Heap))
   returns (s#0: int where LitInt(0) <= s#0, $_reverifyPost: bool);
  free requires 22 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.IMapCommonUseCase1(m#0: IMap Box Box) returns (s#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var m#1: IMap Box Box
     where $Is(m#1, TIMap(Tclass._module.MyClass(), TBitvector(3)))
       && $IsAlloc(m#1, TIMap(Tclass._module.MyClass(), TBitvector(3)), $Heap);
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: ISet Box;
  var $w$loop#0: bool;
  var $decr$loop#00: ISet Box;
  var defass#kv#0_0: bool;
  var kv#0_0: DatatypeType
     where defass#kv#0_0
       ==> $Is(kv#0_0, Tclass._System.Tuple2(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(kv#0_0, Tclass._System.Tuple2(Tclass._module.MyClass(), TBitvector(3)), $Heap);
  var kv#0_1: DatatypeType;
  var k#0_0: ref;
  var v#0_0: bv3;
  var let#0_0#0#0: DatatypeType;

    // AddMethodImpl: IMapCommonUseCase1, Impl$$_module.__default.IMapCommonUseCase1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(573,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(574,5)
    assume true;
    assume true;
    assert $Is(LitInt(0), Tclass._System.nat());
    s#0 := LitInt(0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(574,8)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(575,9)
    assume true;
    assume true;
    m#1 := m#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(575,12)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(576,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := IMap#Domain(m#1);
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
      free invariant ISet#Equal(IMap#Domain(m#1), $decr_init$loop#00)
         && (ISet#Equal(IMap#Domain(m#1), $decr_init$loop#00) ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(576,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assume true;
            assume false;
        }

        assume true;
        if (IMap#Equal(m#1, IMap#Empty(): IMap Box Box))
        {
            break;
        }

        $decr$loop#00 := IMap#Domain(m#1);
        // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(579,12)
        havoc kv#0_1;
        if ($Is(kv#0_1, Tclass._System.Tuple2(Tclass._module.MyClass(), TBitvector(3)))
           && $IsAlloc(kv#0_1, Tclass._System.Tuple2(Tclass._module.MyClass(), TBitvector(3)), $Heap))
        {
            assume true;
        }

        assert (exists $as#kv0_0#0_0: DatatypeType :: 
          $Is($as#kv0_0#0_0, Tclass._System.Tuple2(Tclass._module.MyClass(), TBitvector(3)))
             && IMap#Items(m#1)[$Box($as#kv0_0#0_0)]);
        defass#kv#0_0 := true;
        havoc kv#0_0;
        assume IMap#Items(m#1)[$Box(kv#0_0)];
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(579,27)"} true;
        havoc k#0_0;
        assume $Is(k#0_0, Tclass._module.MyClass())
           && $IsAlloc(k#0_0, Tclass._module.MyClass(), $Heap);
        havoc v#0_0;
        assert defass#kv#0_0;
        assume let#0_0#0#0 == kv#0_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_0#0#0, Tclass._System.Tuple2(Tclass._module.MyClass(), TBitvector(3)));
        assume _System.Tuple2.___hMake2_q(let#0_0#0#0);
        assume #_System._tuple#2._#Make2($Box(k#0_0), $Box(v#0_0)) == let#0_0#0#0;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(581,7)
        assume true;
        assume true;
        assert $Is(s#0 + nat_from_bv3(v#0_0), Tclass._System.nat());
        s#0 := s#0 + nat_from_bv3(v#0_0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(581,21)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(582,7)
        assume true;
        assume true;
        m#1 := IMap#Subtract(m#1, Set#UnionOne(Set#Empty(): Set Box, $Box(k#0_0)));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(582,16)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(576,3)
        assert false;
    }
}



procedure CheckWellformed$$_module.__default.IMapCommonUseCase2(m#0: IMap Box Box
       where $Is(m#0, TIMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TIMap(Tclass._module.MyClass(), TBitvector(3)), $Heap))
   returns (s#0: int where LitInt(0) <= s#0);
  free requires 23 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.IMapCommonUseCase2(m#0: IMap Box Box
       where $Is(m#0, TIMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TIMap(Tclass._module.MyClass(), TBitvector(3)), $Heap))
   returns (s#0: int where LitInt(0) <= s#0);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.IMapCommonUseCase2(m#0: IMap Box Box
       where $Is(m#0, TIMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TIMap(Tclass._module.MyClass(), TBitvector(3)), $Heap))
   returns (s#0: int where LitInt(0) <= s#0, $_reverifyPost: bool);
  free requires 23 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.IMapCommonUseCase2(m#0: IMap Box Box) returns (s#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var m#1: IMap Box Box
     where $Is(m#1, TIMap(Tclass._module.MyClass(), TBitvector(3)))
       && $IsAlloc(m#1, TIMap(Tclass._module.MyClass(), TBitvector(3)), $Heap);
  var $PreLoopHeap$loop#0: Heap;
  var $w$loop#0: bool;
  var defass#k#0_0: bool;
  var k#0_0: ref
     where defass#k#0_0
       ==> $Is(k#0_0, Tclass._module.MyClass())
         && $IsAlloc(k#0_0, Tclass._module.MyClass(), $Heap);
  var v#0_0: bv3;
  var k#0_1: ref;
  var v#0_1: bv3;

    // AddMethodImpl: IMapCommonUseCase2, Impl$$_module.__default.IMapCommonUseCase2
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(588,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(589,5)
    assume true;
    assume true;
    assert $Is(LitInt(0), Tclass._System.nat());
    s#0 := LitInt(0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(589,8)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(590,9)
    assume true;
    assume true;
    m#1 := m#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(590,12)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(591,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
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
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(591,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assume true;
            assume false;
        }

        assume true;
        if (IMap#Equal(m#1, IMap#Empty(): IMap Box Box))
        {
            break;
        }

        // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(594,14)
        havoc k#0_1;
        havoc v#0_1;
        if ($Is(k#0_1, Tclass._module.MyClass())
           && $IsAlloc(k#0_1, Tclass._module.MyClass(), $Heap))
        {
            assume true;
        }

        assert (exists $as#v0_0#0_0: bv3 :: 
            $Is(null, Tclass._module.MyClass())
               && IMap#Items(m#1)[$Box(#_System._tuple#2._#Make2($Box(null), $Box($as#v0_0#0_0)))])
           || (exists $as#k0_0#0_0: ref, $as#v0_0#0_0: bv3 :: 
            $Is($as#k0_0#0_0, Tclass._module.MyClass())
               && IMap#Items(m#1)[$Box(#_System._tuple#2._#Make2($Box($as#k0_0#0_0), $Box($as#v0_0#0_0)))]);
        defass#k#0_0 := true;
        havoc k#0_0, v#0_0;
        assume IMap#Items(m#1)[$Box(#_System._tuple#2._#Make2($Box(k#0_0), $Box(v#0_0)))];
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(594,33)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(595,7)
        assume true;
        assume true;
        assert $Is(s#0 + nat_from_bv3(v#0_0), Tclass._System.nat());
        s#0 := s#0 + nat_from_bv3(v#0_0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(595,21)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(596,7)
        assume true;
        assert defass#k#0_0;
        assume true;
        m#1 := IMap#Subtract(m#1, Set#UnionOne(Set#Empty(): Set Box, $Box(k#0_0)));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(596,16)"} true;
    }
}



procedure CheckWellformed$$_module.__default.TestIMapPropertyNonempty(m#0: IMap Box Box
       where $Is(m#0, TIMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TIMap(Tclass._module.MyClass(), TBitvector(3)), $Heap));
  free requires 24 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.TestIMapPropertyNonempty(m#0: IMap Box Box
       where $Is(m#0, TIMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TIMap(Tclass._module.MyClass(), TBitvector(3)), $Heap));
  // user-defined preconditions
  requires !IMap#Equal(m#0, IMap#Empty(): IMap Box Box);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.TestIMapPropertyNonempty(m#0: IMap Box Box
       where $Is(m#0, TIMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TIMap(Tclass._module.MyClass(), TBitvector(3)), $Heap))
   returns ($_reverifyPost: bool);
  free requires 24 == $FunctionContextHeight;
  // user-defined preconditions
  requires !IMap#Equal(m#0, IMap#Empty(): IMap Box Box);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.TestIMapPropertyNonempty(m#0: IMap Box Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: TestIMapPropertyNonempty, Impl$$_module.__default.TestIMapPropertyNonempty
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(606,0): initial state"} true;
    $_reverifyPost := false;
    // ----- alternative statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(607,3)
    if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(609,5)
        assume true;
        assert !ISet#Equal(IMap#Domain(m#0), ISet#Empty(): ISet Box);
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(611,5)
        assume true;
        assert !ISet#Equal(IMap#Values(m#0), ISet#Empty(): ISet Box);
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(613,5)
        assume true;
        assert !ISet#Equal(IMap#Items(m#0), ISet#Empty(): ISet Box);
    }
    else
    {
        assume true;
        assume true;
        assume true;
        assume !Lit(true) && !Lit(true) && !Lit(true);
        assert false;
    }
}



procedure CheckWellformed$$_module.__default.TestIMapPropertyMembership0(m#0: IMap Box Box
       where $Is(m#0, TIMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TIMap(Tclass._module.MyClass(), TBitvector(3)), $Heap));
  free requires 25 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.TestIMapPropertyMembership0(m#0: IMap Box Box
       where $Is(m#0, TIMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TIMap(Tclass._module.MyClass(), TBitvector(3)), $Heap));
  // user-defined preconditions
  requires !ISet#Equal(IMap#Values(m#0), ISet#Empty(): ISet Box)
     || !ISet#Equal(IMap#Items(m#0), ISet#Empty(): ISet Box);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.TestIMapPropertyMembership0(m#0: IMap Box Box
       where $Is(m#0, TIMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TIMap(Tclass._module.MyClass(), TBitvector(3)), $Heap))
   returns ($_reverifyPost: bool);
  free requires 25 == $FunctionContextHeight;
  // user-defined preconditions
  requires !ISet#Equal(IMap#Values(m#0), ISet#Empty(): ISet Box)
     || !ISet#Equal(IMap#Items(m#0), ISet#Empty(): ISet Box);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.TestIMapPropertyMembership0(m#0: IMap Box Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var k#0: ref;

    // AddMethodImpl: TestIMapPropertyMembership0, Impl$$_module.__default.TestIMapPropertyMembership0
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(618,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(619,3)
    // Begin Comprehension WF check
    havoc k#0;
    if ($Is(k#0, Tclass._module.MyClass()))
    {
    }

    // End Comprehension WF check
    assume true;
    assert (exists k#1: ref :: 
      { IMap#Domain(m#0)[$Box(k#1)] } 
      $Is(k#1, Tclass._module.MyClass()) && IMap#Domain(m#0)[$Box(k#1)]);
}



procedure CheckWellformed$$_module.__default.TestIMapPropertyMembership1(m#0: IMap Box Box
       where $Is(m#0, TIMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TIMap(Tclass._module.MyClass(), TBitvector(3)), $Heap));
  free requires 26 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.TestIMapPropertyMembership1(m#0: IMap Box Box
       where $Is(m#0, TIMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TIMap(Tclass._module.MyClass(), TBitvector(3)), $Heap));
  // user-defined preconditions
  requires !ISet#Equal(IMap#Items(m#0), ISet#Empty(): ISet Box)
     || !ISet#Equal(IMap#Domain(m#0), ISet#Empty(): ISet Box);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.TestIMapPropertyMembership1(m#0: IMap Box Box
       where $Is(m#0, TIMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TIMap(Tclass._module.MyClass(), TBitvector(3)), $Heap))
   returns ($_reverifyPost: bool);
  free requires 26 == $FunctionContextHeight;
  // user-defined preconditions
  requires !ISet#Equal(IMap#Items(m#0), ISet#Empty(): ISet Box)
     || !ISet#Equal(IMap#Domain(m#0), ISet#Empty(): ISet Box);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.TestIMapPropertyMembership1(m#0: IMap Box Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var v#0: bv3;

    // AddMethodImpl: TestIMapPropertyMembership1, Impl$$_module.__default.TestIMapPropertyMembership1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(624,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(625,3)
    // Begin Comprehension WF check
    havoc v#0;
    if (true)
    {
    }

    // End Comprehension WF check
    assume true;
    assert (exists v#1: bv3 :: { IMap#Values(m#0)[$Box(v#1)] } IMap#Values(m#0)[$Box(v#1)]);
}



procedure CheckWellformed$$_module.__default.TestIMapPropertyMembership2(m#0: IMap Box Box
       where $Is(m#0, TIMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TIMap(Tclass._module.MyClass(), TBitvector(3)), $Heap));
  free requires 27 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.TestIMapPropertyMembership2(m#0: IMap Box Box
       where $Is(m#0, TIMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TIMap(Tclass._module.MyClass(), TBitvector(3)), $Heap));
  // user-defined preconditions
  requires !ISet#Equal(IMap#Domain(m#0), ISet#Empty(): ISet Box)
     || !ISet#Equal(IMap#Values(m#0), ISet#Empty(): ISet Box);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.TestIMapPropertyMembership2(m#0: IMap Box Box
       where $Is(m#0, TIMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TIMap(Tclass._module.MyClass(), TBitvector(3)), $Heap))
   returns ($_reverifyPost: bool);
  free requires 27 == $FunctionContextHeight;
  // user-defined preconditions
  requires !ISet#Equal(IMap#Domain(m#0), ISet#Empty(): ISet Box)
     || !ISet#Equal(IMap#Values(m#0), ISet#Empty(): ISet Box);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.TestIMapPropertyMembership2(m#0: IMap Box Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var kv#0: DatatypeType;

    // AddMethodImpl: TestIMapPropertyMembership2, Impl$$_module.__default.TestIMapPropertyMembership2
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(630,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(631,3)
    // Begin Comprehension WF check
    havoc kv#0;
    if ($Is(kv#0, Tclass._System.Tuple2(Tclass._module.MyClass(), TBitvector(3))))
    {
    }

    // End Comprehension WF check
    assume true;
    assert (exists kv#1: DatatypeType :: 
      { IMap#Items(m#0)[$Box(kv#1)] } 
      $Is(kv#1, Tclass._System.Tuple2(Tclass._module.MyClass(), TBitvector(3)))
         && IMap#Items(m#0)[$Box(kv#1)]);
}



procedure CheckWellformed$$_module.__default.TestIMapPropertyMembership3(m#0: IMap Box Box
       where $Is(m#0, TIMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TIMap(Tclass._module.MyClass(), TBitvector(3)), $Heap));
  free requires 28 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.TestIMapPropertyMembership3(m#0: IMap Box Box
       where $Is(m#0, TIMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TIMap(Tclass._module.MyClass(), TBitvector(3)), $Heap));
  // user-defined preconditions
  requires !ISet#Equal(IMap#Domain(m#0), ISet#Empty(): ISet Box)
     || !ISet#Equal(IMap#Values(m#0), ISet#Empty(): ISet Box);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.TestIMapPropertyMembership3(m#0: IMap Box Box
       where $Is(m#0, TIMap(Tclass._module.MyClass(), TBitvector(3)))
         && $IsAlloc(m#0, TIMap(Tclass._module.MyClass(), TBitvector(3)), $Heap))
   returns ($_reverifyPost: bool);
  free requires 28 == $FunctionContextHeight;
  // user-defined preconditions
  requires !ISet#Equal(IMap#Domain(m#0), ISet#Empty(): ISet Box)
     || !ISet#Equal(IMap#Values(m#0), ISet#Empty(): ISet Box);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.TestIMapPropertyMembership3(m#0: IMap Box Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var v#0: bv3;
  var k#0: ref;

    // AddMethodImpl: TestIMapPropertyMembership3, Impl$$_module.__default.TestIMapPropertyMembership3
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(636,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Maps.dfy(637,3)
    // Begin Comprehension WF check
    havoc v#0;
    havoc k#0;
    if ($Is(k#0, Tclass._module.MyClass()))
    {
    }

    // End Comprehension WF check
    assume true;
    assert (exists v#1: bv3, k#1: ref :: 
      { #_System._tuple#2._#Make2($Box(k#1), $Box(v#1)) } 
      $Is(k#1, Tclass._module.MyClass())
         && IMap#Items(m#0)[$Box(#_System._tuple#2._#Make2($Box(k#1), $Box(v#1)))]);
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

const unique tytagFamily$A: TyTagFamily;

const unique tytagFamily$Elem: TyTagFamily;

const unique tytagFamily$MyClass: TyTagFamily;

const unique tytagFamily$_default: TyTagFamily;

const unique field$x: NameFamily;
