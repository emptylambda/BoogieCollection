// Dafny 3.0.0.30204
// Command Line Options: -compile:0 -noVerify /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy -print:./Iterators.bpl

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

const unique class._module.MyIter?: ClassName;

function Tclass._module.MyIter?(Ty) : Ty;

const unique Tagclass._module.MyIter?: TyTag;

// Tclass._module.MyIter? Tag
axiom (forall _module.MyIter$T: Ty :: 
  { Tclass._module.MyIter?(_module.MyIter$T) } 
  Tag(Tclass._module.MyIter?(_module.MyIter$T)) == Tagclass._module.MyIter?
     && TagFamily(Tclass._module.MyIter?(_module.MyIter$T)) == tytagFamily$MyIter);

// Tclass._module.MyIter? injectivity 0
axiom (forall _module.MyIter$T: Ty :: 
  { Tclass._module.MyIter?(_module.MyIter$T) } 
  Tclass._module.MyIter?_0(Tclass._module.MyIter?(_module.MyIter$T))
     == _module.MyIter$T);

function Tclass._module.MyIter?_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.MyIter?
axiom (forall _module.MyIter$T: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.MyIter?(_module.MyIter$T)) } 
  $IsBox(bx, Tclass._module.MyIter?(_module.MyIter$T))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.MyIter?(_module.MyIter$T)));

// MyIter: Class $Is
axiom (forall _module.MyIter$T: Ty, $o: ref :: 
  { $Is($o, Tclass._module.MyIter?(_module.MyIter$T)) } 
  $Is($o, Tclass._module.MyIter?(_module.MyIter$T))
     <==> $o == null || dtype($o) == Tclass._module.MyIter?(_module.MyIter$T));

// MyIter: Class $IsAlloc
axiom (forall _module.MyIter$T: Ty, $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.MyIter?(_module.MyIter$T), $h) } 
  $IsAlloc($o, Tclass._module.MyIter?(_module.MyIter$T), $h)
     <==> $o == null || read($h, $o, alloc));

function _module.MyIter.q(ref) : Box;

// MyIter.q: Type axiom
axiom (forall _module.MyIter$T: Ty, $o: ref :: 
  { _module.MyIter.q($o), Tclass._module.MyIter?(_module.MyIter$T) } 
  $o != null && dtype($o) == Tclass._module.MyIter?(_module.MyIter$T)
     ==> $IsBox(_module.MyIter.q($o), _module.MyIter$T));

// MyIter.q: Allocation axiom
axiom (forall _module.MyIter$T: Ty, $h: Heap, $o: ref :: 
  { _module.MyIter.q($o), read($h, $o, alloc), Tclass._module.MyIter?(_module.MyIter$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.MyIter?(_module.MyIter$T)
       && read($h, $o, alloc)
     ==> $IsAllocBox(_module.MyIter.q($o), _module.MyIter$T, $h));

axiom FDim(_module.MyIter.x) == 0
   && FieldOfDecl(class._module.MyIter?, field$x) == _module.MyIter.x
   && !$IsGhostField(_module.MyIter.x);

const _module.MyIter.x: Field Box;

// MyIter.x: Type axiom
axiom (forall _module.MyIter$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.MyIter.x), Tclass._module.MyIter?(_module.MyIter$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.MyIter?(_module.MyIter$T)
     ==> $IsBox(read($h, $o, _module.MyIter.x), _module.MyIter$T));

// MyIter.x: Allocation axiom
axiom (forall _module.MyIter$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.MyIter.x), Tclass._module.MyIter?(_module.MyIter$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.MyIter?(_module.MyIter$T)
       && read($h, $o, alloc)
     ==> $IsAllocBox(read($h, $o, _module.MyIter.x), _module.MyIter$T, $h));

axiom FDim(_module.MyIter.y) == 0
   && FieldOfDecl(class._module.MyIter?, field$y) == _module.MyIter.y
   && !$IsGhostField(_module.MyIter.y);

const _module.MyIter.y: Field Box;

// MyIter.y: Type axiom
axiom (forall _module.MyIter$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.MyIter.y), Tclass._module.MyIter?(_module.MyIter$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.MyIter?(_module.MyIter$T)
     ==> $IsBox(read($h, $o, _module.MyIter.y), _module.MyIter$T));

// MyIter.y: Allocation axiom
axiom (forall _module.MyIter$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.MyIter.y), Tclass._module.MyIter?(_module.MyIter$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.MyIter?(_module.MyIter$T)
       && read($h, $o, alloc)
     ==> $IsAllocBox(read($h, $o, _module.MyIter.y), _module.MyIter$T, $h));

axiom FDim(_module.MyIter.xs) == 0
   && FieldOfDecl(class._module.MyIter?, field$xs) == _module.MyIter.xs
   && $IsGhostField(_module.MyIter.xs);

const _module.MyIter.xs: Field (Seq Box);

// MyIter.xs: Type axiom
axiom (forall _module.MyIter$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.MyIter.xs), Tclass._module.MyIter?(_module.MyIter$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.MyIter?(_module.MyIter$T)
     ==> $Is(read($h, $o, _module.MyIter.xs), TSeq(_module.MyIter$T)));

// MyIter.xs: Allocation axiom
axiom (forall _module.MyIter$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.MyIter.xs), Tclass._module.MyIter?(_module.MyIter$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.MyIter?(_module.MyIter$T)
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.MyIter.xs), TSeq(_module.MyIter$T), $h));

axiom FDim(_module.MyIter.ys) == 0
   && FieldOfDecl(class._module.MyIter?, field$ys) == _module.MyIter.ys
   && $IsGhostField(_module.MyIter.ys);

const _module.MyIter.ys: Field (Seq Box);

// MyIter.ys: Type axiom
axiom (forall _module.MyIter$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.MyIter.ys), Tclass._module.MyIter?(_module.MyIter$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.MyIter?(_module.MyIter$T)
     ==> $Is(read($h, $o, _module.MyIter.ys), TSeq(_module.MyIter$T)));

// MyIter.ys: Allocation axiom
axiom (forall _module.MyIter$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.MyIter.ys), Tclass._module.MyIter?(_module.MyIter$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.MyIter?(_module.MyIter$T)
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.MyIter.ys), TSeq(_module.MyIter$T), $h));

function _module.MyIter.__reads(ref) : Set Box;

// MyIter._reads: Type axiom
axiom (forall _module.MyIter$T: Ty, $o: ref :: 
  { _module.MyIter.__reads($o), Tclass._module.MyIter?(_module.MyIter$T) } 
  $o != null && dtype($o) == Tclass._module.MyIter?(_module.MyIter$T)
     ==> $Is(_module.MyIter.__reads($o), TSet(Tclass._System.object?())));

// MyIter._reads: Allocation axiom
axiom (forall _module.MyIter$T: Ty, $h: Heap, $o: ref :: 
  { _module.MyIter.__reads($o), read($h, $o, alloc), Tclass._module.MyIter?(_module.MyIter$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.MyIter?(_module.MyIter$T)
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.MyIter.__reads($o), TSet(Tclass._System.object?()), $h));

function _module.MyIter.__modifies(ref) : Set Box;

// MyIter._modifies: Type axiom
axiom (forall _module.MyIter$T: Ty, $o: ref :: 
  { _module.MyIter.__modifies($o), Tclass._module.MyIter?(_module.MyIter$T) } 
  $o != null && dtype($o) == Tclass._module.MyIter?(_module.MyIter$T)
     ==> $Is(_module.MyIter.__modifies($o), TSet(Tclass._System.object?())));

// MyIter._modifies: Allocation axiom
axiom (forall _module.MyIter$T: Ty, $h: Heap, $o: ref :: 
  { _module.MyIter.__modifies($o), read($h, $o, alloc), Tclass._module.MyIter?(_module.MyIter$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.MyIter?(_module.MyIter$T)
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.MyIter.__modifies($o), TSet(Tclass._System.object?()), $h));

axiom FDim(_module.MyIter.__new) == 0
   && FieldOfDecl(class._module.MyIter?, field$_new) == _module.MyIter.__new
   && $IsGhostField(_module.MyIter.__new);

const _module.MyIter.__new: Field (Set Box);

// MyIter._new: Type axiom
axiom (forall _module.MyIter$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.MyIter.__new), Tclass._module.MyIter?(_module.MyIter$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.MyIter?(_module.MyIter$T)
     ==> $Is(read($h, $o, _module.MyIter.__new), TSet(Tclass._System.object?())));

// MyIter._new: Allocation axiom
axiom (forall _module.MyIter$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.MyIter.__new), Tclass._module.MyIter?(_module.MyIter$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.MyIter?(_module.MyIter$T)
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.MyIter.__new), TSet(Tclass._System.object?()), $h));

function _module.MyIter.__decreases0(ref) : Box;

// MyIter._decreases0: Type axiom
axiom (forall _module.MyIter$T: Ty, $o: ref :: 
  { _module.MyIter.__decreases0($o), Tclass._module.MyIter?(_module.MyIter$T) } 
  $o != null && dtype($o) == Tclass._module.MyIter?(_module.MyIter$T)
     ==> $IsBox(_module.MyIter.__decreases0($o), _module.MyIter$T));

// MyIter._decreases0: Allocation axiom
axiom (forall _module.MyIter$T: Ty, $h: Heap, $o: ref :: 
  { _module.MyIter.__decreases0($o), read($h, $o, alloc), Tclass._module.MyIter?(_module.MyIter$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.MyIter?(_module.MyIter$T)
       && read($h, $o, alloc)
     ==> $IsAllocBox(_module.MyIter.__decreases0($o), _module.MyIter$T, $h));

function Tclass._module.MyIter(Ty) : Ty;

const unique Tagclass._module.MyIter: TyTag;

// Tclass._module.MyIter Tag
axiom (forall _module.MyIter$T: Ty :: 
  { Tclass._module.MyIter(_module.MyIter$T) } 
  Tag(Tclass._module.MyIter(_module.MyIter$T)) == Tagclass._module.MyIter
     && TagFamily(Tclass._module.MyIter(_module.MyIter$T)) == tytagFamily$MyIter);

// Tclass._module.MyIter injectivity 0
axiom (forall _module.MyIter$T: Ty :: 
  { Tclass._module.MyIter(_module.MyIter$T) } 
  Tclass._module.MyIter_0(Tclass._module.MyIter(_module.MyIter$T))
     == _module.MyIter$T);

function Tclass._module.MyIter_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.MyIter
axiom (forall _module.MyIter$T: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.MyIter(_module.MyIter$T)) } 
  $IsBox(bx, Tclass._module.MyIter(_module.MyIter$T))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.MyIter(_module.MyIter$T)));

procedure CheckWellformed$$_module.MyIter.__ctor(_module.MyIter$T: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.MyIter(_module.MyIter$T))
         && $IsAlloc(this, Tclass._module.MyIter(_module.MyIter$T), $Heap), 
    q#0: Box
       where $IsBox(q#0, _module.MyIter$T) && $IsAllocBox(q#0, _module.MyIter$T, $Heap));
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.MyIter.__ctor(_module.MyIter$T: Ty, 
    q#0: Box
       where $IsBox(q#0, _module.MyIter$T) && $IsAllocBox(q#0, _module.MyIter$T, $Heap))
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass._module.MyIter(_module.MyIter$T))
         && $IsAlloc(this, Tclass._module.MyIter(_module.MyIter$T), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures _module.MyIter.q(this) == q#0;
  free ensures true;
  ensures Seq#Equal(read($Heap, this, _module.MyIter.xs), Seq#Empty(): Seq Box);
  free ensures true;
  ensures Seq#Equal(read($Heap, this, _module.MyIter.ys), Seq#Empty(): Seq Box);
  free ensures _module.MyIter.Valid#canCall(_module.MyIter$T, $Heap, this);
  ensures _module.MyIter.Valid(_module.MyIter$T, $Heap, this);
  free ensures true;
  ensures Set#Equal(_module.MyIter.__reads(this), Set#Empty(): Set Box);
  free ensures true;
  ensures Set#Equal(_module.MyIter.__modifies(this), Set#Empty(): Set Box);
  free ensures true;
  ensures Set#Equal(read($Heap, this, _module.MyIter.__new), Set#Empty(): Set Box);
  free ensures true;
  ensures _module.MyIter.__decreases0(this) == q#0;
  // constructor allocates the object
  ensures !read(old($Heap), this, alloc);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



// function declaration for _module.MyIter.Valid
function _module.MyIter.Valid(_module.MyIter$T: Ty, $heap: Heap, this: ref) : bool;

function _module.MyIter.Valid#canCall(_module.MyIter$T: Ty, $heap: Heap, this: ref) : bool;

// frame axiom for _module.MyIter.Valid
axiom (forall _module.MyIter$T: Ty, $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.MyIter.Valid(_module.MyIter$T, $h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.MyIter(_module.MyIter$T))
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && (
            $o == this
             || _module.MyIter.__reads(this)[$Box($o)]
             || read($h0, this, _module.MyIter.__new)[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.MyIter.Valid(_module.MyIter$T, $h0, this)
       == _module.MyIter.Valid(_module.MyIter$T, $h1, this));

// consequence axiom for _module.MyIter.Valid
axiom 7 <= $FunctionContextHeight
   ==> (forall _module.MyIter$T: Ty, $Heap: Heap, this: ref :: 
    { _module.MyIter.Valid(_module.MyIter$T, $Heap, this) } 
    _module.MyIter.Valid#canCall(_module.MyIter$T, $Heap, this)
         || (7 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.MyIter(_module.MyIter$T))
           && $IsAlloc(this, Tclass._module.MyIter(_module.MyIter$T), $Heap))
       ==> true);

function _module.MyIter.Valid#requires(Ty, Heap, ref) : bool;

// #requires axiom for _module.MyIter.Valid
axiom (forall _module.MyIter$T: Ty, $Heap: Heap, this: ref :: 
  { _module.MyIter.Valid#requires(_module.MyIter$T, $Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.MyIter(_module.MyIter$T))
       && $IsAlloc(this, Tclass._module.MyIter(_module.MyIter$T), $Heap)
     ==> _module.MyIter.Valid#requires(_module.MyIter$T, $Heap, this) == true);

procedure CheckWellformed$$_module.MyIter.Valid(_module.MyIter$T: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.MyIter(_module.MyIter$T))
         && $IsAlloc(this, Tclass._module.MyIter(_module.MyIter$T), $Heap));
  free requires 7 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.MyIter.Valid(_module.MyIter$T: Ty, this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function Valid
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(4,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> $o == this
           || _module.MyIter.__reads(this)[$Box($o)]
           || read($Heap, this, _module.MyIter.__new)[$Box($o)]);
    b$reqreads#0 := $_Frame[this, _module.MyIter.__new];
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



procedure Call$$_module.MyIter.MoveNext(_module.MyIter$T: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.MyIter(_module.MyIter$T))
         && $IsAlloc(this, Tclass._module.MyIter(_module.MyIter$T), $Heap))
   returns (more#0: bool);
  // user-defined preconditions
  requires _module.MyIter.Valid(_module.MyIter$T, $Heap, this);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    read($Heap, this, _module.MyIter.__new)[$Box($o)]
         && !read(old($Heap), this, _module.MyIter.__new)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures !read($Heap, this, _module.MyIter.__new)[$Box(null)];
  free ensures more#0 ==> _module.MyIter.Valid#canCall(_module.MyIter$T, $Heap, this);
  ensures more#0 ==> _module.MyIter.Valid(_module.MyIter$T, $Heap, this);
  free ensures true;
  ensures Seq#Equal(read($Heap, this, _module.MyIter.xs), 
    (if more#0
       then Seq#Append(read(old($Heap), this, _module.MyIter.xs), 
        Seq#Build(Seq#Empty(): Seq Box, read($Heap, this, _module.MyIter.x)))
       else read(old($Heap), this, _module.MyIter.xs)));
  free ensures true;
  ensures Seq#Equal(read($Heap, this, _module.MyIter.ys), 
    (if more#0
       then Seq#Append(read(old($Heap), this, _module.MyIter.ys), 
        Seq#Build(Seq#Empty(): Seq Box, read($Heap, this, _module.MyIter.y)))
       else read(old($Heap), this, _module.MyIter.ys)));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || 
        $o == this
         || _module.MyIter.__modifies(this)[$Box($o)]
         || read(old($Heap), this, _module.MyIter.__new)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



// _module.MyIter: subset type $Is
axiom (forall _module.MyIter$T: Ty, c#0: ref :: 
  { $Is(c#0, Tclass._module.MyIter(_module.MyIter$T)) } 
  $Is(c#0, Tclass._module.MyIter(_module.MyIter$T))
     <==> $Is(c#0, Tclass._module.MyIter?(_module.MyIter$T)) && c#0 != null);

// _module.MyIter: subset type $IsAlloc
axiom (forall _module.MyIter$T: Ty, c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.MyIter(_module.MyIter$T), $h) } 
  $IsAlloc(c#0, Tclass._module.MyIter(_module.MyIter$T), $h)
     <==> $IsAlloc(c#0, Tclass._module.MyIter?(_module.MyIter$T), $h));

procedure CheckWellformed$$_module.MyIter(_module.MyIter$T: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.MyIter(_module.MyIter$T))
         && $IsAlloc(this, Tclass._module.MyIter(_module.MyIter$T), $Heap), 
    q#0: Box
       where $IsBox(q#0, _module.MyIter$T) && $IsAllocBox(q#0, _module.MyIter$T, $Heap));
  free requires 53 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Impl$$_module.MyIter(_module.MyIter$T: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.MyIter(_module.MyIter$T))
         && $IsAlloc(this, Tclass._module.MyIter(_module.MyIter$T), $Heap), 
    q#0: Box
       where $IsBox(q#0, _module.MyIter$T) && $IsAllocBox(q#0, _module.MyIter$T, $Heap));
  free requires 53 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



const unique class._module.MyIntIter?: ClassName;

function Tclass._module.MyIntIter?() : Ty;

const unique Tagclass._module.MyIntIter?: TyTag;

// Tclass._module.MyIntIter? Tag
axiom Tag(Tclass._module.MyIntIter?()) == Tagclass._module.MyIntIter?
   && TagFamily(Tclass._module.MyIntIter?()) == tytagFamily$MyIntIter;

// Box/unbox axiom for Tclass._module.MyIntIter?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.MyIntIter?()) } 
  $IsBox(bx, Tclass._module.MyIntIter?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.MyIntIter?()));

// MyIntIter: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.MyIntIter?()) } 
  $Is($o, Tclass._module.MyIntIter?())
     <==> $o == null || dtype($o) == Tclass._module.MyIntIter?());

// MyIntIter: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.MyIntIter?(), $h) } 
  $IsAlloc($o, Tclass._module.MyIntIter?(), $h)
     <==> $o == null || read($h, $o, alloc));

axiom FDim(_module.MyIntIter.x) == 0
   && FieldOfDecl(class._module.MyIntIter?, field$x) == _module.MyIntIter.x
   && !$IsGhostField(_module.MyIntIter.x);

const _module.MyIntIter.x: Field int;

// MyIntIter.x: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.MyIntIter.x) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.MyIntIter?()
     ==> $Is(read($h, $o, _module.MyIntIter.x), TInt));

// MyIntIter.x: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.MyIntIter.x) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.MyIntIter?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.MyIntIter.x), TInt, $h));

axiom FDim(_module.MyIntIter.y) == 0
   && FieldOfDecl(class._module.MyIntIter?, field$y) == _module.MyIntIter.y
   && !$IsGhostField(_module.MyIntIter.y);

const _module.MyIntIter.y: Field int;

// MyIntIter.y: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.MyIntIter.y) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.MyIntIter?()
     ==> $Is(read($h, $o, _module.MyIntIter.y), TInt));

// MyIntIter.y: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.MyIntIter.y) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.MyIntIter?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.MyIntIter.y), TInt, $h));

axiom FDim(_module.MyIntIter.xs) == 0
   && FieldOfDecl(class._module.MyIntIter?, field$xs) == _module.MyIntIter.xs
   && $IsGhostField(_module.MyIntIter.xs);

const _module.MyIntIter.xs: Field (Seq Box);

// MyIntIter.xs: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.MyIntIter.xs) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.MyIntIter?()
     ==> $Is(read($h, $o, _module.MyIntIter.xs), TSeq(TInt)));

// MyIntIter.xs: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.MyIntIter.xs) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.MyIntIter?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.MyIntIter.xs), TSeq(TInt), $h));

axiom FDim(_module.MyIntIter.ys) == 0
   && FieldOfDecl(class._module.MyIntIter?, field$ys) == _module.MyIntIter.ys
   && $IsGhostField(_module.MyIntIter.ys);

const _module.MyIntIter.ys: Field (Seq Box);

// MyIntIter.ys: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.MyIntIter.ys) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.MyIntIter?()
     ==> $Is(read($h, $o, _module.MyIntIter.ys), TSeq(TInt)));

// MyIntIter.ys: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.MyIntIter.ys) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.MyIntIter?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.MyIntIter.ys), TSeq(TInt), $h));

function _module.MyIntIter.__reads(ref) : Set Box;

// MyIntIter._reads: Type axiom
axiom (forall $o: ref :: 
  { _module.MyIntIter.__reads($o) } 
  $o != null && dtype($o) == Tclass._module.MyIntIter?()
     ==> $Is(_module.MyIntIter.__reads($o), TSet(Tclass._System.object?())));

// MyIntIter._reads: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.MyIntIter.__reads($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.MyIntIter?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.MyIntIter.__reads($o), TSet(Tclass._System.object?()), $h));

function _module.MyIntIter.__modifies(ref) : Set Box;

// MyIntIter._modifies: Type axiom
axiom (forall $o: ref :: 
  { _module.MyIntIter.__modifies($o) } 
  $o != null && dtype($o) == Tclass._module.MyIntIter?()
     ==> $Is(_module.MyIntIter.__modifies($o), TSet(Tclass._System.object?())));

// MyIntIter._modifies: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.MyIntIter.__modifies($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.MyIntIter?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.MyIntIter.__modifies($o), TSet(Tclass._System.object?()), $h));

axiom FDim(_module.MyIntIter.__new) == 0
   && FieldOfDecl(class._module.MyIntIter?, field$_new) == _module.MyIntIter.__new
   && $IsGhostField(_module.MyIntIter.__new);

const _module.MyIntIter.__new: Field (Set Box);

// MyIntIter._new: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.MyIntIter.__new) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.MyIntIter?()
     ==> $Is(read($h, $o, _module.MyIntIter.__new), TSet(Tclass._System.object?())));

// MyIntIter._new: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.MyIntIter.__new) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.MyIntIter?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.MyIntIter.__new), TSet(Tclass._System.object?()), $h));

function Tclass._module.MyIntIter() : Ty;

const unique Tagclass._module.MyIntIter: TyTag;

// Tclass._module.MyIntIter Tag
axiom Tag(Tclass._module.MyIntIter()) == Tagclass._module.MyIntIter
   && TagFamily(Tclass._module.MyIntIter()) == tytagFamily$MyIntIter;

// Box/unbox axiom for Tclass._module.MyIntIter
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.MyIntIter()) } 
  $IsBox(bx, Tclass._module.MyIntIter())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.MyIntIter()));

procedure CheckWellformed$$_module.MyIntIter.__ctor(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.MyIntIter())
         && $IsAlloc(this, Tclass._module.MyIntIter(), $Heap));
  free requires 11 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.MyIntIter.__ctor()
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass._module.MyIntIter())
         && $IsAlloc(this, Tclass._module.MyIntIter(), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures Seq#Equal(read($Heap, this, _module.MyIntIter.xs), Seq#Empty(): Seq Box);
  free ensures true;
  ensures Seq#Equal(read($Heap, this, _module.MyIntIter.ys), Seq#Empty(): Seq Box);
  free ensures _module.MyIntIter.Valid#canCall($Heap, this);
  ensures _module.MyIntIter.Valid($Heap, this);
  free ensures true;
  ensures Set#Equal(_module.MyIntIter.__reads(this), Set#Empty(): Set Box);
  free ensures true;
  ensures Set#Equal(_module.MyIntIter.__modifies(this), Set#Empty(): Set Box);
  free ensures true;
  ensures Set#Equal(read($Heap, this, _module.MyIntIter.__new), Set#Empty(): Set Box);
  // constructor allocates the object
  ensures !read(old($Heap), this, alloc);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



// function declaration for _module.MyIntIter.Valid
function _module.MyIntIter.Valid($heap: Heap, this: ref) : bool;

function _module.MyIntIter.Valid#canCall($heap: Heap, this: ref) : bool;

// frame axiom for _module.MyIntIter.Valid
axiom (forall $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.MyIntIter.Valid($h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.MyIntIter())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && (
            $o == this
             || _module.MyIntIter.__reads(this)[$Box($o)]
             || read($h0, this, _module.MyIntIter.__new)[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.MyIntIter.Valid($h0, this) == _module.MyIntIter.Valid($h1, this));

// consequence axiom for _module.MyIntIter.Valid
axiom 10 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref :: 
    { _module.MyIntIter.Valid($Heap, this) } 
    _module.MyIntIter.Valid#canCall($Heap, this)
         || (10 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.MyIntIter())
           && $IsAlloc(this, Tclass._module.MyIntIter(), $Heap))
       ==> true);

function _module.MyIntIter.Valid#requires(Heap, ref) : bool;

// #requires axiom for _module.MyIntIter.Valid
axiom (forall $Heap: Heap, this: ref :: 
  { _module.MyIntIter.Valid#requires($Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.MyIntIter())
       && $IsAlloc(this, Tclass._module.MyIntIter(), $Heap)
     ==> _module.MyIntIter.Valid#requires($Heap, this) == true);

procedure CheckWellformed$$_module.MyIntIter.Valid(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.MyIntIter())
         && $IsAlloc(this, Tclass._module.MyIntIter(), $Heap));
  free requires 10 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.MyIntIter.Valid(this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function Valid
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(8,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> $o == this
           || _module.MyIntIter.__reads(this)[$Box($o)]
           || read($Heap, this, _module.MyIntIter.__new)[$Box($o)]);
    b$reqreads#0 := $_Frame[this, _module.MyIntIter.__new];
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



procedure Call$$_module.MyIntIter.MoveNext(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.MyIntIter())
         && $IsAlloc(this, Tclass._module.MyIntIter(), $Heap))
   returns (more#0: bool);
  // user-defined preconditions
  requires _module.MyIntIter.Valid($Heap, this);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    read($Heap, this, _module.MyIntIter.__new)[$Box($o)]
         && !read(old($Heap), this, _module.MyIntIter.__new)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures !read($Heap, this, _module.MyIntIter.__new)[$Box(null)];
  free ensures more#0 ==> _module.MyIntIter.Valid#canCall($Heap, this);
  ensures more#0 ==> _module.MyIntIter.Valid($Heap, this);
  free ensures true;
  ensures Seq#Equal(read($Heap, this, _module.MyIntIter.xs), 
    (if more#0
       then Seq#Append(read(old($Heap), this, _module.MyIntIter.xs), 
        Seq#Build(Seq#Empty(): Seq Box, $Box(read($Heap, this, _module.MyIntIter.x))))
       else read(old($Heap), this, _module.MyIntIter.xs)));
  free ensures true;
  ensures Seq#Equal(read($Heap, this, _module.MyIntIter.ys), 
    (if more#0
       then Seq#Append(read(old($Heap), this, _module.MyIntIter.ys), 
        Seq#Build(Seq#Empty(): Seq Box, $Box(read($Heap, this, _module.MyIntIter.y))))
       else read(old($Heap), this, _module.MyIntIter.ys)));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || 
        $o == this
         || _module.MyIntIter.__modifies(this)[$Box($o)]
         || read(old($Heap), this, _module.MyIntIter.__new)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



// _module.MyIntIter: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.MyIntIter()) } 
  $Is(c#0, Tclass._module.MyIntIter())
     <==> $Is(c#0, Tclass._module.MyIntIter?()) && c#0 != null);

// _module.MyIntIter: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.MyIntIter(), $h) } 
  $IsAlloc(c#0, Tclass._module.MyIntIter(), $h)
     <==> $IsAlloc(c#0, Tclass._module.MyIntIter?(), $h));

procedure CheckWellformed$$_module.MyIntIter(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.MyIntIter())
         && $IsAlloc(this, Tclass._module.MyIntIter(), $Heap));
  free requires 54 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Impl$$_module.MyIntIter(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.MyIntIter())
         && $IsAlloc(this, Tclass._module.MyIntIter(), $Heap));
  free requires 54 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.MyIntIter(this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _yieldCount#0: int
     where _yieldCount#0 == Seq#Length(read($Heap, this, _module.MyIntIter.xs))
       && _yieldCount#0 == Seq#Length(read($Heap, this, _module.MyIntIter.ys));
  var $_OldIterHeap: Heap
     where $IsGoodHeap($_OldIterHeap) && $HeapSucc($_OldIterHeap, $Heap);
  var $obj0: ref;
  var $obj1: ref;
  var $rhs#0: int;
  var $rhs#1: int;
  var $rhs#2: int;
  var $rhs#3: int;
  var $rhs#4: int;
  var $rhs#5: int;

    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(8,9): initial state"} true;
    assume Seq#Equal(read($Heap, this, _module.MyIntIter.xs), Seq#Empty(): Seq Box);
    assume Seq#Equal(read($Heap, this, _module.MyIntIter.ys), Seq#Empty(): Seq Box);
    assume _module.MyIntIter.Valid($Heap, this);
    assume Set#Equal(_module.MyIntIter.__reads(this), Set#Empty(): Set Box);
    assume Set#Equal(_module.MyIntIter.__modifies(this), Set#Empty(): Set Box);
    assume Set#Equal(read($Heap, this, _module.MyIntIter.__new), Set#Empty(): Set Box);
    assume _yieldCount#0 == 0;
    call $YieldHavoc(this, _module.MyIntIter.__reads(this), read($Heap, this, _module.MyIntIter.__new));
    $_OldIterHeap := $Heap;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(10,8)
    assume true;
    $obj0 := this;
    assert $_Frame[$obj0, _module.MyIntIter.x];
    assume true;
    $obj1 := this;
    assert $_Frame[$obj1, _module.MyIntIter.y];
    assume true;
    $rhs#0 := LitInt(0);
    assume true;
    $rhs#1 := LitInt(0);
    $Heap := update($Heap, $obj0, _module.MyIntIter.x, $rhs#0);
    assume $IsGoodHeap($Heap);
    $Heap := update($Heap, $obj1, _module.MyIntIter.y, $rhs#1);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(10,14)"} true;
    // ----- yield statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(11,3)
    $Heap := update($Heap, 
      this, 
      _module.MyIntIter.xs, 
      Seq#Append(read($Heap, this, _module.MyIntIter.xs), 
        Seq#Build(Seq#Empty(): Seq Box, $Box(read($Heap, this, _module.MyIntIter.x)))));
    $Heap := update($Heap, 
      this, 
      _module.MyIntIter.ys, 
      Seq#Append(read($Heap, this, _module.MyIntIter.ys), 
        Seq#Build(Seq#Empty(): Seq Box, $Box(read($Heap, this, _module.MyIntIter.y)))));
    _yieldCount#0 := _yieldCount#0 + 1;
    assume _yieldCount#0 == Seq#Length(read($Heap, this, _module.MyIntIter.xs))
       && _yieldCount#0 == Seq#Length(read($Heap, this, _module.MyIntIter.ys));
    assume $IsGoodHeap($Heap);
    call $YieldHavoc(this, _module.MyIntIter.__reads(this), read($Heap, this, _module.MyIntIter.__new));
    $_OldIterHeap := $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(11,7)"} true;
    // ----- yield statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(12,3)
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(12,3)
    assume true;
    $obj0 := this;
    assert $_Frame[$obj0, _module.MyIntIter.x];
    assume true;
    $obj1 := this;
    assert $_Frame[$obj1, _module.MyIntIter.y];
    assume true;
    $rhs#2 := LitInt(2);
    assume true;
    $rhs#3 := LitInt(3);
    $Heap := update($Heap, $obj0, _module.MyIntIter.x, $rhs#2);
    assume $IsGoodHeap($Heap);
    $Heap := update($Heap, $obj1, _module.MyIntIter.y, $rhs#3);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(12,12)"} true;
    $Heap := update($Heap, 
      this, 
      _module.MyIntIter.xs, 
      Seq#Append(read($Heap, this, _module.MyIntIter.xs), 
        Seq#Build(Seq#Empty(): Seq Box, $Box(read($Heap, this, _module.MyIntIter.x)))));
    $Heap := update($Heap, 
      this, 
      _module.MyIntIter.ys, 
      Seq#Append(read($Heap, this, _module.MyIntIter.ys), 
        Seq#Build(Seq#Empty(): Seq Box, $Box(read($Heap, this, _module.MyIntIter.y)))));
    _yieldCount#0 := _yieldCount#0 + 1;
    assume _yieldCount#0 == Seq#Length(read($Heap, this, _module.MyIntIter.xs))
       && _yieldCount#0 == Seq#Length(read($Heap, this, _module.MyIntIter.ys));
    assume $IsGoodHeap($Heap);
    call $YieldHavoc(this, _module.MyIntIter.__reads(this), read($Heap, this, _module.MyIntIter.__new));
    $_OldIterHeap := $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(12,12)"} true;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(13,8)
    assume true;
    $obj0 := this;
    assert $_Frame[$obj0, _module.MyIntIter.x];
    assume true;
    $obj1 := this;
    assert $_Frame[$obj1, _module.MyIntIter.y];
    assume true;
    $rhs#4 := read($Heap, this, _module.MyIntIter.y);
    assume true;
    $rhs#5 := read($Heap, this, _module.MyIntIter.x);
    $Heap := update($Heap, $obj0, _module.MyIntIter.x, $rhs#4);
    assume $IsGoodHeap($Heap);
    $Heap := update($Heap, $obj1, _module.MyIntIter.y, $rhs#5);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(13,14)"} true;
    // ----- yield statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(14,3)
    $Heap := update($Heap, 
      this, 
      _module.MyIntIter.xs, 
      Seq#Append(read($Heap, this, _module.MyIntIter.xs), 
        Seq#Build(Seq#Empty(): Seq Box, $Box(read($Heap, this, _module.MyIntIter.x)))));
    $Heap := update($Heap, 
      this, 
      _module.MyIntIter.ys, 
      Seq#Append(read($Heap, this, _module.MyIntIter.ys), 
        Seq#Build(Seq#Empty(): Seq Box, $Box(read($Heap, this, _module.MyIntIter.y)))));
    _yieldCount#0 := _yieldCount#0 + 1;
    assume _yieldCount#0 == Seq#Length(read($Heap, this, _module.MyIntIter.xs))
       && _yieldCount#0 == Seq#Length(read($Heap, this, _module.MyIntIter.ys));
    assume $IsGoodHeap($Heap);
    call $YieldHavoc(this, _module.MyIntIter.__reads(this), read($Heap, this, _module.MyIntIter.__new));
    $_OldIterHeap := $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(14,7)"} true;
}



const unique class._module.Naturals?: ClassName;

function Tclass._module.Naturals?() : Ty;

const unique Tagclass._module.Naturals?: TyTag;

// Tclass._module.Naturals? Tag
axiom Tag(Tclass._module.Naturals?()) == Tagclass._module.Naturals?
   && TagFamily(Tclass._module.Naturals?()) == tytagFamily$Naturals;

// Box/unbox axiom for Tclass._module.Naturals?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Naturals?()) } 
  $IsBox(bx, Tclass._module.Naturals?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Naturals?()));

// Naturals: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.Naturals?()) } 
  $Is($o, Tclass._module.Naturals?())
     <==> $o == null || dtype($o) == Tclass._module.Naturals?());

// Naturals: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.Naturals?(), $h) } 
  $IsAlloc($o, Tclass._module.Naturals?(), $h)
     <==> $o == null || read($h, $o, alloc));

function _module.Naturals.u(ref) : int;

// Naturals.u: Type axiom
axiom (forall $o: ref :: 
  { _module.Naturals.u($o) } 
  $o != null && dtype($o) == Tclass._module.Naturals?()
     ==> $Is(_module.Naturals.u($o), TInt));

// Naturals.u: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.Naturals.u($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Naturals?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.Naturals.u($o), TInt, $h));

axiom FDim(_module.Naturals.n) == 0
   && FieldOfDecl(class._module.Naturals?, field$n) == _module.Naturals.n
   && !$IsGhostField(_module.Naturals.n);

const _module.Naturals.n: Field int;

// Naturals.n: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Naturals.n) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Naturals?()
     ==> $Is(read($h, $o, _module.Naturals.n), Tclass._System.nat()));

// Naturals.n: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Naturals.n) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Naturals?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Naturals.n), Tclass._System.nat(), $h));

axiom FDim(_module.Naturals.ns) == 0
   && FieldOfDecl(class._module.Naturals?, field$ns) == _module.Naturals.ns
   && $IsGhostField(_module.Naturals.ns);

const _module.Naturals.ns: Field (Seq Box);

// Naturals.ns: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Naturals.ns) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Naturals?()
     ==> $Is(read($h, $o, _module.Naturals.ns), TSeq(Tclass._System.nat())));

// Naturals.ns: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Naturals.ns) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Naturals?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Naturals.ns), TSeq(Tclass._System.nat()), $h));

function _module.Naturals.__reads(ref) : Set Box;

// Naturals._reads: Type axiom
axiom (forall $o: ref :: 
  { _module.Naturals.__reads($o) } 
  $o != null && dtype($o) == Tclass._module.Naturals?()
     ==> $Is(_module.Naturals.__reads($o), TSet(Tclass._System.object?())));

// Naturals._reads: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.Naturals.__reads($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Naturals?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.Naturals.__reads($o), TSet(Tclass._System.object?()), $h));

function _module.Naturals.__modifies(ref) : Set Box;

// Naturals._modifies: Type axiom
axiom (forall $o: ref :: 
  { _module.Naturals.__modifies($o) } 
  $o != null && dtype($o) == Tclass._module.Naturals?()
     ==> $Is(_module.Naturals.__modifies($o), TSet(Tclass._System.object?())));

// Naturals._modifies: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.Naturals.__modifies($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Naturals?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.Naturals.__modifies($o), TSet(Tclass._System.object?()), $h));

axiom FDim(_module.Naturals.__new) == 0
   && FieldOfDecl(class._module.Naturals?, field$_new) == _module.Naturals.__new
   && $IsGhostField(_module.Naturals.__new);

const _module.Naturals.__new: Field (Set Box);

// Naturals._new: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Naturals.__new) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Naturals?()
     ==> $Is(read($h, $o, _module.Naturals.__new), TSet(Tclass._System.object?())));

// Naturals._new: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Naturals.__new) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Naturals?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Naturals.__new), TSet(Tclass._System.object?()), $h));

function _module.Naturals.__decreases0(ref) : int;

// Naturals._decreases0: Type axiom
axiom (forall $o: ref :: 
  { _module.Naturals.__decreases0($o) } 
  $o != null && dtype($o) == Tclass._module.Naturals?()
     ==> $Is(_module.Naturals.__decreases0($o), TInt));

// Naturals._decreases0: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.Naturals.__decreases0($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Naturals?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.Naturals.__decreases0($o), TInt, $h));

function Tclass._module.Naturals() : Ty;

const unique Tagclass._module.Naturals: TyTag;

// Tclass._module.Naturals Tag
axiom Tag(Tclass._module.Naturals()) == Tagclass._module.Naturals
   && TagFamily(Tclass._module.Naturals()) == tytagFamily$Naturals;

// Box/unbox axiom for Tclass._module.Naturals
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Naturals()) } 
  $IsBox(bx, Tclass._module.Naturals())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Naturals()));

procedure CheckWellformed$$_module.Naturals.__ctor(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Naturals())
         && $IsAlloc(this, Tclass._module.Naturals(), $Heap), 
    u#0: int);
  free requires 14 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Naturals.__ctor(u#0: int)
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Naturals())
         && $IsAlloc(this, Tclass._module.Naturals(), $Heap));
  // user-defined preconditions
  requires u#0 < 25;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures _module.Naturals.u(this) == u#0;
  free ensures true;
  ensures Seq#Equal(read($Heap, this, _module.Naturals.ns), Seq#Empty(): Seq Box);
  free ensures _module.Naturals.Valid#canCall($Heap, this);
  ensures _module.Naturals.Valid($Heap, this);
  free ensures true;
  ensures Set#Equal(_module.Naturals.__reads(this), Set#Empty(): Set Box);
  free ensures true;
  ensures Set#Equal(_module.Naturals.__modifies(this), Set#Empty(): Set Box);
  free ensures true;
  ensures Set#Equal(read($Heap, this, _module.Naturals.__new), Set#Empty(): Set Box);
  free ensures true;
  ensures _module.Naturals.__decreases0(this) == u#0;
  // constructor allocates the object
  ensures !read(old($Heap), this, alloc);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



// function declaration for _module.Naturals.Valid
function _module.Naturals.Valid($heap: Heap, this: ref) : bool;

function _module.Naturals.Valid#canCall($heap: Heap, this: ref) : bool;

// frame axiom for _module.Naturals.Valid
axiom (forall $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.Naturals.Valid($h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.Naturals())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && (
            $o == this
             || _module.Naturals.__reads(this)[$Box($o)]
             || read($h0, this, _module.Naturals.__new)[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.Naturals.Valid($h0, this) == _module.Naturals.Valid($h1, this));

// consequence axiom for _module.Naturals.Valid
axiom 13 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref :: 
    { _module.Naturals.Valid($Heap, this) } 
    _module.Naturals.Valid#canCall($Heap, this)
         || (13 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.Naturals())
           && $IsAlloc(this, Tclass._module.Naturals(), $Heap))
       ==> true);

function _module.Naturals.Valid#requires(Heap, ref) : bool;

// #requires axiom for _module.Naturals.Valid
axiom (forall $Heap: Heap, this: ref :: 
  { _module.Naturals.Valid#requires($Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.Naturals())
       && $IsAlloc(this, Tclass._module.Naturals(), $Heap)
     ==> _module.Naturals.Valid#requires($Heap, this) == true);

procedure CheckWellformed$$_module.Naturals.Valid(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Naturals())
         && $IsAlloc(this, Tclass._module.Naturals(), $Heap));
  free requires 13 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Naturals.Valid(this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function Valid
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(17,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> $o == this
           || _module.Naturals.__reads(this)[$Box($o)]
           || read($Heap, this, _module.Naturals.__new)[$Box($o)]);
    b$reqreads#0 := $_Frame[this, _module.Naturals.__new];
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



procedure Call$$_module.Naturals.MoveNext(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Naturals())
         && $IsAlloc(this, Tclass._module.Naturals(), $Heap))
   returns (more#0: bool);
  // user-defined preconditions
  requires _module.Naturals.Valid($Heap, this);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    read($Heap, this, _module.Naturals.__new)[$Box($o)]
         && !read(old($Heap), this, _module.Naturals.__new)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures !read($Heap, this, _module.Naturals.__new)[$Box(null)];
  free ensures more#0 ==> _module.Naturals.Valid#canCall($Heap, this);
  ensures more#0 ==> _module.Naturals.Valid($Heap, this);
  free ensures true;
  ensures Seq#Equal(read($Heap, this, _module.Naturals.ns), 
    (if more#0
       then Seq#Append(read(old($Heap), this, _module.Naturals.ns), 
        Seq#Build(Seq#Empty(): Seq Box, $Box(read($Heap, this, _module.Naturals.n))))
       else read(old($Heap), this, _module.Naturals.ns)));
  free ensures true;
  ensures !more#0 ==> Lit(false);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || 
        $o == this
         || _module.Naturals.__modifies(this)[$Box($o)]
         || read(old($Heap), this, _module.Naturals.__new)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



// _module.Naturals: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.Naturals()) } 
  $Is(c#0, Tclass._module.Naturals())
     <==> $Is(c#0, Tclass._module.Naturals?()) && c#0 != null);

// _module.Naturals: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.Naturals(), $h) } 
  $IsAlloc(c#0, Tclass._module.Naturals(), $h)
     <==> $IsAlloc(c#0, Tclass._module.Naturals?(), $h));

procedure CheckWellformed$$_module.Naturals(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Naturals())
         && $IsAlloc(this, Tclass._module.Naturals(), $Heap), 
    u#0: int);
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Impl$$_module.Naturals(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Naturals())
         && $IsAlloc(this, Tclass._module.Naturals(), $Heap), 
    u#0: int);
  free requires 1 == $FunctionContextHeight;
  // user-defined preconditions
  requires u#0 < 25;
  modifies $Heap, $Tick;
  // user-defined postconditions
  ensures Lit(false);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Naturals(this: ref, u#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _yieldCount#0: int
     where _yieldCount#0 == Seq#Length(read($Heap, this, _module.Naturals.ns));
  var $_OldIterHeap: Heap
     where $IsGoodHeap($_OldIterHeap) && $HeapSucc($_OldIterHeap, $Heap);
  var $rhs#0: int where LitInt(0) <= $rhs#0;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var $decr$loop#00: int;
  var $rhs#0_0: int where LitInt(0) <= $rhs#0_0;
  var $rhs#0_1: int where LitInt(0) <= $rhs#0_1;

    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(17,9): initial state"} true;
    assume u#0 < 25;
    assume _module.Naturals.u(this) == u#0;
    assume Seq#Equal(read($Heap, this, _module.Naturals.ns), Seq#Empty(): Seq Box);
    assume _module.Naturals.Valid($Heap, this);
    assume Set#Equal(_module.Naturals.__reads(this), Set#Empty(): Set Box);
    assume Set#Equal(_module.Naturals.__modifies(this), Set#Empty(): Set Box);
    assume Set#Equal(read($Heap, this, _module.Naturals.__new), Set#Empty(): Set Box);
    assume _module.Naturals.__decreases0(this) == u#0;
    assume _yieldCount#0 == 0;
    call $YieldHavoc(this, _module.Naturals.__reads(this), read($Heap, this, _module.Naturals.__new));
    $_OldIterHeap := $Heap;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(21,5)
    assume true;
    assert $_Frame[this, _module.Naturals.n];
    assume true;
    assert $Is(LitInt(0), Tclass._System.nat());
    $rhs#0 := LitInt(0);
    $Heap := update($Heap, this, _module.Naturals.n, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(21,8)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(22,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := _yieldCount#0;
    havoc $w$loop#0;
    while (true)
      free invariant (forall $o: ref :: 
        { $Heap[$o] } 
        $o != null && read(old($Heap), $o, alloc)
           ==> $Heap[$o] == $PreLoopHeap$loop#0[$o] || $o == this);
      free invariant $HeapSucc($PreLoopHeap$loop#0, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
        { read($Heap, $o, $f) } 
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
      invariant (forall $o: ref :: 
        { read($Heap, this, _module.Naturals.__new)[$Box($o)] } 
        read($Heap, this, _module.Naturals.__new)[$Box($o)]
           ==> $o != null && !read(old($Heap), $o, alloc));
      free invariant _yieldCount#0 >= $decr_init$loop#00
         && (_yieldCount#0 == $decr_init$loop#00 ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(22,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assume true;
            assume false;
        }

        assume true;
        if (!Lit(true))
        {
            break;
        }

        $decr$loop#00 := _yieldCount#0;
        // ----- yield statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(24,5)
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(24,5)
        assume true;
        assert $_Frame[this, _module.Naturals.n];
        assume true;
        $rhs#0_0 := read($Heap, this, _module.Naturals.n);
        $Heap := update($Heap, this, _module.Naturals.n, $rhs#0_0);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(24,11)"} true;
        $Heap := update($Heap, 
          this, 
          _module.Naturals.ns, 
          Seq#Append(read($Heap, this, _module.Naturals.ns), 
            Seq#Build(Seq#Empty(): Seq Box, $Box(read($Heap, this, _module.Naturals.n)))));
        _yieldCount#0 := _yieldCount#0 + 1;
        assume _yieldCount#0 == Seq#Length(read($Heap, this, _module.Naturals.ns));
        assume $IsGoodHeap($Heap);
        call $YieldHavoc(this, _module.Naturals.__reads(this), read($Heap, this, _module.Naturals.__new));
        $_OldIterHeap := $Heap;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(24,11)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(25,7)
        assume true;
        assert $_Frame[this, _module.Naturals.n];
        assume true;
        assert $Is(read($Heap, this, _module.Naturals.n) + 1, Tclass._System.nat());
        $rhs#0_1 := read($Heap, this, _module.Naturals.n) + 1;
        $Heap := update($Heap, this, _module.Naturals.n, $rhs#0_1);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(25,14)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(22,3)
        assert _yieldCount#0 > $decr$loop#00;
    }
}



const unique class._module.Cell?: ClassName;

function Tclass._module.Cell?() : Ty;

const unique Tagclass._module.Cell?: TyTag;

// Tclass._module.Cell? Tag
axiom Tag(Tclass._module.Cell?()) == Tagclass._module.Cell?
   && TagFamily(Tclass._module.Cell?()) == tytagFamily$Cell;

// Box/unbox axiom for Tclass._module.Cell?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Cell?()) } 
  $IsBox(bx, Tclass._module.Cell?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Cell?()));

// Cell: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.Cell?()) } 
  $Is($o, Tclass._module.Cell?())
     <==> $o == null || dtype($o) == Tclass._module.Cell?());

// Cell: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.Cell?(), $h) } 
  $IsAlloc($o, Tclass._module.Cell?(), $h) <==> $o == null || read($h, $o, alloc));

axiom FDim(_module.Cell.data) == 0
   && FieldOfDecl(class._module.Cell?, field$data) == _module.Cell.data
   && !$IsGhostField(_module.Cell.data);

const _module.Cell.data: Field int;

// Cell.data: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Cell.data) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Cell?()
     ==> $Is(read($h, $o, _module.Cell.data), TInt));

// Cell.data: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Cell.data) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Cell?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Cell.data), TInt, $h));

function Tclass._module.Cell() : Ty;

const unique Tagclass._module.Cell: TyTag;

// Tclass._module.Cell Tag
axiom Tag(Tclass._module.Cell()) == Tagclass._module.Cell
   && TagFamily(Tclass._module.Cell()) == tytagFamily$Cell;

// Box/unbox axiom for Tclass._module.Cell
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Cell()) } 
  $IsBox(bx, Tclass._module.Cell())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Cell()));

// _module.Cell: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.Cell()) } 
  $Is(c#0, Tclass._module.Cell())
     <==> $Is(c#0, Tclass._module.Cell?()) && c#0 != null);

// _module.Cell: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.Cell(), $h) } 
  $IsAlloc(c#0, Tclass._module.Cell(), $h)
     <==> $IsAlloc(c#0, Tclass._module.Cell?(), $h));

const unique class._module.IterA?: ClassName;

function Tclass._module.IterA?() : Ty;

const unique Tagclass._module.IterA?: TyTag;

// Tclass._module.IterA? Tag
axiom Tag(Tclass._module.IterA?()) == Tagclass._module.IterA?
   && TagFamily(Tclass._module.IterA?()) == tytagFamily$IterA;

// Box/unbox axiom for Tclass._module.IterA?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.IterA?()) } 
  $IsBox(bx, Tclass._module.IterA?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.IterA?()));

// IterA: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.IterA?()) } 
  $Is($o, Tclass._module.IterA?())
     <==> $o == null || dtype($o) == Tclass._module.IterA?());

// IterA: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.IterA?(), $h) } 
  $IsAlloc($o, Tclass._module.IterA?(), $h) <==> $o == null || read($h, $o, alloc));

function _module.IterA.c(ref) : ref;

// IterA.c: Type axiom
axiom (forall $o: ref :: 
  { _module.IterA.c($o) } 
  $o != null && dtype($o) == Tclass._module.IterA?()
     ==> $Is(_module.IterA.c($o), Tclass._module.Cell?()));

// IterA.c: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.IterA.c($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.IterA?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.IterA.c($o), Tclass._module.Cell?(), $h));

function _module.IterA.__reads(ref) : Set Box;

// IterA._reads: Type axiom
axiom (forall $o: ref :: 
  { _module.IterA.__reads($o) } 
  $o != null && dtype($o) == Tclass._module.IterA?()
     ==> $Is(_module.IterA.__reads($o), TSet(Tclass._System.object?())));

// IterA._reads: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.IterA.__reads($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.IterA?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.IterA.__reads($o), TSet(Tclass._System.object?()), $h));

function _module.IterA.__modifies(ref) : Set Box;

// IterA._modifies: Type axiom
axiom (forall $o: ref :: 
  { _module.IterA.__modifies($o) } 
  $o != null && dtype($o) == Tclass._module.IterA?()
     ==> $Is(_module.IterA.__modifies($o), TSet(Tclass._System.object?())));

// IterA._modifies: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.IterA.__modifies($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.IterA?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.IterA.__modifies($o), TSet(Tclass._System.object?()), $h));

axiom FDim(_module.IterA.__new) == 0
   && FieldOfDecl(class._module.IterA?, field$_new) == _module.IterA.__new
   && $IsGhostField(_module.IterA.__new);

const _module.IterA.__new: Field (Set Box);

// IterA._new: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.IterA.__new) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.IterA?()
     ==> $Is(read($h, $o, _module.IterA.__new), TSet(Tclass._System.object?())));

// IterA._new: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.IterA.__new) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.IterA?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.IterA.__new), TSet(Tclass._System.object?()), $h));

function _module.IterA.__decreases0(ref) : ref;

// IterA._decreases0: Type axiom
axiom (forall $o: ref :: 
  { _module.IterA.__decreases0($o) } 
  $o != null && dtype($o) == Tclass._module.IterA?()
     ==> $Is(_module.IterA.__decreases0($o), Tclass._module.Cell?()));

// IterA._decreases0: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.IterA.__decreases0($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.IterA?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.IterA.__decreases0($o), Tclass._module.Cell?(), $h));

function Tclass._module.IterA() : Ty;

const unique Tagclass._module.IterA: TyTag;

// Tclass._module.IterA Tag
axiom Tag(Tclass._module.IterA()) == Tagclass._module.IterA
   && TagFamily(Tclass._module.IterA()) == tytagFamily$IterA;

// Box/unbox axiom for Tclass._module.IterA
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.IterA()) } 
  $IsBox(bx, Tclass._module.IterA())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.IterA()));

procedure CheckWellformed$$_module.IterA.__ctor(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.IterA())
         && $IsAlloc(this, Tclass._module.IterA(), $Heap), 
    c#0: ref
       where $Is(c#0, Tclass._module.Cell?()) && $IsAlloc(c#0, Tclass._module.Cell?(), $Heap));
  free requires 17 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.IterA.__ctor(c#0: ref
       where $Is(c#0, Tclass._module.Cell?()) && $IsAlloc(c#0, Tclass._module.Cell?(), $Heap))
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass._module.IterA())
         && $IsAlloc(this, Tclass._module.IterA(), $Heap));
  // user-defined preconditions
  requires c#0 != null;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures _module.IterA.c(this) == c#0;
  free ensures _module.IterA.Valid#canCall($Heap, this);
  ensures _module.IterA.Valid($Heap, this);
  free ensures true;
  ensures Set#Equal(_module.IterA.__reads(this), Set#Empty(): Set Box);
  free ensures true;
  ensures Set#Equal(_module.IterA.__modifies(this), Set#UnionOne(Set#Empty(): Set Box, $Box(c#0)));
  free ensures true;
  ensures Set#Equal(read($Heap, this, _module.IterA.__new), Set#Empty(): Set Box);
  free ensures true;
  ensures _module.IterA.__decreases0(this) == c#0;
  // constructor allocates the object
  ensures !read(old($Heap), this, alloc);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



// function declaration for _module.IterA.Valid
function _module.IterA.Valid($heap: Heap, this: ref) : bool;

function _module.IterA.Valid#canCall($heap: Heap, this: ref) : bool;

// frame axiom for _module.IterA.Valid
axiom (forall $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.IterA.Valid($h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.IterA())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && (
            $o == this
             || _module.IterA.__reads(this)[$Box($o)]
             || read($h0, this, _module.IterA.__new)[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.IterA.Valid($h0, this) == _module.IterA.Valid($h1, this));

// consequence axiom for _module.IterA.Valid
axiom 16 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref :: 
    { _module.IterA.Valid($Heap, this) } 
    _module.IterA.Valid#canCall($Heap, this)
         || (16 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.IterA())
           && $IsAlloc(this, Tclass._module.IterA(), $Heap))
       ==> true);

function _module.IterA.Valid#requires(Heap, ref) : bool;

// #requires axiom for _module.IterA.Valid
axiom (forall $Heap: Heap, this: ref :: 
  { _module.IterA.Valid#requires($Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.IterA())
       && $IsAlloc(this, Tclass._module.IterA(), $Heap)
     ==> _module.IterA.Valid#requires($Heap, this) == true);

procedure CheckWellformed$$_module.IterA.Valid(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.IterA())
         && $IsAlloc(this, Tclass._module.IterA(), $Heap));
  free requires 16 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.IterA.Valid(this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function Valid
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(73,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> $o == this
           || _module.IterA.__reads(this)[$Box($o)]
           || read($Heap, this, _module.IterA.__new)[$Box($o)]);
    b$reqreads#0 := $_Frame[this, _module.IterA.__new];
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



procedure Call$$_module.IterA.MoveNext(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.IterA())
         && $IsAlloc(this, Tclass._module.IterA(), $Heap))
   returns (more#0: bool);
  // user-defined preconditions
  requires _module.IterA.Valid($Heap, this);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    read($Heap, this, _module.IterA.__new)[$Box($o)]
         && !read(old($Heap), this, _module.IterA.__new)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures !read($Heap, this, _module.IterA.__new)[$Box(null)];
  free ensures more#0 ==> _module.IterA.Valid#canCall($Heap, this);
  ensures more#0 ==> _module.IterA.Valid($Heap, this);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || 
        $o == this
         || _module.IterA.__modifies(this)[$Box($o)]
         || read(old($Heap), this, _module.IterA.__new)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



// _module.IterA: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.IterA()) } 
  $Is(c#0, Tclass._module.IterA())
     <==> $Is(c#0, Tclass._module.IterA?()) && c#0 != null);

// _module.IterA: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.IterA(), $h) } 
  $IsAlloc(c#0, Tclass._module.IterA(), $h)
     <==> $IsAlloc(c#0, Tclass._module.IterA?(), $h));

procedure CheckWellformed$$_module.IterA(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.IterA())
         && $IsAlloc(this, Tclass._module.IterA(), $Heap), 
    c#0: ref
       where $Is(c#0, Tclass._module.Cell?()) && $IsAlloc(c#0, Tclass._module.Cell?(), $Heap));
  free requires 55 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Impl$$_module.IterA(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.IterA())
         && $IsAlloc(this, Tclass._module.IterA(), $Heap), 
    c#0: ref
       where $Is(c#0, Tclass._module.Cell?()) && $IsAlloc(c#0, Tclass._module.Cell?(), $Heap));
  free requires 55 == $FunctionContextHeight;
  // user-defined preconditions
  requires c#0 != null;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == c#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.IterA(this: ref, c#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _yieldCount#0: int where true;
  var $_OldIterHeap: Heap
     where $IsGoodHeap($_OldIterHeap) && $HeapSucc($_OldIterHeap, $Heap);
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var $decr$loop#00: int;
  var $rhs#0_0: int;

    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this || $o == c#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(73,9): initial state"} true;
    assume c#0 != null;
    assume _module.IterA.c(this) == c#0;
    assume _module.IterA.Valid($Heap, this);
    assume Set#Equal(_module.IterA.__reads(this), Set#Empty(): Set Box);
    assume Set#Equal(_module.IterA.__modifies(this), Set#UnionOne(Set#Empty(): Set Box, $Box(c#0)));
    assume Set#Equal(read($Heap, this, _module.IterA.__new), Set#Empty(): Set Box);
    assume _module.IterA.__decreases0(this) == c#0;
    assume _yieldCount#0 == 0;
    call $YieldHavoc(this, _module.IterA.__reads(this), read($Heap, this, _module.IterA.__new));
    $_OldIterHeap := $Heap;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(77,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := _yieldCount#0;
    havoc $w$loop#0;
    while (true)
      free invariant (forall $o: ref :: 
        { $Heap[$o] } 
        $o != null && read(old($Heap), $o, alloc)
           ==> $Heap[$o] == $PreLoopHeap$loop#0[$o] || $o == this || $o == c#0);
      free invariant $HeapSucc($PreLoopHeap$loop#0, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
        { read($Heap, $o, $f) } 
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
      invariant (forall $o: ref :: 
        { read($Heap, this, _module.IterA.__new)[$Box($o)] } 
        read($Heap, this, _module.IterA.__new)[$Box($o)]
           ==> $o != null && !read(old($Heap), $o, alloc));
      free invariant _yieldCount#0 >= $decr_init$loop#00
         && (_yieldCount#0 == $decr_init$loop#00 ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(77,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assume true;
            assume false;
        }

        assume true;
        if (!Lit(true))
        {
            break;
        }

        $decr$loop#00 := _yieldCount#0;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(78,12)
        assert _module.IterA.c(this) != null;
        assume true;
        assert $_Frame[_module.IterA.c(this), _module.Cell.data];
        havoc $rhs#0_0;
        $Heap := update($Heap, _module.IterA.c(this), _module.Cell.data, $rhs#0_0);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(78,15)"} true;
        // ----- yield statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(79,5)
        _yieldCount#0 := _yieldCount#0 + 1;
        assume true;
        assume $IsGoodHeap($Heap);
        call $YieldHavoc(this, _module.IterA.__reads(this), read($Heap, this, _module.IterA.__new));
        $_OldIterHeap := $Heap;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(79,9)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(77,3)
        assert _yieldCount#0 > $decr$loop#00;
    }
}



const unique class._module.IterB?: ClassName;

function Tclass._module.IterB?() : Ty;

const unique Tagclass._module.IterB?: TyTag;

// Tclass._module.IterB? Tag
axiom Tag(Tclass._module.IterB?()) == Tagclass._module.IterB?
   && TagFamily(Tclass._module.IterB?()) == tytagFamily$IterB;

// Box/unbox axiom for Tclass._module.IterB?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.IterB?()) } 
  $IsBox(bx, Tclass._module.IterB?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.IterB?()));

// IterB: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.IterB?()) } 
  $Is($o, Tclass._module.IterB?())
     <==> $o == null || dtype($o) == Tclass._module.IterB?());

// IterB: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.IterB?(), $h) } 
  $IsAlloc($o, Tclass._module.IterB?(), $h) <==> $o == null || read($h, $o, alloc));

function _module.IterB.c(ref) : ref;

// IterB.c: Type axiom
axiom (forall $o: ref :: 
  { _module.IterB.c($o) } 
  $o != null && dtype($o) == Tclass._module.IterB?()
     ==> $Is(_module.IterB.c($o), Tclass._module.Cell?()));

// IterB.c: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.IterB.c($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.IterB?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.IterB.c($o), Tclass._module.Cell?(), $h));

function _module.IterB.__reads(ref) : Set Box;

// IterB._reads: Type axiom
axiom (forall $o: ref :: 
  { _module.IterB.__reads($o) } 
  $o != null && dtype($o) == Tclass._module.IterB?()
     ==> $Is(_module.IterB.__reads($o), TSet(Tclass._System.object?())));

// IterB._reads: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.IterB.__reads($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.IterB?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.IterB.__reads($o), TSet(Tclass._System.object?()), $h));

function _module.IterB.__modifies(ref) : Set Box;

// IterB._modifies: Type axiom
axiom (forall $o: ref :: 
  { _module.IterB.__modifies($o) } 
  $o != null && dtype($o) == Tclass._module.IterB?()
     ==> $Is(_module.IterB.__modifies($o), TSet(Tclass._System.object?())));

// IterB._modifies: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.IterB.__modifies($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.IterB?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.IterB.__modifies($o), TSet(Tclass._System.object?()), $h));

axiom FDim(_module.IterB.__new) == 0
   && FieldOfDecl(class._module.IterB?, field$_new) == _module.IterB.__new
   && $IsGhostField(_module.IterB.__new);

const _module.IterB.__new: Field (Set Box);

// IterB._new: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.IterB.__new) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.IterB?()
     ==> $Is(read($h, $o, _module.IterB.__new), TSet(Tclass._System.object?())));

// IterB._new: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.IterB.__new) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.IterB?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.IterB.__new), TSet(Tclass._System.object?()), $h));

function _module.IterB.__decreases0(ref) : ref;

// IterB._decreases0: Type axiom
axiom (forall $o: ref :: 
  { _module.IterB.__decreases0($o) } 
  $o != null && dtype($o) == Tclass._module.IterB?()
     ==> $Is(_module.IterB.__decreases0($o), Tclass._module.Cell?()));

// IterB._decreases0: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.IterB.__decreases0($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.IterB?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.IterB.__decreases0($o), Tclass._module.Cell?(), $h));

function _module.IterB.__decreases1(ref) : bool;

// IterB._decreases1: Type axiom
axiom (forall $o: ref :: 
  { _module.IterB.__decreases1($o) } 
  $o != null && dtype($o) == Tclass._module.IterB?()
     ==> $Is(_module.IterB.__decreases1($o), TBool));

// IterB._decreases1: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.IterB.__decreases1($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.IterB?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.IterB.__decreases1($o), TBool, $h));

function _module.IterB.__decreases2(ref) : int;

// IterB._decreases2: Type axiom
axiom (forall $o: ref :: 
  { _module.IterB.__decreases2($o) } 
  $o != null && dtype($o) == Tclass._module.IterB?()
     ==> $Is(_module.IterB.__decreases2($o), TInt));

// IterB._decreases2: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.IterB.__decreases2($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.IterB?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.IterB.__decreases2($o), TInt, $h));

function Tclass._module.IterB() : Ty;

const unique Tagclass._module.IterB: TyTag;

// Tclass._module.IterB Tag
axiom Tag(Tclass._module.IterB()) == Tagclass._module.IterB
   && TagFamily(Tclass._module.IterB()) == tytagFamily$IterB;

// Box/unbox axiom for Tclass._module.IterB
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.IterB()) } 
  $IsBox(bx, Tclass._module.IterB())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.IterB()));

procedure CheckWellformed$$_module.IterB.__ctor(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.IterB())
         && $IsAlloc(this, Tclass._module.IterB(), $Heap), 
    c#0: ref
       where $Is(c#0, Tclass._module.Cell?()) && $IsAlloc(c#0, Tclass._module.Cell?(), $Heap));
  free requires 20 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.IterB.__ctor(this: ref, c#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: _ctor, CheckWellformed$$_module.IterB.__ctor
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(94,9): initial state"} true;
    assume c#0 != null;
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
    assume $HeapSucc(old($Heap), $Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(94,15): post-state"} true;
    assume _module.IterB.c(this) == c#0;
    assume _module.IterB.Valid#canCall($Heap, this);
    assume _module.IterB.Valid($Heap, this);
    assume Set#Equal(_module.IterB.__reads(this), Set#Empty(): Set Box);
    assume Set#Equal(_module.IterB.__modifies(this), Set#UnionOne(Set#Empty(): Set Box, $Box(c#0)));
    assume Set#Equal(read($Heap, this, _module.IterB.__new), Set#Empty(): Set Box);
    assume _module.IterB.__decreases0(this) == c#0;
    assume _module.IterB.__decreases1(this) == (c#0 != null);
    assert c#0 != null;
    assert $IsAlloc(c#0, Tclass._module.Cell?(), old($Heap));
    assume _module.IterB.__decreases2(this) == read(old($Heap), c#0, _module.Cell.data);
}



procedure Call$$_module.IterB.__ctor(c#0: ref
       where $Is(c#0, Tclass._module.Cell?()) && $IsAlloc(c#0, Tclass._module.Cell?(), $Heap))
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass._module.IterB())
         && $IsAlloc(this, Tclass._module.IterB(), $Heap));
  // user-defined preconditions
  requires c#0 != null;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures _module.IterB.c(this) == c#0;
  free ensures _module.IterB.Valid#canCall($Heap, this);
  ensures _module.IterB.Valid($Heap, this);
  free ensures true;
  ensures Set#Equal(_module.IterB.__reads(this), Set#Empty(): Set Box);
  free ensures true;
  ensures Set#Equal(_module.IterB.__modifies(this), Set#UnionOne(Set#Empty(): Set Box, $Box(c#0)));
  free ensures true;
  ensures Set#Equal(read($Heap, this, _module.IterB.__new), Set#Empty(): Set Box);
  free ensures true;
  ensures _module.IterB.__decreases0(this) == c#0;
  free ensures true;
  ensures _module.IterB.__decreases1(this) == (c#0 != null);
  free ensures true;
  ensures _module.IterB.__decreases2(this) == read(old($Heap), c#0, _module.Cell.data);
  // constructor allocates the object
  ensures !read(old($Heap), this, alloc);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



// function declaration for _module.IterB.Valid
function _module.IterB.Valid($heap: Heap, this: ref) : bool;

function _module.IterB.Valid#canCall($heap: Heap, this: ref) : bool;

// frame axiom for _module.IterB.Valid
axiom (forall $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.IterB.Valid($h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.IterB())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && (
            $o == this
             || _module.IterB.__reads(this)[$Box($o)]
             || read($h0, this, _module.IterB.__new)[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.IterB.Valid($h0, this) == _module.IterB.Valid($h1, this));

// consequence axiom for _module.IterB.Valid
axiom 19 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref :: 
    { _module.IterB.Valid($Heap, this) } 
    _module.IterB.Valid#canCall($Heap, this)
         || (19 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.IterB())
           && $IsAlloc(this, Tclass._module.IterB(), $Heap))
       ==> true);

function _module.IterB.Valid#requires(Heap, ref) : bool;

// #requires axiom for _module.IterB.Valid
axiom (forall $Heap: Heap, this: ref :: 
  { _module.IterB.Valid#requires($Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.IterB())
       && $IsAlloc(this, Tclass._module.IterB(), $Heap)
     ==> _module.IterB.Valid#requires($Heap, this) == true);

procedure CheckWellformed$$_module.IterB.Valid(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.IterB())
         && $IsAlloc(this, Tclass._module.IterB(), $Heap));
  free requires 19 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.IterB.Valid(this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function Valid
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(94,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> $o == this
           || _module.IterB.__reads(this)[$Box($o)]
           || read($Heap, this, _module.IterB.__new)[$Box($o)]);
    b$reqreads#0 := $_Frame[this, _module.IterB.__new];
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



procedure Call$$_module.IterB.MoveNext(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.IterB())
         && $IsAlloc(this, Tclass._module.IterB(), $Heap))
   returns (more#0: bool);
  // user-defined preconditions
  requires _module.IterB.Valid($Heap, this);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    read($Heap, this, _module.IterB.__new)[$Box($o)]
         && !read(old($Heap), this, _module.IterB.__new)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures !read($Heap, this, _module.IterB.__new)[$Box(null)];
  free ensures more#0 ==> _module.IterB.Valid#canCall($Heap, this);
  ensures more#0 ==> _module.IterB.Valid($Heap, this);
  free ensures true;
  ensures more#0
     ==> read($Heap, _module.IterB.c(this), _module.Cell.data)
       == read(old($Heap), _module.IterB.c(this), _module.Cell.data);
  free ensures true;
  ensures !more#0 ==> Lit(true);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || 
        $o == this
         || _module.IterB.__modifies(this)[$Box($o)]
         || read(old($Heap), this, _module.IterB.__new)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



// _module.IterB: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.IterB()) } 
  $Is(c#0, Tclass._module.IterB())
     <==> $Is(c#0, Tclass._module.IterB?()) && c#0 != null);

// _module.IterB: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.IterB(), $h) } 
  $IsAlloc(c#0, Tclass._module.IterB(), $h)
     <==> $IsAlloc(c#0, Tclass._module.IterB?(), $h));

procedure CheckWellformed$$_module.IterB(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.IterB())
         && $IsAlloc(this, Tclass._module.IterB(), $Heap), 
    c#0: ref
       where $Is(c#0, Tclass._module.Cell?()) && $IsAlloc(c#0, Tclass._module.Cell?(), $Heap));
  free requires 56 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.IterB(this: ref, c#0: ref)
{
  var $_OldIterHeap: Heap;

    assume c#0 != null;
    assert c#0 != null;
    assume _module.IterB.c(this) == c#0;
    assume _module.IterB.Valid($Heap, this);
    assume Set#Equal(_module.IterB.__reads(this), Set#Empty(): Set Box);
    assume Set#Equal(_module.IterB.__modifies(this), Set#UnionOne(Set#Empty(): Set Box, $Box(c#0)));
    assume Set#Equal(read($Heap, this, _module.IterB.__new), Set#Empty(): Set Box);
    assume _module.IterB.__decreases0(this) == c#0;
    assume _module.IterB.__decreases1(this) == (c#0 != null);
    assume _module.IterB.__decreases2(this) == read(old($Heap), c#0, _module.Cell.data);
    call $IterHavoc0(this, _module.IterB.__reads(this), _module.IterB.__modifies(this));
    assume _module.IterB.Valid($Heap, this);
    $_OldIterHeap := $Heap;
    call $IterHavoc1(this, _module.IterB.__modifies(this), read($Heap, this, _module.IterB.__new));
    assume (forall $o: ref :: 
      { read($_OldIterHeap, $o, alloc) } 
      read($Heap, this, _module.IterB.__new)[$Box($o)]
           && !read($_OldIterHeap, this, _module.IterB.__new)[$Box($o)]
         ==> $o != null && !read($_OldIterHeap, $o, alloc));
    if (*)
    {
        assume _module.IterB.Valid($Heap, this);
        assert _module.IterB.c(this) != null;
        assert _module.IterB.c(this) != null;
        assume read($Heap, _module.IterB.c(this), _module.Cell.data)
           == read($_OldIterHeap, _module.IterB.c(this), _module.Cell.data);
    }
    else
    {
        assume true;
    }
}



procedure Impl$$_module.IterB(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.IterB())
         && $IsAlloc(this, Tclass._module.IterB(), $Heap), 
    c#0: ref
       where $Is(c#0, Tclass._module.Cell?()) && $IsAlloc(c#0, Tclass._module.Cell?(), $Heap));
  free requires 56 == $FunctionContextHeight;
  // user-defined preconditions
  requires c#0 != null;
  modifies $Heap, $Tick;
  // user-defined postconditions
  ensures Lit(true);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == c#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.IterB(this: ref, c#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _yieldCount#0: int where true;
  var $_OldIterHeap: Heap
     where $IsGoodHeap($_OldIterHeap) && $HeapSucc($_OldIterHeap, $Heap);
  var tmp#0: int;
  var $rhs#0: int;

    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this || $o == c#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(94,9): initial state"} true;
    assume c#0 != null;
    assume _module.IterB.c(this) == c#0;
    assume _module.IterB.Valid($Heap, this);
    assume Set#Equal(_module.IterB.__reads(this), Set#Empty(): Set Box);
    assume Set#Equal(_module.IterB.__modifies(this), Set#UnionOne(Set#Empty(): Set Box, $Box(c#0)));
    assume Set#Equal(read($Heap, this, _module.IterB.__new), Set#Empty(): Set Box);
    assume _module.IterB.__decreases0(this) == c#0;
    assume _module.IterB.__decreases1(this) == (c#0 != null);
    assume _module.IterB.__decreases2(this) == read(old($Heap), c#0, _module.Cell.data);
    assume _yieldCount#0 == 0;
    call $YieldHavoc(this, _module.IterB.__reads(this), read($Heap, this, _module.IterB.__new));
    $_OldIterHeap := $Heap;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(101,3)
    assume true;
    assert _module.IterB.__decreases0(this) == _module.IterB.c(this);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(102,3)
    assume true;
    assert _module.IterB.__decreases1(this) == (_module.IterB.c(this) != null);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(103,3)
    assert {:subsumption 0} _module.IterB.c(this) != null;
    assume true;
    assert _module.IterB.__decreases2(this)
       == read($Heap, _module.IterB.c(this), _module.Cell.data);
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(104,11)
    assume true;
    assert _module.IterB.c(this) != null;
    assume true;
    tmp#0 := read($Heap, _module.IterB.c(this), _module.Cell.data);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(104,19)"} true;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(105,3)
    if (*)
    {
        // ----- yield statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(105,12)
        _yieldCount#0 := _yieldCount#0 + 1;
        assume true;
        assume $IsGoodHeap($Heap);
        assert {:subsumption 0} read($Heap, _module.IterB.c(this), _module.Cell.data)
           == read($_OldIterHeap, _module.IterB.c(this), _module.Cell.data);
        assume read($Heap, _module.IterB.c(this), _module.Cell.data)
           == read($_OldIterHeap, _module.IterB.c(this), _module.Cell.data);
        call $YieldHavoc(this, _module.IterB.__reads(this), read($Heap, this, _module.IterB.__new));
        $_OldIterHeap := $Heap;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(105,16)"} true;
    }
    else
    {
    }

    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(106,3)
    assert {:subsumption 0} _module.IterB.c(this) != null;
    assume true;
    assert tmp#0 == read($Heap, _module.IterB.c(this), _module.Cell.data);
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(107,10)
    assert _module.IterB.c(this) != null;
    assume true;
    assert $_Frame[_module.IterB.c(this), _module.Cell.data];
    havoc $rhs#0;
    $Heap := update($Heap, _module.IterB.c(this), _module.Cell.data, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(107,13)"} true;
}



const unique class._module.IterC?: ClassName;

function Tclass._module.IterC?() : Ty;

const unique Tagclass._module.IterC?: TyTag;

// Tclass._module.IterC? Tag
axiom Tag(Tclass._module.IterC?()) == Tagclass._module.IterC?
   && TagFamily(Tclass._module.IterC?()) == tytagFamily$IterC;

// Box/unbox axiom for Tclass._module.IterC?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.IterC?()) } 
  $IsBox(bx, Tclass._module.IterC?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.IterC?()));

// IterC: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.IterC?()) } 
  $Is($o, Tclass._module.IterC?())
     <==> $o == null || dtype($o) == Tclass._module.IterC?());

// IterC: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.IterC?(), $h) } 
  $IsAlloc($o, Tclass._module.IterC?(), $h) <==> $o == null || read($h, $o, alloc));

function _module.IterC.c(ref) : ref;

// IterC.c: Type axiom
axiom (forall $o: ref :: 
  { _module.IterC.c($o) } 
  $o != null && dtype($o) == Tclass._module.IterC?()
     ==> $Is(_module.IterC.c($o), Tclass._module.Cell?()));

// IterC.c: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.IterC.c($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.IterC?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.IterC.c($o), Tclass._module.Cell?(), $h));

function _module.IterC.__reads(ref) : Set Box;

// IterC._reads: Type axiom
axiom (forall $o: ref :: 
  { _module.IterC.__reads($o) } 
  $o != null && dtype($o) == Tclass._module.IterC?()
     ==> $Is(_module.IterC.__reads($o), TSet(Tclass._System.object?())));

// IterC._reads: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.IterC.__reads($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.IterC?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.IterC.__reads($o), TSet(Tclass._System.object?()), $h));

function _module.IterC.__modifies(ref) : Set Box;

// IterC._modifies: Type axiom
axiom (forall $o: ref :: 
  { _module.IterC.__modifies($o) } 
  $o != null && dtype($o) == Tclass._module.IterC?()
     ==> $Is(_module.IterC.__modifies($o), TSet(Tclass._System.object?())));

// IterC._modifies: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.IterC.__modifies($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.IterC?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.IterC.__modifies($o), TSet(Tclass._System.object?()), $h));

axiom FDim(_module.IterC.__new) == 0
   && FieldOfDecl(class._module.IterC?, field$_new) == _module.IterC.__new
   && $IsGhostField(_module.IterC.__new);

const _module.IterC.__new: Field (Set Box);

// IterC._new: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.IterC.__new) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.IterC?()
     ==> $Is(read($h, $o, _module.IterC.__new), TSet(Tclass._System.object?())));

// IterC._new: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.IterC.__new) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.IterC?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.IterC.__new), TSet(Tclass._System.object?()), $h));

function _module.IterC.__decreases0(ref) : ref;

// IterC._decreases0: Type axiom
axiom (forall $o: ref :: 
  { _module.IterC.__decreases0($o) } 
  $o != null && dtype($o) == Tclass._module.IterC?()
     ==> $Is(_module.IterC.__decreases0($o), Tclass._module.Cell?()));

// IterC._decreases0: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.IterC.__decreases0($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.IterC?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.IterC.__decreases0($o), Tclass._module.Cell?(), $h));

function _module.IterC.__decreases1(ref) : ref;

// IterC._decreases1: Type axiom
axiom (forall $o: ref :: 
  { _module.IterC.__decreases1($o) } 
  $o != null && dtype($o) == Tclass._module.IterC?()
     ==> $Is(_module.IterC.__decreases1($o), Tclass._module.Cell?()));

// IterC._decreases1: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.IterC.__decreases1($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.IterC?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.IterC.__decreases1($o), Tclass._module.Cell?(), $h));

function _module.IterC.__decreases2(ref) : int;

// IterC._decreases2: Type axiom
axiom (forall $o: ref :: 
  { _module.IterC.__decreases2($o) } 
  $o != null && dtype($o) == Tclass._module.IterC?()
     ==> $Is(_module.IterC.__decreases2($o), TInt));

// IterC._decreases2: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.IterC.__decreases2($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.IterC?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.IterC.__decreases2($o), TInt, $h));

function Tclass._module.IterC() : Ty;

const unique Tagclass._module.IterC: TyTag;

// Tclass._module.IterC Tag
axiom Tag(Tclass._module.IterC()) == Tagclass._module.IterC
   && TagFamily(Tclass._module.IterC()) == tytagFamily$IterC;

// Box/unbox axiom for Tclass._module.IterC
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.IterC()) } 
  $IsBox(bx, Tclass._module.IterC())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.IterC()));

procedure CheckWellformed$$_module.IterC.__ctor(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.IterC())
         && $IsAlloc(this, Tclass._module.IterC(), $Heap), 
    c#0: ref
       where $Is(c#0, Tclass._module.Cell?()) && $IsAlloc(c#0, Tclass._module.Cell?(), $Heap));
  free requires 23 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.IterC.__ctor(this: ref, c#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: _ctor, CheckWellformed$$_module.IterC.__ctor
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(125,9): initial state"} true;
    assume c#0 != null;
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
    assume $HeapSucc(old($Heap), $Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(125,15): post-state"} true;
    assume _module.IterC.c(this) == c#0;
    assume _module.IterC.Valid#canCall($Heap, this);
    assume _module.IterC.Valid($Heap, this);
    assume Set#Equal(_module.IterC.__reads(this), Set#UnionOne(Set#Empty(): Set Box, $Box(c#0)));
    assume Set#Equal(_module.IterC.__modifies(this), Set#UnionOne(Set#Empty(): Set Box, $Box(c#0)));
    assume Set#Equal(read($Heap, this, _module.IterC.__new), Set#Empty(): Set Box);
    assume _module.IterC.__decreases0(this) == c#0;
    assume _module.IterC.__decreases1(this) == c#0;
    assert c#0 != null;
    assert $IsAlloc(c#0, Tclass._module.Cell?(), old($Heap));
    assume _module.IterC.__decreases2(this) == read(old($Heap), c#0, _module.Cell.data);
}



procedure Call$$_module.IterC.__ctor(c#0: ref
       where $Is(c#0, Tclass._module.Cell?()) && $IsAlloc(c#0, Tclass._module.Cell?(), $Heap))
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass._module.IterC())
         && $IsAlloc(this, Tclass._module.IterC(), $Heap));
  // user-defined preconditions
  requires c#0 != null;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures _module.IterC.c(this) == c#0;
  free ensures _module.IterC.Valid#canCall($Heap, this);
  ensures _module.IterC.Valid($Heap, this);
  free ensures true;
  ensures Set#Equal(_module.IterC.__reads(this), Set#UnionOne(Set#Empty(): Set Box, $Box(c#0)));
  free ensures true;
  ensures Set#Equal(_module.IterC.__modifies(this), Set#UnionOne(Set#Empty(): Set Box, $Box(c#0)));
  free ensures true;
  ensures Set#Equal(read($Heap, this, _module.IterC.__new), Set#Empty(): Set Box);
  free ensures true;
  ensures _module.IterC.__decreases0(this) == c#0;
  free ensures true;
  ensures _module.IterC.__decreases1(this) == c#0;
  free ensures true;
  ensures _module.IterC.__decreases2(this) == read(old($Heap), c#0, _module.Cell.data);
  // constructor allocates the object
  ensures !read(old($Heap), this, alloc);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



// function declaration for _module.IterC.Valid
function _module.IterC.Valid($heap: Heap, this: ref) : bool;

function _module.IterC.Valid#canCall($heap: Heap, this: ref) : bool;

// frame axiom for _module.IterC.Valid
axiom (forall $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.IterC.Valid($h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.IterC())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && (
            $o == this
             || _module.IterC.__reads(this)[$Box($o)]
             || read($h0, this, _module.IterC.__new)[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.IterC.Valid($h0, this) == _module.IterC.Valid($h1, this));

// consequence axiom for _module.IterC.Valid
axiom 22 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref :: 
    { _module.IterC.Valid($Heap, this) } 
    _module.IterC.Valid#canCall($Heap, this)
         || (22 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.IterC())
           && $IsAlloc(this, Tclass._module.IterC(), $Heap))
       ==> true);

function _module.IterC.Valid#requires(Heap, ref) : bool;

// #requires axiom for _module.IterC.Valid
axiom (forall $Heap: Heap, this: ref :: 
  { _module.IterC.Valid#requires($Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.IterC())
       && $IsAlloc(this, Tclass._module.IterC(), $Heap)
     ==> _module.IterC.Valid#requires($Heap, this) == true);

procedure CheckWellformed$$_module.IterC.Valid(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.IterC())
         && $IsAlloc(this, Tclass._module.IterC(), $Heap));
  free requires 22 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.IterC.Valid(this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function Valid
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(125,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> $o == this
           || _module.IterC.__reads(this)[$Box($o)]
           || read($Heap, this, _module.IterC.__new)[$Box($o)]);
    b$reqreads#0 := $_Frame[this, _module.IterC.__new];
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



procedure Call$$_module.IterC.MoveNext(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.IterC())
         && $IsAlloc(this, Tclass._module.IterC(), $Heap))
   returns (more#0: bool);
  // user-defined preconditions
  requires _module.IterC.Valid($Heap, this);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    read($Heap, this, _module.IterC.__new)[$Box($o)]
         && !read(old($Heap), this, _module.IterC.__new)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures !read($Heap, this, _module.IterC.__new)[$Box(null)];
  free ensures more#0 ==> _module.IterC.Valid#canCall($Heap, this);
  ensures more#0 ==> _module.IterC.Valid($Heap, this);
  free ensures true;
  ensures more#0
     ==> read($Heap, _module.IterC.c(this), _module.Cell.data)
       == read(old($Heap), _module.IterC.c(this), _module.Cell.data);
  free ensures true;
  ensures !more#0 ==> Lit(true);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || 
        $o == this
         || _module.IterC.__modifies(this)[$Box($o)]
         || read(old($Heap), this, _module.IterC.__new)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



// _module.IterC: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.IterC()) } 
  $Is(c#0, Tclass._module.IterC())
     <==> $Is(c#0, Tclass._module.IterC?()) && c#0 != null);

// _module.IterC: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.IterC(), $h) } 
  $IsAlloc(c#0, Tclass._module.IterC(), $h)
     <==> $IsAlloc(c#0, Tclass._module.IterC?(), $h));

procedure CheckWellformed$$_module.IterC(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.IterC())
         && $IsAlloc(this, Tclass._module.IterC(), $Heap), 
    c#0: ref
       where $Is(c#0, Tclass._module.Cell?()) && $IsAlloc(c#0, Tclass._module.Cell?(), $Heap));
  free requires 57 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.IterC(this: ref, c#0: ref)
{
  var $_OldIterHeap: Heap;

    assume c#0 != null;
    assert c#0 != null;
    assume _module.IterC.c(this) == c#0;
    assume _module.IterC.Valid($Heap, this);
    assume Set#Equal(_module.IterC.__reads(this), Set#UnionOne(Set#Empty(): Set Box, $Box(c#0)));
    assume Set#Equal(_module.IterC.__modifies(this), Set#UnionOne(Set#Empty(): Set Box, $Box(c#0)));
    assume Set#Equal(read($Heap, this, _module.IterC.__new), Set#Empty(): Set Box);
    assume _module.IterC.__decreases0(this) == c#0;
    assume _module.IterC.__decreases1(this) == c#0;
    assume _module.IterC.__decreases2(this) == read(old($Heap), c#0, _module.Cell.data);
    call $IterHavoc0(this, _module.IterC.__reads(this), _module.IterC.__modifies(this));
    assume _module.IterC.Valid($Heap, this);
    $_OldIterHeap := $Heap;
    call $IterHavoc1(this, _module.IterC.__modifies(this), read($Heap, this, _module.IterC.__new));
    assume (forall $o: ref :: 
      { read($_OldIterHeap, $o, alloc) } 
      read($Heap, this, _module.IterC.__new)[$Box($o)]
           && !read($_OldIterHeap, this, _module.IterC.__new)[$Box($o)]
         ==> $o != null && !read($_OldIterHeap, $o, alloc));
    if (*)
    {
        assume _module.IterC.Valid($Heap, this);
        assert _module.IterC.c(this) != null;
        assert _module.IterC.c(this) != null;
        assume read($Heap, _module.IterC.c(this), _module.Cell.data)
           == read($_OldIterHeap, _module.IterC.c(this), _module.Cell.data);
    }
    else
    {
        assume true;
    }
}



procedure Impl$$_module.IterC(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.IterC())
         && $IsAlloc(this, Tclass._module.IterC(), $Heap), 
    c#0: ref
       where $Is(c#0, Tclass._module.Cell?()) && $IsAlloc(c#0, Tclass._module.Cell?(), $Heap));
  free requires 57 == $FunctionContextHeight;
  // user-defined preconditions
  requires c#0 != null;
  modifies $Heap, $Tick;
  // user-defined postconditions
  ensures Lit(true);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == c#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.IterC(this: ref, c#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _yieldCount#0: int where true;
  var $_OldIterHeap: Heap
     where $IsGoodHeap($_OldIterHeap) && $HeapSucc($_OldIterHeap, $Heap);
  var tmp#0: int;
  var $rhs#0: int;

    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this || $o == c#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(125,9): initial state"} true;
    assume c#0 != null;
    assume _module.IterC.c(this) == c#0;
    assume _module.IterC.Valid($Heap, this);
    assume Set#Equal(_module.IterC.__reads(this), Set#UnionOne(Set#Empty(): Set Box, $Box(c#0)));
    assume Set#Equal(_module.IterC.__modifies(this), Set#UnionOne(Set#Empty(): Set Box, $Box(c#0)));
    assume Set#Equal(read($Heap, this, _module.IterC.__new), Set#Empty(): Set Box);
    assume _module.IterC.__decreases0(this) == c#0;
    assume _module.IterC.__decreases1(this) == c#0;
    assume _module.IterC.__decreases2(this) == read(old($Heap), c#0, _module.Cell.data);
    assume _yieldCount#0 == 0;
    call $YieldHavoc(this, _module.IterC.__reads(this), read($Heap, this, _module.IterC.__new));
    $_OldIterHeap := $Heap;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(133,3)
    assert {:subsumption 0} _module.IterC.c(this) != null;
    assume true;
    assert _module.IterC.__decreases2(this)
       == read($Heap, _module.IterC.c(this), _module.Cell.data);
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(134,11)
    assume true;
    assert _module.IterC.c(this) != null;
    assume true;
    tmp#0 := read($Heap, _module.IterC.c(this), _module.Cell.data);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(134,19)"} true;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(135,3)
    if (*)
    {
        // ----- yield statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(135,12)
        _yieldCount#0 := _yieldCount#0 + 1;
        assume true;
        assume $IsGoodHeap($Heap);
        assert {:subsumption 0} read($Heap, _module.IterC.c(this), _module.Cell.data)
           == read($_OldIterHeap, _module.IterC.c(this), _module.Cell.data);
        assume read($Heap, _module.IterC.c(this), _module.Cell.data)
           == read($_OldIterHeap, _module.IterC.c(this), _module.Cell.data);
        call $YieldHavoc(this, _module.IterC.__reads(this), read($Heap, this, _module.IterC.__new));
        $_OldIterHeap := $Heap;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(135,16)"} true;
    }
    else
    {
    }

    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(136,3)
    if (*)
    {
        // ----- yield statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(136,12)
        _yieldCount#0 := _yieldCount#0 + 1;
        assume true;
        assume $IsGoodHeap($Heap);
        assert {:subsumption 0} read($Heap, _module.IterC.c(this), _module.Cell.data)
           == read($_OldIterHeap, _module.IterC.c(this), _module.Cell.data);
        assume read($Heap, _module.IterC.c(this), _module.Cell.data)
           == read($_OldIterHeap, _module.IterC.c(this), _module.Cell.data);
        call $YieldHavoc(this, _module.IterC.__reads(this), read($Heap, this, _module.IterC.__new));
        $_OldIterHeap := $Heap;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(136,16)"} true;
    }
    else
    {
    }

    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(137,3)
    assert {:subsumption 0} _module.IterC.c(this) != null;
    assume true;
    assert tmp#0 == read($Heap, _module.IterC.c(this), _module.Cell.data);
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(138,10)
    assert _module.IterC.c(this) != null;
    assume true;
    assert $_Frame[_module.IterC.c(this), _module.Cell.data];
    havoc $rhs#0;
    $Heap := update($Heap, _module.IterC.c(this), _module.Cell.data, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(138,13)"} true;
}



const unique class._module.AllocationIterator?: ClassName;

function Tclass._module.AllocationIterator?() : Ty;

const unique Tagclass._module.AllocationIterator?: TyTag;

// Tclass._module.AllocationIterator? Tag
axiom Tag(Tclass._module.AllocationIterator?())
     == Tagclass._module.AllocationIterator?
   && TagFamily(Tclass._module.AllocationIterator?())
     == tytagFamily$AllocationIterator;

// Box/unbox axiom for Tclass._module.AllocationIterator?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.AllocationIterator?()) } 
  $IsBox(bx, Tclass._module.AllocationIterator?())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.AllocationIterator?()));

// AllocationIterator: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.AllocationIterator?()) } 
  $Is($o, Tclass._module.AllocationIterator?())
     <==> $o == null || dtype($o) == Tclass._module.AllocationIterator?());

// AllocationIterator: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.AllocationIterator?(), $h) } 
  $IsAlloc($o, Tclass._module.AllocationIterator?(), $h)
     <==> $o == null || read($h, $o, alloc));

function _module.AllocationIterator.x(ref) : ref;

// AllocationIterator.x: Type axiom
axiom (forall $o: ref :: 
  { _module.AllocationIterator.x($o) } 
  $o != null && dtype($o) == Tclass._module.AllocationIterator?()
     ==> $Is(_module.AllocationIterator.x($o), Tclass._module.Cell?()));

// AllocationIterator.x: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.AllocationIterator.x($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.AllocationIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.AllocationIterator.x($o), Tclass._module.Cell?(), $h));

function _module.AllocationIterator.__reads(ref) : Set Box;

// AllocationIterator._reads: Type axiom
axiom (forall $o: ref :: 
  { _module.AllocationIterator.__reads($o) } 
  $o != null && dtype($o) == Tclass._module.AllocationIterator?()
     ==> $Is(_module.AllocationIterator.__reads($o), TSet(Tclass._System.object?())));

// AllocationIterator._reads: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.AllocationIterator.__reads($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.AllocationIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.AllocationIterator.__reads($o), TSet(Tclass._System.object?()), $h));

function _module.AllocationIterator.__modifies(ref) : Set Box;

// AllocationIterator._modifies: Type axiom
axiom (forall $o: ref :: 
  { _module.AllocationIterator.__modifies($o) } 
  $o != null && dtype($o) == Tclass._module.AllocationIterator?()
     ==> $Is(_module.AllocationIterator.__modifies($o), TSet(Tclass._System.object?())));

// AllocationIterator._modifies: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.AllocationIterator.__modifies($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.AllocationIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.AllocationIterator.__modifies($o), TSet(Tclass._System.object?()), $h));

axiom FDim(_module.AllocationIterator.__new) == 0
   && FieldOfDecl(class._module.AllocationIterator?, field$_new)
     == _module.AllocationIterator.__new
   && $IsGhostField(_module.AllocationIterator.__new);

const _module.AllocationIterator.__new: Field (Set Box);

// AllocationIterator._new: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.AllocationIterator.__new) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.AllocationIterator?()
     ==> $Is(read($h, $o, _module.AllocationIterator.__new), TSet(Tclass._System.object?())));

// AllocationIterator._new: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.AllocationIterator.__new) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.AllocationIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.AllocationIterator.__new), 
      TSet(Tclass._System.object?()), 
      $h));

function _module.AllocationIterator.__decreases0(ref) : ref;

// AllocationIterator._decreases0: Type axiom
axiom (forall $o: ref :: 
  { _module.AllocationIterator.__decreases0($o) } 
  $o != null && dtype($o) == Tclass._module.AllocationIterator?()
     ==> $Is(_module.AllocationIterator.__decreases0($o), Tclass._module.Cell?()));

// AllocationIterator._decreases0: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.AllocationIterator.__decreases0($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.AllocationIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.AllocationIterator.__decreases0($o), Tclass._module.Cell?(), $h));

function Tclass._module.AllocationIterator() : Ty;

const unique Tagclass._module.AllocationIterator: TyTag;

// Tclass._module.AllocationIterator Tag
axiom Tag(Tclass._module.AllocationIterator()) == Tagclass._module.AllocationIterator
   && TagFamily(Tclass._module.AllocationIterator()) == tytagFamily$AllocationIterator;

// Box/unbox axiom for Tclass._module.AllocationIterator
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.AllocationIterator()) } 
  $IsBox(bx, Tclass._module.AllocationIterator())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.AllocationIterator()));

procedure CheckWellformed$$_module.AllocationIterator.__ctor(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AllocationIterator())
         && $IsAlloc(this, Tclass._module.AllocationIterator(), $Heap), 
    x#0: ref
       where $Is(x#0, Tclass._module.Cell?()) && $IsAlloc(x#0, Tclass._module.Cell?(), $Heap));
  free requires 30 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.AllocationIterator.__ctor(x#0: ref
       where $Is(x#0, Tclass._module.Cell?()) && $IsAlloc(x#0, Tclass._module.Cell?(), $Heap))
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AllocationIterator())
         && $IsAlloc(this, Tclass._module.AllocationIterator(), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures _module.AllocationIterator.x(this) == x#0;
  free ensures _module.AllocationIterator.Valid#canCall($Heap, this);
  ensures _module.AllocationIterator.Valid($Heap, this);
  free ensures true;
  ensures Set#Equal(_module.AllocationIterator.__reads(this), Set#Empty(): Set Box);
  free ensures true;
  ensures Set#Equal(_module.AllocationIterator.__modifies(this), Set#Empty(): Set Box);
  free ensures true;
  ensures Set#Equal(read($Heap, this, _module.AllocationIterator.__new), Set#Empty(): Set Box);
  free ensures true;
  ensures _module.AllocationIterator.__decreases0(this) == x#0;
  // constructor allocates the object
  ensures !read(old($Heap), this, alloc);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



// function declaration for _module.AllocationIterator.Valid
function _module.AllocationIterator.Valid($heap: Heap, this: ref) : bool;

function _module.AllocationIterator.Valid#canCall($heap: Heap, this: ref) : bool;

// frame axiom for _module.AllocationIterator.Valid
axiom (forall $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.AllocationIterator.Valid($h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.AllocationIterator())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && (
            $o == this
             || _module.AllocationIterator.__reads(this)[$Box($o)]
             || read($h0, this, _module.AllocationIterator.__new)[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.AllocationIterator.Valid($h0, this)
       == _module.AllocationIterator.Valid($h1, this));

// consequence axiom for _module.AllocationIterator.Valid
axiom 28 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref :: 
    { _module.AllocationIterator.Valid($Heap, this) } 
    _module.AllocationIterator.Valid#canCall($Heap, this)
         || (28 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.AllocationIterator())
           && $IsAlloc(this, Tclass._module.AllocationIterator(), $Heap))
       ==> true);

function _module.AllocationIterator.Valid#requires(Heap, ref) : bool;

// #requires axiom for _module.AllocationIterator.Valid
axiom (forall $Heap: Heap, this: ref :: 
  { _module.AllocationIterator.Valid#requires($Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.AllocationIterator())
       && $IsAlloc(this, Tclass._module.AllocationIterator(), $Heap)
     ==> _module.AllocationIterator.Valid#requires($Heap, this) == true);

procedure CheckWellformed$$_module.AllocationIterator.Valid(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AllocationIterator())
         && $IsAlloc(this, Tclass._module.AllocationIterator(), $Heap));
  free requires 28 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.AllocationIterator.Valid(this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function Valid
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(160,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> $o == this
           || _module.AllocationIterator.__reads(this)[$Box($o)]
           || read($Heap, this, _module.AllocationIterator.__new)[$Box($o)]);
    b$reqreads#0 := $_Frame[this, _module.AllocationIterator.__new];
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



procedure Call$$_module.AllocationIterator.MoveNext(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AllocationIterator())
         && $IsAlloc(this, Tclass._module.AllocationIterator(), $Heap))
   returns (more#0: bool);
  // user-defined preconditions
  requires _module.AllocationIterator.Valid($Heap, this);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    read($Heap, this, _module.AllocationIterator.__new)[$Box($o)]
         && !read(old($Heap), this, _module.AllocationIterator.__new)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures !read($Heap, this, _module.AllocationIterator.__new)[$Box(null)];
  free ensures more#0 ==> _module.AllocationIterator.Valid#canCall($Heap, this);
  ensures more#0 ==> _module.AllocationIterator.Valid($Heap, this);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || 
        $o == this
         || _module.AllocationIterator.__modifies(this)[$Box($o)]
         || read(old($Heap), this, _module.AllocationIterator.__new)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



// _module.AllocationIterator: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.AllocationIterator()) } 
  $Is(c#0, Tclass._module.AllocationIterator())
     <==> $Is(c#0, Tclass._module.AllocationIterator?()) && c#0 != null);

// _module.AllocationIterator: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.AllocationIterator(), $h) } 
  $IsAlloc(c#0, Tclass._module.AllocationIterator(), $h)
     <==> $IsAlloc(c#0, Tclass._module.AllocationIterator?(), $h));

procedure CheckWellformed$$_module.AllocationIterator(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AllocationIterator())
         && $IsAlloc(this, Tclass._module.AllocationIterator(), $Heap), 
    x#0: ref
       where $Is(x#0, Tclass._module.Cell?()) && $IsAlloc(x#0, Tclass._module.Cell?(), $Heap));
  free requires 25 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Impl$$_module.AllocationIterator(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AllocationIterator())
         && $IsAlloc(this, Tclass._module.AllocationIterator(), $Heap), 
    x#0: ref
       where $Is(x#0, Tclass._module.Cell?()) && $IsAlloc(x#0, Tclass._module.Cell?(), $Heap));
  free requires 25 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.AllocationIterator(this: ref, x#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _yieldCount#0: int where true;
  var $_OldIterHeap: Heap
     where $IsGoodHeap($_OldIterHeap) && $HeapSucc($_OldIterHeap, $Heap);
  var h#0: ref
     where $Is(h#0, Tclass._module.Cell()) && $IsAlloc(h#0, Tclass._module.Cell(), $Heap);
  var $nw: ref;
  var $initHeapCallStmt#0: Heap;
  var $iter_newUpdate0: Set Box;
  var saveNew#0: Set Box
     where $Is(saveNew#0, TSet(Tclass._System.object?()))
       && $IsAlloc(saveNew#0, TSet(Tclass._System.object?()), $Heap);
  var u#0: ref
     where $Is(u#0, Tclass._module.Cell?()) && $IsAlloc(u#0, Tclass._module.Cell?(), $Heap);
  var v#0: ref
     where $Is(v#0, Tclass._module.Cell?()) && $IsAlloc(v#0, Tclass._module.Cell?(), $Heap);
  var $rhs##0: ref
     where $Is($rhs##0, Tclass._module.Cell?())
       && $IsAlloc($rhs##0, Tclass._module.Cell?(), $Heap);
  var $rhs##1: ref
     where $Is($rhs##1, Tclass._module.Cell?())
       && $IsAlloc($rhs##1, Tclass._module.Cell?(), $Heap);
  var $initHeapCallStmt#1: Heap;
  var $iter_newUpdate1: Set Box;

    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(160,9): initial state"} true;
    assume _module.AllocationIterator.x(this) == x#0;
    assume _module.AllocationIterator.Valid($Heap, this);
    assume Set#Equal(_module.AllocationIterator.__reads(this), Set#Empty(): Set Box);
    assume Set#Equal(_module.AllocationIterator.__modifies(this), Set#Empty(): Set Box);
    assume Set#Equal(read($Heap, this, _module.AllocationIterator.__new), Set#Empty(): Set Box);
    assume _module.AllocationIterator.__decreases0(this) == x#0;
    assume _yieldCount#0 == 0;
    call $YieldHavoc(this, _module.AllocationIterator.__reads(this), read($Heap, this, _module.AllocationIterator.__new));
    $_OldIterHeap := $Heap;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(162,3)
    assume true;
    assert Set#Equal(read($Heap, this, _module.AllocationIterator.__new), Set#Empty(): Set Box);
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(163,9)
    assume true;
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._module.Cell?();
    assume !read($Heap, $nw, alloc);
    $Heap := update($Heap, $nw, alloc, true);
    $Heap := update($Heap, 
      this, 
      _module.AllocationIterator.__new, 
      Set#UnionOne(read($Heap, this, _module.AllocationIterator.__new), $Box($nw)));
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    h#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(163,19)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(164,3)
    assume true;
    assert Set#Equal(read($Heap, this, _module.AllocationIterator.__new), 
      Set#UnionOne(Set#Empty(): Set Box, $Box(h#0)));
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(166,13)
    $initHeapCallStmt#0 := $Heap;
    // TrCallStmt: Before ProcessCallStmt
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.SomeMethod();
    // TrCallStmt: After ProcessCallStmt
    call $iter_newUpdate0 := $IterCollectNewObjects($initHeapCallStmt#0, $Heap, this, _module.AllocationIterator.__new);
    $Heap := update($Heap, this, _module.AllocationIterator.__new, $iter_newUpdate0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(166,14)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(167,3)
    assume true;
    assert !read($Heap, this, _module.AllocationIterator.__new)[$Box(_module.AllocationIterator.x(this))];
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(168,3)
    assume true;
    assert !read($Heap, this, _module.AllocationIterator.__new)[$Box(null)];
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(169,3)
    assume true;
    assert read($Heap, this, _module.AllocationIterator.__new)[$Box(h#0)];
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(171,21)
    assume true;
    assume true;
    saveNew#0 := read($Heap, this, _module.AllocationIterator.__new);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(171,27)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(172,28)
    assume true;
    assume true;
    // TrCallStmt: Adding lhs with type Cell?
    // TrCallStmt: Adding lhs with type Cell?
    $initHeapCallStmt#1 := $Heap;
    // TrCallStmt: Before ProcessCallStmt
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0, $rhs##1 := Call$$_module.__default.AnotherMethod();
    // TrCallStmt: After ProcessCallStmt
    u#0 := $rhs##0;
    v#0 := $rhs##1;
    call $iter_newUpdate1 := $IterCollectNewObjects($initHeapCallStmt#1, $Heap, this, _module.AllocationIterator.__new);
    $Heap := update($Heap, this, _module.AllocationIterator.__new, $iter_newUpdate1);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(172,29)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(173,3)
    assume true;
    assert read($Heap, this, _module.AllocationIterator.__new)[$Box(u#0)];
    // ----- alternative statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(174,3)
    if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(175,19)
        if (read($Heap, this, _module.AllocationIterator.__new)[$Box(v#0)]
           && !saveNew#0[$Box(v#0)])
        {
            if (v#0 != null)
            {
            }
        }

        assume true;
        assert {:subsumption 0} read($Heap, this, _module.AllocationIterator.__new)[$Box(v#0)]
             && !saveNew#0[$Box(v#0)]
           ==> v#0 != null;
        assert {:subsumption 0} read($Heap, this, _module.AllocationIterator.__new)[$Box(v#0)]
             && !saveNew#0[$Box(v#0)]
           ==> v#0 != null && !read(old($Heap), v#0, alloc);
        assume read($Heap, this, _module.AllocationIterator.__new)[$Box(v#0)]
             && !saveNew#0[$Box(v#0)]
           ==> v#0 != null && v#0 != null && !read(old($Heap), v#0, alloc);
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(176,19)
        if (!(v#0 != null && !read(old($Heap), v#0, alloc)))
        {
        }

        assume true;
        assert {:subsumption 0} !(v#0 != null && !read(old($Heap), v#0, alloc))
           ==> !read($Heap, this, _module.AllocationIterator.__new)[$Box(v#0)];
        assume !(v#0 != null && !read(old($Heap), v#0, alloc))
           ==> !read($Heap, this, _module.AllocationIterator.__new)[$Box(v#0)];
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(177,19)
        assume true;
        assert read($Heap, this, _module.AllocationIterator.__new)[$Box(v#0)];
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



const unique class._module.DoleOutReferences?: ClassName;

function Tclass._module.DoleOutReferences?() : Ty;

const unique Tagclass._module.DoleOutReferences?: TyTag;

// Tclass._module.DoleOutReferences? Tag
axiom Tag(Tclass._module.DoleOutReferences?()) == Tagclass._module.DoleOutReferences?
   && TagFamily(Tclass._module.DoleOutReferences?()) == tytagFamily$DoleOutReferences;

// Box/unbox axiom for Tclass._module.DoleOutReferences?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.DoleOutReferences?()) } 
  $IsBox(bx, Tclass._module.DoleOutReferences?())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.DoleOutReferences?()));

// DoleOutReferences: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.DoleOutReferences?()) } 
  $Is($o, Tclass._module.DoleOutReferences?())
     <==> $o == null || dtype($o) == Tclass._module.DoleOutReferences?());

// DoleOutReferences: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.DoleOutReferences?(), $h) } 
  $IsAlloc($o, Tclass._module.DoleOutReferences?(), $h)
     <==> $o == null || read($h, $o, alloc));

function _module.DoleOutReferences.u(ref) : ref;

// DoleOutReferences.u: Type axiom
axiom (forall $o: ref :: 
  { _module.DoleOutReferences.u($o) } 
  $o != null && dtype($o) == Tclass._module.DoleOutReferences?()
     ==> $Is(_module.DoleOutReferences.u($o), Tclass._module.Cell?()));

// DoleOutReferences.u: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.DoleOutReferences.u($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.DoleOutReferences?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.DoleOutReferences.u($o), Tclass._module.Cell?(), $h));

axiom FDim(_module.DoleOutReferences.r) == 0
   && FieldOfDecl(class._module.DoleOutReferences?, field$r)
     == _module.DoleOutReferences.r
   && !$IsGhostField(_module.DoleOutReferences.r);

const _module.DoleOutReferences.r: Field ref;

// DoleOutReferences.r: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.DoleOutReferences.r) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.DoleOutReferences?()
     ==> $Is(read($h, $o, _module.DoleOutReferences.r), Tclass._module.Cell?()));

// DoleOutReferences.r: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.DoleOutReferences.r) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.DoleOutReferences?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.DoleOutReferences.r), Tclass._module.Cell?(), $h));

axiom FDim(_module.DoleOutReferences.c) == 0
   && FieldOfDecl(class._module.DoleOutReferences?, field$c)
     == _module.DoleOutReferences.c
   && !$IsGhostField(_module.DoleOutReferences.c);

const _module.DoleOutReferences.c: Field ref;

// DoleOutReferences.c: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.DoleOutReferences.c) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.DoleOutReferences?()
     ==> $Is(read($h, $o, _module.DoleOutReferences.c), Tclass._module.Cell?()));

// DoleOutReferences.c: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.DoleOutReferences.c) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.DoleOutReferences?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.DoleOutReferences.c), Tclass._module.Cell?(), $h));

axiom FDim(_module.DoleOutReferences.rs) == 0
   && FieldOfDecl(class._module.DoleOutReferences?, field$rs)
     == _module.DoleOutReferences.rs
   && $IsGhostField(_module.DoleOutReferences.rs);

const _module.DoleOutReferences.rs: Field (Seq Box);

// DoleOutReferences.rs: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.DoleOutReferences.rs) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.DoleOutReferences?()
     ==> $Is(read($h, $o, _module.DoleOutReferences.rs), TSeq(Tclass._module.Cell?())));

// DoleOutReferences.rs: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.DoleOutReferences.rs) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.DoleOutReferences?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.DoleOutReferences.rs), TSeq(Tclass._module.Cell?()), $h));

axiom FDim(_module.DoleOutReferences.cs) == 0
   && FieldOfDecl(class._module.DoleOutReferences?, field$cs)
     == _module.DoleOutReferences.cs
   && $IsGhostField(_module.DoleOutReferences.cs);

const _module.DoleOutReferences.cs: Field (Seq Box);

// DoleOutReferences.cs: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.DoleOutReferences.cs) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.DoleOutReferences?()
     ==> $Is(read($h, $o, _module.DoleOutReferences.cs), TSeq(Tclass._module.Cell?())));

// DoleOutReferences.cs: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.DoleOutReferences.cs) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.DoleOutReferences?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.DoleOutReferences.cs), TSeq(Tclass._module.Cell?()), $h));

function _module.DoleOutReferences.__reads(ref) : Set Box;

// DoleOutReferences._reads: Type axiom
axiom (forall $o: ref :: 
  { _module.DoleOutReferences.__reads($o) } 
  $o != null && dtype($o) == Tclass._module.DoleOutReferences?()
     ==> $Is(_module.DoleOutReferences.__reads($o), TSet(Tclass._System.object?())));

// DoleOutReferences._reads: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.DoleOutReferences.__reads($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.DoleOutReferences?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.DoleOutReferences.__reads($o), TSet(Tclass._System.object?()), $h));

function _module.DoleOutReferences.__modifies(ref) : Set Box;

// DoleOutReferences._modifies: Type axiom
axiom (forall $o: ref :: 
  { _module.DoleOutReferences.__modifies($o) } 
  $o != null && dtype($o) == Tclass._module.DoleOutReferences?()
     ==> $Is(_module.DoleOutReferences.__modifies($o), TSet(Tclass._System.object?())));

// DoleOutReferences._modifies: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.DoleOutReferences.__modifies($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.DoleOutReferences?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.DoleOutReferences.__modifies($o), TSet(Tclass._System.object?()), $h));

axiom FDim(_module.DoleOutReferences.__new) == 0
   && FieldOfDecl(class._module.DoleOutReferences?, field$_new)
     == _module.DoleOutReferences.__new
   && $IsGhostField(_module.DoleOutReferences.__new);

const _module.DoleOutReferences.__new: Field (Set Box);

// DoleOutReferences._new: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.DoleOutReferences.__new) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.DoleOutReferences?()
     ==> $Is(read($h, $o, _module.DoleOutReferences.__new), TSet(Tclass._System.object?())));

// DoleOutReferences._new: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.DoleOutReferences.__new) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.DoleOutReferences?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.DoleOutReferences.__new), 
      TSet(Tclass._System.object?()), 
      $h));

function _module.DoleOutReferences.__decreases0(ref) : ref;

// DoleOutReferences._decreases0: Type axiom
axiom (forall $o: ref :: 
  { _module.DoleOutReferences.__decreases0($o) } 
  $o != null && dtype($o) == Tclass._module.DoleOutReferences?()
     ==> $Is(_module.DoleOutReferences.__decreases0($o), Tclass._module.Cell?()));

// DoleOutReferences._decreases0: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.DoleOutReferences.__decreases0($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.DoleOutReferences?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.DoleOutReferences.__decreases0($o), Tclass._module.Cell?(), $h));

function Tclass._module.DoleOutReferences() : Ty;

const unique Tagclass._module.DoleOutReferences: TyTag;

// Tclass._module.DoleOutReferences Tag
axiom Tag(Tclass._module.DoleOutReferences()) == Tagclass._module.DoleOutReferences
   && TagFamily(Tclass._module.DoleOutReferences()) == tytagFamily$DoleOutReferences;

// Box/unbox axiom for Tclass._module.DoleOutReferences
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.DoleOutReferences()) } 
  $IsBox(bx, Tclass._module.DoleOutReferences())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.DoleOutReferences()));

procedure CheckWellformed$$_module.DoleOutReferences.__ctor(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.DoleOutReferences())
         && $IsAlloc(this, Tclass._module.DoleOutReferences(), $Heap), 
    u#0: ref
       where $Is(u#0, Tclass._module.Cell?()) && $IsAlloc(u#0, Tclass._module.Cell?(), $Heap));
  free requires 33 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.DoleOutReferences.__ctor(u#0: ref
       where $Is(u#0, Tclass._module.Cell?()) && $IsAlloc(u#0, Tclass._module.Cell?(), $Heap))
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass._module.DoleOutReferences())
         && $IsAlloc(this, Tclass._module.DoleOutReferences(), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures _module.DoleOutReferences.u(this) == u#0;
  free ensures true;
  ensures Seq#Equal(read($Heap, this, _module.DoleOutReferences.rs), Seq#Empty(): Seq Box);
  free ensures true;
  ensures Seq#Equal(read($Heap, this, _module.DoleOutReferences.cs), Seq#Empty(): Seq Box);
  free ensures _module.DoleOutReferences.Valid#canCall($Heap, this);
  ensures _module.DoleOutReferences.Valid($Heap, this);
  free ensures true;
  ensures Set#Equal(_module.DoleOutReferences.__reads(this), Set#Empty(): Set Box);
  free ensures true;
  ensures Set#Equal(_module.DoleOutReferences.__modifies(this), Set#Empty(): Set Box);
  free ensures true;
  ensures Set#Equal(read($Heap, this, _module.DoleOutReferences.__new), Set#Empty(): Set Box);
  free ensures true;
  ensures _module.DoleOutReferences.__decreases0(this) == u#0;
  // constructor allocates the object
  ensures !read(old($Heap), this, alloc);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



// function declaration for _module.DoleOutReferences.Valid
function _module.DoleOutReferences.Valid($heap: Heap, this: ref) : bool;

function _module.DoleOutReferences.Valid#canCall($heap: Heap, this: ref) : bool;

// frame axiom for _module.DoleOutReferences.Valid
axiom (forall $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.DoleOutReferences.Valid($h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.DoleOutReferences())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && (
            $o == this
             || _module.DoleOutReferences.__reads(this)[$Box($o)]
             || read($h0, this, _module.DoleOutReferences.__new)[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.DoleOutReferences.Valid($h0, this)
       == _module.DoleOutReferences.Valid($h1, this));

// consequence axiom for _module.DoleOutReferences.Valid
axiom 32 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref :: 
    { _module.DoleOutReferences.Valid($Heap, this) } 
    _module.DoleOutReferences.Valid#canCall($Heap, this)
         || (32 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.DoleOutReferences())
           && $IsAlloc(this, Tclass._module.DoleOutReferences(), $Heap))
       ==> true);

function _module.DoleOutReferences.Valid#requires(Heap, ref) : bool;

// #requires axiom for _module.DoleOutReferences.Valid
axiom (forall $Heap: Heap, this: ref :: 
  { _module.DoleOutReferences.Valid#requires($Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.DoleOutReferences())
       && $IsAlloc(this, Tclass._module.DoleOutReferences(), $Heap)
     ==> _module.DoleOutReferences.Valid#requires($Heap, this) == true);

procedure CheckWellformed$$_module.DoleOutReferences.Valid(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.DoleOutReferences())
         && $IsAlloc(this, Tclass._module.DoleOutReferences(), $Heap));
  free requires 32 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.DoleOutReferences.Valid(this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function Valid
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(191,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> $o == this
           || _module.DoleOutReferences.__reads(this)[$Box($o)]
           || read($Heap, this, _module.DoleOutReferences.__new)[$Box($o)]);
    b$reqreads#0 := $_Frame[this, _module.DoleOutReferences.__new];
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



procedure Call$$_module.DoleOutReferences.MoveNext(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.DoleOutReferences())
         && $IsAlloc(this, Tclass._module.DoleOutReferences(), $Heap))
   returns (more#0: bool);
  // user-defined preconditions
  requires _module.DoleOutReferences.Valid($Heap, this);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    read($Heap, this, _module.DoleOutReferences.__new)[$Box($o)]
         && !read(old($Heap), this, _module.DoleOutReferences.__new)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures !read($Heap, this, _module.DoleOutReferences.__new)[$Box(null)];
  free ensures more#0 ==> _module.DoleOutReferences.Valid#canCall($Heap, this);
  ensures more#0 ==> _module.DoleOutReferences.Valid($Heap, this);
  free ensures true;
  ensures Seq#Equal(read($Heap, this, _module.DoleOutReferences.rs), 
    (if more#0
       then Seq#Append(read(old($Heap), this, _module.DoleOutReferences.rs), 
        Seq#Build(Seq#Empty(): Seq Box, $Box(read($Heap, this, _module.DoleOutReferences.r))))
       else read(old($Heap), this, _module.DoleOutReferences.rs)));
  free ensures true;
  ensures Seq#Equal(read($Heap, this, _module.DoleOutReferences.cs), 
    (if more#0
       then Seq#Append(read(old($Heap), this, _module.DoleOutReferences.cs), 
        Seq#Build(Seq#Empty(): Seq Box, $Box(read($Heap, this, _module.DoleOutReferences.c))))
       else read(old($Heap), this, _module.DoleOutReferences.cs)));
  free ensures true;
  ensures more#0 ==> read($Heap, this, _module.DoleOutReferences.r) != null;
  ensures more#0
     ==> read($Heap, this, _module.DoleOutReferences.r) != null
       && !read(old($Heap), read($Heap, this, _module.DoleOutReferences.r), alloc);
  ensures more#0
     ==> !read($Heap, this, _module.DoleOutReferences.__new)[$Box(read($Heap, this, _module.DoleOutReferences.r))];
  free ensures true;
  ensures more#0 ==> read($Heap, this, _module.DoleOutReferences.c) != null;
  ensures more#0
     ==> read($Heap, this, _module.DoleOutReferences.c) != null
       && !read(old($Heap), read($Heap, this, _module.DoleOutReferences.c), alloc);
  free ensures true;
  ensures !more#0 ==> Lit(false);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || 
        $o == this
         || _module.DoleOutReferences.__modifies(this)[$Box($o)]
         || read(old($Heap), this, _module.DoleOutReferences.__new)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



// _module.DoleOutReferences: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.DoleOutReferences()) } 
  $Is(c#0, Tclass._module.DoleOutReferences())
     <==> $Is(c#0, Tclass._module.DoleOutReferences?()) && c#0 != null);

// _module.DoleOutReferences: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.DoleOutReferences(), $h) } 
  $IsAlloc(c#0, Tclass._module.DoleOutReferences(), $h)
     <==> $IsAlloc(c#0, Tclass._module.DoleOutReferences?(), $h));

procedure CheckWellformed$$_module.DoleOutReferences(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.DoleOutReferences())
         && $IsAlloc(this, Tclass._module.DoleOutReferences(), $Heap), 
    u#0: ref
       where $Is(u#0, Tclass._module.Cell?()) && $IsAlloc(u#0, Tclass._module.Cell?(), $Heap));
  free requires 31 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Impl$$_module.DoleOutReferences(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.DoleOutReferences())
         && $IsAlloc(this, Tclass._module.DoleOutReferences(), $Heap), 
    u#0: ref
       where $Is(u#0, Tclass._module.Cell?()) && $IsAlloc(u#0, Tclass._module.Cell?(), $Heap));
  free requires 31 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  ensures Lit(false);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.DoleOutReferences(this: ref, u#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _yieldCount#0: int
     where _yieldCount#0 == Seq#Length(read($Heap, this, _module.DoleOutReferences.rs))
       && _yieldCount#0 == Seq#Length(read($Heap, this, _module.DoleOutReferences.cs));
  var $_OldIterHeap: Heap
     where $IsGoodHeap($_OldIterHeap) && $HeapSucc($_OldIterHeap, $Heap);
  var myCells#0: Seq Box
     where $Is(myCells#0, TSeq(Tclass._module.Cell?()))
       && $IsAlloc(myCells#0, TSeq(Tclass._module.Cell?()), $Heap);
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var z#0: ref;
  var $decr$loop#00: int;
  var $rhs#0_0: ref where $Is($rhs#0_0, Tclass._module.Cell?());
  var $nw: ref;
  var $rhs#0_1: ref where $Is($rhs#0_1, Tclass._module.Cell?());
  var $obj0: ref;
  var $obj1: ref;
  var $rhs#0_2: int;
  var $rhs#0_3: int;
  var $rhs#0_4: Set Box where $Is($rhs#0_4, TSet(Tclass._System.object?()));
  var $rhs#0_0_0: Set Box where $Is($rhs#0_0_0, TSet(Tclass._System.object?()));
  var $rhs#0_0_1: Set Box where $Is($rhs#0_0_1, TSet(Tclass._System.object?()));
  var z#2: ref;
  var z#3: ref;
  var $prevHeap: Heap;

    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(191,9): initial state"} true;
    assume _module.DoleOutReferences.u(this) == u#0;
    assume Seq#Equal(read($Heap, this, _module.DoleOutReferences.rs), Seq#Empty(): Seq Box);
    assume Seq#Equal(read($Heap, this, _module.DoleOutReferences.cs), Seq#Empty(): Seq Box);
    assume _module.DoleOutReferences.Valid($Heap, this);
    assume Set#Equal(_module.DoleOutReferences.__reads(this), Set#Empty(): Set Box);
    assume Set#Equal(_module.DoleOutReferences.__modifies(this), Set#Empty(): Set Box);
    assume Set#Equal(read($Heap, this, _module.DoleOutReferences.__new), Set#Empty(): Set Box);
    assume _module.DoleOutReferences.__decreases0(this) == u#0;
    assume _yieldCount#0 == 0;
    call $YieldHavoc(this, _module.DoleOutReferences.__reads(this), read($Heap, this, _module.DoleOutReferences.__new));
    $_OldIterHeap := $Heap;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(196,27)
    assume true;
    assume true;
    myCells#0 := Lit(Seq#Empty(): Seq Box);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(196,31)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(197,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := _yieldCount#0;
    havoc $w$loop#0;
    while (true)
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0
         ==> (forall z#1: ref :: 
          $Is(z#1, Tclass._module.Cell?())
             ==> 
            Seq#Contains(myCells#0, $Box(z#1))
             ==> read($Heap, this, _module.DoleOutReferences.__new)[$Box(z#1)]);
      free invariant (forall $o: ref :: 
        { $Heap[$o] } 
        $o != null && read(old($Heap), $o, alloc)
           ==> $Heap[$o] == $PreLoopHeap$loop#0[$o] || $o == this);
      free invariant $HeapSucc($PreLoopHeap$loop#0, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
        { read($Heap, $o, $f) } 
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
      invariant (forall $o: ref :: 
        { read($Heap, this, _module.DoleOutReferences.__new)[$Box($o)] } 
        read($Heap, this, _module.DoleOutReferences.__new)[$Box($o)]
           ==> $o != null && !read(old($Heap), $o, alloc));
      free invariant _yieldCount#0 >= $decr_init$loop#00
         && (_yieldCount#0 == $decr_init$loop#00 ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(197,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            // Begin Comprehension WF check
            havoc z#0;
            if ($Is(z#0, Tclass._module.Cell?()))
            {
                if (Seq#Contains(myCells#0, $Box(z#0)))
                {
                }
            }

            // End Comprehension WF check
            assume true;
            assume (forall z#1: ref :: 
              $Is(z#1, Tclass._module.Cell?())
                 ==> 
                Seq#Contains(myCells#0, $Box(z#1))
                 ==> read($Heap, this, _module.DoleOutReferences.__new)[$Box(z#1)]);
            assume true;
            assume false;
        }

        assume true;
        if (!Lit(true))
        {
            break;
        }

        $decr$loop#00 := _yieldCount#0;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(200,7)
        assume true;
        assert $_Frame[this, _module.DoleOutReferences.c];
        havoc $nw;
        assume $nw != null && dtype($nw) == Tclass._module.Cell?();
        assume !read($Heap, $nw, alloc);
        $Heap := update($Heap, $nw, alloc, true);
        $Heap := update($Heap, 
          this, 
          _module.DoleOutReferences.__new, 
          Set#UnionOne(read($Heap, this, _module.DoleOutReferences.__new), $Box($nw)));
        assume $IsGoodHeap($Heap);
        assume $IsHeapAnchor($Heap);
        $rhs#0_0 := $nw;
        $Heap := update($Heap, this, _module.DoleOutReferences.c, $rhs#0_0);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(200,17)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(201,7)
        assume true;
        assert $_Frame[this, _module.DoleOutReferences.r];
        havoc $nw;
        assume $nw != null && dtype($nw) == Tclass._module.Cell?();
        assume !read($Heap, $nw, alloc);
        $Heap := update($Heap, $nw, alloc, true);
        $Heap := update($Heap, 
          this, 
          _module.DoleOutReferences.__new, 
          Set#UnionOne(read($Heap, this, _module.DoleOutReferences.__new), $Box($nw)));
        assume $IsGoodHeap($Heap);
        assume $IsHeapAnchor($Heap);
        $rhs#0_1 := $nw;
        $Heap := update($Heap, this, _module.DoleOutReferences.r, $rhs#0_1);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(201,17)"} true;
        // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(202,20)
        assert read($Heap, this, _module.DoleOutReferences.c) != null;
        assume true;
        $obj0 := read($Heap, this, _module.DoleOutReferences.c);
        assert $_Frame[$obj0, _module.Cell.data];
        assert read($Heap, this, _module.DoleOutReferences.r) != null;
        assume true;
        $obj1 := read($Heap, this, _module.DoleOutReferences.r);
        assert $_Frame[$obj1, _module.Cell.data];
        assume true;
        $rhs#0_2 := LitInt(12);
        assume true;
        $rhs#0_3 := LitInt(12);
        assert read($Heap, this, _module.DoleOutReferences.r)
             != read($Heap, this, _module.DoleOutReferences.c)
           || $rhs#0_3 == $rhs#0_2;
        $Heap := update($Heap, $obj0, _module.Cell.data, $rhs#0_2);
        assume $IsGoodHeap($Heap);
        $Heap := update($Heap, $obj1, _module.Cell.data, $rhs#0_3);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(202,28)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(203,13)
        assume true;
        assume true;
        myCells#0 := Seq#Append(myCells#0, 
          Seq#Build(Seq#Empty(): Seq Box, $Box(read($Heap, this, _module.DoleOutReferences.c))));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(203,28)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(204,10)
        assume true;
        assert $_Frame[this, _module.DoleOutReferences.__new];
        assume true;
        $rhs#0_4 := Set#Difference(read($Heap, this, _module.DoleOutReferences.__new), 
          Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.DoleOutReferences.r))));
        assert Set#Subset($rhs#0_4, read($Heap, this, _module.DoleOutReferences.__new));
        $Heap := update($Heap, this, _module.DoleOutReferences.__new, $rhs#0_4);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(204,22)"} true;
        // ----- yield statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(205,5)
        $Heap := update($Heap, 
          this, 
          _module.DoleOutReferences.rs, 
          Seq#Append(read($Heap, this, _module.DoleOutReferences.rs), 
            Seq#Build(Seq#Empty(): Seq Box, $Box(read($Heap, this, _module.DoleOutReferences.r)))));
        $Heap := update($Heap, 
          this, 
          _module.DoleOutReferences.cs, 
          Seq#Append(read($Heap, this, _module.DoleOutReferences.cs), 
            Seq#Build(Seq#Empty(): Seq Box, $Box(read($Heap, this, _module.DoleOutReferences.c)))));
        _yieldCount#0 := _yieldCount#0 + 1;
        assume _yieldCount#0 == Seq#Length(read($Heap, this, _module.DoleOutReferences.rs))
           && _yieldCount#0 == Seq#Length(read($Heap, this, _module.DoleOutReferences.cs));
        assume $IsGoodHeap($Heap);
        assert {:subsumption 0} read($Heap, this, _module.DoleOutReferences.r) != null;
        assert {:subsumption 0} read($Heap, this, _module.DoleOutReferences.r) != null
           && !read($_OldIterHeap, read($Heap, this, _module.DoleOutReferences.r), alloc);
        assert {:subsumption 0} !read($Heap, this, _module.DoleOutReferences.__new)[$Box(read($Heap, this, _module.DoleOutReferences.r))];
        assume read($Heap, this, _module.DoleOutReferences.r) != null
           && 
          read($Heap, this, _module.DoleOutReferences.r) != null
           && !read($_OldIterHeap, read($Heap, this, _module.DoleOutReferences.r), alloc)
           && !read($Heap, this, _module.DoleOutReferences.__new)[$Box(read($Heap, this, _module.DoleOutReferences.r))];
        assert {:subsumption 0} read($Heap, this, _module.DoleOutReferences.c) != null;
        assert {:subsumption 0} read($Heap, this, _module.DoleOutReferences.c) != null
           && !read($_OldIterHeap, read($Heap, this, _module.DoleOutReferences.c), alloc);
        assume read($Heap, this, _module.DoleOutReferences.c) != null
           && 
          read($Heap, this, _module.DoleOutReferences.c) != null
           && !read($_OldIterHeap, read($Heap, this, _module.DoleOutReferences.c), alloc);
        call $YieldHavoc(this, _module.DoleOutReferences.__reads(this), read($Heap, this, _module.DoleOutReferences.__new));
        $_OldIterHeap := $Heap;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(205,9)"} true;
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(206,5)
        if (*)
        {
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(207,12)
            assume true;
            assert $_Frame[this, _module.DoleOutReferences.__new];
            assume true;
            $rhs#0_0_0 := Set#Union(read($Heap, this, _module.DoleOutReferences.__new), 
              Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.DoleOutReferences.c))));
            assert Set#Subset($rhs#0_0_0, read($Heap, this, _module.DoleOutReferences.__new));
            $Heap := update($Heap, this, _module.DoleOutReferences.__new, $rhs#0_0_0);
            assume $IsGoodHeap($Heap);
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(207,24)"} true;
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(208,12)
            assume true;
            assert $_Frame[this, _module.DoleOutReferences.__new];
            assume true;
            $rhs#0_0_1 := Set#Union(read($Heap, this, _module.DoleOutReferences.__new), 
              Set#UnionOne(Set#Empty(): Set Box, $Box(_module.DoleOutReferences.u(this))));
            assert Set#Subset($rhs#0_0_1, read($Heap, this, _module.DoleOutReferences.__new));
            $Heap := update($Heap, this, _module.DoleOutReferences.__new, $rhs#0_0_1);
            assume $IsGoodHeap($Heap);
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(208,24)"} true;
        }
        else
        {
            // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(209,12)
            if (*)
            {
                // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(210,7)
                assert {:subsumption 0} read($Heap, this, _module.DoleOutReferences.c) != null;
                assume true;
                assert read($Heap, read($Heap, this, _module.DoleOutReferences.c), _module.Cell.data)
                   == LitInt(12);
                // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(211,7)
                assume true;
                assert read($Heap, this, _module.DoleOutReferences.__new)[$Box(read($Heap, this, _module.DoleOutReferences.c))];
                // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(212,7)
                assert {:subsumption 0} read($Heap, this, _module.DoleOutReferences.r) != null;
                assume true;
                assert read($Heap, read($Heap, this, _module.DoleOutReferences.r), _module.Cell.data)
                   == LitInt(12);
            }
            else
            {
                // ----- forall statement (assign) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(214,7)
                if (*)
                {
                    // Assume Fuel Constant
                    havoc z#2;
                    assume $Is(z#2, Tclass._module.Cell?());
                    assume true;
                    assume Seq#Contains(myCells#0, $Box(z#2));
                    assert {:subsumption 0} z#2 != null;
                    assume true;
                    assert $_Frame[z#2, _module.Cell.data];
                    assert {:subsumption 0} z#2 != null;
                    assume true;
                    havoc z#3;
                    assume $Is(z#3, Tclass._module.Cell?());
                    assume Seq#Contains(myCells#0, $Box(z#3));
                    assume z#2 != z#3;
                    assert z#2 != z#3
                       || _module.Cell.data != _module.Cell.data
                       || read($Heap, z#2, _module.Cell.data) + 1
                         == read($Heap, z#3, _module.Cell.data) + 1;
                    assume false;
                }
                else
                {
                    $prevHeap := $Heap;
                    havoc $Heap;
                    assume $HeapSucc($prevHeap, $Heap);
                    assume (forall<alpha> $o: ref, $f: Field alpha :: 
                      { read($Heap, $o, $f) } 
                      read($Heap, $o, $f) == read($prevHeap, $o, $f)
                         || (exists z#4: ref :: 
                          $Is(z#4, Tclass._module.Cell?())
                             && Seq#Contains(myCells#0, $Box(z#4))
                             && $o == z#4
                             && $f == _module.Cell.data));
                }

                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(216,6)"} true;
            }
        }

        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(197,3)
        assert _yieldCount#0 > $decr$loop#00;
        assume true;
    }
}



const unique class._module.Cls?: ClassName;

function Tclass._module.Cls?() : Ty;

const unique Tagclass._module.Cls?: TyTag;

// Tclass._module.Cls? Tag
axiom Tag(Tclass._module.Cls?()) == Tagclass._module.Cls?
   && TagFamily(Tclass._module.Cls?()) == tytagFamily$Cls;

// Box/unbox axiom for Tclass._module.Cls?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Cls?()) } 
  $IsBox(bx, Tclass._module.Cls?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Cls?()));

// Cls: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.Cls?()) } 
  $Is($o, Tclass._module.Cls?())
     <==> $o == null || dtype($o) == Tclass._module.Cls?());

// Cls: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.Cls?(), $h) } 
  $IsAlloc($o, Tclass._module.Cls?(), $h) <==> $o == null || read($h, $o, alloc));

axiom FDim(_module.Cls.y) == 0
   && FieldOfDecl(class._module.Cls?, field$y) == _module.Cls.y
   && !$IsGhostField(_module.Cls.y);

const _module.Cls.y: Field int;

// Cls.y: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Cls.y) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Cls?()
     ==> $Is(read($h, $o, _module.Cls.y), TInt));

// Cls.y: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Cls.y) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Cls?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Cls.y), TInt, $h));

function Tclass._module.Cls() : Ty;

const unique Tagclass._module.Cls: TyTag;

// Tclass._module.Cls Tag
axiom Tag(Tclass._module.Cls()) == Tagclass._module.Cls
   && TagFamily(Tclass._module.Cls()) == tytagFamily$Cls;

// Box/unbox axiom for Tclass._module.Cls
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Cls()) } 
  $IsBox(bx, Tclass._module.Cls())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Cls()));

procedure CheckWellformed$$_module.Cls.LoopFrame__Constructor(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Cls())
         && $IsAlloc(this, Tclass._module.Cls(), $Heap), 
    c#0: ref
       where $Is(c#0, Tclass._module.Cell()) && $IsAlloc(c#0, Tclass._module.Cell(), $Heap));
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Cls.LoopFrame__Constructor(c#0: ref
       where $Is(c#0, Tclass._module.Cell()) && $IsAlloc(c#0, Tclass._module.Cell(), $Heap))
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Cls())
         && $IsAlloc(this, Tclass._module.Cls(), $Heap));
  modifies $Heap, $Tick;
  // constructor allocates the object
  ensures !read(old($Heap), this, alloc);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == c#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Cls.LoopFrame__Constructor(c#0: ref
       where $Is(c#0, Tclass._module.Cell()) && $IsAlloc(c#0, Tclass._module.Cell(), $Heap))
   returns (this: ref where this != null && $Is(this, Tclass._module.Cls()), 
    $_reverifyPost: bool);
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == c#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Cls.LoopFrame__Constructor(c#0: ref) returns (this: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var this.y: int;
  var $rhs#0: int;
  var d#0: ref
     where $Is(d#0, Tclass._module.Cell()) && $IsAlloc(d#0, Tclass._module.Cell(), $Heap);
  var $nw: ref;
  var $rhs#1: int;
  var $PreLoopHeap$loop#0: Heap;
  var $w$loop#0: bool;
  var $rhs#0_0: int;
  var $rhs#0_1: int;
  var $rhs#0_2: int;

    // AddMethodImpl: LoopFrame_Constructor, Impl$$_module.Cls.LoopFrame__Constructor
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == c#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(429,2): initial state"} true;
    $_reverifyPost := false;
    // ----- divided block before new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(429,3)
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(430,7)
    assume true;
    assume true;
    this.y := LitInt(10);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(430,11)"} true;
    // ----- new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(429,3)
    assume !read($Heap, this, alloc);
    assume read($Heap, this, _module.Cls.y) == this.y;
    $Heap := update($Heap, this, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    // ----- divided block after new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(429,3)
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(432,12)
    assert c#0 != null;
    assume true;
    assert $_Frame[c#0, _module.Cell.data];
    assume true;
    $rhs#0 := LitInt(10);
    $Heap := update($Heap, c#0, _module.Cell.data, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(432,16)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(433,11)
    assume true;
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._module.Cell?();
    assume !read($Heap, $nw, alloc);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    d#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(433,21)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(434,12)
    assert d#0 != null;
    assume true;
    assert $_Frame[d#0, _module.Cell.data];
    assume true;
    $rhs#1 := LitInt(10);
    $Heap := update($Heap, d#0, _module.Cell.data, $rhs#1);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(434,16)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(435,5)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    havoc $w$loop#0;
    while (true)
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> read($Heap, this, _module.Cls.y) <= LitInt(11);
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> read($Heap, d#0, _module.Cell.data) <= LitInt(11);
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> read($Heap, c#0, _module.Cell.data) <= LitInt(11);
      free invariant (forall $o: ref :: 
        { $Heap[$o] } 
        $o != null && read(old($Heap), $o, alloc)
           ==> $Heap[$o] == $PreLoopHeap$loop#0[$o] || $o == c#0);
      free invariant $HeapSucc($PreLoopHeap$loop#0, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
        { read($Heap, $o, $f) } 
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(435,4): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assume true;
            assume read($Heap, this, _module.Cls.y) <= LitInt(11);
            assert {:subsumption 0} d#0 != null;
            assume true;
            assume read($Heap, d#0, _module.Cell.data) <= LitInt(11);
            assert {:subsumption 0} c#0 != null;
            assume true;
            assume read($Heap, c#0, _module.Cell.data) <= LitInt(11);
            assume true;
            assume false;
        }

        assume true;
        if (!Lit(true))
        {
            break;
        }

        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(441,9)
        assume true;
        assert $_Frame[this, _module.Cls.y];
        assume true;
        $rhs#0_0 := read($Heap, this, _module.Cls.y) + 1;
        $Heap := update($Heap, this, _module.Cls.y, $rhs#0_0);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(441,16)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(442,14)
        assert c#0 != null;
        assume true;
        assert $_Frame[c#0, _module.Cell.data];
        assert c#0 != null;
        assume true;
        $rhs#0_1 := read($Heap, c#0, _module.Cell.data) + 1;
        $Heap := update($Heap, c#0, _module.Cell.data, $rhs#0_1);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(442,26)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(443,14)
        assert d#0 != null;
        assume true;
        assert $_Frame[d#0, _module.Cell.data];
        assert d#0 != null;
        assume true;
        $rhs#0_2 := read($Heap, d#0, _module.Cell.data) + 1;
        $Heap := update($Heap, d#0, _module.Cell.data, $rhs#0_2);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(443,26)"} true;
        assume true;
        assume true;
        assume true;
    }
}



// _module.Cls: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.Cls()) } 
  $Is(c#0, Tclass._module.Cls())
     <==> $Is(c#0, Tclass._module.Cls?()) && c#0 != null);

// _module.Cls: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.Cls(), $h) } 
  $IsAlloc(c#0, Tclass._module.Cls(), $h)
     <==> $IsAlloc(c#0, Tclass._module.Cls?(), $h));

const unique class._module.LoopFrame__Iter?: ClassName;

function Tclass._module.LoopFrame__Iter?() : Ty;

const unique Tagclass._module.LoopFrame__Iter?: TyTag;

// Tclass._module.LoopFrame__Iter? Tag
axiom Tag(Tclass._module.LoopFrame__Iter?()) == Tagclass._module.LoopFrame__Iter?
   && TagFamily(Tclass._module.LoopFrame__Iter?()) == tytagFamily$LoopFrame_Iter;

// Box/unbox axiom for Tclass._module.LoopFrame__Iter?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.LoopFrame__Iter?()) } 
  $IsBox(bx, Tclass._module.LoopFrame__Iter?())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.LoopFrame__Iter?()));

// LoopFrame_Iter: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.LoopFrame__Iter?()) } 
  $Is($o, Tclass._module.LoopFrame__Iter?())
     <==> $o == null || dtype($o) == Tclass._module.LoopFrame__Iter?());

// LoopFrame_Iter: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.LoopFrame__Iter?(), $h) } 
  $IsAlloc($o, Tclass._module.LoopFrame__Iter?(), $h)
     <==> $o == null || read($h, $o, alloc));

function _module.LoopFrame__Iter.c(ref) : ref;

// LoopFrame_Iter.c: Type axiom
axiom (forall $o: ref :: 
  { _module.LoopFrame__Iter.c($o) } 
  $o != null && dtype($o) == Tclass._module.LoopFrame__Iter?()
     ==> $Is(_module.LoopFrame__Iter.c($o), Tclass._module.Cell()));

// LoopFrame_Iter.c: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.LoopFrame__Iter.c($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.LoopFrame__Iter?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.LoopFrame__Iter.c($o), Tclass._module.Cell(), $h));

axiom FDim(_module.LoopFrame__Iter.y) == 0
   && FieldOfDecl(class._module.LoopFrame__Iter?, field$y)
     == _module.LoopFrame__Iter.y
   && !$IsGhostField(_module.LoopFrame__Iter.y);

const _module.LoopFrame__Iter.y: Field int;

// LoopFrame_Iter.y: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.LoopFrame__Iter.y) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.LoopFrame__Iter?()
     ==> $Is(read($h, $o, _module.LoopFrame__Iter.y), TInt));

// LoopFrame_Iter.y: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.LoopFrame__Iter.y) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.LoopFrame__Iter?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.LoopFrame__Iter.y), TInt, $h));

axiom FDim(_module.LoopFrame__Iter.ys) == 0
   && FieldOfDecl(class._module.LoopFrame__Iter?, field$ys)
     == _module.LoopFrame__Iter.ys
   && $IsGhostField(_module.LoopFrame__Iter.ys);

const _module.LoopFrame__Iter.ys: Field (Seq Box);

// LoopFrame_Iter.ys: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.LoopFrame__Iter.ys) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.LoopFrame__Iter?()
     ==> $Is(read($h, $o, _module.LoopFrame__Iter.ys), TSeq(TInt)));

// LoopFrame_Iter.ys: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.LoopFrame__Iter.ys) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.LoopFrame__Iter?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.LoopFrame__Iter.ys), TSeq(TInt), $h));

function _module.LoopFrame__Iter.__reads(ref) : Set Box;

// LoopFrame_Iter._reads: Type axiom
axiom (forall $o: ref :: 
  { _module.LoopFrame__Iter.__reads($o) } 
  $o != null && dtype($o) == Tclass._module.LoopFrame__Iter?()
     ==> $Is(_module.LoopFrame__Iter.__reads($o), TSet(Tclass._System.object?())));

// LoopFrame_Iter._reads: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.LoopFrame__Iter.__reads($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.LoopFrame__Iter?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.LoopFrame__Iter.__reads($o), TSet(Tclass._System.object?()), $h));

function _module.LoopFrame__Iter.__modifies(ref) : Set Box;

// LoopFrame_Iter._modifies: Type axiom
axiom (forall $o: ref :: 
  { _module.LoopFrame__Iter.__modifies($o) } 
  $o != null && dtype($o) == Tclass._module.LoopFrame__Iter?()
     ==> $Is(_module.LoopFrame__Iter.__modifies($o), TSet(Tclass._System.object?())));

// LoopFrame_Iter._modifies: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.LoopFrame__Iter.__modifies($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.LoopFrame__Iter?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.LoopFrame__Iter.__modifies($o), TSet(Tclass._System.object?()), $h));

axiom FDim(_module.LoopFrame__Iter.__new) == 0
   && FieldOfDecl(class._module.LoopFrame__Iter?, field$_new)
     == _module.LoopFrame__Iter.__new
   && $IsGhostField(_module.LoopFrame__Iter.__new);

const _module.LoopFrame__Iter.__new: Field (Set Box);

// LoopFrame_Iter._new: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.LoopFrame__Iter.__new) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.LoopFrame__Iter?()
     ==> $Is(read($h, $o, _module.LoopFrame__Iter.__new), TSet(Tclass._System.object?())));

// LoopFrame_Iter._new: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.LoopFrame__Iter.__new) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.LoopFrame__Iter?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.LoopFrame__Iter.__new), TSet(Tclass._System.object?()), $h));

function _module.LoopFrame__Iter.__decreases0(ref) : ref;

// LoopFrame_Iter._decreases0: Type axiom
axiom (forall $o: ref :: 
  { _module.LoopFrame__Iter.__decreases0($o) } 
  $o != null && dtype($o) == Tclass._module.LoopFrame__Iter?()
     ==> $Is(_module.LoopFrame__Iter.__decreases0($o), Tclass._module.Cell?()));

// LoopFrame_Iter._decreases0: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.LoopFrame__Iter.__decreases0($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.LoopFrame__Iter?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.LoopFrame__Iter.__decreases0($o), Tclass._module.Cell?(), $h));

function Tclass._module.LoopFrame__Iter() : Ty;

const unique Tagclass._module.LoopFrame__Iter: TyTag;

// Tclass._module.LoopFrame__Iter Tag
axiom Tag(Tclass._module.LoopFrame__Iter()) == Tagclass._module.LoopFrame__Iter
   && TagFamily(Tclass._module.LoopFrame__Iter()) == tytagFamily$LoopFrame_Iter;

// Box/unbox axiom for Tclass._module.LoopFrame__Iter
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.LoopFrame__Iter()) } 
  $IsBox(bx, Tclass._module.LoopFrame__Iter())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.LoopFrame__Iter()));

procedure CheckWellformed$$_module.LoopFrame__Iter.__ctor(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.LoopFrame__Iter())
         && $IsAlloc(this, Tclass._module.LoopFrame__Iter(), $Heap), 
    c#0: ref
       where $Is(c#0, Tclass._module.Cell()) && $IsAlloc(c#0, Tclass._module.Cell(), $Heap));
  free requires 36 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.LoopFrame__Iter.__ctor(c#0: ref
       where $Is(c#0, Tclass._module.Cell()) && $IsAlloc(c#0, Tclass._module.Cell(), $Heap))
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass._module.LoopFrame__Iter())
         && $IsAlloc(this, Tclass._module.LoopFrame__Iter(), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures _module.LoopFrame__Iter.c(this) == c#0;
  free ensures true;
  ensures Seq#Equal(read($Heap, this, _module.LoopFrame__Iter.ys), Seq#Empty(): Seq Box);
  free ensures _module.LoopFrame__Iter.Valid#canCall($Heap, this);
  ensures _module.LoopFrame__Iter.Valid($Heap, this);
  free ensures true;
  ensures Set#Equal(_module.LoopFrame__Iter.__reads(this), 
    Set#UnionOne(Set#Empty(): Set Box, $Box(c#0)));
  free ensures true;
  ensures Set#Equal(_module.LoopFrame__Iter.__modifies(this), 
    Set#UnionOne(Set#Empty(): Set Box, $Box(c#0)));
  free ensures true;
  ensures Set#Equal(read($Heap, this, _module.LoopFrame__Iter.__new), Set#Empty(): Set Box);
  free ensures true;
  ensures _module.LoopFrame__Iter.__decreases0(this) == c#0;
  // constructor allocates the object
  ensures !read(old($Heap), this, alloc);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



// function declaration for _module.LoopFrame_Iter.Valid
function _module.LoopFrame__Iter.Valid($heap: Heap, this: ref) : bool;

function _module.LoopFrame__Iter.Valid#canCall($heap: Heap, this: ref) : bool;

// frame axiom for _module.LoopFrame__Iter.Valid
axiom (forall $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.LoopFrame__Iter.Valid($h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.LoopFrame__Iter())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && (
            $o == this
             || _module.LoopFrame__Iter.__reads(this)[$Box($o)]
             || read($h0, this, _module.LoopFrame__Iter.__new)[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.LoopFrame__Iter.Valid($h0, this)
       == _module.LoopFrame__Iter.Valid($h1, this));

// consequence axiom for _module.LoopFrame__Iter.Valid
axiom 35 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref :: 
    { _module.LoopFrame__Iter.Valid($Heap, this) } 
    _module.LoopFrame__Iter.Valid#canCall($Heap, this)
         || (35 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.LoopFrame__Iter())
           && $IsAlloc(this, Tclass._module.LoopFrame__Iter(), $Heap))
       ==> true);

function _module.LoopFrame__Iter.Valid#requires(Heap, ref) : bool;

// #requires axiom for _module.LoopFrame__Iter.Valid
axiom (forall $Heap: Heap, this: ref :: 
  { _module.LoopFrame__Iter.Valid#requires($Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.LoopFrame__Iter())
       && $IsAlloc(this, Tclass._module.LoopFrame__Iter(), $Heap)
     ==> _module.LoopFrame__Iter.Valid#requires($Heap, this) == true);

procedure CheckWellformed$$_module.LoopFrame__Iter.Valid(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.LoopFrame__Iter())
         && $IsAlloc(this, Tclass._module.LoopFrame__Iter(), $Heap));
  free requires 35 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.LoopFrame__Iter.Valid(this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function Valid
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(448,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> $o == this
           || _module.LoopFrame__Iter.__reads(this)[$Box($o)]
           || read($Heap, this, _module.LoopFrame__Iter.__new)[$Box($o)]);
    b$reqreads#0 := $_Frame[this, _module.LoopFrame__Iter.__new];
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



procedure Call$$_module.LoopFrame__Iter.MoveNext(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.LoopFrame__Iter())
         && $IsAlloc(this, Tclass._module.LoopFrame__Iter(), $Heap))
   returns (more#0: bool);
  // user-defined preconditions
  requires _module.LoopFrame__Iter.Valid($Heap, this);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    read($Heap, this, _module.LoopFrame__Iter.__new)[$Box($o)]
         && !read(old($Heap), this, _module.LoopFrame__Iter.__new)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures !read($Heap, this, _module.LoopFrame__Iter.__new)[$Box(null)];
  free ensures more#0 ==> _module.LoopFrame__Iter.Valid#canCall($Heap, this);
  ensures more#0 ==> _module.LoopFrame__Iter.Valid($Heap, this);
  free ensures true;
  ensures Seq#Equal(read($Heap, this, _module.LoopFrame__Iter.ys), 
    (if more#0
       then Seq#Append(read(old($Heap), this, _module.LoopFrame__Iter.ys), 
        Seq#Build(Seq#Empty(): Seq Box, $Box(read($Heap, this, _module.LoopFrame__Iter.y))))
       else read(old($Heap), this, _module.LoopFrame__Iter.ys)));
  free ensures true;
  ensures more#0
     ==> Seq#Length(read($Heap, this, _module.LoopFrame__Iter.ys)) <= LitInt(2);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || 
        $o == this
         || _module.LoopFrame__Iter.__modifies(this)[$Box($o)]
         || read(old($Heap), this, _module.LoopFrame__Iter.__new)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



// _module.LoopFrame_Iter: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.LoopFrame__Iter()) } 
  $Is(c#0, Tclass._module.LoopFrame__Iter())
     <==> $Is(c#0, Tclass._module.LoopFrame__Iter?()) && c#0 != null);

// _module.LoopFrame_Iter: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.LoopFrame__Iter(), $h) } 
  $IsAlloc(c#0, Tclass._module.LoopFrame__Iter(), $h)
     <==> $IsAlloc(c#0, Tclass._module.LoopFrame__Iter?(), $h));

procedure CheckWellformed$$_module.LoopFrame__Iter(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.LoopFrame__Iter())
         && $IsAlloc(this, Tclass._module.LoopFrame__Iter(), $Heap), 
    c#0: ref
       where $Is(c#0, Tclass._module.Cell()) && $IsAlloc(c#0, Tclass._module.Cell(), $Heap));
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Impl$$_module.LoopFrame__Iter(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.LoopFrame__Iter())
         && $IsAlloc(this, Tclass._module.LoopFrame__Iter(), $Heap), 
    c#0: ref
       where $Is(c#0, Tclass._module.Cell()) && $IsAlloc(c#0, Tclass._module.Cell(), $Heap));
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == c#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.LoopFrame__Iter(this: ref, c#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _yieldCount#0: int
     where _yieldCount#0 == Seq#Length(read($Heap, this, _module.LoopFrame__Iter.ys));
  var $_OldIterHeap: Heap
     where $IsGoodHeap($_OldIterHeap) && $HeapSucc($_OldIterHeap, $Heap);
  var $rhs#0: int;
  var $rhs#1: int;
  var d#0: ref
     where $Is(d#0, Tclass._module.Cell()) && $IsAlloc(d#0, Tclass._module.Cell(), $Heap);
  var $nw: ref;
  var $rhs#2: int;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var $decr$loop#00: int;
  var $rhs#0_0_0: int;
  var $rhs#0_0: int;
  var $rhs#0_1: int;
  var $rhs#0_2: int;

    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this || $o == c#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(448,9): initial state"} true;
    assume _module.LoopFrame__Iter.c(this) == c#0;
    assume Seq#Equal(read($Heap, this, _module.LoopFrame__Iter.ys), Seq#Empty(): Seq Box);
    assume _module.LoopFrame__Iter.Valid($Heap, this);
    assume Set#Equal(_module.LoopFrame__Iter.__reads(this), 
      Set#UnionOne(Set#Empty(): Set Box, $Box(c#0)));
    assume Set#Equal(_module.LoopFrame__Iter.__modifies(this), 
      Set#UnionOne(Set#Empty(): Set Box, $Box(c#0)));
    assume Set#Equal(read($Heap, this, _module.LoopFrame__Iter.__new), Set#Empty(): Set Box);
    assume _module.LoopFrame__Iter.__decreases0(this) == c#0;
    assume _yieldCount#0 == 0;
    call $YieldHavoc(this, _module.LoopFrame__Iter.__reads(this), read($Heap, this, _module.LoopFrame__Iter.__new));
    $_OldIterHeap := $Heap;
    // ----- yield statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(453,3)
    $Heap := update($Heap, 
      this, 
      _module.LoopFrame__Iter.ys, 
      Seq#Append(read($Heap, this, _module.LoopFrame__Iter.ys), 
        Seq#Build(Seq#Empty(): Seq Box, $Box(read($Heap, this, _module.LoopFrame__Iter.y)))));
    _yieldCount#0 := _yieldCount#0 + 1;
    assume _yieldCount#0 == Seq#Length(read($Heap, this, _module.LoopFrame__Iter.ys));
    assume $IsGoodHeap($Heap);
    assert {:subsumption 0} Seq#Length(read($Heap, this, _module.LoopFrame__Iter.ys)) <= LitInt(2);
    assume Seq#Length(read($Heap, this, _module.LoopFrame__Iter.ys)) <= LitInt(2);
    call $YieldHavoc(this, _module.LoopFrame__Iter.__reads(this), read($Heap, this, _module.LoopFrame__Iter.__new));
    $_OldIterHeap := $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(453,7)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(454,5)
    assume true;
    assert $_Frame[this, _module.LoopFrame__Iter.y];
    assume true;
    $rhs#0 := LitInt(10);
    $Heap := update($Heap, this, _module.LoopFrame__Iter.y, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(454,9)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(455,10)
    assert _module.LoopFrame__Iter.c(this) != null;
    assume true;
    assert $_Frame[_module.LoopFrame__Iter.c(this), _module.Cell.data];
    assume true;
    $rhs#1 := LitInt(10);
    $Heap := update($Heap, _module.LoopFrame__Iter.c(this), _module.Cell.data, $rhs#1);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(455,14)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(456,9)
    assume true;
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._module.Cell?();
    assume !read($Heap, $nw, alloc);
    $Heap := update($Heap, $nw, alloc, true);
    $Heap := update($Heap, 
      this, 
      _module.LoopFrame__Iter.__new, 
      Set#UnionOne(read($Heap, this, _module.LoopFrame__Iter.__new), $Box($nw)));
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    d#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(456,19)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(457,10)
    assert d#0 != null;
    assume true;
    assert $_Frame[d#0, _module.Cell.data];
    assume true;
    $rhs#2 := LitInt(10);
    $Heap := update($Heap, d#0, _module.Cell.data, $rhs#2);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(457,14)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(458,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := _yieldCount#0;
    havoc $w$loop#0;
    while (true)
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> read($Heap, this, _module.LoopFrame__Iter.y) <= LitInt(11);
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> read($Heap, d#0, _module.Cell.data) <= LitInt(11);
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0
         ==> read($Heap, _module.LoopFrame__Iter.c(this), _module.Cell.data) <= LitInt(11);
      free invariant (forall $o: ref :: 
        { $Heap[$o] } 
        $o != null && read(old($Heap), $o, alloc)
           ==> $Heap[$o] == $PreLoopHeap$loop#0[$o] || $o == this || $o == c#0);
      free invariant $HeapSucc($PreLoopHeap$loop#0, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
        { read($Heap, $o, $f) } 
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
      invariant (forall $o: ref :: 
        { read($Heap, this, _module.LoopFrame__Iter.__new)[$Box($o)] } 
        read($Heap, this, _module.LoopFrame__Iter.__new)[$Box($o)]
           ==> $o != null && !read(old($Heap), $o, alloc));
      free invariant _yieldCount#0 >= $decr_init$loop#00
         && (_yieldCount#0 == $decr_init$loop#00 ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(458,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assume true;
            assume read($Heap, this, _module.LoopFrame__Iter.y) <= LitInt(11);
            assert {:subsumption 0} d#0 != null;
            assume true;
            assume read($Heap, d#0, _module.Cell.data) <= LitInt(11);
            assert {:subsumption 0} _module.LoopFrame__Iter.c(this) != null;
            assume true;
            assume read($Heap, _module.LoopFrame__Iter.c(this), _module.Cell.data) <= LitInt(11);
            assume true;
            assume false;
        }

        assume true;
        if (!Lit(true))
        {
            break;
        }

        $decr$loop#00 := _yieldCount#0;
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(463,5)
        if (*)
        {
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(464,14)
            assume true;
            assert $_Frame[this, _module.LoopFrame__Iter.y];
            assume true;
            $rhs#0_0_0 := read($Heap, this, _module.LoopFrame__Iter.y) + 1;
            $Heap := update($Heap, this, _module.LoopFrame__Iter.y, $rhs#0_0_0);
            assume $IsGoodHeap($Heap);
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(464,26)"} true;
        }
        else
        {
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(466,9)
            assume true;
            assert $_Frame[this, _module.LoopFrame__Iter.y];
            assume true;
            $rhs#0_0 := read($Heap, this, _module.LoopFrame__Iter.y) + 1;
            $Heap := update($Heap, this, _module.LoopFrame__Iter.y, $rhs#0_0);
            assume $IsGoodHeap($Heap);
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(466,16)"} true;
        }

        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(468,12)
        assert _module.LoopFrame__Iter.c(this) != null;
        assume true;
        assert $_Frame[_module.LoopFrame__Iter.c(this), _module.Cell.data];
        assert _module.LoopFrame__Iter.c(this) != null;
        assume true;
        $rhs#0_1 := read($Heap, _module.LoopFrame__Iter.c(this), _module.Cell.data) + 1;
        $Heap := update($Heap, _module.LoopFrame__Iter.c(this), _module.Cell.data, $rhs#0_1);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(468,24)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(469,12)
        assert d#0 != null;
        assume true;
        assert $_Frame[d#0, _module.Cell.data];
        assert d#0 != null;
        assume true;
        $rhs#0_2 := read($Heap, d#0, _module.Cell.data) + 1;
        $Heap := update($Heap, d#0, _module.Cell.data, $rhs#0_2);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(469,24)"} true;
        // ----- yield statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(470,5)
        $Heap := update($Heap, 
          this, 
          _module.LoopFrame__Iter.ys, 
          Seq#Append(read($Heap, this, _module.LoopFrame__Iter.ys), 
            Seq#Build(Seq#Empty(): Seq Box, $Box(read($Heap, this, _module.LoopFrame__Iter.y)))));
        _yieldCount#0 := _yieldCount#0 + 1;
        assume _yieldCount#0 == Seq#Length(read($Heap, this, _module.LoopFrame__Iter.ys));
        assume $IsGoodHeap($Heap);
        assert {:subsumption 0} Seq#Length(read($Heap, this, _module.LoopFrame__Iter.ys)) <= LitInt(2);
        assume Seq#Length(read($Heap, this, _module.LoopFrame__Iter.ys)) <= LitInt(2);
        call $YieldHavoc(this, _module.LoopFrame__Iter.__reads(this), read($Heap, this, _module.LoopFrame__Iter.__new));
        $_OldIterHeap := $Heap;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(470,9)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(458,3)
        assert _yieldCount#0 > $decr$loop#00;
        assume true;
        assume true;
        assume true;
    }
}



const unique class._module.NewRemainsFresh?: ClassName;

function Tclass._module.NewRemainsFresh?() : Ty;

const unique Tagclass._module.NewRemainsFresh?: TyTag;

// Tclass._module.NewRemainsFresh? Tag
axiom Tag(Tclass._module.NewRemainsFresh?()) == Tagclass._module.NewRemainsFresh?
   && TagFamily(Tclass._module.NewRemainsFresh?()) == tytagFamily$NewRemainsFresh;

// Box/unbox axiom for Tclass._module.NewRemainsFresh?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.NewRemainsFresh?()) } 
  $IsBox(bx, Tclass._module.NewRemainsFresh?())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.NewRemainsFresh?()));

// NewRemainsFresh: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.NewRemainsFresh?()) } 
  $Is($o, Tclass._module.NewRemainsFresh?())
     <==> $o == null || dtype($o) == Tclass._module.NewRemainsFresh?());

// NewRemainsFresh: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.NewRemainsFresh?(), $h) } 
  $IsAlloc($o, Tclass._module.NewRemainsFresh?(), $h)
     <==> $o == null || read($h, $o, alloc));

function _module.NewRemainsFresh.x(ref) : int;

// NewRemainsFresh.x: Type axiom
axiom (forall $o: ref :: 
  { _module.NewRemainsFresh.x($o) } 
  $o != null && dtype($o) == Tclass._module.NewRemainsFresh?()
     ==> $Is(_module.NewRemainsFresh.x($o), Tclass._System.nat()));

// NewRemainsFresh.x: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.NewRemainsFresh.x($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.NewRemainsFresh?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.NewRemainsFresh.x($o), Tclass._System.nat(), $h));

axiom FDim(_module.NewRemainsFresh.y) == 0
   && FieldOfDecl(class._module.NewRemainsFresh?, field$y)
     == _module.NewRemainsFresh.y
   && !$IsGhostField(_module.NewRemainsFresh.y);

const _module.NewRemainsFresh.y: Field int;

// NewRemainsFresh.y: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.NewRemainsFresh.y) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.NewRemainsFresh?()
     ==> $Is(read($h, $o, _module.NewRemainsFresh.y), Tclass._System.nat()));

// NewRemainsFresh.y: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.NewRemainsFresh.y) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.NewRemainsFresh?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.NewRemainsFresh.y), Tclass._System.nat(), $h));

axiom FDim(_module.NewRemainsFresh.ys) == 0
   && FieldOfDecl(class._module.NewRemainsFresh?, field$ys)
     == _module.NewRemainsFresh.ys
   && $IsGhostField(_module.NewRemainsFresh.ys);

const _module.NewRemainsFresh.ys: Field (Seq Box);

// NewRemainsFresh.ys: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.NewRemainsFresh.ys) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.NewRemainsFresh?()
     ==> $Is(read($h, $o, _module.NewRemainsFresh.ys), TSeq(Tclass._System.nat())));

// NewRemainsFresh.ys: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.NewRemainsFresh.ys) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.NewRemainsFresh?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.NewRemainsFresh.ys), TSeq(Tclass._System.nat()), $h));

function _module.NewRemainsFresh.__reads(ref) : Set Box;

// NewRemainsFresh._reads: Type axiom
axiom (forall $o: ref :: 
  { _module.NewRemainsFresh.__reads($o) } 
  $o != null && dtype($o) == Tclass._module.NewRemainsFresh?()
     ==> $Is(_module.NewRemainsFresh.__reads($o), TSet(Tclass._System.object?())));

// NewRemainsFresh._reads: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.NewRemainsFresh.__reads($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.NewRemainsFresh?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.NewRemainsFresh.__reads($o), TSet(Tclass._System.object?()), $h));

function _module.NewRemainsFresh.__modifies(ref) : Set Box;

// NewRemainsFresh._modifies: Type axiom
axiom (forall $o: ref :: 
  { _module.NewRemainsFresh.__modifies($o) } 
  $o != null && dtype($o) == Tclass._module.NewRemainsFresh?()
     ==> $Is(_module.NewRemainsFresh.__modifies($o), TSet(Tclass._System.object?())));

// NewRemainsFresh._modifies: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.NewRemainsFresh.__modifies($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.NewRemainsFresh?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.NewRemainsFresh.__modifies($o), TSet(Tclass._System.object?()), $h));

axiom FDim(_module.NewRemainsFresh.__new) == 0
   && FieldOfDecl(class._module.NewRemainsFresh?, field$_new)
     == _module.NewRemainsFresh.__new
   && $IsGhostField(_module.NewRemainsFresh.__new);

const _module.NewRemainsFresh.__new: Field (Set Box);

// NewRemainsFresh._new: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.NewRemainsFresh.__new) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.NewRemainsFresh?()
     ==> $Is(read($h, $o, _module.NewRemainsFresh.__new), TSet(Tclass._System.object?())));

// NewRemainsFresh._new: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.NewRemainsFresh.__new) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.NewRemainsFresh?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.NewRemainsFresh.__new), TSet(Tclass._System.object?()), $h));

function _module.NewRemainsFresh.__decreases0(ref) : int;

// NewRemainsFresh._decreases0: Type axiom
axiom (forall $o: ref :: 
  { _module.NewRemainsFresh.__decreases0($o) } 
  $o != null && dtype($o) == Tclass._module.NewRemainsFresh?()
     ==> $Is(_module.NewRemainsFresh.__decreases0($o), TInt));

// NewRemainsFresh._decreases0: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.NewRemainsFresh.__decreases0($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.NewRemainsFresh?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.NewRemainsFresh.__decreases0($o), TInt, $h));

function Tclass._module.NewRemainsFresh() : Ty;

const unique Tagclass._module.NewRemainsFresh: TyTag;

// Tclass._module.NewRemainsFresh Tag
axiom Tag(Tclass._module.NewRemainsFresh()) == Tagclass._module.NewRemainsFresh
   && TagFamily(Tclass._module.NewRemainsFresh()) == tytagFamily$NewRemainsFresh;

// Box/unbox axiom for Tclass._module.NewRemainsFresh
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.NewRemainsFresh()) } 
  $IsBox(bx, Tclass._module.NewRemainsFresh())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.NewRemainsFresh()));

procedure CheckWellformed$$_module.NewRemainsFresh.__ctor(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.NewRemainsFresh())
         && $IsAlloc(this, Tclass._module.NewRemainsFresh(), $Heap), 
    x#0: int where LitInt(0) <= x#0);
  free requires 39 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.NewRemainsFresh.__ctor(x#0: int where LitInt(0) <= x#0)
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass._module.NewRemainsFresh())
         && $IsAlloc(this, Tclass._module.NewRemainsFresh(), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures _module.NewRemainsFresh.x(this) == x#0;
  free ensures true;
  ensures Seq#Equal(read($Heap, this, _module.NewRemainsFresh.ys), Seq#Empty(): Seq Box);
  free ensures _module.NewRemainsFresh.Valid#canCall($Heap, this);
  ensures _module.NewRemainsFresh.Valid($Heap, this);
  free ensures true;
  ensures Set#Equal(_module.NewRemainsFresh.__reads(this), Set#Empty(): Set Box);
  free ensures true;
  ensures Set#Equal(_module.NewRemainsFresh.__modifies(this), Set#Empty(): Set Box);
  free ensures true;
  ensures Set#Equal(read($Heap, this, _module.NewRemainsFresh.__new), Set#Empty(): Set Box);
  free ensures true;
  ensures _module.NewRemainsFresh.__decreases0(this) == x#0;
  // constructor allocates the object
  ensures !read(old($Heap), this, alloc);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



// function declaration for _module.NewRemainsFresh.Valid
function _module.NewRemainsFresh.Valid($heap: Heap, this: ref) : bool;

function _module.NewRemainsFresh.Valid#canCall($heap: Heap, this: ref) : bool;

// frame axiom for _module.NewRemainsFresh.Valid
axiom (forall $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.NewRemainsFresh.Valid($h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.NewRemainsFresh())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && (
            $o == this
             || _module.NewRemainsFresh.__reads(this)[$Box($o)]
             || read($h0, this, _module.NewRemainsFresh.__new)[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.NewRemainsFresh.Valid($h0, this)
       == _module.NewRemainsFresh.Valid($h1, this));

// consequence axiom for _module.NewRemainsFresh.Valid
axiom 38 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref :: 
    { _module.NewRemainsFresh.Valid($Heap, this) } 
    _module.NewRemainsFresh.Valid#canCall($Heap, this)
         || (38 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.NewRemainsFresh())
           && $IsAlloc(this, Tclass._module.NewRemainsFresh(), $Heap))
       ==> true);

function _module.NewRemainsFresh.Valid#requires(Heap, ref) : bool;

// #requires axiom for _module.NewRemainsFresh.Valid
axiom (forall $Heap: Heap, this: ref :: 
  { _module.NewRemainsFresh.Valid#requires($Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.NewRemainsFresh())
       && $IsAlloc(this, Tclass._module.NewRemainsFresh(), $Heap)
     ==> _module.NewRemainsFresh.Valid#requires($Heap, this) == true);

procedure CheckWellformed$$_module.NewRemainsFresh.Valid(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.NewRemainsFresh())
         && $IsAlloc(this, Tclass._module.NewRemainsFresh(), $Heap));
  free requires 38 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.NewRemainsFresh.Valid(this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function Valid
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(474,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> $o == this
           || _module.NewRemainsFresh.__reads(this)[$Box($o)]
           || read($Heap, this, _module.NewRemainsFresh.__new)[$Box($o)]);
    b$reqreads#0 := $_Frame[this, _module.NewRemainsFresh.__new];
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



procedure Call$$_module.NewRemainsFresh.MoveNext(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.NewRemainsFresh())
         && $IsAlloc(this, Tclass._module.NewRemainsFresh(), $Heap))
   returns (more#0: bool);
  // user-defined preconditions
  requires _module.NewRemainsFresh.Valid($Heap, this);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    read($Heap, this, _module.NewRemainsFresh.__new)[$Box($o)]
         && !read(old($Heap), this, _module.NewRemainsFresh.__new)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures !read($Heap, this, _module.NewRemainsFresh.__new)[$Box(null)];
  free ensures more#0 ==> _module.NewRemainsFresh.Valid#canCall($Heap, this);
  ensures more#0 ==> _module.NewRemainsFresh.Valid($Heap, this);
  free ensures true;
  ensures Seq#Equal(read($Heap, this, _module.NewRemainsFresh.ys), 
    (if more#0
       then Seq#Append(read(old($Heap), this, _module.NewRemainsFresh.ys), 
        Seq#Build(Seq#Empty(): Seq Box, $Box(read($Heap, this, _module.NewRemainsFresh.y))))
       else read(old($Heap), this, _module.NewRemainsFresh.ys)));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || 
        $o == this
         || _module.NewRemainsFresh.__modifies(this)[$Box($o)]
         || read(old($Heap), this, _module.NewRemainsFresh.__new)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



// _module.NewRemainsFresh: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.NewRemainsFresh()) } 
  $Is(c#0, Tclass._module.NewRemainsFresh())
     <==> $Is(c#0, Tclass._module.NewRemainsFresh?()) && c#0 != null);

// _module.NewRemainsFresh: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.NewRemainsFresh(), $h) } 
  $IsAlloc(c#0, Tclass._module.NewRemainsFresh(), $h)
     <==> $IsAlloc(c#0, Tclass._module.NewRemainsFresh?(), $h));

procedure CheckWellformed$$_module.NewRemainsFresh(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.NewRemainsFresh())
         && $IsAlloc(this, Tclass._module.NewRemainsFresh(), $Heap), 
    x#0: int where LitInt(0) <= x#0);
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Impl$$_module.NewRemainsFresh(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.NewRemainsFresh())
         && $IsAlloc(this, Tclass._module.NewRemainsFresh(), $Heap), 
    x#0: int where LitInt(0) <= x#0);
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.NewRemainsFresh(this: ref, x#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _yieldCount#0: int
     where _yieldCount#0 == Seq#Length(read($Heap, this, _module.NewRemainsFresh.ys));
  var $_OldIterHeap: Heap
     where $IsGoodHeap($_OldIterHeap) && $HeapSucc($_OldIterHeap, $Heap);
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var $decr$loop#00: int;
  var z#0: ref;
  var c#0: ref
     where $Is(c#0, Tclass._module.Cell()) && $IsAlloc(c#0, Tclass._module.Cell(), $Heap);
  var $nw: ref;
  var z#2: ref;
  var z#4: ref;

    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(474,9): initial state"} true;
    assume _module.NewRemainsFresh.x(this) == x#0;
    assume Seq#Equal(read($Heap, this, _module.NewRemainsFresh.ys), Seq#Empty(): Seq Box);
    assume _module.NewRemainsFresh.Valid($Heap, this);
    assume Set#Equal(_module.NewRemainsFresh.__reads(this), Set#Empty(): Set Box);
    assume Set#Equal(_module.NewRemainsFresh.__modifies(this), Set#Empty(): Set Box);
    assume Set#Equal(read($Heap, this, _module.NewRemainsFresh.__new), Set#Empty(): Set Box);
    assume _module.NewRemainsFresh.__decreases0(this) == x#0;
    assume _yieldCount#0 == 0;
    call $YieldHavoc(this, _module.NewRemainsFresh.__reads(this), read($Heap, this, _module.NewRemainsFresh.__new));
    $_OldIterHeap := $Heap;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(476,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := _yieldCount#0;
    havoc $w$loop#0;
    while (true)
      free invariant (forall $o: ref :: 
        { $Heap[$o] } 
        $o != null && read(old($Heap), $o, alloc)
           ==> $Heap[$o] == $PreLoopHeap$loop#0[$o] || $o == this);
      free invariant $HeapSucc($PreLoopHeap$loop#0, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
        { read($Heap, $o, $f) } 
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
      invariant (forall $o: ref :: 
        { read($Heap, this, _module.NewRemainsFresh.__new)[$Box($o)] } 
        read($Heap, this, _module.NewRemainsFresh.__new)[$Box($o)]
           ==> $o != null && !read(old($Heap), $o, alloc));
      free invariant _yieldCount#0 >= $decr_init$loop#00
         && (_yieldCount#0 == $decr_init$loop#00 ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(476,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assume true;
            assume false;
        }

        if (*)
        {
            break;
        }

        $decr$loop#00 := _yieldCount#0;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(478,5)
        assume true;
        assert LitInt(0)
           <= _module.NewRemainsFresh.x(this) + read($Heap, this, _module.NewRemainsFresh.y);
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(479,5)
        if (*)
        {
            // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(480,7)
            // Begin Comprehension WF check
            havoc z#0;
            if ($Is(z#0, Tclass._System.object?()))
            {
                if (read($Heap, this, _module.NewRemainsFresh.__new)[$Box(z#0)])
                {
                }
            }

            // End Comprehension WF check
            assume true;
            assert (forall z#1: ref :: 
              $Is(z#1, Tclass._System.object?())
                 ==> 
                read($Heap, this, _module.NewRemainsFresh.__new)[$Box(z#1)]
                 ==> z#1 != null && !read(old($Heap), z#1, alloc));
        }
        else
        {
        }

        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(482,11)
        assume true;
        havoc $nw;
        assume $nw != null && dtype($nw) == Tclass._module.Cell?();
        assume !read($Heap, $nw, alloc);
        $Heap := update($Heap, $nw, alloc, true);
        $Heap := update($Heap, 
          this, 
          _module.NewRemainsFresh.__new, 
          Set#UnionOne(read($Heap, this, _module.NewRemainsFresh.__new), $Box($nw)));
        assume $IsGoodHeap($Heap);
        assume $IsHeapAnchor($Heap);
        c#0 := $nw;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(482,21)"} true;
        // ----- yield statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(483,5)
        $Heap := update($Heap, 
          this, 
          _module.NewRemainsFresh.ys, 
          Seq#Append(read($Heap, this, _module.NewRemainsFresh.ys), 
            Seq#Build(Seq#Empty(): Seq Box, $Box(read($Heap, this, _module.NewRemainsFresh.y)))));
        _yieldCount#0 := _yieldCount#0 + 1;
        assume _yieldCount#0 == Seq#Length(read($Heap, this, _module.NewRemainsFresh.ys));
        assume $IsGoodHeap($Heap);
        call $YieldHavoc(this, _module.NewRemainsFresh.__reads(this), read($Heap, this, _module.NewRemainsFresh.__new));
        $_OldIterHeap := $Heap;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(483,9)"} true;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(484,5)
        // Begin Comprehension WF check
        havoc z#2;
        if ($Is(z#2, Tclass._System.object?()))
        {
            if (read($Heap, this, _module.NewRemainsFresh.__new)[$Box(z#2)])
            {
            }
        }

        // End Comprehension WF check
        assume true;
        assert (forall z#3: ref :: 
          $Is(z#3, Tclass._System.object?())
             ==> 
            read($Heap, this, _module.NewRemainsFresh.__new)[$Box(z#3)]
             ==> z#3 != null && !read(old($Heap), z#3, alloc));
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(476,3)
        assert _yieldCount#0 > $decr$loop#00;
    }

    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(486,3)
    // Begin Comprehension WF check
    havoc z#4;
    if ($Is(z#4, Tclass._System.object?()))
    {
        if (read($Heap, this, _module.NewRemainsFresh.__new)[$Box(z#4)])
        {
        }
    }

    // End Comprehension WF check
    assume true;
    assert (forall z#5: ref :: 
      $Is(z#5, Tclass._System.object?())
         ==> 
        read($Heap, this, _module.NewRemainsFresh.__new)[$Box(z#5)]
         ==> z#5 != null && !read(old($Heap), z#5, alloc));
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

procedure CheckWellformed$$_module.__default._default_Main();
  free requires 44 == $FunctionContextHeight;
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
  free requires 44 == $FunctionContextHeight;
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
  var m#0: ref
     where $Is(m#0, Tclass._module.MyIter(TInt))
       && $IsAlloc(m#0, Tclass._module.MyIter(TInt), $Heap);
  var $nw: ref;
  var q##0: int;
  var a#0: int;
  var mer#0: bool;
  var $rhs##0: bool;
  var $rhs##1_0: bool;
  var $rhs##1_1: bool;
  var n#0: ref
     where $Is(n#0, Tclass._module.MyIntIter())
       && $IsAlloc(n#0, Tclass._module.MyIntIter(), $Heap);
  var patience#0: int;
  var $Heap_at_0: Heap;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var $decr$loop#00: int;
  var more#2_0: bool;
  var $rhs##2_0: bool;
  var o#0: ref
     where $Is(o#0, Tclass._module.Naturals())
       && $IsAlloc(o#0, Tclass._module.Naturals(), $Heap);
  var u##0: int;
  var remaining#0: int;
  var $PreLoopHeap$loop#1: Heap;
  var $decr_init$loop#10: int;
  var $w$loop#1: bool;
  var $decr$loop#10: int;
  var more#3_0: bool;
  var $rhs##3_0: bool;

    // AddMethodImpl: Main, Impl$$_module.__default._default_Main
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(29,14): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(30,9)
    assume true;
    // ----- init call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(30,12)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    q##0 := LitInt(12);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $nw := Call$$_module.MyIter.__ctor(TInt, $Box(q##0));
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(30,25)"} true;
    m#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(30,25)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(31,3)
    assert {:subsumption 0} m#0 != null;
    assert {:subsumption 0} m#0 != null;
    if (Seq#Equal(read($Heap, m#0, _module.MyIter.ys), read($Heap, m#0, _module.MyIter.xs)))
    {
        assert {:subsumption 0} m#0 != null;
    }

    assume true;
    assert {:subsumption 0} Seq#Equal(read($Heap, m#0, _module.MyIter.ys), read($Heap, m#0, _module.MyIter.xs));
    assert {:subsumption 0} Seq#Equal(read($Heap, m#0, _module.MyIter.xs), Seq#Empty(): Seq Box);
    assume Seq#Equal(read($Heap, m#0, _module.MyIter.ys), read($Heap, m#0, _module.MyIter.xs))
       && Seq#Equal(read($Heap, m#0, _module.MyIter.xs), Seq#Empty(): Seq Box);
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(32,9)
    assume true;
    assert m#0 != null;
    assume true;
    a#0 := $Unbox(read($Heap, m#0, _module.MyIter.x)): int;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(32,14)"} true;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(33,3)
    assume true;
    if (a#0 <= LitInt(13))
    {
        // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(34,5)
        assume true;
        assert {:subsumption 0} m#0 != null;
        assume true;
        assume true;
    }
    else
    {
    }

    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(37,24)
    assume true;
    // TrCallStmt: Adding lhs with type bool
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert m#0 != null;
    assert (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && read($Heap, $o, alloc)
           && (
            $o == m#0
             || _module.MyIter.__modifies(m#0)[$Box($o)]
             || read($Heap, m#0, _module.MyIter.__new)[$Box($o)])
         ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0 := Call$$_module.MyIter.MoveNext(TInt, m#0);
    // TrCallStmt: After ProcessCallStmt
    mer#0 := $rhs##0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(37,25)"} true;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(38,3)
    assume true;
    if (mer#0)
    {
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(39,22)
        assume true;
        // TrCallStmt: Adding lhs with type bool
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        assert m#0 != null;
        assert (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null
               && read($Heap, $o, alloc)
               && (
                $o == m#0
                 || _module.MyIter.__modifies(m#0)[$Box($o)]
                 || read($Heap, m#0, _module.MyIter.__new)[$Box($o)])
             ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call $rhs##1_0 := Call$$_module.MyIter.MoveNext(TInt, m#0);
        // TrCallStmt: After ProcessCallStmt
        mer#0 := $rhs##1_0;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(39,23)"} true;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(40,22)
        assume true;
        // TrCallStmt: Adding lhs with type bool
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        assert m#0 != null;
        assert (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null
               && read($Heap, $o, alloc)
               && (
                $o == m#0
                 || _module.MyIter.__modifies(m#0)[$Box($o)]
                 || read($Heap, m#0, _module.MyIter.__new)[$Box($o)])
             ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call $rhs##1_1 := Call$$_module.MyIter.MoveNext(TInt, m#0);
        // TrCallStmt: After ProcessCallStmt
        mer#0 := $rhs##1_1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(40,23)"} true;
    }
    else
    {
    }

    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(43,9)
    assume true;
    // ----- init call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(43,12)
    // TrCallStmt: Before ProcessCallStmt
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $nw := Call$$_module.MyIntIter.__ctor();
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(43,26)"} true;
    n#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(43,26)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(44,16)
    assume true;
    assume true;
    patience#0 := LitInt(10);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(44,20)"} true;
    $Heap_at_0 := $Heap;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(45,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := (if patience#0 <= LitInt(0) then 0 - patience#0 else patience#0 - 0);
    havoc $w$loop#0;
    while (true)
      free invariant $w$loop#0 ==> _module.MyIntIter.Valid#canCall($Heap, n#0);
      invariant $w$loop#0 ==> _module.MyIntIter.Valid($Heap, n#0);
      invariant $w$loop#0
         ==> (forall $o: ref :: 
          { read($Heap, n#0, _module.MyIntIter.__new)[$Box($o)] } 
          read($Heap, n#0, _module.MyIntIter.__new)[$Box($o)]
             ==> $o != null && !read(old($Heap), $o, alloc));
      free invariant (forall $o: ref :: 
        { $Heap[$o] } 
        $o != null && read(old($Heap), $o, alloc)
           ==> $Heap[$o] == $PreLoopHeap$loop#0[$o]);
      free invariant $HeapSucc($PreLoopHeap$loop#0, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
        { read($Heap, $o, $f) } 
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
      free invariant (if patience#0 <= LitInt(0) then 0 - patience#0 else patience#0 - 0)
           <= $decr_init$loop#00
         && ((if patience#0 <= LitInt(0) then 0 - patience#0 else patience#0 - 0)
             == $decr_init$loop#00
           ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(45,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assert {:subsumption 0} n#0 != null;
            assume _module.MyIntIter.Valid#canCall($Heap, n#0);
            if (_module.MyIntIter.Valid($Heap, n#0))
            {
                assert {:subsumption 0} n#0 != null;
            }

            assume _module.MyIntIter.Valid#canCall($Heap, n#0);
            assume _module.MyIntIter.Valid($Heap, n#0)
               && (forall $o: ref :: 
                { read($Heap, n#0, _module.MyIntIter.__new)[$Box($o)] } 
                read($Heap, n#0, _module.MyIntIter.__new)[$Box($o)]
                   ==> $o != null && !read(old($Heap), $o, alloc));
            if (patience#0 <= LitInt(0))
            {
            }
            else
            {
            }

            assume true;
            assume false;
        }

        assume true;
        if (patience#0 == 0)
        {
            break;
        }

        $decr$loop#00 := (if patience#0 <= LitInt(0) then 0 - patience#0 else patience#0 - 0);
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(48,27)
        assume true;
        // TrCallStmt: Adding lhs with type bool
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        assert n#0 != null;
        assert (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null
               && read($Heap, $o, alloc)
               && (
                $o == n#0
                 || _module.MyIntIter.__modifies(n#0)[$Box($o)]
                 || read($Heap, n#0, _module.MyIntIter.__new)[$Box($o)])
             ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call $rhs##2_0 := Call$$_module.MyIntIter.MoveNext(n#0);
        // TrCallStmt: After ProcessCallStmt
        more#2_0 := $rhs##2_0;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(48,28)"} true;
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(49,5)
        assume true;
        if (!more#2_0)
        {
            // ----- break statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(49,18)
            goto after_0;
        }
        else
        {
        }

        // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(50,5)
        assert {:subsumption 0} n#0 != null;
        assume true;
        assume true;
        assert {:subsumption 0} n#0 != null;
        assume true;
        assume true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(51,14)
        assume true;
        assume true;
        patience#0 := patience#0 - 1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(51,28)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(45,3)
        assert 0 <= $decr$loop#00
           || (if patience#0 <= LitInt(0) then 0 - patience#0 else patience#0 - 0)
             == $decr$loop#00;
        assert (if patience#0 <= LitInt(0) then 0 - patience#0 else patience#0 - 0)
           < $decr$loop#00;
        assume _module.MyIntIter.Valid#canCall($Heap, n#0);
    }

  after_0:
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(54,9)
    assume true;
    // ----- init call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(54,12)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    u##0 := LitInt(18);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $nw := Call$$_module.Naturals.__ctor(u##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(54,27)"} true;
    o#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(54,27)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(55,17)
    assume true;
    assume true;
    remaining#0 := LitInt(100);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(55,22)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(56,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#1 := $Heap;
    $decr_init$loop#10 := (if remaining#0 <= LitInt(0) then 0 - remaining#0 else remaining#0 - 0);
    havoc $w$loop#1;
    while (true)
      free invariant $w$loop#1 ==> _module.Naturals.Valid#canCall($Heap, o#0);
      invariant $w$loop#1 ==> _module.Naturals.Valid($Heap, o#0);
      invariant $w$loop#1
         ==> (forall $o: ref :: 
          { read($Heap, o#0, _module.Naturals.__new)[$Box($o)] } 
          read($Heap, o#0, _module.Naturals.__new)[$Box($o)]
             ==> $o != null && !read(old($Heap), $o, alloc));
      free invariant (forall $o: ref :: 
        { $Heap[$o] } 
        $o != null && read(old($Heap), $o, alloc)
           ==> $Heap[$o] == $PreLoopHeap$loop#1[$o]);
      free invariant $HeapSucc($PreLoopHeap$loop#1, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
        { read($Heap, $o, $f) } 
        $o != null && read($PreLoopHeap$loop#1, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#1, $o, $f) || $_Frame[$o, $f]);
      free invariant (if remaining#0 <= LitInt(0) then 0 - remaining#0 else remaining#0 - 0)
           <= $decr_init$loop#10
         && ((if remaining#0 <= LitInt(0) then 0 - remaining#0 else remaining#0 - 0)
             == $decr_init$loop#10
           ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(56,2): after some loop iterations"} true;
        if (!$w$loop#1)
        {
            assert {:subsumption 0} o#0 != null;
            assume _module.Naturals.Valid#canCall($Heap, o#0);
            if (_module.Naturals.Valid($Heap, o#0))
            {
                assert {:subsumption 0} o#0 != null;
            }

            assume _module.Naturals.Valid#canCall($Heap, o#0);
            assume _module.Naturals.Valid($Heap, o#0)
               && (forall $o: ref :: 
                { read($Heap, o#0, _module.Naturals.__new)[$Box($o)] } 
                read($Heap, o#0, _module.Naturals.__new)[$Box($o)]
                   ==> $o != null && !read(old($Heap), $o, alloc));
            if (remaining#0 <= LitInt(0))
            {
            }
            else
            {
            }

            assume true;
            assume false;
        }

        assume true;
        if (remaining#0 == 0)
        {
            break;
        }

        $decr$loop#10 := (if remaining#0 <= LitInt(0) then 0 - remaining#0 else remaining#0 - 0);
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(59,27)
        assume true;
        // TrCallStmt: Adding lhs with type bool
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        assert o#0 != null;
        assert (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null
               && read($Heap, $o, alloc)
               && (
                $o == o#0
                 || _module.Naturals.__modifies(o#0)[$Box($o)]
                 || read($Heap, o#0, _module.Naturals.__new)[$Box($o)])
             ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call $rhs##3_0 := Call$$_module.Naturals.MoveNext(o#0);
        // TrCallStmt: After ProcessCallStmt
        more#3_0 := $rhs##3_0;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(59,28)"} true;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(60,5)
        assume true;
        assert more#3_0;
        // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(61,5)
        assert {:subsumption 0} o#0 != null;
        assume true;
        assume true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(62,15)
        assume true;
        assume true;
        remaining#0 := remaining#0 - 1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(62,30)"} true;
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(63,5)
        assert LitInt(10) != 0;
        assume true;
        if (Mod(remaining#0, LitInt(10)) == LitInt(0))
        {
            // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(63,32)
            assume true;
        }
        else
        {
        }

        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(56,3)
        assert 0 <= $decr$loop#10
           || (if remaining#0 <= LitInt(0) then 0 - remaining#0 else remaining#0 - 0)
             == $decr$loop#10;
        assert (if remaining#0 <= LitInt(0) then 0 - remaining#0 else remaining#0 - 0)
           < $decr$loop#10;
        assume _module.Naturals.Valid#canCall($Heap, o#0);
    }
}



procedure CheckWellformed$$_module.__default.TestIterA();
  free requires 46 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.TestIterA();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.TestIterA() returns ($_reverifyPost: bool);
  free requires 46 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.TestIterA() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var c#0: ref
     where $Is(c#0, Tclass._module.Cell()) && $IsAlloc(c#0, Tclass._module.Cell(), $Heap);
  var $nw: ref;
  var iter#0: ref
     where $Is(iter#0, Tclass._module.IterA())
       && $IsAlloc(iter#0, Tclass._module.IterA(), $Heap);
  var c##0: ref;
  var tmp#0: int;
  var more#0: bool;
  var $rhs##0: bool;

    // AddMethodImpl: TestIterA, Impl$$_module.__default.TestIterA
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(84,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(85,9)
    assume true;
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._module.Cell?();
    assume !read($Heap, $nw, alloc);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    c#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(85,19)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(86,12)
    assume true;
    // ----- init call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(86,15)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    c##0 := c#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $nw := Call$$_module.IterA.__ctor(c##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(86,26)"} true;
    iter#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(86,26)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(87,11)
    assume true;
    assert c#0 != null;
    assume true;
    tmp#0 := read($Heap, c#0, _module.Cell.data);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(87,19)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(88,28)
    assume true;
    // TrCallStmt: Adding lhs with type bool
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert iter#0 != null;
    assert (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && read($Heap, $o, alloc)
           && (
            $o == iter#0
             || _module.IterA.__modifies(iter#0)[$Box($o)]
             || read($Heap, iter#0, _module.IterA.__new)[$Box($o)])
         ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0 := Call$$_module.IterA.MoveNext(iter#0);
    // TrCallStmt: After ProcessCallStmt
    more#0 := $rhs##0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(88,29)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(89,3)
    assert {:subsumption 0} c#0 != null;
    assume true;
    assert tmp#0 == read($Heap, c#0, _module.Cell.data);
}



procedure CheckWellformed$$_module.__default.TestIterB();
  free requires 48 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.TestIterB();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.TestIterB() returns ($_reverifyPost: bool);
  free requires 48 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.TestIterB() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var c#0: ref
     where $Is(c#0, Tclass._module.Cell()) && $IsAlloc(c#0, Tclass._module.Cell(), $Heap);
  var $nw: ref;
  var iter#0: ref
     where $Is(iter#0, Tclass._module.IterB())
       && $IsAlloc(iter#0, Tclass._module.IterB(), $Heap);
  var c##0: ref;
  var tmp#0: int;
  var more#0: bool;
  var $rhs##0: bool;

    // AddMethodImpl: TestIterB, Impl$$_module.__default.TestIterB
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(111,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(112,9)
    assume true;
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._module.Cell?();
    assume !read($Heap, $nw, alloc);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    c#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(112,19)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(113,12)
    assume true;
    // ----- init call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(113,15)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    c##0 := c#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $nw := Call$$_module.IterB.__ctor(c##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(113,26)"} true;
    iter#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(113,26)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(114,11)
    assume true;
    assert c#0 != null;
    assume true;
    tmp#0 := read($Heap, c#0, _module.Cell.data);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(114,19)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(115,28)
    assume true;
    // TrCallStmt: Adding lhs with type bool
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert iter#0 != null;
    assert (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && read($Heap, $o, alloc)
           && (
            $o == iter#0
             || _module.IterB.__modifies(iter#0)[$Box($o)]
             || read($Heap, iter#0, _module.IterB.__new)[$Box($o)])
         ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0 := Call$$_module.IterB.MoveNext(iter#0);
    // TrCallStmt: After ProcessCallStmt
    more#0 := $rhs##0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(115,29)"} true;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(116,3)
    assume true;
    if (more#0)
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(117,5)
        assert {:subsumption 0} c#0 != null;
        assume true;
        assert tmp#0 == read($Heap, c#0, _module.Cell.data);
    }
    else
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(119,5)
        assert {:subsumption 0} c#0 != null;
        assume true;
        assert tmp#0 == read($Heap, c#0, _module.Cell.data);
    }
}



procedure CheckWellformed$$_module.__default.TestIterC();
  free requires 50 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.TestIterC();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.TestIterC() returns ($_reverifyPost: bool);
  free requires 50 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.TestIterC() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var c#0: ref
     where $Is(c#0, Tclass._module.Cell()) && $IsAlloc(c#0, Tclass._module.Cell(), $Heap);
  var $nw: ref;
  var iter#0: ref
     where $Is(iter#0, Tclass._module.IterC())
       && $IsAlloc(iter#0, Tclass._module.IterC(), $Heap);
  var c##0: ref;
  var tmp#0: int;
  var more#0: bool;
  var $rhs##0: bool;
  var c##1: ref;
  var $rhs#0: int;
  var $rhs##1: bool;

    // AddMethodImpl: TestIterC, Impl$$_module.__default.TestIterC
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(142,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(143,9)
    assume true;
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._module.Cell?();
    assume !read($Heap, $nw, alloc);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    c#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(143,19)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(144,12)
    assume true;
    // ----- init call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(144,15)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    c##0 := c#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $nw := Call$$_module.IterC.__ctor(c##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(144,26)"} true;
    iter#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(144,26)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(145,11)
    assume true;
    assert c#0 != null;
    assume true;
    tmp#0 := read($Heap, c#0, _module.Cell.data);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(145,19)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(146,28)
    assume true;
    // TrCallStmt: Adding lhs with type bool
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert iter#0 != null;
    assert (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && read($Heap, $o, alloc)
           && (
            $o == iter#0
             || _module.IterC.__modifies(iter#0)[$Box($o)]
             || read($Heap, iter#0, _module.IterC.__new)[$Box($o)])
         ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0 := Call$$_module.IterC.MoveNext(iter#0);
    // TrCallStmt: After ProcessCallStmt
    more#0 := $rhs##0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(146,29)"} true;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(147,3)
    assume true;
    if (more#0)
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(148,5)
        assert {:subsumption 0} c#0 != null;
        assume true;
        assert tmp#0 == read($Heap, c#0, _module.Cell.data);
    }
    else
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(150,5)
        assert {:subsumption 0} c#0 != null;
        assume true;
        assert tmp#0 == read($Heap, c#0, _module.Cell.data);
    }

    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(153,8)
    assume true;
    // ----- init call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(153,11)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    c##1 := c#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $nw := Call$$_module.IterC.__ctor(c##1);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(153,22)"} true;
    iter#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(153,22)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(154,10)
    assert c#0 != null;
    assume true;
    assert $_Frame[c#0, _module.Cell.data];
    assume true;
    $rhs#0 := LitInt(17);
    $Heap := update($Heap, c#0, _module.Cell.data, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(154,14)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(155,24)
    assume true;
    // TrCallStmt: Adding lhs with type bool
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert iter#0 != null;
    assert (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && read($Heap, $o, alloc)
           && (
            $o == iter#0
             || _module.IterC.__modifies(iter#0)[$Box($o)]
             || read($Heap, iter#0, _module.IterC.__new)[$Box($o)])
         ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##1 := Call$$_module.IterC.MoveNext(iter#0);
    // TrCallStmt: After ProcessCallStmt
    more#0 := $rhs##1;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(155,25)"} true;
}



procedure CheckWellformed$$_module.__default.SomeMethod();
  free requires 26 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.SomeMethod();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.SomeMethod() returns ($_reverifyPost: bool);
  free requires 26 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure CheckWellformed$$_module.__default.AnotherMethod()
   returns (u#0: ref
       where $Is(u#0, Tclass._module.Cell?()) && $IsAlloc(u#0, Tclass._module.Cell?(), $Heap), 
    v#0: ref
       where $Is(v#0, Tclass._module.Cell?()) && $IsAlloc(v#0, Tclass._module.Cell?(), $Heap));
  free requires 27 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.AnotherMethod()
   returns (u#0: ref
       where $Is(u#0, Tclass._module.Cell?()) && $IsAlloc(u#0, Tclass._module.Cell?(), $Heap), 
    v#0: ref
       where $Is(v#0, Tclass._module.Cell?()) && $IsAlloc(v#0, Tclass._module.Cell?(), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures u#0 != null;
  ensures u#0 != null && !read(old($Heap), u#0, alloc);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.AnotherMethod()
   returns (u#0: ref
       where $Is(u#0, Tclass._module.Cell?()) && $IsAlloc(u#0, Tclass._module.Cell?(), $Heap), 
    v#0: ref
       where $Is(v#0, Tclass._module.Cell?()) && $IsAlloc(v#0, Tclass._module.Cell?(), $Heap), 
    $_reverifyPost: bool);
  free requires 27 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures u#0 != null;
  ensures u#0 != null && !read(old($Heap), u#0, alloc);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.AnotherMethod() returns (u#0: ref, v#0: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $nw: ref;

    // AddMethodImpl: AnotherMethod, Impl$$_module.__default.AnotherMethod
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(187,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(188,5)
    assume true;
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._module.Cell?();
    assume !read($Heap, $nw, alloc);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    u#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(188,15)"} true;
}



procedure CheckWellformed$$_module.__default.ClientOfNewReferences();
  free requires 52 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.ClientOfNewReferences();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.ClientOfNewReferences() returns ($_reverifyPost: bool);
  free requires 52 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.ClientOfNewReferences() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var m#0: ref
     where $Is(m#0, Tclass._module.DoleOutReferences())
       && $IsAlloc(m#0, Tclass._module.DoleOutReferences(), $Heap);
  var $nw: ref;
  var u##0: ref;
  var i#0: int;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var $decr$loop#00: int;
  var more#0_0: bool;
  var $rhs##0_0: bool;
  var $rhs#0_0_0: int;
  var $rhs#0_0: int;

    // AddMethodImpl: ClientOfNewReferences, Impl$$_module.__default.ClientOfNewReferences
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(222,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(223,9)
    assume true;
    // ----- init call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(223,12)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    u##0 := null;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $nw := Call$$_module.DoleOutReferences.__ctor(u##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(223,38)"} true;
    m#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(223,38)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(224,9)
    assume true;
    assume true;
    i#0 := LitInt(86);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(224,13)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(225,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := (if i#0 <= LitInt(0) then 0 - i#0 else i#0 - 0);
    havoc $w$loop#0;
    while (true)
      free invariant $w$loop#0 ==> _module.DoleOutReferences.Valid#canCall($Heap, m#0);
      invariant $w$loop#0 ==> _module.DoleOutReferences.Valid($Heap, m#0);
      invariant $w$loop#0
         ==> (forall $o: ref :: 
          { read($Heap, m#0, _module.DoleOutReferences.__new)[$Box($o)] } 
          read($Heap, m#0, _module.DoleOutReferences.__new)[$Box($o)]
             ==> $o != null && !read(old($Heap), $o, alloc));
      free invariant (forall $o: ref :: 
        { $Heap[$o] } 
        $o != null && read(old($Heap), $o, alloc)
           ==> $Heap[$o] == $PreLoopHeap$loop#0[$o]);
      free invariant $HeapSucc($PreLoopHeap$loop#0, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
        { read($Heap, $o, $f) } 
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
      free invariant (if i#0 <= LitInt(0) then 0 - i#0 else i#0 - 0) <= $decr_init$loop#00
         && ((if i#0 <= LitInt(0) then 0 - i#0 else i#0 - 0) == $decr_init$loop#00 ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(225,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assert {:subsumption 0} m#0 != null;
            assume _module.DoleOutReferences.Valid#canCall($Heap, m#0);
            if (_module.DoleOutReferences.Valid($Heap, m#0))
            {
                assert {:subsumption 0} m#0 != null;
            }

            assume _module.DoleOutReferences.Valid#canCall($Heap, m#0);
            assume _module.DoleOutReferences.Valid($Heap, m#0)
               && (forall $o: ref :: 
                { read($Heap, m#0, _module.DoleOutReferences.__new)[$Box($o)] } 
                read($Heap, m#0, _module.DoleOutReferences.__new)[$Box($o)]
                   ==> $o != null && !read(old($Heap), $o, alloc));
            if (i#0 <= LitInt(0))
            {
            }
            else
            {
            }

            assume true;
            assume false;
        }

        assume true;
        if (i#0 == 0)
        {
            break;
        }

        $decr$loop#00 := (if i#0 <= LitInt(0) then 0 - i#0 else i#0 - 0);
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(228,27)
        assume true;
        // TrCallStmt: Adding lhs with type bool
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        assert m#0 != null;
        assert (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null
               && read($Heap, $o, alloc)
               && (
                $o == m#0
                 || _module.DoleOutReferences.__modifies(m#0)[$Box($o)]
                 || read($Heap, m#0, _module.DoleOutReferences.__new)[$Box($o)])
             ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call $rhs##0_0 := Call$$_module.DoleOutReferences.MoveNext(m#0);
        // TrCallStmt: After ProcessCallStmt
        more#0_0 := $rhs##0_0;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(228,28)"} true;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(229,5)
        assume true;
        assert more#0_0;
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(230,5)
        if (*)
        {
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(231,16)
            assert m#0 != null;
            assert read($Heap, m#0, _module.DoleOutReferences.r) != null;
            assume true;
            assert $_Frame[read($Heap, m#0, _module.DoleOutReferences.r), _module.Cell.data];
            assume true;
            $rhs#0_0_0 := i#0;
            $Heap := update($Heap, 
              read($Heap, m#0, _module.DoleOutReferences.r), 
              _module.Cell.data, 
              $rhs#0_0_0);
            assume $IsGoodHeap($Heap);
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(231,19)"} true;
        }
        else
        {
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(233,16)
            assert m#0 != null;
            assert read($Heap, m#0, _module.DoleOutReferences.c) != null;
            assume true;
            assert $_Frame[read($Heap, m#0, _module.DoleOutReferences.c), _module.Cell.data];
            assume true;
            $rhs#0_0 := i#0;
            $Heap := update($Heap, 
              read($Heap, m#0, _module.DoleOutReferences.c), 
              _module.Cell.data, 
              $rhs#0_0);
            assume $IsGoodHeap($Heap);
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(233,19)"} true;
            // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(234,7)
            assert {:subsumption 0} m#0 != null;
            assume _module.DoleOutReferences.Valid#canCall($Heap, m#0);
            assume _module.DoleOutReferences.Valid#canCall($Heap, m#0);
            assert _module.DoleOutReferences.Valid($Heap, m#0);
        }

        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(236,7)
        assume true;
        assume true;
        i#0 := i#0 - 1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(236,14)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(225,3)
        assert 0 <= $decr$loop#00
           || (if i#0 <= LitInt(0) then 0 - i#0 else i#0 - 0) == $decr$loop#00;
        assert (if i#0 <= LitInt(0) then 0 - i#0 else i#0 - 0) < $decr$loop#00;
        assume _module.DoleOutReferences.Valid#canCall($Heap, m#0);
    }
}



procedure CheckWellformed$$_module.__default.LoopFrame__OrdinaryMethod(c#0: ref
       where $Is(c#0, Tclass._module.Cell()) && $IsAlloc(c#0, Tclass._module.Cell(), $Heap))
   returns (y#0: int);
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.LoopFrame__OrdinaryMethod(c#0: ref
       where $Is(c#0, Tclass._module.Cell()) && $IsAlloc(c#0, Tclass._module.Cell(), $Heap))
   returns (y#0: int);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == c#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.LoopFrame__OrdinaryMethod(c#0: ref
       where $Is(c#0, Tclass._module.Cell()) && $IsAlloc(c#0, Tclass._module.Cell(), $Heap))
   returns (y#0: int, $_reverifyPost: bool);
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == c#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.LoopFrame__OrdinaryMethod(c#0: ref) returns (y#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: int;
  var d#0: ref
     where $Is(d#0, Tclass._module.Cell()) && $IsAlloc(d#0, Tclass._module.Cell(), $Heap);
  var $nw: ref;
  var $rhs#1: int;
  var $PreLoopHeap$loop#0: Heap;
  var $w$loop#0: bool;
  var $rhs#0_0: int;
  var $rhs#0_1: int;

    // AddMethodImpl: LoopFrame_OrdinaryMethod, Impl$$_module.__default.LoopFrame__OrdinaryMethod
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == c#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(407,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(408,5)
    assume true;
    assume true;
    y#0 := LitInt(10);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(408,9)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(409,10)
    assert c#0 != null;
    assume true;
    assert $_Frame[c#0, _module.Cell.data];
    assume true;
    $rhs#0 := LitInt(10);
    $Heap := update($Heap, c#0, _module.Cell.data, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(409,14)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(410,9)
    assume true;
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._module.Cell?();
    assume !read($Heap, $nw, alloc);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    d#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(410,19)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(411,10)
    assert d#0 != null;
    assume true;
    assert $_Frame[d#0, _module.Cell.data];
    assume true;
    $rhs#1 := LitInt(10);
    $Heap := update($Heap, d#0, _module.Cell.data, $rhs#1);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(411,14)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(412,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    havoc $w$loop#0;
    while (true)
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> y#0 <= LitInt(11);
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> read($Heap, d#0, _module.Cell.data) <= LitInt(11);
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> read($Heap, c#0, _module.Cell.data) <= LitInt(11);
      free invariant (forall $o: ref :: 
        { $Heap[$o] } 
        $o != null && read(old($Heap), $o, alloc)
           ==> $Heap[$o] == $PreLoopHeap$loop#0[$o] || $o == c#0);
      free invariant $HeapSucc($PreLoopHeap$loop#0, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
        { read($Heap, $o, $f) } 
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(412,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assume true;
            assume y#0 <= LitInt(11);
            assert {:subsumption 0} d#0 != null;
            assume true;
            assume read($Heap, d#0, _module.Cell.data) <= LitInt(11);
            assert {:subsumption 0} c#0 != null;
            assume true;
            assume read($Heap, c#0, _module.Cell.data) <= LitInt(11);
            assume true;
            assume false;
        }

        assume true;
        if (!Lit(true))
        {
            break;
        }

        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(418,7)
        assume true;
        assume true;
        y#0 := y#0 + 1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(418,14)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(419,12)
        assert c#0 != null;
        assume true;
        assert $_Frame[c#0, _module.Cell.data];
        assert c#0 != null;
        assume true;
        $rhs#0_0 := read($Heap, c#0, _module.Cell.data) + 1;
        $Heap := update($Heap, c#0, _module.Cell.data, $rhs#0_0);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(419,24)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(420,12)
        assert d#0 != null;
        assume true;
        assert $_Frame[d#0, _module.Cell.data];
        assert d#0 != null;
        assume true;
        $rhs#0_1 := read($Heap, d#0, _module.Cell.data) + 1;
        $Heap := update($Heap, d#0, _module.Cell.data, $rhs#0_1);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Iterators.dfy(420,24)"} true;
        assume true;
        assume true;
        assume true;
    }
}



const unique class.ITER__A.RecursiveIterator?: ClassName;

function Tclass.ITER__A.RecursiveIterator?() : Ty;

const unique Tagclass.ITER__A.RecursiveIterator?: TyTag;

// Tclass.ITER__A.RecursiveIterator? Tag
axiom Tag(Tclass.ITER__A.RecursiveIterator?()) == Tagclass.ITER__A.RecursiveIterator?
   && TagFamily(Tclass.ITER__A.RecursiveIterator?()) == tytagFamily$RecursiveIterator;

// Box/unbox axiom for Tclass.ITER__A.RecursiveIterator?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.ITER__A.RecursiveIterator?()) } 
  $IsBox(bx, Tclass.ITER__A.RecursiveIterator?())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.ITER__A.RecursiveIterator?()));

// RecursiveIterator: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.ITER__A.RecursiveIterator?()) } 
  $Is($o, Tclass.ITER__A.RecursiveIterator?())
     <==> $o == null || dtype($o) == Tclass.ITER__A.RecursiveIterator?());

// RecursiveIterator: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.ITER__A.RecursiveIterator?(), $h) } 
  $IsAlloc($o, Tclass.ITER__A.RecursiveIterator?(), $h)
     <==> $o == null || read($h, $o, alloc));

function ITER__A.RecursiveIterator.n(ref) : int;

// RecursiveIterator.n: Type axiom
axiom (forall $o: ref :: 
  { ITER__A.RecursiveIterator.n($o) } 
  $o != null && dtype($o) == Tclass.ITER__A.RecursiveIterator?()
     ==> $Is(ITER__A.RecursiveIterator.n($o), Tclass._System.nat()));

// RecursiveIterator.n: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { ITER__A.RecursiveIterator.n($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__A.RecursiveIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(ITER__A.RecursiveIterator.n($o), Tclass._System.nat(), $h));

function ITER__A.RecursiveIterator.r(ref) : ref;

function Tclass.ITER__A.RecIterCaller?() : Ty;

const unique Tagclass.ITER__A.RecIterCaller?: TyTag;

// Tclass.ITER__A.RecIterCaller? Tag
axiom Tag(Tclass.ITER__A.RecIterCaller?()) == Tagclass.ITER__A.RecIterCaller?
   && TagFamily(Tclass.ITER__A.RecIterCaller?()) == tytagFamily$RecIterCaller;

// Box/unbox axiom for Tclass.ITER__A.RecIterCaller?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.ITER__A.RecIterCaller?()) } 
  $IsBox(bx, Tclass.ITER__A.RecIterCaller?())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.ITER__A.RecIterCaller?()));

// RecursiveIterator.r: Type axiom
axiom (forall $o: ref :: 
  { ITER__A.RecursiveIterator.r($o) } 
  $o != null && dtype($o) == Tclass.ITER__A.RecursiveIterator?()
     ==> $Is(ITER__A.RecursiveIterator.r($o), Tclass.ITER__A.RecIterCaller?()));

// RecursiveIterator.r: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { ITER__A.RecursiveIterator.r($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__A.RecursiveIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(ITER__A.RecursiveIterator.r($o), Tclass.ITER__A.RecIterCaller?(), $h));

function ITER__A.RecursiveIterator.good(ref) : bool;

// RecursiveIterator.good: Type axiom
axiom (forall $o: ref :: 
  { ITER__A.RecursiveIterator.good($o) } 
  $o != null && dtype($o) == Tclass.ITER__A.RecursiveIterator?()
     ==> $Is(ITER__A.RecursiveIterator.good($o), TBool));

// RecursiveIterator.good: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { ITER__A.RecursiveIterator.good($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__A.RecursiveIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(ITER__A.RecursiveIterator.good($o), TBool, $h));

function ITER__A.RecursiveIterator.__reads(ref) : Set Box;

// RecursiveIterator._reads: Type axiom
axiom (forall $o: ref :: 
  { ITER__A.RecursiveIterator.__reads($o) } 
  $o != null && dtype($o) == Tclass.ITER__A.RecursiveIterator?()
     ==> $Is(ITER__A.RecursiveIterator.__reads($o), TSet(Tclass._System.object?())));

// RecursiveIterator._reads: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { ITER__A.RecursiveIterator.__reads($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__A.RecursiveIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(ITER__A.RecursiveIterator.__reads($o), TSet(Tclass._System.object?()), $h));

function ITER__A.RecursiveIterator.__modifies(ref) : Set Box;

// RecursiveIterator._modifies: Type axiom
axiom (forall $o: ref :: 
  { ITER__A.RecursiveIterator.__modifies($o) } 
  $o != null && dtype($o) == Tclass.ITER__A.RecursiveIterator?()
     ==> $Is(ITER__A.RecursiveIterator.__modifies($o), TSet(Tclass._System.object?())));

// RecursiveIterator._modifies: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { ITER__A.RecursiveIterator.__modifies($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__A.RecursiveIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(ITER__A.RecursiveIterator.__modifies($o), TSet(Tclass._System.object?()), $h));

axiom FDim(ITER__A.RecursiveIterator.__new) == 0
   && FieldOfDecl(class.ITER__A.RecursiveIterator?, field$_new)
     == ITER__A.RecursiveIterator.__new
   && $IsGhostField(ITER__A.RecursiveIterator.__new);

const ITER__A.RecursiveIterator.__new: Field (Set Box);

// RecursiveIterator._new: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, ITER__A.RecursiveIterator.__new) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__A.RecursiveIterator?()
     ==> $Is(read($h, $o, ITER__A.RecursiveIterator.__new), TSet(Tclass._System.object?())));

// RecursiveIterator._new: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, ITER__A.RecursiveIterator.__new) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__A.RecursiveIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, ITER__A.RecursiveIterator.__new), 
      TSet(Tclass._System.object?()), 
      $h));

function ITER__A.RecursiveIterator.__decreases0(ref) : int;

// RecursiveIterator._decreases0: Type axiom
axiom (forall $o: ref :: 
  { ITER__A.RecursiveIterator.__decreases0($o) } 
  $o != null && dtype($o) == Tclass.ITER__A.RecursiveIterator?()
     ==> $Is(ITER__A.RecursiveIterator.__decreases0($o), TInt));

// RecursiveIterator._decreases0: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { ITER__A.RecursiveIterator.__decreases0($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__A.RecursiveIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(ITER__A.RecursiveIterator.__decreases0($o), TInt, $h));

function ITER__A.RecursiveIterator.__decreases1(ref) : int;

// RecursiveIterator._decreases1: Type axiom
axiom (forall $o: ref :: 
  { ITER__A.RecursiveIterator.__decreases1($o) } 
  $o != null && dtype($o) == Tclass.ITER__A.RecursiveIterator?()
     ==> $Is(ITER__A.RecursiveIterator.__decreases1($o), TInt));

// RecursiveIterator._decreases1: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { ITER__A.RecursiveIterator.__decreases1($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__A.RecursiveIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(ITER__A.RecursiveIterator.__decreases1($o), TInt, $h));

// function declaration for ITER_A.RecursiveIterator.Valid
function ITER__A.RecursiveIterator.Valid($heap: Heap, this: ref) : bool;

function ITER__A.RecursiveIterator.Valid#canCall($heap: Heap, this: ref) : bool;

function Tclass.ITER__A.RecursiveIterator() : Ty;

const unique Tagclass.ITER__A.RecursiveIterator: TyTag;

// Tclass.ITER__A.RecursiveIterator Tag
axiom Tag(Tclass.ITER__A.RecursiveIterator()) == Tagclass.ITER__A.RecursiveIterator
   && TagFamily(Tclass.ITER__A.RecursiveIterator()) == tytagFamily$RecursiveIterator;

// Box/unbox axiom for Tclass.ITER__A.RecursiveIterator
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.ITER__A.RecursiveIterator()) } 
  $IsBox(bx, Tclass.ITER__A.RecursiveIterator())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.ITER__A.RecursiveIterator()));

// frame axiom for ITER__A.RecursiveIterator.Valid
axiom (forall $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), ITER__A.RecursiveIterator.Valid($h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass.ITER__A.RecursiveIterator())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && (
            $o == this
             || ITER__A.RecursiveIterator.__reads(this)[$Box($o)]
             || read($h0, this, ITER__A.RecursiveIterator.__new)[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> ITER__A.RecursiveIterator.Valid($h0, this)
       == ITER__A.RecursiveIterator.Valid($h1, this));

// consequence axiom for ITER__A.RecursiveIterator.Valid
axiom true
   ==> (forall $Heap: Heap, this: ref :: 
    { ITER__A.RecursiveIterator.Valid($Heap, this) } 
    ITER__A.RecursiveIterator.Valid#canCall($Heap, this)
         || ($IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass.ITER__A.RecursiveIterator())
           && $IsAlloc(this, Tclass.ITER__A.RecursiveIterator(), $Heap))
       ==> true);

function ITER__A.RecursiveIterator.Valid#requires(Heap, ref) : bool;

// #requires axiom for ITER__A.RecursiveIterator.Valid
axiom (forall $Heap: Heap, this: ref :: 
  { ITER__A.RecursiveIterator.Valid#requires($Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass.ITER__A.RecursiveIterator())
       && $IsAlloc(this, Tclass.ITER__A.RecursiveIterator(), $Heap)
     ==> ITER__A.RecursiveIterator.Valid#requires($Heap, this) == true);

// ITER_A.RecursiveIterator: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass.ITER__A.RecursiveIterator()) } 
  $Is(c#0, Tclass.ITER__A.RecursiveIterator())
     <==> $Is(c#0, Tclass.ITER__A.RecursiveIterator?()) && c#0 != null);

// ITER_A.RecursiveIterator: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass.ITER__A.RecursiveIterator(), $h) } 
  $IsAlloc(c#0, Tclass.ITER__A.RecursiveIterator(), $h)
     <==> $IsAlloc(c#0, Tclass.ITER__A.RecursiveIterator?(), $h));

procedure CheckWellformed$$ITER__A.RecursiveIterator(this: ref
       where this != null
         && 
        $Is(this, Tclass.ITER__A.RecursiveIterator())
         && $IsAlloc(this, Tclass.ITER__A.RecursiveIterator(), $Heap), 
    n#0: int where LitInt(0) <= n#0, 
    r#0: ref
       where $Is(r#0, Tclass.ITER__A.RecIterCaller?())
         && $IsAlloc(r#0, Tclass.ITER__A.RecIterCaller?(), $Heap), 
    good#0: bool);
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



const unique class.ITER__A.RecIterCaller?: ClassName;

// RecIterCaller: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.ITER__A.RecIterCaller?()) } 
  $Is($o, Tclass.ITER__A.RecIterCaller?())
     <==> $o == null || dtype($o) == Tclass.ITER__A.RecIterCaller?());

// RecIterCaller: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.ITER__A.RecIterCaller?(), $h) } 
  $IsAlloc($o, Tclass.ITER__A.RecIterCaller?(), $h)
     <==> $o == null || read($h, $o, alloc));

function Tclass.ITER__A.RecIterCaller() : Ty;

const unique Tagclass.ITER__A.RecIterCaller: TyTag;

// Tclass.ITER__A.RecIterCaller Tag
axiom Tag(Tclass.ITER__A.RecIterCaller()) == Tagclass.ITER__A.RecIterCaller
   && TagFamily(Tclass.ITER__A.RecIterCaller()) == tytagFamily$RecIterCaller;

// Box/unbox axiom for Tclass.ITER__A.RecIterCaller
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.ITER__A.RecIterCaller()) } 
  $IsBox(bx, Tclass.ITER__A.RecIterCaller())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.ITER__A.RecIterCaller()));

// ITER_A.RecIterCaller: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass.ITER__A.RecIterCaller()) } 
  $Is(c#0, Tclass.ITER__A.RecIterCaller())
     <==> $Is(c#0, Tclass.ITER__A.RecIterCaller?()) && c#0 != null);

// ITER_A.RecIterCaller: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass.ITER__A.RecIterCaller(), $h) } 
  $IsAlloc(c#0, Tclass.ITER__A.RecIterCaller(), $h)
     <==> $IsAlloc(c#0, Tclass.ITER__A.RecIterCaller?(), $h));

const unique class.ITER__A.__default: ClassName;

function Tclass.ITER__A.__default() : Ty;

const unique Tagclass.ITER__A.__default: TyTag;

// Tclass.ITER__A.__default Tag
axiom Tag(Tclass.ITER__A.__default()) == Tagclass.ITER__A.__default
   && TagFamily(Tclass.ITER__A.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.ITER__A.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.ITER__A.__default()) } 
  $IsBox(bx, Tclass.ITER__A.__default())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.ITER__A.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.ITER__A.__default()) } 
  $Is($o, Tclass.ITER__A.__default())
     <==> $o == null || dtype($o) == Tclass.ITER__A.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.ITER__A.__default(), $h) } 
  $IsAlloc($o, Tclass.ITER__A.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

const unique class.ITER__B.RecursiveIterator?: ClassName;

function Tclass.ITER__B.RecursiveIterator?() : Ty;

const unique Tagclass.ITER__B.RecursiveIterator?: TyTag;

// Tclass.ITER__B.RecursiveIterator? Tag
axiom Tag(Tclass.ITER__B.RecursiveIterator?()) == Tagclass.ITER__B.RecursiveIterator?
   && TagFamily(Tclass.ITER__B.RecursiveIterator?()) == tytagFamily$RecursiveIterator;

// Box/unbox axiom for Tclass.ITER__B.RecursiveIterator?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.ITER__B.RecursiveIterator?()) } 
  $IsBox(bx, Tclass.ITER__B.RecursiveIterator?())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.ITER__B.RecursiveIterator?()));

// RecursiveIterator: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.ITER__B.RecursiveIterator?()) } 
  $Is($o, Tclass.ITER__B.RecursiveIterator?())
     <==> $o == null || dtype($o) == Tclass.ITER__B.RecursiveIterator?());

// RecursiveIterator: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.ITER__B.RecursiveIterator?(), $h) } 
  $IsAlloc($o, Tclass.ITER__B.RecursiveIterator?(), $h)
     <==> $o == null || read($h, $o, alloc));

function ITER__B.RecursiveIterator.n(ref) : int;

// RecursiveIterator.n: Type axiom
axiom (forall $o: ref :: 
  { ITER__B.RecursiveIterator.n($o) } 
  $o != null && dtype($o) == Tclass.ITER__B.RecursiveIterator?()
     ==> $Is(ITER__B.RecursiveIterator.n($o), Tclass._System.nat()));

// RecursiveIterator.n: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { ITER__B.RecursiveIterator.n($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__B.RecursiveIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(ITER__B.RecursiveIterator.n($o), Tclass._System.nat(), $h));

function ITER__B.RecursiveIterator.r(ref) : ref;

function Tclass.ITER__B.RecIterCaller?() : Ty;

const unique Tagclass.ITER__B.RecIterCaller?: TyTag;

// Tclass.ITER__B.RecIterCaller? Tag
axiom Tag(Tclass.ITER__B.RecIterCaller?()) == Tagclass.ITER__B.RecIterCaller?
   && TagFamily(Tclass.ITER__B.RecIterCaller?()) == tytagFamily$RecIterCaller;

// Box/unbox axiom for Tclass.ITER__B.RecIterCaller?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.ITER__B.RecIterCaller?()) } 
  $IsBox(bx, Tclass.ITER__B.RecIterCaller?())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.ITER__B.RecIterCaller?()));

// RecursiveIterator.r: Type axiom
axiom (forall $o: ref :: 
  { ITER__B.RecursiveIterator.r($o) } 
  $o != null && dtype($o) == Tclass.ITER__B.RecursiveIterator?()
     ==> $Is(ITER__B.RecursiveIterator.r($o), Tclass.ITER__B.RecIterCaller?()));

// RecursiveIterator.r: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { ITER__B.RecursiveIterator.r($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__B.RecursiveIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(ITER__B.RecursiveIterator.r($o), Tclass.ITER__B.RecIterCaller?(), $h));

function ITER__B.RecursiveIterator.good(ref) : bool;

// RecursiveIterator.good: Type axiom
axiom (forall $o: ref :: 
  { ITER__B.RecursiveIterator.good($o) } 
  $o != null && dtype($o) == Tclass.ITER__B.RecursiveIterator?()
     ==> $Is(ITER__B.RecursiveIterator.good($o), TBool));

// RecursiveIterator.good: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { ITER__B.RecursiveIterator.good($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__B.RecursiveIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(ITER__B.RecursiveIterator.good($o), TBool, $h));

function ITER__B.RecursiveIterator.__reads(ref) : Set Box;

// RecursiveIterator._reads: Type axiom
axiom (forall $o: ref :: 
  { ITER__B.RecursiveIterator.__reads($o) } 
  $o != null && dtype($o) == Tclass.ITER__B.RecursiveIterator?()
     ==> $Is(ITER__B.RecursiveIterator.__reads($o), TSet(Tclass._System.object?())));

// RecursiveIterator._reads: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { ITER__B.RecursiveIterator.__reads($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__B.RecursiveIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(ITER__B.RecursiveIterator.__reads($o), TSet(Tclass._System.object?()), $h));

function ITER__B.RecursiveIterator.__modifies(ref) : Set Box;

// RecursiveIterator._modifies: Type axiom
axiom (forall $o: ref :: 
  { ITER__B.RecursiveIterator.__modifies($o) } 
  $o != null && dtype($o) == Tclass.ITER__B.RecursiveIterator?()
     ==> $Is(ITER__B.RecursiveIterator.__modifies($o), TSet(Tclass._System.object?())));

// RecursiveIterator._modifies: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { ITER__B.RecursiveIterator.__modifies($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__B.RecursiveIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(ITER__B.RecursiveIterator.__modifies($o), TSet(Tclass._System.object?()), $h));

axiom FDim(ITER__B.RecursiveIterator.__new) == 0
   && FieldOfDecl(class.ITER__B.RecursiveIterator?, field$_new)
     == ITER__B.RecursiveIterator.__new
   && $IsGhostField(ITER__B.RecursiveIterator.__new);

const ITER__B.RecursiveIterator.__new: Field (Set Box);

// RecursiveIterator._new: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, ITER__B.RecursiveIterator.__new) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__B.RecursiveIterator?()
     ==> $Is(read($h, $o, ITER__B.RecursiveIterator.__new), TSet(Tclass._System.object?())));

// RecursiveIterator._new: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, ITER__B.RecursiveIterator.__new) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__B.RecursiveIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, ITER__B.RecursiveIterator.__new), 
      TSet(Tclass._System.object?()), 
      $h));

function ITER__B.RecursiveIterator.__decreases0(ref) : int;

// RecursiveIterator._decreases0: Type axiom
axiom (forall $o: ref :: 
  { ITER__B.RecursiveIterator.__decreases0($o) } 
  $o != null && dtype($o) == Tclass.ITER__B.RecursiveIterator?()
     ==> $Is(ITER__B.RecursiveIterator.__decreases0($o), TInt));

// RecursiveIterator._decreases0: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { ITER__B.RecursiveIterator.__decreases0($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__B.RecursiveIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(ITER__B.RecursiveIterator.__decreases0($o), TInt, $h));

// function declaration for ITER_B.RecursiveIterator.Valid
function ITER__B.RecursiveIterator.Valid($heap: Heap, this: ref) : bool;

function ITER__B.RecursiveIterator.Valid#canCall($heap: Heap, this: ref) : bool;

function Tclass.ITER__B.RecursiveIterator() : Ty;

const unique Tagclass.ITER__B.RecursiveIterator: TyTag;

// Tclass.ITER__B.RecursiveIterator Tag
axiom Tag(Tclass.ITER__B.RecursiveIterator()) == Tagclass.ITER__B.RecursiveIterator
   && TagFamily(Tclass.ITER__B.RecursiveIterator()) == tytagFamily$RecursiveIterator;

// Box/unbox axiom for Tclass.ITER__B.RecursiveIterator
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.ITER__B.RecursiveIterator()) } 
  $IsBox(bx, Tclass.ITER__B.RecursiveIterator())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.ITER__B.RecursiveIterator()));

// frame axiom for ITER__B.RecursiveIterator.Valid
axiom (forall $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), ITER__B.RecursiveIterator.Valid($h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass.ITER__B.RecursiveIterator())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && (
            $o == this
             || ITER__B.RecursiveIterator.__reads(this)[$Box($o)]
             || read($h0, this, ITER__B.RecursiveIterator.__new)[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> ITER__B.RecursiveIterator.Valid($h0, this)
       == ITER__B.RecursiveIterator.Valid($h1, this));

// consequence axiom for ITER__B.RecursiveIterator.Valid
axiom true
   ==> (forall $Heap: Heap, this: ref :: 
    { ITER__B.RecursiveIterator.Valid($Heap, this) } 
    ITER__B.RecursiveIterator.Valid#canCall($Heap, this)
         || ($IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass.ITER__B.RecursiveIterator())
           && $IsAlloc(this, Tclass.ITER__B.RecursiveIterator(), $Heap))
       ==> true);

function ITER__B.RecursiveIterator.Valid#requires(Heap, ref) : bool;

// #requires axiom for ITER__B.RecursiveIterator.Valid
axiom (forall $Heap: Heap, this: ref :: 
  { ITER__B.RecursiveIterator.Valid#requires($Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass.ITER__B.RecursiveIterator())
       && $IsAlloc(this, Tclass.ITER__B.RecursiveIterator(), $Heap)
     ==> ITER__B.RecursiveIterator.Valid#requires($Heap, this) == true);

// ITER_B.RecursiveIterator: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass.ITER__B.RecursiveIterator()) } 
  $Is(c#0, Tclass.ITER__B.RecursiveIterator())
     <==> $Is(c#0, Tclass.ITER__B.RecursiveIterator?()) && c#0 != null);

// ITER_B.RecursiveIterator: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass.ITER__B.RecursiveIterator(), $h) } 
  $IsAlloc(c#0, Tclass.ITER__B.RecursiveIterator(), $h)
     <==> $IsAlloc(c#0, Tclass.ITER__B.RecursiveIterator?(), $h));

procedure CheckWellformed$$ITER__B.RecursiveIterator(this: ref
       where this != null
         && 
        $Is(this, Tclass.ITER__B.RecursiveIterator())
         && $IsAlloc(this, Tclass.ITER__B.RecursiveIterator(), $Heap), 
    n#0: int where LitInt(0) <= n#0, 
    r#0: ref
       where $Is(r#0, Tclass.ITER__B.RecIterCaller?())
         && $IsAlloc(r#0, Tclass.ITER__B.RecIterCaller?(), $Heap), 
    good#0: bool);
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



const unique class.ITER__B.RecIterCaller?: ClassName;

// RecIterCaller: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.ITER__B.RecIterCaller?()) } 
  $Is($o, Tclass.ITER__B.RecIterCaller?())
     <==> $o == null || dtype($o) == Tclass.ITER__B.RecIterCaller?());

// RecIterCaller: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.ITER__B.RecIterCaller?(), $h) } 
  $IsAlloc($o, Tclass.ITER__B.RecIterCaller?(), $h)
     <==> $o == null || read($h, $o, alloc));

function Tclass.ITER__B.RecIterCaller() : Ty;

const unique Tagclass.ITER__B.RecIterCaller: TyTag;

// Tclass.ITER__B.RecIterCaller Tag
axiom Tag(Tclass.ITER__B.RecIterCaller()) == Tagclass.ITER__B.RecIterCaller
   && TagFamily(Tclass.ITER__B.RecIterCaller()) == tytagFamily$RecIterCaller;

// Box/unbox axiom for Tclass.ITER__B.RecIterCaller
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.ITER__B.RecIterCaller()) } 
  $IsBox(bx, Tclass.ITER__B.RecIterCaller())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.ITER__B.RecIterCaller()));

// ITER_B.RecIterCaller: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass.ITER__B.RecIterCaller()) } 
  $Is(c#0, Tclass.ITER__B.RecIterCaller())
     <==> $Is(c#0, Tclass.ITER__B.RecIterCaller?()) && c#0 != null);

// ITER_B.RecIterCaller: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass.ITER__B.RecIterCaller(), $h) } 
  $IsAlloc(c#0, Tclass.ITER__B.RecIterCaller(), $h)
     <==> $IsAlloc(c#0, Tclass.ITER__B.RecIterCaller?(), $h));

const unique class.ITER__B.__default: ClassName;

function Tclass.ITER__B.__default() : Ty;

const unique Tagclass.ITER__B.__default: TyTag;

// Tclass.ITER__B.__default Tag
axiom Tag(Tclass.ITER__B.__default()) == Tagclass.ITER__B.__default
   && TagFamily(Tclass.ITER__B.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.ITER__B.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.ITER__B.__default()) } 
  $IsBox(bx, Tclass.ITER__B.__default())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.ITER__B.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.ITER__B.__default()) } 
  $Is($o, Tclass.ITER__B.__default())
     <==> $o == null || dtype($o) == Tclass.ITER__B.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.ITER__B.__default(), $h) } 
  $IsAlloc($o, Tclass.ITER__B.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

const unique class.ITER__C.RecursiveIterator?: ClassName;

function Tclass.ITER__C.RecursiveIterator?() : Ty;

const unique Tagclass.ITER__C.RecursiveIterator?: TyTag;

// Tclass.ITER__C.RecursiveIterator? Tag
axiom Tag(Tclass.ITER__C.RecursiveIterator?()) == Tagclass.ITER__C.RecursiveIterator?
   && TagFamily(Tclass.ITER__C.RecursiveIterator?()) == tytagFamily$RecursiveIterator;

// Box/unbox axiom for Tclass.ITER__C.RecursiveIterator?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.ITER__C.RecursiveIterator?()) } 
  $IsBox(bx, Tclass.ITER__C.RecursiveIterator?())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.ITER__C.RecursiveIterator?()));

// RecursiveIterator: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.ITER__C.RecursiveIterator?()) } 
  $Is($o, Tclass.ITER__C.RecursiveIterator?())
     <==> $o == null || dtype($o) == Tclass.ITER__C.RecursiveIterator?());

// RecursiveIterator: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.ITER__C.RecursiveIterator?(), $h) } 
  $IsAlloc($o, Tclass.ITER__C.RecursiveIterator?(), $h)
     <==> $o == null || read($h, $o, alloc));

function ITER__C.RecursiveIterator.n(ref) : int;

// RecursiveIterator.n: Type axiom
axiom (forall $o: ref :: 
  { ITER__C.RecursiveIterator.n($o) } 
  $o != null && dtype($o) == Tclass.ITER__C.RecursiveIterator?()
     ==> $Is(ITER__C.RecursiveIterator.n($o), Tclass._System.nat()));

// RecursiveIterator.n: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { ITER__C.RecursiveIterator.n($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__C.RecursiveIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(ITER__C.RecursiveIterator.n($o), Tclass._System.nat(), $h));

function ITER__C.RecursiveIterator.r(ref) : ref;

function Tclass.ITER__C.RecIterCaller?() : Ty;

const unique Tagclass.ITER__C.RecIterCaller?: TyTag;

// Tclass.ITER__C.RecIterCaller? Tag
axiom Tag(Tclass.ITER__C.RecIterCaller?()) == Tagclass.ITER__C.RecIterCaller?
   && TagFamily(Tclass.ITER__C.RecIterCaller?()) == tytagFamily$RecIterCaller;

// Box/unbox axiom for Tclass.ITER__C.RecIterCaller?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.ITER__C.RecIterCaller?()) } 
  $IsBox(bx, Tclass.ITER__C.RecIterCaller?())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.ITER__C.RecIterCaller?()));

// RecursiveIterator.r: Type axiom
axiom (forall $o: ref :: 
  { ITER__C.RecursiveIterator.r($o) } 
  $o != null && dtype($o) == Tclass.ITER__C.RecursiveIterator?()
     ==> $Is(ITER__C.RecursiveIterator.r($o), Tclass.ITER__C.RecIterCaller?()));

// RecursiveIterator.r: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { ITER__C.RecursiveIterator.r($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__C.RecursiveIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(ITER__C.RecursiveIterator.r($o), Tclass.ITER__C.RecIterCaller?(), $h));

function ITER__C.RecursiveIterator.good(ref) : bool;

// RecursiveIterator.good: Type axiom
axiom (forall $o: ref :: 
  { ITER__C.RecursiveIterator.good($o) } 
  $o != null && dtype($o) == Tclass.ITER__C.RecursiveIterator?()
     ==> $Is(ITER__C.RecursiveIterator.good($o), TBool));

// RecursiveIterator.good: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { ITER__C.RecursiveIterator.good($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__C.RecursiveIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(ITER__C.RecursiveIterator.good($o), TBool, $h));

function ITER__C.RecursiveIterator.__reads(ref) : Set Box;

// RecursiveIterator._reads: Type axiom
axiom (forall $o: ref :: 
  { ITER__C.RecursiveIterator.__reads($o) } 
  $o != null && dtype($o) == Tclass.ITER__C.RecursiveIterator?()
     ==> $Is(ITER__C.RecursiveIterator.__reads($o), TSet(Tclass._System.object?())));

// RecursiveIterator._reads: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { ITER__C.RecursiveIterator.__reads($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__C.RecursiveIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(ITER__C.RecursiveIterator.__reads($o), TSet(Tclass._System.object?()), $h));

function ITER__C.RecursiveIterator.__modifies(ref) : Set Box;

// RecursiveIterator._modifies: Type axiom
axiom (forall $o: ref :: 
  { ITER__C.RecursiveIterator.__modifies($o) } 
  $o != null && dtype($o) == Tclass.ITER__C.RecursiveIterator?()
     ==> $Is(ITER__C.RecursiveIterator.__modifies($o), TSet(Tclass._System.object?())));

// RecursiveIterator._modifies: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { ITER__C.RecursiveIterator.__modifies($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__C.RecursiveIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(ITER__C.RecursiveIterator.__modifies($o), TSet(Tclass._System.object?()), $h));

axiom FDim(ITER__C.RecursiveIterator.__new) == 0
   && FieldOfDecl(class.ITER__C.RecursiveIterator?, field$_new)
     == ITER__C.RecursiveIterator.__new
   && $IsGhostField(ITER__C.RecursiveIterator.__new);

const ITER__C.RecursiveIterator.__new: Field (Set Box);

// RecursiveIterator._new: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, ITER__C.RecursiveIterator.__new) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__C.RecursiveIterator?()
     ==> $Is(read($h, $o, ITER__C.RecursiveIterator.__new), TSet(Tclass._System.object?())));

// RecursiveIterator._new: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, ITER__C.RecursiveIterator.__new) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__C.RecursiveIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, ITER__C.RecursiveIterator.__new), 
      TSet(Tclass._System.object?()), 
      $h));

function ITER__C.RecursiveIterator.__decreases0(ref) : int;

// RecursiveIterator._decreases0: Type axiom
axiom (forall $o: ref :: 
  { ITER__C.RecursiveIterator.__decreases0($o) } 
  $o != null && dtype($o) == Tclass.ITER__C.RecursiveIterator?()
     ==> $Is(ITER__C.RecursiveIterator.__decreases0($o), TInt));

// RecursiveIterator._decreases0: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { ITER__C.RecursiveIterator.__decreases0($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__C.RecursiveIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(ITER__C.RecursiveIterator.__decreases0($o), TInt, $h));

function ITER__C.RecursiveIterator.__decreases1(ref) : ref;

// RecursiveIterator._decreases1: Type axiom
axiom (forall $o: ref :: 
  { ITER__C.RecursiveIterator.__decreases1($o) } 
  $o != null && dtype($o) == Tclass.ITER__C.RecursiveIterator?()
     ==> $Is(ITER__C.RecursiveIterator.__decreases1($o), Tclass.ITER__C.RecIterCaller?()));

// RecursiveIterator._decreases1: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { ITER__C.RecursiveIterator.__decreases1($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__C.RecursiveIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(ITER__C.RecursiveIterator.__decreases1($o), Tclass.ITER__C.RecIterCaller?(), $h));

function ITER__C.RecursiveIterator.__decreases2(ref) : bool;

// RecursiveIterator._decreases2: Type axiom
axiom (forall $o: ref :: 
  { ITER__C.RecursiveIterator.__decreases2($o) } 
  $o != null && dtype($o) == Tclass.ITER__C.RecursiveIterator?()
     ==> $Is(ITER__C.RecursiveIterator.__decreases2($o), TBool));

// RecursiveIterator._decreases2: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { ITER__C.RecursiveIterator.__decreases2($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__C.RecursiveIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(ITER__C.RecursiveIterator.__decreases2($o), TBool, $h));

// function declaration for ITER_C.RecursiveIterator.Valid
function ITER__C.RecursiveIterator.Valid($heap: Heap, this: ref) : bool;

function ITER__C.RecursiveIterator.Valid#canCall($heap: Heap, this: ref) : bool;

function Tclass.ITER__C.RecursiveIterator() : Ty;

const unique Tagclass.ITER__C.RecursiveIterator: TyTag;

// Tclass.ITER__C.RecursiveIterator Tag
axiom Tag(Tclass.ITER__C.RecursiveIterator()) == Tagclass.ITER__C.RecursiveIterator
   && TagFamily(Tclass.ITER__C.RecursiveIterator()) == tytagFamily$RecursiveIterator;

// Box/unbox axiom for Tclass.ITER__C.RecursiveIterator
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.ITER__C.RecursiveIterator()) } 
  $IsBox(bx, Tclass.ITER__C.RecursiveIterator())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.ITER__C.RecursiveIterator()));

// frame axiom for ITER__C.RecursiveIterator.Valid
axiom (forall $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), ITER__C.RecursiveIterator.Valid($h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass.ITER__C.RecursiveIterator())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && (
            $o == this
             || ITER__C.RecursiveIterator.__reads(this)[$Box($o)]
             || read($h0, this, ITER__C.RecursiveIterator.__new)[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> ITER__C.RecursiveIterator.Valid($h0, this)
       == ITER__C.RecursiveIterator.Valid($h1, this));

// consequence axiom for ITER__C.RecursiveIterator.Valid
axiom true
   ==> (forall $Heap: Heap, this: ref :: 
    { ITER__C.RecursiveIterator.Valid($Heap, this) } 
    ITER__C.RecursiveIterator.Valid#canCall($Heap, this)
         || ($IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass.ITER__C.RecursiveIterator())
           && $IsAlloc(this, Tclass.ITER__C.RecursiveIterator(), $Heap))
       ==> true);

function ITER__C.RecursiveIterator.Valid#requires(Heap, ref) : bool;

// #requires axiom for ITER__C.RecursiveIterator.Valid
axiom (forall $Heap: Heap, this: ref :: 
  { ITER__C.RecursiveIterator.Valid#requires($Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass.ITER__C.RecursiveIterator())
       && $IsAlloc(this, Tclass.ITER__C.RecursiveIterator(), $Heap)
     ==> ITER__C.RecursiveIterator.Valid#requires($Heap, this) == true);

// ITER_C.RecursiveIterator: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass.ITER__C.RecursiveIterator()) } 
  $Is(c#0, Tclass.ITER__C.RecursiveIterator())
     <==> $Is(c#0, Tclass.ITER__C.RecursiveIterator?()) && c#0 != null);

// ITER_C.RecursiveIterator: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass.ITER__C.RecursiveIterator(), $h) } 
  $IsAlloc(c#0, Tclass.ITER__C.RecursiveIterator(), $h)
     <==> $IsAlloc(c#0, Tclass.ITER__C.RecursiveIterator?(), $h));

procedure CheckWellformed$$ITER__C.RecursiveIterator(this: ref
       where this != null
         && 
        $Is(this, Tclass.ITER__C.RecursiveIterator())
         && $IsAlloc(this, Tclass.ITER__C.RecursiveIterator(), $Heap), 
    n#0: int where LitInt(0) <= n#0, 
    r#0: ref
       where $Is(r#0, Tclass.ITER__C.RecIterCaller?())
         && $IsAlloc(r#0, Tclass.ITER__C.RecIterCaller?(), $Heap), 
    good#0: bool);
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



const unique class.ITER__C.RecIterCaller?: ClassName;

// RecIterCaller: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.ITER__C.RecIterCaller?()) } 
  $Is($o, Tclass.ITER__C.RecIterCaller?())
     <==> $o == null || dtype($o) == Tclass.ITER__C.RecIterCaller?());

// RecIterCaller: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.ITER__C.RecIterCaller?(), $h) } 
  $IsAlloc($o, Tclass.ITER__C.RecIterCaller?(), $h)
     <==> $o == null || read($h, $o, alloc));

function Tclass.ITER__C.RecIterCaller() : Ty;

const unique Tagclass.ITER__C.RecIterCaller: TyTag;

// Tclass.ITER__C.RecIterCaller Tag
axiom Tag(Tclass.ITER__C.RecIterCaller()) == Tagclass.ITER__C.RecIterCaller
   && TagFamily(Tclass.ITER__C.RecIterCaller()) == tytagFamily$RecIterCaller;

// Box/unbox axiom for Tclass.ITER__C.RecIterCaller
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.ITER__C.RecIterCaller()) } 
  $IsBox(bx, Tclass.ITER__C.RecIterCaller())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.ITER__C.RecIterCaller()));

// ITER_C.RecIterCaller: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass.ITER__C.RecIterCaller()) } 
  $Is(c#0, Tclass.ITER__C.RecIterCaller())
     <==> $Is(c#0, Tclass.ITER__C.RecIterCaller?()) && c#0 != null);

// ITER_C.RecIterCaller: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass.ITER__C.RecIterCaller(), $h) } 
  $IsAlloc(c#0, Tclass.ITER__C.RecIterCaller(), $h)
     <==> $IsAlloc(c#0, Tclass.ITER__C.RecIterCaller?(), $h));

const unique class.ITER__C.__default: ClassName;

function Tclass.ITER__C.__default() : Ty;

const unique Tagclass.ITER__C.__default: TyTag;

// Tclass.ITER__C.__default Tag
axiom Tag(Tclass.ITER__C.__default()) == Tagclass.ITER__C.__default
   && TagFamily(Tclass.ITER__C.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.ITER__C.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.ITER__C.__default()) } 
  $IsBox(bx, Tclass.ITER__C.__default())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.ITER__C.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.ITER__C.__default()) } 
  $Is($o, Tclass.ITER__C.__default())
     <==> $o == null || dtype($o) == Tclass.ITER__C.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.ITER__C.__default(), $h) } 
  $IsAlloc($o, Tclass.ITER__C.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

const unique class.ITER__D.RecursiveIterator?: ClassName;

function Tclass.ITER__D.RecursiveIterator?() : Ty;

const unique Tagclass.ITER__D.RecursiveIterator?: TyTag;

// Tclass.ITER__D.RecursiveIterator? Tag
axiom Tag(Tclass.ITER__D.RecursiveIterator?()) == Tagclass.ITER__D.RecursiveIterator?
   && TagFamily(Tclass.ITER__D.RecursiveIterator?()) == tytagFamily$RecursiveIterator;

// Box/unbox axiom for Tclass.ITER__D.RecursiveIterator?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.ITER__D.RecursiveIterator?()) } 
  $IsBox(bx, Tclass.ITER__D.RecursiveIterator?())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.ITER__D.RecursiveIterator?()));

// RecursiveIterator: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.ITER__D.RecursiveIterator?()) } 
  $Is($o, Tclass.ITER__D.RecursiveIterator?())
     <==> $o == null || dtype($o) == Tclass.ITER__D.RecursiveIterator?());

// RecursiveIterator: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.ITER__D.RecursiveIterator?(), $h) } 
  $IsAlloc($o, Tclass.ITER__D.RecursiveIterator?(), $h)
     <==> $o == null || read($h, $o, alloc));

function ITER__D.RecursiveIterator.n(ref) : int;

// RecursiveIterator.n: Type axiom
axiom (forall $o: ref :: 
  { ITER__D.RecursiveIterator.n($o) } 
  $o != null && dtype($o) == Tclass.ITER__D.RecursiveIterator?()
     ==> $Is(ITER__D.RecursiveIterator.n($o), Tclass._System.nat()));

// RecursiveIterator.n: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { ITER__D.RecursiveIterator.n($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__D.RecursiveIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(ITER__D.RecursiveIterator.n($o), Tclass._System.nat(), $h));

function ITER__D.RecursiveIterator.r(ref) : ref;

function Tclass.ITER__D.RecIterCaller?() : Ty;

const unique Tagclass.ITER__D.RecIterCaller?: TyTag;

// Tclass.ITER__D.RecIterCaller? Tag
axiom Tag(Tclass.ITER__D.RecIterCaller?()) == Tagclass.ITER__D.RecIterCaller?
   && TagFamily(Tclass.ITER__D.RecIterCaller?()) == tytagFamily$RecIterCaller;

// Box/unbox axiom for Tclass.ITER__D.RecIterCaller?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.ITER__D.RecIterCaller?()) } 
  $IsBox(bx, Tclass.ITER__D.RecIterCaller?())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.ITER__D.RecIterCaller?()));

// RecursiveIterator.r: Type axiom
axiom (forall $o: ref :: 
  { ITER__D.RecursiveIterator.r($o) } 
  $o != null && dtype($o) == Tclass.ITER__D.RecursiveIterator?()
     ==> $Is(ITER__D.RecursiveIterator.r($o), Tclass.ITER__D.RecIterCaller?()));

// RecursiveIterator.r: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { ITER__D.RecursiveIterator.r($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__D.RecursiveIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(ITER__D.RecursiveIterator.r($o), Tclass.ITER__D.RecIterCaller?(), $h));

function ITER__D.RecursiveIterator.good(ref) : bool;

// RecursiveIterator.good: Type axiom
axiom (forall $o: ref :: 
  { ITER__D.RecursiveIterator.good($o) } 
  $o != null && dtype($o) == Tclass.ITER__D.RecursiveIterator?()
     ==> $Is(ITER__D.RecursiveIterator.good($o), TBool));

// RecursiveIterator.good: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { ITER__D.RecursiveIterator.good($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__D.RecursiveIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(ITER__D.RecursiveIterator.good($o), TBool, $h));

function ITER__D.RecursiveIterator.__reads(ref) : Set Box;

// RecursiveIterator._reads: Type axiom
axiom (forall $o: ref :: 
  { ITER__D.RecursiveIterator.__reads($o) } 
  $o != null && dtype($o) == Tclass.ITER__D.RecursiveIterator?()
     ==> $Is(ITER__D.RecursiveIterator.__reads($o), TSet(Tclass._System.object?())));

// RecursiveIterator._reads: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { ITER__D.RecursiveIterator.__reads($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__D.RecursiveIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(ITER__D.RecursiveIterator.__reads($o), TSet(Tclass._System.object?()), $h));

function ITER__D.RecursiveIterator.__modifies(ref) : Set Box;

// RecursiveIterator._modifies: Type axiom
axiom (forall $o: ref :: 
  { ITER__D.RecursiveIterator.__modifies($o) } 
  $o != null && dtype($o) == Tclass.ITER__D.RecursiveIterator?()
     ==> $Is(ITER__D.RecursiveIterator.__modifies($o), TSet(Tclass._System.object?())));

// RecursiveIterator._modifies: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { ITER__D.RecursiveIterator.__modifies($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__D.RecursiveIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(ITER__D.RecursiveIterator.__modifies($o), TSet(Tclass._System.object?()), $h));

axiom FDim(ITER__D.RecursiveIterator.__new) == 0
   && FieldOfDecl(class.ITER__D.RecursiveIterator?, field$_new)
     == ITER__D.RecursiveIterator.__new
   && $IsGhostField(ITER__D.RecursiveIterator.__new);

const ITER__D.RecursiveIterator.__new: Field (Set Box);

// RecursiveIterator._new: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, ITER__D.RecursiveIterator.__new) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__D.RecursiveIterator?()
     ==> $Is(read($h, $o, ITER__D.RecursiveIterator.__new), TSet(Tclass._System.object?())));

// RecursiveIterator._new: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, ITER__D.RecursiveIterator.__new) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__D.RecursiveIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, ITER__D.RecursiveIterator.__new), 
      TSet(Tclass._System.object?()), 
      $h));

function ITER__D.RecursiveIterator.__decreases0(ref) : int;

// RecursiveIterator._decreases0: Type axiom
axiom (forall $o: ref :: 
  { ITER__D.RecursiveIterator.__decreases0($o) } 
  $o != null && dtype($o) == Tclass.ITER__D.RecursiveIterator?()
     ==> $Is(ITER__D.RecursiveIterator.__decreases0($o), TInt));

// RecursiveIterator._decreases0: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { ITER__D.RecursiveIterator.__decreases0($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__D.RecursiveIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(ITER__D.RecursiveIterator.__decreases0($o), TInt, $h));

function ITER__D.RecursiveIterator.__decreases1(ref) : ref;

// RecursiveIterator._decreases1: Type axiom
axiom (forall $o: ref :: 
  { ITER__D.RecursiveIterator.__decreases1($o) } 
  $o != null && dtype($o) == Tclass.ITER__D.RecursiveIterator?()
     ==> $Is(ITER__D.RecursiveIterator.__decreases1($o), Tclass.ITER__D.RecIterCaller?()));

// RecursiveIterator._decreases1: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { ITER__D.RecursiveIterator.__decreases1($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__D.RecursiveIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(ITER__D.RecursiveIterator.__decreases1($o), Tclass.ITER__D.RecIterCaller?(), $h));

function ITER__D.RecursiveIterator.__decreases2(ref) : bool;

// RecursiveIterator._decreases2: Type axiom
axiom (forall $o: ref :: 
  { ITER__D.RecursiveIterator.__decreases2($o) } 
  $o != null && dtype($o) == Tclass.ITER__D.RecursiveIterator?()
     ==> $Is(ITER__D.RecursiveIterator.__decreases2($o), TBool));

// RecursiveIterator._decreases2: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { ITER__D.RecursiveIterator.__decreases2($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__D.RecursiveIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(ITER__D.RecursiveIterator.__decreases2($o), TBool, $h));

// function declaration for ITER_D.RecursiveIterator.Valid
function ITER__D.RecursiveIterator.Valid($heap: Heap, this: ref) : bool;

function ITER__D.RecursiveIterator.Valid#canCall($heap: Heap, this: ref) : bool;

function Tclass.ITER__D.RecursiveIterator() : Ty;

const unique Tagclass.ITER__D.RecursiveIterator: TyTag;

// Tclass.ITER__D.RecursiveIterator Tag
axiom Tag(Tclass.ITER__D.RecursiveIterator()) == Tagclass.ITER__D.RecursiveIterator
   && TagFamily(Tclass.ITER__D.RecursiveIterator()) == tytagFamily$RecursiveIterator;

// Box/unbox axiom for Tclass.ITER__D.RecursiveIterator
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.ITER__D.RecursiveIterator()) } 
  $IsBox(bx, Tclass.ITER__D.RecursiveIterator())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.ITER__D.RecursiveIterator()));

// frame axiom for ITER__D.RecursiveIterator.Valid
axiom (forall $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), ITER__D.RecursiveIterator.Valid($h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass.ITER__D.RecursiveIterator())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && (
            $o == this
             || ITER__D.RecursiveIterator.__reads(this)[$Box($o)]
             || read($h0, this, ITER__D.RecursiveIterator.__new)[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> ITER__D.RecursiveIterator.Valid($h0, this)
       == ITER__D.RecursiveIterator.Valid($h1, this));

// consequence axiom for ITER__D.RecursiveIterator.Valid
axiom true
   ==> (forall $Heap: Heap, this: ref :: 
    { ITER__D.RecursiveIterator.Valid($Heap, this) } 
    ITER__D.RecursiveIterator.Valid#canCall($Heap, this)
         || ($IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass.ITER__D.RecursiveIterator())
           && $IsAlloc(this, Tclass.ITER__D.RecursiveIterator(), $Heap))
       ==> true);

function ITER__D.RecursiveIterator.Valid#requires(Heap, ref) : bool;

// #requires axiom for ITER__D.RecursiveIterator.Valid
axiom (forall $Heap: Heap, this: ref :: 
  { ITER__D.RecursiveIterator.Valid#requires($Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass.ITER__D.RecursiveIterator())
       && $IsAlloc(this, Tclass.ITER__D.RecursiveIterator(), $Heap)
     ==> ITER__D.RecursiveIterator.Valid#requires($Heap, this) == true);

// ITER_D.RecursiveIterator: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass.ITER__D.RecursiveIterator()) } 
  $Is(c#0, Tclass.ITER__D.RecursiveIterator())
     <==> $Is(c#0, Tclass.ITER__D.RecursiveIterator?()) && c#0 != null);

// ITER_D.RecursiveIterator: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass.ITER__D.RecursiveIterator(), $h) } 
  $IsAlloc(c#0, Tclass.ITER__D.RecursiveIterator(), $h)
     <==> $IsAlloc(c#0, Tclass.ITER__D.RecursiveIterator?(), $h));

procedure CheckWellformed$$ITER__D.RecursiveIterator(this: ref
       where this != null
         && 
        $Is(this, Tclass.ITER__D.RecursiveIterator())
         && $IsAlloc(this, Tclass.ITER__D.RecursiveIterator(), $Heap), 
    n#0: int where LitInt(0) <= n#0, 
    r#0: ref
       where $Is(r#0, Tclass.ITER__D.RecIterCaller?())
         && $IsAlloc(r#0, Tclass.ITER__D.RecIterCaller?(), $Heap), 
    good#0: bool);
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



const unique class.ITER__D.RecIterCaller?: ClassName;

// RecIterCaller: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.ITER__D.RecIterCaller?()) } 
  $Is($o, Tclass.ITER__D.RecIterCaller?())
     <==> $o == null || dtype($o) == Tclass.ITER__D.RecIterCaller?());

// RecIterCaller: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.ITER__D.RecIterCaller?(), $h) } 
  $IsAlloc($o, Tclass.ITER__D.RecIterCaller?(), $h)
     <==> $o == null || read($h, $o, alloc));

function Tclass.ITER__D.RecIterCaller() : Ty;

const unique Tagclass.ITER__D.RecIterCaller: TyTag;

// Tclass.ITER__D.RecIterCaller Tag
axiom Tag(Tclass.ITER__D.RecIterCaller()) == Tagclass.ITER__D.RecIterCaller
   && TagFamily(Tclass.ITER__D.RecIterCaller()) == tytagFamily$RecIterCaller;

// Box/unbox axiom for Tclass.ITER__D.RecIterCaller
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.ITER__D.RecIterCaller()) } 
  $IsBox(bx, Tclass.ITER__D.RecIterCaller())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.ITER__D.RecIterCaller()));

// ITER_D.RecIterCaller: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass.ITER__D.RecIterCaller()) } 
  $Is(c#0, Tclass.ITER__D.RecIterCaller())
     <==> $Is(c#0, Tclass.ITER__D.RecIterCaller?()) && c#0 != null);

// ITER_D.RecIterCaller: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass.ITER__D.RecIterCaller(), $h) } 
  $IsAlloc(c#0, Tclass.ITER__D.RecIterCaller(), $h)
     <==> $IsAlloc(c#0, Tclass.ITER__D.RecIterCaller?(), $h));

const unique class.ITER__D.__default: ClassName;

function Tclass.ITER__D.__default() : Ty;

const unique Tagclass.ITER__D.__default: TyTag;

// Tclass.ITER__D.__default Tag
axiom Tag(Tclass.ITER__D.__default()) == Tagclass.ITER__D.__default
   && TagFamily(Tclass.ITER__D.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.ITER__D.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.ITER__D.__default()) } 
  $IsBox(bx, Tclass.ITER__D.__default())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.ITER__D.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.ITER__D.__default()) } 
  $Is($o, Tclass.ITER__D.__default())
     <==> $o == null || dtype($o) == Tclass.ITER__D.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.ITER__D.__default(), $h) } 
  $IsAlloc($o, Tclass.ITER__D.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

const unique class.ITER__E.Cell?: ClassName;

function Tclass.ITER__E.Cell?() : Ty;

const unique Tagclass.ITER__E.Cell?: TyTag;

// Tclass.ITER__E.Cell? Tag
axiom Tag(Tclass.ITER__E.Cell?()) == Tagclass.ITER__E.Cell?
   && TagFamily(Tclass.ITER__E.Cell?()) == tytagFamily$Cell;

// Box/unbox axiom for Tclass.ITER__E.Cell?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.ITER__E.Cell?()) } 
  $IsBox(bx, Tclass.ITER__E.Cell?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.ITER__E.Cell?()));

// Cell: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.ITER__E.Cell?()) } 
  $Is($o, Tclass.ITER__E.Cell?())
     <==> $o == null || dtype($o) == Tclass.ITER__E.Cell?());

// Cell: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.ITER__E.Cell?(), $h) } 
  $IsAlloc($o, Tclass.ITER__E.Cell?(), $h) <==> $o == null || read($h, $o, alloc));

axiom FDim(ITER__E.Cell.data) == 0
   && FieldOfDecl(class.ITER__E.Cell?, field$data) == ITER__E.Cell.data
   && !$IsGhostField(ITER__E.Cell.data);

const ITER__E.Cell.data: Field int;

// Cell.data: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, ITER__E.Cell.data) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass.ITER__E.Cell?()
     ==> $Is(read($h, $o, ITER__E.Cell.data), Tclass._System.nat()));

// Cell.data: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, ITER__E.Cell.data) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__E.Cell?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, ITER__E.Cell.data), Tclass._System.nat(), $h));

function Tclass.ITER__E.Cell() : Ty;

const unique Tagclass.ITER__E.Cell: TyTag;

// Tclass.ITER__E.Cell Tag
axiom Tag(Tclass.ITER__E.Cell()) == Tagclass.ITER__E.Cell
   && TagFamily(Tclass.ITER__E.Cell()) == tytagFamily$Cell;

// Box/unbox axiom for Tclass.ITER__E.Cell
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.ITER__E.Cell()) } 
  $IsBox(bx, Tclass.ITER__E.Cell())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.ITER__E.Cell()));

// ITER_E.Cell: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass.ITER__E.Cell()) } 
  $Is(c#0, Tclass.ITER__E.Cell())
     <==> $Is(c#0, Tclass.ITER__E.Cell?()) && c#0 != null);

// ITER_E.Cell: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass.ITER__E.Cell(), $h) } 
  $IsAlloc(c#0, Tclass.ITER__E.Cell(), $h)
     <==> $IsAlloc(c#0, Tclass.ITER__E.Cell?(), $h));

const unique class.ITER__E.RecursiveIterator?: ClassName;

function Tclass.ITER__E.RecursiveIterator?() : Ty;

const unique Tagclass.ITER__E.RecursiveIterator?: TyTag;

// Tclass.ITER__E.RecursiveIterator? Tag
axiom Tag(Tclass.ITER__E.RecursiveIterator?()) == Tagclass.ITER__E.RecursiveIterator?
   && TagFamily(Tclass.ITER__E.RecursiveIterator?()) == tytagFamily$RecursiveIterator;

// Box/unbox axiom for Tclass.ITER__E.RecursiveIterator?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.ITER__E.RecursiveIterator?()) } 
  $IsBox(bx, Tclass.ITER__E.RecursiveIterator?())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.ITER__E.RecursiveIterator?()));

// RecursiveIterator: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.ITER__E.RecursiveIterator?()) } 
  $Is($o, Tclass.ITER__E.RecursiveIterator?())
     <==> $o == null || dtype($o) == Tclass.ITER__E.RecursiveIterator?());

// RecursiveIterator: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.ITER__E.RecursiveIterator?(), $h) } 
  $IsAlloc($o, Tclass.ITER__E.RecursiveIterator?(), $h)
     <==> $o == null || read($h, $o, alloc));

function ITER__E.RecursiveIterator.cell(ref) : ref;

// RecursiveIterator.cell: Type axiom
axiom (forall $o: ref :: 
  { ITER__E.RecursiveIterator.cell($o) } 
  $o != null && dtype($o) == Tclass.ITER__E.RecursiveIterator?()
     ==> $Is(ITER__E.RecursiveIterator.cell($o), Tclass.ITER__E.Cell?()));

// RecursiveIterator.cell: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { ITER__E.RecursiveIterator.cell($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__E.RecursiveIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(ITER__E.RecursiveIterator.cell($o), Tclass.ITER__E.Cell?(), $h));

function ITER__E.RecursiveIterator.n(ref) : int;

// RecursiveIterator.n: Type axiom
axiom (forall $o: ref :: 
  { ITER__E.RecursiveIterator.n($o) } 
  $o != null && dtype($o) == Tclass.ITER__E.RecursiveIterator?()
     ==> $Is(ITER__E.RecursiveIterator.n($o), Tclass._System.nat()));

// RecursiveIterator.n: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { ITER__E.RecursiveIterator.n($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__E.RecursiveIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(ITER__E.RecursiveIterator.n($o), Tclass._System.nat(), $h));

function ITER__E.RecursiveIterator.r(ref) : ref;

function Tclass.ITER__E.RecIterCaller?() : Ty;

const unique Tagclass.ITER__E.RecIterCaller?: TyTag;

// Tclass.ITER__E.RecIterCaller? Tag
axiom Tag(Tclass.ITER__E.RecIterCaller?()) == Tagclass.ITER__E.RecIterCaller?
   && TagFamily(Tclass.ITER__E.RecIterCaller?()) == tytagFamily$RecIterCaller;

// Box/unbox axiom for Tclass.ITER__E.RecIterCaller?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.ITER__E.RecIterCaller?()) } 
  $IsBox(bx, Tclass.ITER__E.RecIterCaller?())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.ITER__E.RecIterCaller?()));

// RecursiveIterator.r: Type axiom
axiom (forall $o: ref :: 
  { ITER__E.RecursiveIterator.r($o) } 
  $o != null && dtype($o) == Tclass.ITER__E.RecursiveIterator?()
     ==> $Is(ITER__E.RecursiveIterator.r($o), Tclass.ITER__E.RecIterCaller?()));

// RecursiveIterator.r: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { ITER__E.RecursiveIterator.r($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__E.RecursiveIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(ITER__E.RecursiveIterator.r($o), Tclass.ITER__E.RecIterCaller?(), $h));

function ITER__E.RecursiveIterator.good(ref) : bool;

// RecursiveIterator.good: Type axiom
axiom (forall $o: ref :: 
  { ITER__E.RecursiveIterator.good($o) } 
  $o != null && dtype($o) == Tclass.ITER__E.RecursiveIterator?()
     ==> $Is(ITER__E.RecursiveIterator.good($o), TBool));

// RecursiveIterator.good: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { ITER__E.RecursiveIterator.good($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__E.RecursiveIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(ITER__E.RecursiveIterator.good($o), TBool, $h));

function ITER__E.RecursiveIterator.__reads(ref) : Set Box;

// RecursiveIterator._reads: Type axiom
axiom (forall $o: ref :: 
  { ITER__E.RecursiveIterator.__reads($o) } 
  $o != null && dtype($o) == Tclass.ITER__E.RecursiveIterator?()
     ==> $Is(ITER__E.RecursiveIterator.__reads($o), TSet(Tclass._System.object?())));

// RecursiveIterator._reads: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { ITER__E.RecursiveIterator.__reads($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__E.RecursiveIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(ITER__E.RecursiveIterator.__reads($o), TSet(Tclass._System.object?()), $h));

function ITER__E.RecursiveIterator.__modifies(ref) : Set Box;

// RecursiveIterator._modifies: Type axiom
axiom (forall $o: ref :: 
  { ITER__E.RecursiveIterator.__modifies($o) } 
  $o != null && dtype($o) == Tclass.ITER__E.RecursiveIterator?()
     ==> $Is(ITER__E.RecursiveIterator.__modifies($o), TSet(Tclass._System.object?())));

// RecursiveIterator._modifies: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { ITER__E.RecursiveIterator.__modifies($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__E.RecursiveIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(ITER__E.RecursiveIterator.__modifies($o), TSet(Tclass._System.object?()), $h));

axiom FDim(ITER__E.RecursiveIterator.__new) == 0
   && FieldOfDecl(class.ITER__E.RecursiveIterator?, field$_new)
     == ITER__E.RecursiveIterator.__new
   && $IsGhostField(ITER__E.RecursiveIterator.__new);

const ITER__E.RecursiveIterator.__new: Field (Set Box);

// RecursiveIterator._new: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, ITER__E.RecursiveIterator.__new) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__E.RecursiveIterator?()
     ==> $Is(read($h, $o, ITER__E.RecursiveIterator.__new), TSet(Tclass._System.object?())));

// RecursiveIterator._new: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, ITER__E.RecursiveIterator.__new) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__E.RecursiveIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, ITER__E.RecursiveIterator.__new), 
      TSet(Tclass._System.object?()), 
      $h));

function ITER__E.RecursiveIterator.__decreases0(ref) : int;

// RecursiveIterator._decreases0: Type axiom
axiom (forall $o: ref :: 
  { ITER__E.RecursiveIterator.__decreases0($o) } 
  $o != null && dtype($o) == Tclass.ITER__E.RecursiveIterator?()
     ==> $Is(ITER__E.RecursiveIterator.__decreases0($o), TInt));

// RecursiveIterator._decreases0: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { ITER__E.RecursiveIterator.__decreases0($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__E.RecursiveIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(ITER__E.RecursiveIterator.__decreases0($o), TInt, $h));

// function declaration for ITER_E.RecursiveIterator.Valid
function ITER__E.RecursiveIterator.Valid($heap: Heap, this: ref) : bool;

function ITER__E.RecursiveIterator.Valid#canCall($heap: Heap, this: ref) : bool;

function Tclass.ITER__E.RecursiveIterator() : Ty;

const unique Tagclass.ITER__E.RecursiveIterator: TyTag;

// Tclass.ITER__E.RecursiveIterator Tag
axiom Tag(Tclass.ITER__E.RecursiveIterator()) == Tagclass.ITER__E.RecursiveIterator
   && TagFamily(Tclass.ITER__E.RecursiveIterator()) == tytagFamily$RecursiveIterator;

// Box/unbox axiom for Tclass.ITER__E.RecursiveIterator
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.ITER__E.RecursiveIterator()) } 
  $IsBox(bx, Tclass.ITER__E.RecursiveIterator())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.ITER__E.RecursiveIterator()));

// frame axiom for ITER__E.RecursiveIterator.Valid
axiom (forall $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), ITER__E.RecursiveIterator.Valid($h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass.ITER__E.RecursiveIterator())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && (
            $o == this
             || ITER__E.RecursiveIterator.__reads(this)[$Box($o)]
             || read($h0, this, ITER__E.RecursiveIterator.__new)[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> ITER__E.RecursiveIterator.Valid($h0, this)
       == ITER__E.RecursiveIterator.Valid($h1, this));

// consequence axiom for ITER__E.RecursiveIterator.Valid
axiom true
   ==> (forall $Heap: Heap, this: ref :: 
    { ITER__E.RecursiveIterator.Valid($Heap, this) } 
    ITER__E.RecursiveIterator.Valid#canCall($Heap, this)
         || ($IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass.ITER__E.RecursiveIterator())
           && $IsAlloc(this, Tclass.ITER__E.RecursiveIterator(), $Heap))
       ==> true);

function ITER__E.RecursiveIterator.Valid#requires(Heap, ref) : bool;

// #requires axiom for ITER__E.RecursiveIterator.Valid
axiom (forall $Heap: Heap, this: ref :: 
  { ITER__E.RecursiveIterator.Valid#requires($Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass.ITER__E.RecursiveIterator())
       && $IsAlloc(this, Tclass.ITER__E.RecursiveIterator(), $Heap)
     ==> ITER__E.RecursiveIterator.Valid#requires($Heap, this) == true);

// ITER_E.RecursiveIterator: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass.ITER__E.RecursiveIterator()) } 
  $Is(c#0, Tclass.ITER__E.RecursiveIterator())
     <==> $Is(c#0, Tclass.ITER__E.RecursiveIterator?()) && c#0 != null);

// ITER_E.RecursiveIterator: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass.ITER__E.RecursiveIterator(), $h) } 
  $IsAlloc(c#0, Tclass.ITER__E.RecursiveIterator(), $h)
     <==> $IsAlloc(c#0, Tclass.ITER__E.RecursiveIterator?(), $h));

procedure CheckWellformed$$ITER__E.RecursiveIterator(this: ref
       where this != null
         && 
        $Is(this, Tclass.ITER__E.RecursiveIterator())
         && $IsAlloc(this, Tclass.ITER__E.RecursiveIterator(), $Heap), 
    cell#0: ref
       where $Is(cell#0, Tclass.ITER__E.Cell?())
         && $IsAlloc(cell#0, Tclass.ITER__E.Cell?(), $Heap), 
    n#0: int where LitInt(0) <= n#0, 
    r#0: ref
       where $Is(r#0, Tclass.ITER__E.RecIterCaller?())
         && $IsAlloc(r#0, Tclass.ITER__E.RecIterCaller?(), $Heap), 
    good#0: bool);
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



const unique class.ITER__E.RecIterCaller?: ClassName;

// RecIterCaller: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.ITER__E.RecIterCaller?()) } 
  $Is($o, Tclass.ITER__E.RecIterCaller?())
     <==> $o == null || dtype($o) == Tclass.ITER__E.RecIterCaller?());

// RecIterCaller: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.ITER__E.RecIterCaller?(), $h) } 
  $IsAlloc($o, Tclass.ITER__E.RecIterCaller?(), $h)
     <==> $o == null || read($h, $o, alloc));

function Tclass.ITER__E.RecIterCaller() : Ty;

const unique Tagclass.ITER__E.RecIterCaller: TyTag;

// Tclass.ITER__E.RecIterCaller Tag
axiom Tag(Tclass.ITER__E.RecIterCaller()) == Tagclass.ITER__E.RecIterCaller
   && TagFamily(Tclass.ITER__E.RecIterCaller()) == tytagFamily$RecIterCaller;

// Box/unbox axiom for Tclass.ITER__E.RecIterCaller
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.ITER__E.RecIterCaller()) } 
  $IsBox(bx, Tclass.ITER__E.RecIterCaller())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.ITER__E.RecIterCaller()));

// ITER_E.RecIterCaller: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass.ITER__E.RecIterCaller()) } 
  $Is(c#0, Tclass.ITER__E.RecIterCaller())
     <==> $Is(c#0, Tclass.ITER__E.RecIterCaller?()) && c#0 != null);

// ITER_E.RecIterCaller: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass.ITER__E.RecIterCaller(), $h) } 
  $IsAlloc(c#0, Tclass.ITER__E.RecIterCaller(), $h)
     <==> $IsAlloc(c#0, Tclass.ITER__E.RecIterCaller?(), $h));

const unique class.ITER__E.__default: ClassName;

function Tclass.ITER__E.__default() : Ty;

const unique Tagclass.ITER__E.__default: TyTag;

// Tclass.ITER__E.__default Tag
axiom Tag(Tclass.ITER__E.__default()) == Tagclass.ITER__E.__default
   && TagFamily(Tclass.ITER__E.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.ITER__E.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.ITER__E.__default()) } 
  $IsBox(bx, Tclass.ITER__E.__default())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.ITER__E.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.ITER__E.__default()) } 
  $Is($o, Tclass.ITER__E.__default())
     <==> $o == null || dtype($o) == Tclass.ITER__E.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.ITER__E.__default(), $h) } 
  $IsAlloc($o, Tclass.ITER__E.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

const unique class.ITER__F.Cell?: ClassName;

function Tclass.ITER__F.Cell?() : Ty;

const unique Tagclass.ITER__F.Cell?: TyTag;

// Tclass.ITER__F.Cell? Tag
axiom Tag(Tclass.ITER__F.Cell?()) == Tagclass.ITER__F.Cell?
   && TagFamily(Tclass.ITER__F.Cell?()) == tytagFamily$Cell;

// Box/unbox axiom for Tclass.ITER__F.Cell?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.ITER__F.Cell?()) } 
  $IsBox(bx, Tclass.ITER__F.Cell?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.ITER__F.Cell?()));

// Cell: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.ITER__F.Cell?()) } 
  $Is($o, Tclass.ITER__F.Cell?())
     <==> $o == null || dtype($o) == Tclass.ITER__F.Cell?());

// Cell: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.ITER__F.Cell?(), $h) } 
  $IsAlloc($o, Tclass.ITER__F.Cell?(), $h) <==> $o == null || read($h, $o, alloc));

axiom FDim(ITER__F.Cell.data) == 0
   && FieldOfDecl(class.ITER__F.Cell?, field$data) == ITER__F.Cell.data
   && !$IsGhostField(ITER__F.Cell.data);

const ITER__F.Cell.data: Field int;

// Cell.data: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, ITER__F.Cell.data) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass.ITER__F.Cell?()
     ==> $Is(read($h, $o, ITER__F.Cell.data), Tclass._System.nat()));

// Cell.data: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, ITER__F.Cell.data) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__F.Cell?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, ITER__F.Cell.data), Tclass._System.nat(), $h));

function Tclass.ITER__F.Cell() : Ty;

const unique Tagclass.ITER__F.Cell: TyTag;

// Tclass.ITER__F.Cell Tag
axiom Tag(Tclass.ITER__F.Cell()) == Tagclass.ITER__F.Cell
   && TagFamily(Tclass.ITER__F.Cell()) == tytagFamily$Cell;

// Box/unbox axiom for Tclass.ITER__F.Cell
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.ITER__F.Cell()) } 
  $IsBox(bx, Tclass.ITER__F.Cell())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.ITER__F.Cell()));

// ITER_F.Cell: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass.ITER__F.Cell()) } 
  $Is(c#0, Tclass.ITER__F.Cell())
     <==> $Is(c#0, Tclass.ITER__F.Cell?()) && c#0 != null);

// ITER_F.Cell: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass.ITER__F.Cell(), $h) } 
  $IsAlloc(c#0, Tclass.ITER__F.Cell(), $h)
     <==> $IsAlloc(c#0, Tclass.ITER__F.Cell?(), $h));

const unique class.ITER__F.RecursiveIterator?: ClassName;

function Tclass.ITER__F.RecursiveIterator?() : Ty;

const unique Tagclass.ITER__F.RecursiveIterator?: TyTag;

// Tclass.ITER__F.RecursiveIterator? Tag
axiom Tag(Tclass.ITER__F.RecursiveIterator?()) == Tagclass.ITER__F.RecursiveIterator?
   && TagFamily(Tclass.ITER__F.RecursiveIterator?()) == tytagFamily$RecursiveIterator;

// Box/unbox axiom for Tclass.ITER__F.RecursiveIterator?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.ITER__F.RecursiveIterator?()) } 
  $IsBox(bx, Tclass.ITER__F.RecursiveIterator?())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.ITER__F.RecursiveIterator?()));

// RecursiveIterator: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.ITER__F.RecursiveIterator?()) } 
  $Is($o, Tclass.ITER__F.RecursiveIterator?())
     <==> $o == null || dtype($o) == Tclass.ITER__F.RecursiveIterator?());

// RecursiveIterator: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.ITER__F.RecursiveIterator?(), $h) } 
  $IsAlloc($o, Tclass.ITER__F.RecursiveIterator?(), $h)
     <==> $o == null || read($h, $o, alloc));

function ITER__F.RecursiveIterator.cell(ref) : ref;

// RecursiveIterator.cell: Type axiom
axiom (forall $o: ref :: 
  { ITER__F.RecursiveIterator.cell($o) } 
  $o != null && dtype($o) == Tclass.ITER__F.RecursiveIterator?()
     ==> $Is(ITER__F.RecursiveIterator.cell($o), Tclass.ITER__F.Cell?()));

// RecursiveIterator.cell: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { ITER__F.RecursiveIterator.cell($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__F.RecursiveIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(ITER__F.RecursiveIterator.cell($o), Tclass.ITER__F.Cell?(), $h));

function ITER__F.RecursiveIterator.n(ref) : int;

// RecursiveIterator.n: Type axiom
axiom (forall $o: ref :: 
  { ITER__F.RecursiveIterator.n($o) } 
  $o != null && dtype($o) == Tclass.ITER__F.RecursiveIterator?()
     ==> $Is(ITER__F.RecursiveIterator.n($o), Tclass._System.nat()));

// RecursiveIterator.n: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { ITER__F.RecursiveIterator.n($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__F.RecursiveIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(ITER__F.RecursiveIterator.n($o), Tclass._System.nat(), $h));

function ITER__F.RecursiveIterator.r(ref) : ref;

function Tclass.ITER__F.RecIterCaller?() : Ty;

const unique Tagclass.ITER__F.RecIterCaller?: TyTag;

// Tclass.ITER__F.RecIterCaller? Tag
axiom Tag(Tclass.ITER__F.RecIterCaller?()) == Tagclass.ITER__F.RecIterCaller?
   && TagFamily(Tclass.ITER__F.RecIterCaller?()) == tytagFamily$RecIterCaller;

// Box/unbox axiom for Tclass.ITER__F.RecIterCaller?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.ITER__F.RecIterCaller?()) } 
  $IsBox(bx, Tclass.ITER__F.RecIterCaller?())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.ITER__F.RecIterCaller?()));

// RecursiveIterator.r: Type axiom
axiom (forall $o: ref :: 
  { ITER__F.RecursiveIterator.r($o) } 
  $o != null && dtype($o) == Tclass.ITER__F.RecursiveIterator?()
     ==> $Is(ITER__F.RecursiveIterator.r($o), Tclass.ITER__F.RecIterCaller?()));

// RecursiveIterator.r: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { ITER__F.RecursiveIterator.r($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__F.RecursiveIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(ITER__F.RecursiveIterator.r($o), Tclass.ITER__F.RecIterCaller?(), $h));

function ITER__F.RecursiveIterator.good(ref) : bool;

// RecursiveIterator.good: Type axiom
axiom (forall $o: ref :: 
  { ITER__F.RecursiveIterator.good($o) } 
  $o != null && dtype($o) == Tclass.ITER__F.RecursiveIterator?()
     ==> $Is(ITER__F.RecursiveIterator.good($o), TBool));

// RecursiveIterator.good: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { ITER__F.RecursiveIterator.good($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__F.RecursiveIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(ITER__F.RecursiveIterator.good($o), TBool, $h));

function ITER__F.RecursiveIterator.__reads(ref) : Set Box;

// RecursiveIterator._reads: Type axiom
axiom (forall $o: ref :: 
  { ITER__F.RecursiveIterator.__reads($o) } 
  $o != null && dtype($o) == Tclass.ITER__F.RecursiveIterator?()
     ==> $Is(ITER__F.RecursiveIterator.__reads($o), TSet(Tclass._System.object?())));

// RecursiveIterator._reads: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { ITER__F.RecursiveIterator.__reads($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__F.RecursiveIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(ITER__F.RecursiveIterator.__reads($o), TSet(Tclass._System.object?()), $h));

function ITER__F.RecursiveIterator.__modifies(ref) : Set Box;

// RecursiveIterator._modifies: Type axiom
axiom (forall $o: ref :: 
  { ITER__F.RecursiveIterator.__modifies($o) } 
  $o != null && dtype($o) == Tclass.ITER__F.RecursiveIterator?()
     ==> $Is(ITER__F.RecursiveIterator.__modifies($o), TSet(Tclass._System.object?())));

// RecursiveIterator._modifies: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { ITER__F.RecursiveIterator.__modifies($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__F.RecursiveIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(ITER__F.RecursiveIterator.__modifies($o), TSet(Tclass._System.object?()), $h));

axiom FDim(ITER__F.RecursiveIterator.__new) == 0
   && FieldOfDecl(class.ITER__F.RecursiveIterator?, field$_new)
     == ITER__F.RecursiveIterator.__new
   && $IsGhostField(ITER__F.RecursiveIterator.__new);

const ITER__F.RecursiveIterator.__new: Field (Set Box);

// RecursiveIterator._new: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, ITER__F.RecursiveIterator.__new) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__F.RecursiveIterator?()
     ==> $Is(read($h, $o, ITER__F.RecursiveIterator.__new), TSet(Tclass._System.object?())));

// RecursiveIterator._new: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, ITER__F.RecursiveIterator.__new) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__F.RecursiveIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, ITER__F.RecursiveIterator.__new), 
      TSet(Tclass._System.object?()), 
      $h));

function ITER__F.RecursiveIterator.__decreases0(ref) : int;

// RecursiveIterator._decreases0: Type axiom
axiom (forall $o: ref :: 
  { ITER__F.RecursiveIterator.__decreases0($o) } 
  $o != null && dtype($o) == Tclass.ITER__F.RecursiveIterator?()
     ==> $Is(ITER__F.RecursiveIterator.__decreases0($o), TInt));

// RecursiveIterator._decreases0: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { ITER__F.RecursiveIterator.__decreases0($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__F.RecursiveIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(ITER__F.RecursiveIterator.__decreases0($o), TInt, $h));

function ITER__F.RecursiveIterator.__decreases1(ref) : int;

// RecursiveIterator._decreases1: Type axiom
axiom (forall $o: ref :: 
  { ITER__F.RecursiveIterator.__decreases1($o) } 
  $o != null && dtype($o) == Tclass.ITER__F.RecursiveIterator?()
     ==> $Is(ITER__F.RecursiveIterator.__decreases1($o), TInt));

// RecursiveIterator._decreases1: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { ITER__F.RecursiveIterator.__decreases1($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ITER__F.RecursiveIterator?()
       && read($h, $o, alloc)
     ==> $IsAlloc(ITER__F.RecursiveIterator.__decreases1($o), TInt, $h));

// function declaration for ITER_F.RecursiveIterator.Valid
function ITER__F.RecursiveIterator.Valid($heap: Heap, this: ref) : bool;

function ITER__F.RecursiveIterator.Valid#canCall($heap: Heap, this: ref) : bool;

function Tclass.ITER__F.RecursiveIterator() : Ty;

const unique Tagclass.ITER__F.RecursiveIterator: TyTag;

// Tclass.ITER__F.RecursiveIterator Tag
axiom Tag(Tclass.ITER__F.RecursiveIterator()) == Tagclass.ITER__F.RecursiveIterator
   && TagFamily(Tclass.ITER__F.RecursiveIterator()) == tytagFamily$RecursiveIterator;

// Box/unbox axiom for Tclass.ITER__F.RecursiveIterator
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.ITER__F.RecursiveIterator()) } 
  $IsBox(bx, Tclass.ITER__F.RecursiveIterator())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.ITER__F.RecursiveIterator()));

// frame axiom for ITER__F.RecursiveIterator.Valid
axiom (forall $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), ITER__F.RecursiveIterator.Valid($h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass.ITER__F.RecursiveIterator())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && (
            $o == this
             || ITER__F.RecursiveIterator.__reads(this)[$Box($o)]
             || read($h0, this, ITER__F.RecursiveIterator.__new)[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> ITER__F.RecursiveIterator.Valid($h0, this)
       == ITER__F.RecursiveIterator.Valid($h1, this));

// consequence axiom for ITER__F.RecursiveIterator.Valid
axiom true
   ==> (forall $Heap: Heap, this: ref :: 
    { ITER__F.RecursiveIterator.Valid($Heap, this) } 
    ITER__F.RecursiveIterator.Valid#canCall($Heap, this)
         || ($IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass.ITER__F.RecursiveIterator())
           && $IsAlloc(this, Tclass.ITER__F.RecursiveIterator(), $Heap))
       ==> true);

function ITER__F.RecursiveIterator.Valid#requires(Heap, ref) : bool;

// #requires axiom for ITER__F.RecursiveIterator.Valid
axiom (forall $Heap: Heap, this: ref :: 
  { ITER__F.RecursiveIterator.Valid#requires($Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass.ITER__F.RecursiveIterator())
       && $IsAlloc(this, Tclass.ITER__F.RecursiveIterator(), $Heap)
     ==> ITER__F.RecursiveIterator.Valid#requires($Heap, this) == true);

// ITER_F.RecursiveIterator: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass.ITER__F.RecursiveIterator()) } 
  $Is(c#0, Tclass.ITER__F.RecursiveIterator())
     <==> $Is(c#0, Tclass.ITER__F.RecursiveIterator?()) && c#0 != null);

// ITER_F.RecursiveIterator: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass.ITER__F.RecursiveIterator(), $h) } 
  $IsAlloc(c#0, Tclass.ITER__F.RecursiveIterator(), $h)
     <==> $IsAlloc(c#0, Tclass.ITER__F.RecursiveIterator?(), $h));

procedure CheckWellformed$$ITER__F.RecursiveIterator(this: ref
       where this != null
         && 
        $Is(this, Tclass.ITER__F.RecursiveIterator())
         && $IsAlloc(this, Tclass.ITER__F.RecursiveIterator(), $Heap), 
    cell#0: ref
       where $Is(cell#0, Tclass.ITER__F.Cell?())
         && $IsAlloc(cell#0, Tclass.ITER__F.Cell?(), $Heap), 
    n#0: int where LitInt(0) <= n#0, 
    r#0: ref
       where $Is(r#0, Tclass.ITER__F.RecIterCaller?())
         && $IsAlloc(r#0, Tclass.ITER__F.RecIterCaller?(), $Heap), 
    good#0: bool);
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



const unique class.ITER__F.RecIterCaller?: ClassName;

// RecIterCaller: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.ITER__F.RecIterCaller?()) } 
  $Is($o, Tclass.ITER__F.RecIterCaller?())
     <==> $o == null || dtype($o) == Tclass.ITER__F.RecIterCaller?());

// RecIterCaller: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.ITER__F.RecIterCaller?(), $h) } 
  $IsAlloc($o, Tclass.ITER__F.RecIterCaller?(), $h)
     <==> $o == null || read($h, $o, alloc));

function Tclass.ITER__F.RecIterCaller() : Ty;

const unique Tagclass.ITER__F.RecIterCaller: TyTag;

// Tclass.ITER__F.RecIterCaller Tag
axiom Tag(Tclass.ITER__F.RecIterCaller()) == Tagclass.ITER__F.RecIterCaller
   && TagFamily(Tclass.ITER__F.RecIterCaller()) == tytagFamily$RecIterCaller;

// Box/unbox axiom for Tclass.ITER__F.RecIterCaller
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.ITER__F.RecIterCaller()) } 
  $IsBox(bx, Tclass.ITER__F.RecIterCaller())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.ITER__F.RecIterCaller()));

// ITER_F.RecIterCaller: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass.ITER__F.RecIterCaller()) } 
  $Is(c#0, Tclass.ITER__F.RecIterCaller())
     <==> $Is(c#0, Tclass.ITER__F.RecIterCaller?()) && c#0 != null);

// ITER_F.RecIterCaller: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass.ITER__F.RecIterCaller(), $h) } 
  $IsAlloc(c#0, Tclass.ITER__F.RecIterCaller(), $h)
     <==> $IsAlloc(c#0, Tclass.ITER__F.RecIterCaller?(), $h));

const unique class.ITER__F.__default: ClassName;

function Tclass.ITER__F.__default() : Ty;

const unique Tagclass.ITER__F.__default: TyTag;

// Tclass.ITER__F.__default Tag
axiom Tag(Tclass.ITER__F.__default()) == Tagclass.ITER__F.__default
   && TagFamily(Tclass.ITER__F.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.ITER__F.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.ITER__F.__default()) } 
  $IsBox(bx, Tclass.ITER__F.__default())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.ITER__F.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.ITER__F.__default()) } 
  $Is($o, Tclass.ITER__F.__default())
     <==> $o == null || dtype($o) == Tclass.ITER__F.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.ITER__F.__default(), $h) } 
  $IsAlloc($o, Tclass.ITER__F.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

const unique class.ModuleWithIterator.Iter?: ClassName;

function Tclass.ModuleWithIterator.Iter?() : Ty;

const unique Tagclass.ModuleWithIterator.Iter?: TyTag;

// Tclass.ModuleWithIterator.Iter? Tag
axiom Tag(Tclass.ModuleWithIterator.Iter?()) == Tagclass.ModuleWithIterator.Iter?
   && TagFamily(Tclass.ModuleWithIterator.Iter?()) == tytagFamily$Iter;

// Box/unbox axiom for Tclass.ModuleWithIterator.Iter?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.ModuleWithIterator.Iter?()) } 
  $IsBox(bx, Tclass.ModuleWithIterator.Iter?())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.ModuleWithIterator.Iter?()));

// Iter: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.ModuleWithIterator.Iter?()) } 
  $Is($o, Tclass.ModuleWithIterator.Iter?())
     <==> $o == null || dtype($o) == Tclass.ModuleWithIterator.Iter?());

// Iter: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.ModuleWithIterator.Iter?(), $h) } 
  $IsAlloc($o, Tclass.ModuleWithIterator.Iter?(), $h)
     <==> $o == null || read($h, $o, alloc));

function ModuleWithIterator.Iter.x(ref) : int;

// Iter.x: Type axiom
axiom (forall $o: ref :: 
  { ModuleWithIterator.Iter.x($o) } 
  $o != null && dtype($o) == Tclass.ModuleWithIterator.Iter?()
     ==> $Is(ModuleWithIterator.Iter.x($o), TInt));

// Iter.x: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { ModuleWithIterator.Iter.x($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ModuleWithIterator.Iter?()
       && read($h, $o, alloc)
     ==> $IsAlloc(ModuleWithIterator.Iter.x($o), TInt, $h));

axiom FDim(ModuleWithIterator.Iter.y) == 0
   && FieldOfDecl(class.ModuleWithIterator.Iter?, field$y)
     == ModuleWithIterator.Iter.y
   && !$IsGhostField(ModuleWithIterator.Iter.y);

const ModuleWithIterator.Iter.y: Field int;

// Iter.y: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, ModuleWithIterator.Iter.y) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass.ModuleWithIterator.Iter?()
     ==> $Is(read($h, $o, ModuleWithIterator.Iter.y), TInt));

// Iter.y: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, ModuleWithIterator.Iter.y) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ModuleWithIterator.Iter?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, ModuleWithIterator.Iter.y), TInt, $h));

axiom FDim(ModuleWithIterator.Iter.ys) == 0
   && FieldOfDecl(class.ModuleWithIterator.Iter?, field$ys)
     == ModuleWithIterator.Iter.ys
   && $IsGhostField(ModuleWithIterator.Iter.ys);

const ModuleWithIterator.Iter.ys: Field (Seq Box);

// Iter.ys: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, ModuleWithIterator.Iter.ys) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass.ModuleWithIterator.Iter?()
     ==> $Is(read($h, $o, ModuleWithIterator.Iter.ys), TSeq(TInt)));

// Iter.ys: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, ModuleWithIterator.Iter.ys) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ModuleWithIterator.Iter?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, ModuleWithIterator.Iter.ys), TSeq(TInt), $h));

function ModuleWithIterator.Iter.__reads(ref) : Set Box;

// Iter._reads: Type axiom
axiom (forall $o: ref :: 
  { ModuleWithIterator.Iter.__reads($o) } 
  $o != null && dtype($o) == Tclass.ModuleWithIterator.Iter?()
     ==> $Is(ModuleWithIterator.Iter.__reads($o), TSet(Tclass._System.object?())));

// Iter._reads: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { ModuleWithIterator.Iter.__reads($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ModuleWithIterator.Iter?()
       && read($h, $o, alloc)
     ==> $IsAlloc(ModuleWithIterator.Iter.__reads($o), TSet(Tclass._System.object?()), $h));

function ModuleWithIterator.Iter.__modifies(ref) : Set Box;

// Iter._modifies: Type axiom
axiom (forall $o: ref :: 
  { ModuleWithIterator.Iter.__modifies($o) } 
  $o != null && dtype($o) == Tclass.ModuleWithIterator.Iter?()
     ==> $Is(ModuleWithIterator.Iter.__modifies($o), TSet(Tclass._System.object?())));

// Iter._modifies: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { ModuleWithIterator.Iter.__modifies($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ModuleWithIterator.Iter?()
       && read($h, $o, alloc)
     ==> $IsAlloc(ModuleWithIterator.Iter.__modifies($o), TSet(Tclass._System.object?()), $h));

axiom FDim(ModuleWithIterator.Iter.__new) == 0
   && FieldOfDecl(class.ModuleWithIterator.Iter?, field$_new)
     == ModuleWithIterator.Iter.__new
   && $IsGhostField(ModuleWithIterator.Iter.__new);

const ModuleWithIterator.Iter.__new: Field (Set Box);

// Iter._new: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, ModuleWithIterator.Iter.__new) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass.ModuleWithIterator.Iter?()
     ==> $Is(read($h, $o, ModuleWithIterator.Iter.__new), TSet(Tclass._System.object?())));

// Iter._new: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, ModuleWithIterator.Iter.__new) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ModuleWithIterator.Iter?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, ModuleWithIterator.Iter.__new), TSet(Tclass._System.object?()), $h));

function ModuleWithIterator.Iter.__decreases0(ref) : int;

// Iter._decreases0: Type axiom
axiom (forall $o: ref :: 
  { ModuleWithIterator.Iter.__decreases0($o) } 
  $o != null && dtype($o) == Tclass.ModuleWithIterator.Iter?()
     ==> $Is(ModuleWithIterator.Iter.__decreases0($o), TInt));

// Iter._decreases0: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { ModuleWithIterator.Iter.__decreases0($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.ModuleWithIterator.Iter?()
       && read($h, $o, alloc)
     ==> $IsAlloc(ModuleWithIterator.Iter.__decreases0($o), TInt, $h));

// function declaration for ModuleWithIterator.Iter.Valid
function ModuleWithIterator.Iter.Valid($heap: Heap, this: ref) : bool;

function ModuleWithIterator.Iter.Valid#canCall($heap: Heap, this: ref) : bool;

function Tclass.ModuleWithIterator.Iter() : Ty;

const unique Tagclass.ModuleWithIterator.Iter: TyTag;

// Tclass.ModuleWithIterator.Iter Tag
axiom Tag(Tclass.ModuleWithIterator.Iter()) == Tagclass.ModuleWithIterator.Iter
   && TagFamily(Tclass.ModuleWithIterator.Iter()) == tytagFamily$Iter;

// Box/unbox axiom for Tclass.ModuleWithIterator.Iter
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.ModuleWithIterator.Iter()) } 
  $IsBox(bx, Tclass.ModuleWithIterator.Iter())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.ModuleWithIterator.Iter()));

// frame axiom for ModuleWithIterator.Iter.Valid
axiom (forall $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), ModuleWithIterator.Iter.Valid($h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass.ModuleWithIterator.Iter())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && (
            $o == this
             || ModuleWithIterator.Iter.__reads(this)[$Box($o)]
             || read($h0, this, ModuleWithIterator.Iter.__new)[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> ModuleWithIterator.Iter.Valid($h0, this)
       == ModuleWithIterator.Iter.Valid($h1, this));

// consequence axiom for ModuleWithIterator.Iter.Valid
axiom true
   ==> (forall $Heap: Heap, this: ref :: 
    { ModuleWithIterator.Iter.Valid($Heap, this) } 
    ModuleWithIterator.Iter.Valid#canCall($Heap, this)
         || ($IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass.ModuleWithIterator.Iter())
           && $IsAlloc(this, Tclass.ModuleWithIterator.Iter(), $Heap))
       ==> true);

function ModuleWithIterator.Iter.Valid#requires(Heap, ref) : bool;

// #requires axiom for ModuleWithIterator.Iter.Valid
axiom (forall $Heap: Heap, this: ref :: 
  { ModuleWithIterator.Iter.Valid#requires($Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass.ModuleWithIterator.Iter())
       && $IsAlloc(this, Tclass.ModuleWithIterator.Iter(), $Heap)
     ==> ModuleWithIterator.Iter.Valid#requires($Heap, this) == true);

// ModuleWithIterator.Iter: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass.ModuleWithIterator.Iter()) } 
  $Is(c#0, Tclass.ModuleWithIterator.Iter())
     <==> $Is(c#0, Tclass.ModuleWithIterator.Iter?()) && c#0 != null);

// ModuleWithIterator.Iter: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass.ModuleWithIterator.Iter(), $h) } 
  $IsAlloc(c#0, Tclass.ModuleWithIterator.Iter(), $h)
     <==> $IsAlloc(c#0, Tclass.ModuleWithIterator.Iter?(), $h));

procedure CheckWellformed$$ModuleWithIterator.Iter(this: ref
       where this != null
         && 
        $Is(this, Tclass.ModuleWithIterator.Iter())
         && $IsAlloc(this, Tclass.ModuleWithIterator.Iter(), $Heap), 
    x#0: int);
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;



const #$_default: Ty;

const unique class.ModuleWithIterator.__default: ClassName;

function Tclass.ModuleWithIterator.__default() : Ty;

const unique Tagclass.ModuleWithIterator.__default: TyTag;

// Tclass.ModuleWithIterator.__default Tag
axiom Tag(Tclass.ModuleWithIterator.__default())
     == Tagclass.ModuleWithIterator.__default
   && TagFamily(Tclass.ModuleWithIterator.__default()) == tytagFamily$_default;

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.ModuleWithIterator.__default()) } 
  $Is($o, Tclass.ModuleWithIterator.__default())
     <==> $o == null || dtype($o) == Tclass.ModuleWithIterator.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.ModuleWithIterator.__default(), $h) } 
  $IsAlloc($o, Tclass.ModuleWithIterator.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

const unique class.IteratorClient__Reveals.__default: ClassName;

function Tclass.IteratorClient__Reveals.__default() : Ty;

const unique Tagclass.IteratorClient__Reveals.__default: TyTag;

// Tclass.IteratorClient__Reveals.__default Tag
axiom Tag(Tclass.IteratorClient__Reveals.__default())
     == Tagclass.IteratorClient__Reveals.__default
   && TagFamily(Tclass.IteratorClient__Reveals.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.IteratorClient__Reveals.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.IteratorClient__Reveals.__default()) } 
  $IsBox(bx, Tclass.IteratorClient__Reveals.__default())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.IteratorClient__Reveals.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.IteratorClient__Reveals.__default()) } 
  $Is($o, Tclass.IteratorClient__Reveals.__default())
     <==> $o == null || dtype($o) == Tclass.IteratorClient__Reveals.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.IteratorClient__Reveals.__default(), $h) } 
  $IsAlloc($o, Tclass.IteratorClient__Reveals.__default(), $h)
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

const unique tytagFamily$_tuple#2: TyTagFamily;

const unique tytagFamily$_tuple#0: TyTagFamily;

const unique tytagFamily$MyIter: TyTagFamily;

const unique tytagFamily$MyIntIter: TyTagFamily;

const unique tytagFamily$Naturals: TyTagFamily;

const unique tytagFamily$Cell: TyTagFamily;

const unique tytagFamily$IterA: TyTagFamily;

const unique tytagFamily$IterB: TyTagFamily;

const unique tytagFamily$IterC: TyTagFamily;

const unique tytagFamily$AllocationIterator: TyTagFamily;

const unique tytagFamily$DoleOutReferences: TyTagFamily;

const unique tytagFamily$Cls: TyTagFamily;

const unique tytagFamily$LoopFrame_Iter: TyTagFamily;

const unique tytagFamily$NewRemainsFresh: TyTagFamily;

const unique tytagFamily$_default: TyTagFamily;

const unique tytagFamily$RecursiveIterator: TyTagFamily;

const unique tytagFamily$RecIterCaller: TyTagFamily;

const unique tytagFamily$Iter: TyTagFamily;

const unique field$x: NameFamily;

const unique field$y: NameFamily;

const unique field$xs: NameFamily;

const unique field$ys: NameFamily;

const unique field$_new: NameFamily;

const unique field$n: NameFamily;

const unique field$ns: NameFamily;

const unique field$data: NameFamily;

const unique field$r: NameFamily;

const unique field$c: NameFamily;

const unique field$rs: NameFamily;

const unique field$cs: NameFamily;
