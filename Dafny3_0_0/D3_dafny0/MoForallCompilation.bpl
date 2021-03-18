// Dafny 3.0.0.30204
// Command Line Options: -compile:0 -noVerify /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy -print:./MoForallCompilation.bpl

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

const unique class._System.array2?: ClassName;

function Tclass._System.array2?(Ty) : Ty;

const unique Tagclass._System.array2?: TyTag;

// Tclass._System.array2? Tag
axiom (forall _System.array2$arg: Ty :: 
  { Tclass._System.array2?(_System.array2$arg) } 
  Tag(Tclass._System.array2?(_System.array2$arg)) == Tagclass._System.array2?
     && TagFamily(Tclass._System.array2?(_System.array2$arg)) == tytagFamily$array2);

// Tclass._System.array2? injectivity 0
axiom (forall _System.array2$arg: Ty :: 
  { Tclass._System.array2?(_System.array2$arg) } 
  Tclass._System.array2?_0(Tclass._System.array2?(_System.array2$arg))
     == _System.array2$arg);

function Tclass._System.array2?_0(Ty) : Ty;

// Box/unbox axiom for Tclass._System.array2?
axiom (forall _System.array2$arg: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.array2?(_System.array2$arg)) } 
  $IsBox(bx, Tclass._System.array2?(_System.array2$arg))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._System.array2?(_System.array2$arg)));

axiom (forall o: ref :: { _System.array2.Length0(o) } 0 <= _System.array2.Length0(o));

axiom (forall o: ref :: { _System.array2.Length1(o) } 0 <= _System.array2.Length1(o));

// array2.: Type axiom
axiom (forall _System.array2$arg: Ty, $h: Heap, $o: ref, $i0: int, $i1: int :: 
  { read($h, $o, MultiIndexField(IndexField($i0), $i1)), Tclass._System.array2?(_System.array2$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array2?(_System.array2$arg)
       && 
      0 <= $i0
       && $i0 < _System.array2.Length0($o)
       && 
      0 <= $i1
       && $i1 < _System.array2.Length1($o)
     ==> $IsBox(read($h, $o, MultiIndexField(IndexField($i0), $i1)), _System.array2$arg));

// array2.: Allocation axiom
axiom (forall _System.array2$arg: Ty, $h: Heap, $o: ref, $i0: int, $i1: int :: 
  { read($h, $o, MultiIndexField(IndexField($i0), $i1)), Tclass._System.array2?(_System.array2$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array2?(_System.array2$arg)
       && 
      0 <= $i0
       && $i0 < _System.array2.Length0($o)
       && 
      0 <= $i1
       && $i1 < _System.array2.Length1($o)
       && read($h, $o, alloc)
     ==> $IsAllocBox(read($h, $o, MultiIndexField(IndexField($i0), $i1)), _System.array2$arg, $h));

// array2: Class $Is
axiom (forall _System.array2$arg: Ty, $o: ref :: 
  { $Is($o, Tclass._System.array2?(_System.array2$arg)) } 
  $Is($o, Tclass._System.array2?(_System.array2$arg))
     <==> $o == null || dtype($o) == Tclass._System.array2?(_System.array2$arg));

// array2: Class $IsAlloc
axiom (forall _System.array2$arg: Ty, $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._System.array2?(_System.array2$arg), $h) } 
  $IsAlloc($o, Tclass._System.array2?(_System.array2$arg), $h)
     <==> $o == null || read($h, $o, alloc));

function _System.array2.Length0(ref) : int;

// array2.Length0: Type axiom
axiom (forall _System.array2$arg: Ty, $o: ref :: 
  { _System.array2.Length0($o), Tclass._System.array2?(_System.array2$arg) } 
  $o != null && dtype($o) == Tclass._System.array2?(_System.array2$arg)
     ==> $Is(_System.array2.Length0($o), TInt));

// array2.Length0: Allocation axiom
axiom (forall _System.array2$arg: Ty, $h: Heap, $o: ref :: 
  { _System.array2.Length0($o), read($h, $o, alloc), Tclass._System.array2?(_System.array2$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array2?(_System.array2$arg)
       && read($h, $o, alloc)
     ==> $IsAlloc(_System.array2.Length0($o), TInt, $h));

function _System.array2.Length1(ref) : int;

// array2.Length1: Type axiom
axiom (forall _System.array2$arg: Ty, $o: ref :: 
  { _System.array2.Length1($o), Tclass._System.array2?(_System.array2$arg) } 
  $o != null && dtype($o) == Tclass._System.array2?(_System.array2$arg)
     ==> $Is(_System.array2.Length1($o), TInt));

// array2.Length1: Allocation axiom
axiom (forall _System.array2$arg: Ty, $h: Heap, $o: ref :: 
  { _System.array2.Length1($o), read($h, $o, alloc), Tclass._System.array2?(_System.array2$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array2?(_System.array2$arg)
       && read($h, $o, alloc)
     ==> $IsAlloc(_System.array2.Length1($o), TInt, $h));

function Tclass._System.array2(Ty) : Ty;

const unique Tagclass._System.array2: TyTag;

// Tclass._System.array2 Tag
axiom (forall _System.array2$arg: Ty :: 
  { Tclass._System.array2(_System.array2$arg) } 
  Tag(Tclass._System.array2(_System.array2$arg)) == Tagclass._System.array2
     && TagFamily(Tclass._System.array2(_System.array2$arg)) == tytagFamily$array2);

// Tclass._System.array2 injectivity 0
axiom (forall _System.array2$arg: Ty :: 
  { Tclass._System.array2(_System.array2$arg) } 
  Tclass._System.array2_0(Tclass._System.array2(_System.array2$arg))
     == _System.array2$arg);

function Tclass._System.array2_0(Ty) : Ty;

// Box/unbox axiom for Tclass._System.array2
axiom (forall _System.array2$arg: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.array2(_System.array2$arg)) } 
  $IsBox(bx, Tclass._System.array2(_System.array2$arg))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._System.array2(_System.array2$arg)));

// _System.array2: subset type $Is
axiom (forall _System.array2$arg: Ty, c#0: ref :: 
  { $Is(c#0, Tclass._System.array2(_System.array2$arg)) } 
  $Is(c#0, Tclass._System.array2(_System.array2$arg))
     <==> $Is(c#0, Tclass._System.array2?(_System.array2$arg)) && c#0 != null);

// _System.array2: subset type $IsAlloc
axiom (forall _System.array2$arg: Ty, c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._System.array2(_System.array2$arg), $h) } 
  $IsAlloc(c#0, Tclass._System.array2(_System.array2$arg), $h)
     <==> $IsAlloc(c#0, Tclass._System.array2?(_System.array2$arg), $h));

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

const unique class._module.Node?: ClassName;

function Tclass._module.Node?() : Ty;

const unique Tagclass._module.Node?: TyTag;

// Tclass._module.Node? Tag
axiom Tag(Tclass._module.Node?()) == Tagclass._module.Node?
   && TagFamily(Tclass._module.Node?()) == tytagFamily$Node;

// Box/unbox axiom for Tclass._module.Node?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Node?()) } 
  $IsBox(bx, Tclass._module.Node?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Node?()));

// Node: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.Node?()) } 
  $Is($o, Tclass._module.Node?())
     <==> $o == null || dtype($o) == Tclass._module.Node?());

// Node: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.Node?(), $h) } 
  $IsAlloc($o, Tclass._module.Node?(), $h) <==> $o == null || read($h, $o, alloc));

axiom FDim(_module.Node.Repr) == 0
   && FieldOfDecl(class._module.Node?, field$Repr) == _module.Node.Repr
   && !$IsGhostField(_module.Node.Repr);

const _module.Node.Repr: Field (Set Box);

function Tclass._module.Node() : Ty;

const unique Tagclass._module.Node: TyTag;

// Tclass._module.Node Tag
axiom Tag(Tclass._module.Node()) == Tagclass._module.Node
   && TagFamily(Tclass._module.Node()) == tytagFamily$Node;

// Box/unbox axiom for Tclass._module.Node
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Node()) } 
  $IsBox(bx, Tclass._module.Node())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Node()));

// Node.Repr: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Node.Repr) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Node?()
     ==> $Is(read($h, $o, _module.Node.Repr), TSet(Tclass._module.Node())));

// Node.Repr: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Node.Repr) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Node?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Node.Repr), TSet(Tclass._module.Node()), $h));

// function declaration for _module.Node.Valid
function _module.Node.Valid($ly: LayerType, $heap: Heap, this: ref) : bool;

function _module.Node.Valid#canCall($heap: Heap, this: ref) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, $Heap: Heap, this: ref :: 
  { _module.Node.Valid($LS($ly), $Heap, this) } 
  _module.Node.Valid($LS($ly), $Heap, this)
     == _module.Node.Valid($ly, $Heap, this));

// fuel synonym axiom
axiom (forall $ly: LayerType, $Heap: Heap, this: ref :: 
  { _module.Node.Valid(AsFuelBottom($ly), $Heap, this) } 
  _module.Node.Valid($ly, $Heap, this) == _module.Node.Valid($LZ, $Heap, this));

// frame axiom for _module.Node.Valid
axiom (forall $ly: LayerType, $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.Node.Valid($ly, $h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.Node())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && ($o == this || read($h0, this, _module.Node.Repr)[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.Node.Valid($ly, $h0, this) == _module.Node.Valid($ly, $h1, this));

// consequence axiom for _module.Node.Valid
axiom 2 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, this: ref :: 
    { _module.Node.Valid($ly, $Heap, this) } 
    _module.Node.Valid#canCall($Heap, this)
         || (2 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.Node())
           && $IsAlloc(this, Tclass._module.Node(), $Heap))
       ==> true);

function _module.Node.Valid#requires(LayerType, Heap, ref) : bool;

// #requires axiom for _module.Node.Valid
axiom (forall $ly: LayerType, $Heap: Heap, this: ref :: 
  { _module.Node.Valid#requires($ly, $Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.Node())
       && $IsAlloc(this, Tclass._module.Node(), $Heap)
     ==> _module.Node.Valid#requires($ly, $Heap, this) == true);

axiom FDim(_module.Node.next) == 0
   && FieldOfDecl(class._module.Node?, field$next) == _module.Node.next
   && !$IsGhostField(_module.Node.next);

// definition axiom for _module.Node.Valid (revealed)
axiom 2 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, this: ref :: 
    { _module.Node.Valid($LS($ly), $Heap, this), $IsGoodHeap($Heap) } 
    _module.Node.Valid#canCall($Heap, this)
         || (2 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.Node())
           && $IsAlloc(this, Tclass._module.Node(), $Heap))
       ==> (read($Heap, this, _module.Node.Repr)[$Box(this)]
           ==> 
          read($Heap, this, _module.Node.next) != null
           ==> 
          read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.next))]
           ==> 
          Set#Subset(read($Heap, read($Heap, this, _module.Node.next), _module.Node.Repr), 
            read($Heap, this, _module.Node.Repr))
           ==> 
          !read($Heap, read($Heap, this, _module.Node.next), _module.Node.Repr)[$Box(this)]
           ==> _module.Node.Valid#canCall($Heap, read($Heap, this, _module.Node.next)))
         && _module.Node.Valid($LS($ly), $Heap, this)
           == (read($Heap, this, _module.Node.Repr)[$Box(this)]
             && (read($Heap, this, _module.Node.next) != null
               ==> read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.next))]
                 && Set#Subset(read($Heap, read($Heap, this, _module.Node.next), _module.Node.Repr), 
                  read($Heap, this, _module.Node.Repr))
                 && !read($Heap, read($Heap, this, _module.Node.next), _module.Node.Repr)[$Box(this)]
                 && _module.Node.Valid($ly, $Heap, read($Heap, this, _module.Node.next)))));

procedure CheckWellformed$$_module.Node.Valid(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), $Heap));
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Node.Valid(this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;
  var b$reqreads#2: bool;
  var b$reqreads#3: bool;
  var b$reqreads#4: bool;
  var b$reqreads#5: bool;
  var b$reqreads#6: bool;
  var b$reqreads#7: bool;
  var b$reqreads#8: bool;
  var b$reqreads#9: bool;
  var b$reqreads#10: bool;
  var b$reqreads#11: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;
    b$reqreads#3 := true;
    b$reqreads#4 := true;
    b$reqreads#5 := true;
    b$reqreads#6 := true;
    b$reqreads#7 := true;
    b$reqreads#8 := true;
    b$reqreads#9 := true;
    b$reqreads#10 := true;
    b$reqreads#11 := true;

    // AddWellformednessCheck for function Valid
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(110,12): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> $o == this || read($Heap, this, _module.Node.Repr)[$Box($o)]);
    b$reqreads#0 := $_Frame[this, _module.Node.Repr];
    assert b$reqreads#0;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc)
             ==> $o == this || read($Heap, this, _module.Node.Repr)[$Box($o)]);
        b$reqreads#1 := $_Frame[this, _module.Node.Repr];
        if (read($Heap, this, _module.Node.Repr)[$Box(this)])
        {
            b$reqreads#2 := $_Frame[this, _module.Node.next];
            if (read($Heap, this, _module.Node.next) != null)
            {
                b$reqreads#3 := $_Frame[this, _module.Node.next];
                b$reqreads#4 := $_Frame[this, _module.Node.Repr];
                if (read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.next))])
                {
                    b$reqreads#5 := $_Frame[this, _module.Node.next];
                    assert read($Heap, this, _module.Node.next) != null;
                    b$reqreads#6 := $_Frame[read($Heap, this, _module.Node.next), _module.Node.Repr];
                    b$reqreads#7 := $_Frame[this, _module.Node.Repr];
                }

                if (read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.next))]
                   && Set#Subset(read($Heap, read($Heap, this, _module.Node.next), _module.Node.Repr), 
                    read($Heap, this, _module.Node.Repr)))
                {
                    b$reqreads#8 := $_Frame[this, _module.Node.next];
                    assert read($Heap, this, _module.Node.next) != null;
                    b$reqreads#9 := $_Frame[read($Heap, this, _module.Node.next), _module.Node.Repr];
                }

                if (read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.next))]
                   && Set#Subset(read($Heap, read($Heap, this, _module.Node.next), _module.Node.Repr), 
                    read($Heap, this, _module.Node.Repr))
                   && !read($Heap, read($Heap, this, _module.Node.next), _module.Node.Repr)[$Box(this)])
                {
                    b$reqreads#10 := $_Frame[this, _module.Node.next];
                    assert read($Heap, this, _module.Node.next) != null;
                    b$reqreads#11 := (forall<alpha> $o: ref, $f: Field alpha :: 
                      $o != null
                           && read($Heap, $o, alloc)
                           && ($o == read($Heap, this, _module.Node.next)
                             || read($Heap, read($Heap, this, _module.Node.next), _module.Node.Repr)[$Box($o)])
                         ==> $_Frame[$o, $f]);
                    assert Set#Subset(Set#Union(read($Heap, read($Heap, this, _module.Node.next), _module.Node.Repr), 
                          Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.next)))), 
                        Set#Union(read($Heap, this, _module.Node.Repr), 
                          Set#UnionOne(Set#Empty(): Set Box, $Box(this))))
                       && !Set#Subset(Set#Union(read($Heap, this, _module.Node.Repr), 
                          Set#UnionOne(Set#Empty(): Set Box, $Box(this))), 
                        Set#Union(read($Heap, read($Heap, this, _module.Node.next), _module.Node.Repr), 
                          Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.next)))));
                    assume _module.Node.Valid#canCall($Heap, read($Heap, this, _module.Node.next));
                }
            }
        }

        assume _module.Node.Valid($LS($LZ), $Heap, this)
           == (read($Heap, this, _module.Node.Repr)[$Box(this)]
             && (read($Heap, this, _module.Node.next) != null
               ==> read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.next))]
                 && Set#Subset(read($Heap, read($Heap, this, _module.Node.next), _module.Node.Repr), 
                  read($Heap, this, _module.Node.Repr))
                 && !read($Heap, read($Heap, this, _module.Node.next), _module.Node.Repr)[$Box(this)]
                 && _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.next))));
        assume read($Heap, this, _module.Node.Repr)[$Box(this)]
           ==> 
          read($Heap, this, _module.Node.next) != null
           ==> 
          read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.next))]
           ==> 
          Set#Subset(read($Heap, read($Heap, this, _module.Node.next), _module.Node.Repr), 
            read($Heap, this, _module.Node.Repr))
           ==> 
          !read($Heap, read($Heap, this, _module.Node.next), _module.Node.Repr)[$Box(this)]
           ==> _module.Node.Valid#canCall($Heap, read($Heap, this, _module.Node.next));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.Node.Valid($LS($LZ), $Heap, this), TBool);
        assert b$reqreads#1;
        assert b$reqreads#2;
        assert b$reqreads#3;
        assert b$reqreads#4;
        assert b$reqreads#5;
        assert b$reqreads#6;
        assert b$reqreads#7;
        assert b$reqreads#8;
        assert b$reqreads#9;
        assert b$reqreads#10;
        assert b$reqreads#11;
    }
}



axiom FDim(_module.Node.val) == 0
   && FieldOfDecl(class._module.Node?, field$val) == _module.Node.val
   && !$IsGhostField(_module.Node.val);

const _module.Node.val: Field int;

// Node.val: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Node.val) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Node?()
     ==> $Is(read($h, $o, _module.Node.val), TInt));

// Node.val: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Node.val) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Node?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Node.val), TInt, $h));

const _module.Node.next: Field ref;

// Node.next: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Node.next) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Node?()
     ==> $Is(read($h, $o, _module.Node.next), Tclass._module.Node?()));

// Node.next: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Node.next) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Node?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Node.next), Tclass._module.Node?(), $h));

procedure CheckWellformed$$_module.Node.__ctor(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), $Heap), 
    val#0: int, 
    next#0: ref
       where $Is(next#0, Tclass._module.Node?())
         && $IsAlloc(next#0, Tclass._module.Node?(), $Heap));
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Node.__ctor(this: ref, val#0: int, next#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: _ctor, CheckWellformed$$_module.Node.__ctor
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(121,2): initial state"} true;
    if (*)
    {
        assume next#0 != null;
        assert next#0 != null;
        assume _module.Node.Valid#canCall($Heap, next#0);
        assume _module.Node.Valid($LS($LZ), $Heap, next#0);
    }
    else
    {
        assume next#0 != null ==> _module.Node.Valid($LS($LZ), $Heap, next#0);
    }

    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
    assume $HeapSucc(old($Heap), $Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(123,20): post-state"} true;
    assume _module.Node.Valid#canCall($Heap, this);
    assume _module.Node.Valid($LS($LZ), $Heap, this);
    if (next#0 == null)
    {
    }
    else
    {
        assert next#0 != null;
    }

    assume (forall $o: ref :: 
      { read(old($Heap), $o, alloc) } 
      read($Heap, this, _module.Node.Repr)[$Box($o)]
           && !(if next#0 == null
             then Set#Empty(): Set Box
             else read($Heap, next#0, _module.Node.Repr))[$Box($o)]
         ==> $o != null && !read(old($Heap), $o, alloc));
}



procedure Call$$_module.Node.__ctor(val#0: int, 
    next#0: ref
       where $Is(next#0, Tclass._module.Node?())
         && $IsAlloc(next#0, Tclass._module.Node?(), $Heap))
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), $Heap));
  // user-defined preconditions
  requires next#0 != null
     ==> 
    _module.Node.Valid#canCall($Heap, next#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, next#0)
       || read($Heap, next#0, _module.Node.Repr)[$Box(next#0)];
  requires next#0 != null
     ==> 
    _module.Node.Valid#canCall($Heap, next#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, next#0)
       || (read($Heap, next#0, _module.Node.next) != null
         ==> read($Heap, next#0, _module.Node.Repr)[$Box(read($Heap, next#0, _module.Node.next))]);
  requires next#0 != null
     ==> 
    _module.Node.Valid#canCall($Heap, next#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, next#0)
       || (read($Heap, next#0, _module.Node.next) != null
         ==> Set#Subset(read($Heap, read($Heap, next#0, _module.Node.next), _module.Node.Repr), 
          read($Heap, next#0, _module.Node.Repr)));
  requires next#0 != null
     ==> 
    _module.Node.Valid#canCall($Heap, next#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, next#0)
       || (read($Heap, next#0, _module.Node.next) != null
         ==> !read($Heap, read($Heap, next#0, _module.Node.next), _module.Node.Repr)[$Box(next#0)]);
  requires next#0 != null
     ==> 
    _module.Node.Valid#canCall($Heap, next#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, next#0)
       || (read($Heap, next#0, _module.Node.next) != null
         ==> _module.Node.Valid($LS($LS($LZ)), $Heap, read($Heap, next#0, _module.Node.next)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Node.Valid#canCall($Heap, this);
  free ensures _module.Node.Valid#canCall($Heap, this)
     && 
    _module.Node.Valid($LS($LZ), $Heap, this)
     && 
    read($Heap, this, _module.Node.Repr)[$Box(this)]
     && (read($Heap, this, _module.Node.next) != null
       ==> read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.next))]
         && Set#Subset(read($Heap, read($Heap, this, _module.Node.next), _module.Node.Repr), 
          read($Heap, this, _module.Node.Repr))
         && !read($Heap, read($Heap, this, _module.Node.next), _module.Node.Repr)[$Box(this)]
         && _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.next)));
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    read($Heap, this, _module.Node.Repr)[$Box($o)]
         && !(if next#0 == null
           then Set#Empty(): Set Box
           else read($Heap, next#0, _module.Node.Repr))[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  // constructor allocates the object
  ensures !read(old($Heap), this, alloc);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Node.__ctor(val#0: int, 
    next#0: ref
       where $Is(next#0, Tclass._module.Node?())
         && $IsAlloc(next#0, Tclass._module.Node?(), $Heap))
   returns (this: ref where this != null && $Is(this, Tclass._module.Node()), 
    $_reverifyPost: bool);
  free requires 3 == $FunctionContextHeight;
  // user-defined preconditions
  free requires next#0 != null
     ==> _module.Node.Valid#canCall($Heap, next#0)
       && 
      _module.Node.Valid($LS($LZ), $Heap, next#0)
       && 
      read($Heap, next#0, _module.Node.Repr)[$Box(next#0)]
       && (read($Heap, next#0, _module.Node.next) != null
         ==> read($Heap, next#0, _module.Node.Repr)[$Box(read($Heap, next#0, _module.Node.next))]
           && Set#Subset(read($Heap, read($Heap, next#0, _module.Node.next), _module.Node.Repr), 
            read($Heap, next#0, _module.Node.Repr))
           && !read($Heap, read($Heap, next#0, _module.Node.next), _module.Node.Repr)[$Box(next#0)]
           && _module.Node.Valid($LS($LZ), $Heap, read($Heap, next#0, _module.Node.next)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Node.Valid#canCall($Heap, this);
  ensures _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || read($Heap, this, _module.Node.Repr)[$Box(this)];
  ensures _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.next) != null
         ==> read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.next))]);
  ensures _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.next) != null
         ==> Set#Subset(read($Heap, read($Heap, this, _module.Node.next), _module.Node.Repr), 
          read($Heap, this, _module.Node.Repr)));
  ensures _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.next) != null
         ==> !read($Heap, read($Heap, this, _module.Node.next), _module.Node.Repr)[$Box(this)]);
  ensures _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.next) != null
         ==> _module.Node.Valid($LS($LS($LZ)), $Heap, read($Heap, this, _module.Node.next)));
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    read($Heap, this, _module.Node.Repr)[$Box($o)]
         && !(if next#0 == null
           then Set#Empty(): Set Box
           else read($Heap, next#0, _module.Node.Repr))[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Node.__ctor(val#0: int, next#0: ref) returns (this: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var this.Repr: Set Box;
  var this.val: int;
  var this.next: ref;
  var $obj0: ref;
  var $obj1: ref;
  var $rhs#0: int;
  var $rhs#1: ref where $Is($rhs#1, Tclass._module.Node?());

    // AddMethodImpl: _ctor, Impl$$_module.Node.__ctor
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(124,2): initial state"} true;
    $_reverifyPost := false;
    // ----- divided block before new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(124,3)
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(125,25)
    assume true;
    $obj0 := this;
    assume true;
    $obj1 := this;
    assume true;
    $rhs#0 := val#0;
    assume true;
    $rhs#1 := next#0;
    this.val := $rhs#0;
    this.next := $rhs#1;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(125,36)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(126,10)
    assume true;
    if (next#0 == null)
    {
    }
    else
    {
        assert next#0 != null;
    }

    assume true;
    this.Repr := Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(this)), 
      (if next#0 == null
         then Set#Empty(): Set Box
         else read($Heap, next#0, _module.Node.Repr)));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(126,59)"} true;
    // ----- new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(124,3)
    assume !read($Heap, this, alloc);
    assume read($Heap, this, _module.Node.Repr) == this.Repr;
    assume read($Heap, this, _module.Node.val) == this.val;
    assume read($Heap, this, _module.Node.next) == this.next;
    $Heap := update($Heap, this, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    // ----- divided block after new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(124,3)
}



procedure CheckWellformed$$_module.Node.Create(n#0: int where LitInt(0) <= n#0)
   returns (d#0: ref
       where $Is(d#0, Tclass._module.Node()) && $IsAlloc(d#0, Tclass._module.Node(), $Heap));
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Node.Create(n#0: int) returns (d#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Create, CheckWellformed$$_module.Node.Create
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(129,16): initial state"} true;
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
    assume $HeapSucc(old($Heap), $Heap);
    havoc d#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(130,22): post-state"} true;
    assert d#0 != null;
    assume _module.Node.Valid#canCall($Heap, d#0);
    assume _module.Node.Valid($LS($LZ), $Heap, d#0);
    assert d#0 != null;
    assume (forall $o: ref :: 
      { read($Heap, d#0, _module.Node.Repr)[$Box($o)] } 
      read($Heap, d#0, _module.Node.Repr)[$Box($o)]
         ==> $o != null && !read(old($Heap), $o, alloc));
}



procedure Call$$_module.Node.Create(n#0: int where LitInt(0) <= n#0)
   returns (d#0: ref
       where $Is(d#0, Tclass._module.Node()) && $IsAlloc(d#0, Tclass._module.Node(), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Node.Valid#canCall($Heap, d#0);
  free ensures _module.Node.Valid#canCall($Heap, d#0)
     && 
    _module.Node.Valid($LS($LZ), $Heap, d#0)
     && 
    read($Heap, d#0, _module.Node.Repr)[$Box(d#0)]
     && (read($Heap, d#0, _module.Node.next) != null
       ==> read($Heap, d#0, _module.Node.Repr)[$Box(read($Heap, d#0, _module.Node.next))]
         && Set#Subset(read($Heap, read($Heap, d#0, _module.Node.next), _module.Node.Repr), 
          read($Heap, d#0, _module.Node.Repr))
         && !read($Heap, read($Heap, d#0, _module.Node.next), _module.Node.Repr)[$Box(d#0)]
         && _module.Node.Valid($LS($LZ), $Heap, read($Heap, d#0, _module.Node.next)));
  ensures (forall $o: ref :: 
    { read($Heap, d#0, _module.Node.Repr)[$Box($o)] } 
    read($Heap, d#0, _module.Node.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Node.Create(n#0: int where LitInt(0) <= n#0)
   returns (defass#d#0: bool, 
    d#0: ref
       where defass#d#0
         ==> $Is(d#0, Tclass._module.Node()) && $IsAlloc(d#0, Tclass._module.Node(), $Heap), 
    $_reverifyPost: bool);
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Node.Valid#canCall($Heap, d#0);
  ensures _module.Node.Valid#canCall($Heap, d#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, d#0)
       || read($Heap, d#0, _module.Node.Repr)[$Box(d#0)];
  ensures _module.Node.Valid#canCall($Heap, d#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, d#0)
       || (read($Heap, d#0, _module.Node.next) != null
         ==> read($Heap, d#0, _module.Node.Repr)[$Box(read($Heap, d#0, _module.Node.next))]);
  ensures _module.Node.Valid#canCall($Heap, d#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, d#0)
       || (read($Heap, d#0, _module.Node.next) != null
         ==> Set#Subset(read($Heap, read($Heap, d#0, _module.Node.next), _module.Node.Repr), 
          read($Heap, d#0, _module.Node.Repr)));
  ensures _module.Node.Valid#canCall($Heap, d#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, d#0)
       || (read($Heap, d#0, _module.Node.next) != null
         ==> !read($Heap, read($Heap, d#0, _module.Node.next), _module.Node.Repr)[$Box(d#0)]);
  ensures _module.Node.Valid#canCall($Heap, d#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, d#0)
       || (read($Heap, d#0, _module.Node.next) != null
         ==> _module.Node.Valid($LS($LS($LZ)), $Heap, read($Heap, d#0, _module.Node.next)));
  ensures (forall $o: ref :: 
    { read($Heap, d#0, _module.Node.Repr)[$Box($o)] } 
    read($Heap, d#0, _module.Node.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Node.Create(n#0: int) returns (defass#d#0: bool, d#0: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $nw: ref;
  var val##0: int;
  var next##0: ref;
  var i#0: int;
  var $PreLoopHeap$loop#0: Heap;
  var preLoop$loop#0$defass#d#0: bool;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var $decr$loop#00: int;
  var val##0_0: int;
  var next##0_0: ref;

    // AddMethodImpl: Create, Impl$$_module.Node.Create
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(131,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(132,7)
    assume true;
    // ----- init call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(132,10)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    val##0 := LitInt(0);
    assume true;
    // ProcessCallStmt: CheckSubrange
    next##0 := null;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $nw := Call$$_module.Node.__ctor(val##0, next##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(132,26)"} true;
    d#0 := $nw;
    defass#d#0 := true;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(132,26)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(133,11)
    assume true;
    assume true;
    i#0 := LitInt(1);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(133,14)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(134,5)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    preLoop$loop#0$defass#d#0 := defass#d#0;
    $decr_init$loop#00 := n#0 - i#0;
    havoc $w$loop#0;
    while (true)
      free invariant $w$loop#0 ==> _module.Node.Valid#canCall($Heap, d#0);
      invariant $w$loop#0
         ==> 
        _module.Node.Valid#canCall($Heap, d#0)
         ==> _module.Node.Valid($LS($LZ), $Heap, d#0)
           || read($Heap, d#0, _module.Node.Repr)[$Box(d#0)];
      invariant $w$loop#0
         ==> 
        _module.Node.Valid#canCall($Heap, d#0)
         ==> _module.Node.Valid($LS($LZ), $Heap, d#0)
           || (read($Heap, d#0, _module.Node.next) != null
             ==> read($Heap, d#0, _module.Node.Repr)[$Box(read($Heap, d#0, _module.Node.next))]);
      invariant $w$loop#0
         ==> 
        _module.Node.Valid#canCall($Heap, d#0)
         ==> _module.Node.Valid($LS($LZ), $Heap, d#0)
           || (read($Heap, d#0, _module.Node.next) != null
             ==> Set#Subset(read($Heap, read($Heap, d#0, _module.Node.next), _module.Node.Repr), 
              read($Heap, d#0, _module.Node.Repr)));
      invariant $w$loop#0
         ==> 
        _module.Node.Valid#canCall($Heap, d#0)
         ==> _module.Node.Valid($LS($LZ), $Heap, d#0)
           || (read($Heap, d#0, _module.Node.next) != null
             ==> !read($Heap, read($Heap, d#0, _module.Node.next), _module.Node.Repr)[$Box(d#0)]);
      invariant $w$loop#0
         ==> 
        _module.Node.Valid#canCall($Heap, d#0)
         ==> _module.Node.Valid($LS($LZ), $Heap, d#0)
           || (read($Heap, d#0, _module.Node.next) != null
             ==> _module.Node.Valid($LS($LS($LZ)), $Heap, read($Heap, d#0, _module.Node.next)));
      free invariant $w$loop#0
         ==> _module.Node.Valid#canCall($Heap, d#0)
           && 
          _module.Node.Valid($LS($LZ), $Heap, d#0)
           && 
          read($Heap, d#0, _module.Node.Repr)[$Box(d#0)]
           && (read($Heap, d#0, _module.Node.next) != null
             ==> read($Heap, d#0, _module.Node.Repr)[$Box(read($Heap, d#0, _module.Node.next))]
               && Set#Subset(read($Heap, read($Heap, d#0, _module.Node.next), _module.Node.Repr), 
                read($Heap, d#0, _module.Node.Repr))
               && !read($Heap, read($Heap, d#0, _module.Node.next), _module.Node.Repr)[$Box(d#0)]
               && _module.Node.Valid($LS($LZ), $Heap, read($Heap, d#0, _module.Node.next)));
      invariant $w$loop#0
         ==> (forall $o: ref :: 
          { read($Heap, d#0, _module.Node.Repr)[$Box($o)] } 
          read($Heap, d#0, _module.Node.Repr)[$Box($o)]
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
      free invariant preLoop$loop#0$defass#d#0 ==> defass#d#0;
      free invariant n#0 - i#0 <= $decr_init$loop#00 && (n#0 - i#0 == $decr_init$loop#00 ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(134,4): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assert defass#d#0;
            assert {:subsumption 0} d#0 != null;
            assume _module.Node.Valid#canCall($Heap, d#0);
            if (_module.Node.Valid($LS($LZ), $Heap, d#0))
            {
                assert defass#d#0;
                assert {:subsumption 0} d#0 != null;
            }

            assume _module.Node.Valid#canCall($Heap, d#0);
            assume _module.Node.Valid($LS($LZ), $Heap, d#0)
               && (forall $o: ref :: 
                { read($Heap, d#0, _module.Node.Repr)[$Box($o)] } 
                read($Heap, d#0, _module.Node.Repr)[$Box($o)]
                   ==> $o != null && !read(old($Heap), $o, alloc));
            assume true;
            assume false;
        }

        assume true;
        if (n#0 <= i#0)
        {
            break;
        }

        $decr$loop#00 := n#0 - i#0;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(137,9)
        assume true;
        // ----- init call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(137,12)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        val##0_0 := i#0;
        assert defass#d#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        next##0_0 := d#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call $nw := Call$$_module.Node.__ctor(val##0_0, next##0_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(137,25)"} true;
        d#0 := $nw;
        defass#d#0 := true;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(137,25)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(138,9)
        assume true;
        assume true;
        i#0 := i#0 + 1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(138,16)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(134,5)
        assert 0 <= $decr$loop#00 || n#0 - i#0 == $decr$loop#00;
        assert n#0 - i#0 < $decr$loop#00;
        assume _module.Node.Valid#canCall($Heap, d#0);
    }

    assert defass#d#0;
}



procedure CheckWellformed$$_module.Node.Print(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), $Heap));
  free requires 11 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Node.Print(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), $Heap));
  // user-defined preconditions
  requires _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || read($Heap, this, _module.Node.Repr)[$Box(this)];
  requires _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.next) != null
         ==> read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.next))]);
  requires _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.next) != null
         ==> Set#Subset(read($Heap, read($Heap, this, _module.Node.next), _module.Node.Repr), 
          read($Heap, this, _module.Node.Repr)));
  requires _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.next) != null
         ==> !read($Heap, read($Heap, this, _module.Node.next), _module.Node.Repr)[$Box(this)]);
  requires _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.next) != null
         ==> _module.Node.Valid($LS($LS($LZ)), $Heap, read($Heap, this, _module.Node.next)));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Node.Print(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 11 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.Node.Valid#canCall($Heap, this)
     && 
    _module.Node.Valid($LS($LZ), $Heap, this)
     && 
    read($Heap, this, _module.Node.Repr)[$Box(this)]
     && (read($Heap, this, _module.Node.next) != null
       ==> read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.next))]
         && Set#Subset(read($Heap, read($Heap, this, _module.Node.next), _module.Node.Repr), 
          read($Heap, this, _module.Node.Repr))
         && !read($Heap, read($Heap, this, _module.Node.next), _module.Node.Repr)[$Box(this)]
         && _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.next)));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Node.Print(this: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var d#0: ref
     where $Is(d#0, Tclass._module.Node?()) && $IsAlloc(d#0, Tclass._module.Node?(), $Heap);
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: Set Box;
  var $w$loop#0: bool;
  var $decr$loop#00: Set Box;

    // AddMethodImpl: Print, Impl$$_module.Node.Print
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(144,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(145,11)
    assume true;
    assume true;
    d#0 := this;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(145,17)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(146,5)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := (if d#0 == null
       then Set#Empty(): Set Box
       else read($Heap, d#0, _module.Node.Repr));
    havoc $w$loop#0;
    while (true)
      free invariant $w$loop#0 ==> d#0 != null ==> _module.Node.Valid#canCall($Heap, d#0);
      invariant $w$loop#0
         ==> 
        d#0 != null
         ==> 
        _module.Node.Valid#canCall($Heap, d#0)
         ==> _module.Node.Valid($LS($LZ), $Heap, d#0)
           || read($Heap, d#0, _module.Node.Repr)[$Box(d#0)];
      invariant $w$loop#0
         ==> 
        d#0 != null
         ==> 
        _module.Node.Valid#canCall($Heap, d#0)
         ==> _module.Node.Valid($LS($LZ), $Heap, d#0)
           || (read($Heap, d#0, _module.Node.next) != null
             ==> read($Heap, d#0, _module.Node.Repr)[$Box(read($Heap, d#0, _module.Node.next))]);
      invariant $w$loop#0
         ==> 
        d#0 != null
         ==> 
        _module.Node.Valid#canCall($Heap, d#0)
         ==> _module.Node.Valid($LS($LZ), $Heap, d#0)
           || (read($Heap, d#0, _module.Node.next) != null
             ==> Set#Subset(read($Heap, read($Heap, d#0, _module.Node.next), _module.Node.Repr), 
              read($Heap, d#0, _module.Node.Repr)));
      invariant $w$loop#0
         ==> 
        d#0 != null
         ==> 
        _module.Node.Valid#canCall($Heap, d#0)
         ==> _module.Node.Valid($LS($LZ), $Heap, d#0)
           || (read($Heap, d#0, _module.Node.next) != null
             ==> !read($Heap, read($Heap, d#0, _module.Node.next), _module.Node.Repr)[$Box(d#0)]);
      invariant $w$loop#0
         ==> 
        d#0 != null
         ==> 
        _module.Node.Valid#canCall($Heap, d#0)
         ==> _module.Node.Valid($LS($LZ), $Heap, d#0)
           || (read($Heap, d#0, _module.Node.next) != null
             ==> _module.Node.Valid($LS($LS($LZ)), $Heap, read($Heap, d#0, _module.Node.next)));
      free invariant $w$loop#0
         ==> 
        d#0 != null
         ==> _module.Node.Valid#canCall($Heap, d#0)
           && 
          _module.Node.Valid($LS($LZ), $Heap, d#0)
           && 
          read($Heap, d#0, _module.Node.Repr)[$Box(d#0)]
           && (read($Heap, d#0, _module.Node.next) != null
             ==> read($Heap, d#0, _module.Node.Repr)[$Box(read($Heap, d#0, _module.Node.next))]
               && Set#Subset(read($Heap, read($Heap, d#0, _module.Node.next), _module.Node.Repr), 
                read($Heap, d#0, _module.Node.Repr))
               && !read($Heap, read($Heap, d#0, _module.Node.next), _module.Node.Repr)[$Box(d#0)]
               && _module.Node.Valid($LS($LZ), $Heap, read($Heap, d#0, _module.Node.next)));
      free invariant (forall $o: ref :: 
        { $Heap[$o] } 
        $o != null && read(old($Heap), $o, alloc)
           ==> $Heap[$o] == $PreLoopHeap$loop#0[$o]);
      free invariant $HeapSucc($PreLoopHeap$loop#0, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
        { read($Heap, $o, $f) } 
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
      free invariant Set#Subset((if d#0 == null
             then Set#Empty(): Set Box
             else read($Heap, d#0, _module.Node.Repr)), 
          $decr_init$loop#00)
         && (Set#Equal((if d#0 == null
               then Set#Empty(): Set Box
               else read($Heap, d#0, _module.Node.Repr)), 
            $decr_init$loop#00)
           ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(146,4): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            if (d#0 != null)
            {
                assert {:subsumption 0} d#0 != null;
                assume _module.Node.Valid#canCall($Heap, d#0);
            }

            assume d#0 != null ==> _module.Node.Valid#canCall($Heap, d#0);
            assume d#0 != null ==> _module.Node.Valid($LS($LZ), $Heap, d#0);
            if (d#0 == null)
            {
            }
            else
            {
                assert d#0 != null;
            }

            assume true;
            assume false;
        }

        assume true;
        if (d#0 == null)
        {
            break;
        }

        $decr$loop#00 := (if d#0 == null
           then Set#Empty(): Set Box
           else read($Heap, d#0, _module.Node.Repr));
        // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(150,7)
        assert {:subsumption 0} d#0 != null;
        assume true;
        assume true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(151,9)
        assume true;
        assert d#0 != null;
        assume true;
        d#0 := read($Heap, d#0, _module.Node.next);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(151,17)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(146,5)
        assert Set#Subset((if d#0 == null
               then Set#Empty(): Set Box
               else read($Heap, d#0, _module.Node.Repr)), 
            $decr$loop#00)
           && !Set#Subset($decr$loop#00, 
            (if d#0 == null
               then Set#Empty(): Set Box
               else read($Heap, d#0, _module.Node.Repr)));
        assume d#0 != null ==> _module.Node.Valid#canCall($Heap, d#0);
    }

    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(153,5)
    assume true;
}



// function declaration for _module.Node.StartsWith
function _module.Node.StartsWith($ly: LayerType, $heap: Heap, this: ref, that#0: ref) : bool;

function _module.Node.StartsWith#canCall($heap: Heap, this: ref, that#0: ref) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, $Heap: Heap, this: ref, that#0: ref :: 
  { _module.Node.StartsWith($LS($ly), $Heap, this, that#0) } 
  _module.Node.StartsWith($LS($ly), $Heap, this, that#0)
     == _module.Node.StartsWith($ly, $Heap, this, that#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, $Heap: Heap, this: ref, that#0: ref :: 
  { _module.Node.StartsWith(AsFuelBottom($ly), $Heap, this, that#0) } 
  _module.Node.StartsWith($ly, $Heap, this, that#0)
     == _module.Node.StartsWith($LZ, $Heap, this, that#0));

// frame axiom for _module.Node.StartsWith
axiom (forall $ly: LayerType, $h0: Heap, $h1: Heap, this: ref, that#0: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.Node.StartsWith($ly, $h1, this, that#0) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.Node())
       && (_module.Node.StartsWith#canCall($h0, this, that#0)
         || $Is(that#0, Tclass._module.Node?()))
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && (read($h0, this, _module.Node.Repr)[$Box($o)]
             || (if that#0 == null
               then Set#Empty(): Set Box
               else read($h0, that#0, _module.Node.Repr))[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.Node.StartsWith($ly, $h0, this, that#0)
       == _module.Node.StartsWith($ly, $h1, this, that#0));

// consequence axiom for _module.Node.StartsWith
axiom 12 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, this: ref, that#0: ref :: 
    { _module.Node.StartsWith($ly, $Heap, this, that#0) } 
    _module.Node.StartsWith#canCall($Heap, this, that#0)
         || (12 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.Node())
           && $IsAlloc(this, Tclass._module.Node(), $Heap)
           && $Is(that#0, Tclass._module.Node?())
           && 
          _module.Node.Valid($LS($LZ), $Heap, this)
           && (that#0 != null ==> _module.Node.Valid($LS($LZ), $Heap, that#0)))
       ==> true);

function _module.Node.StartsWith#requires(LayerType, Heap, ref, ref) : bool;

// #requires axiom for _module.Node.StartsWith
axiom (forall $ly: LayerType, $Heap: Heap, this: ref, that#0: ref :: 
  { _module.Node.StartsWith#requires($ly, $Heap, this, that#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.Node())
       && $IsAlloc(this, Tclass._module.Node(), $Heap)
       && $Is(that#0, Tclass._module.Node?())
     ==> _module.Node.StartsWith#requires($ly, $Heap, this, that#0)
       == (_module.Node.Valid($LS($LZ), $Heap, this)
         && (that#0 != null ==> _module.Node.Valid($LS($LZ), $Heap, that#0))));

// definition axiom for _module.Node.StartsWith (revealed)
axiom 12 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, this: ref, that#0: ref :: 
    { _module.Node.StartsWith($LS($ly), $Heap, this, that#0), $IsGoodHeap($Heap) } 
    _module.Node.StartsWith#canCall($Heap, this, that#0)
         || (12 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.Node())
           && $IsAlloc(this, Tclass._module.Node(), $Heap)
           && $Is(that#0, Tclass._module.Node?())
           && 
          _module.Node.Valid($LS($LZ), $Heap, this)
           && (that#0 != null ==> _module.Node.Valid($LS($LZ), $Heap, that#0)))
       ==> (that#0 != null
           ==> 
          read($Heap, this, _module.Node.val) == read($Heap, that#0, _module.Node.val)
           ==> 
          read($Heap, this, _module.Node.next) != null
           ==> _module.Node.StartsWith#canCall($Heap, 
            read($Heap, this, _module.Node.next), 
            read($Heap, that#0, _module.Node.next)))
         && _module.Node.StartsWith($LS($ly), $Heap, this, that#0)
           == (that#0 != null
             ==> read($Heap, this, _module.Node.val) == read($Heap, that#0, _module.Node.val)
               && read($Heap, this, _module.Node.next) != null
               && _module.Node.StartsWith($ly, 
                $Heap, 
                read($Heap, this, _module.Node.next), 
                read($Heap, that#0, _module.Node.next))));

procedure CheckWellformed$$_module.Node.StartsWith(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), $Heap), 
    that#0: ref where $Is(that#0, Tclass._module.Node?()));
  free requires 12 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Node.StartsWith(this: ref, that#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;
  var b$reqreads#2: bool;
  var b$reqreads#3: bool;
  var ##that#0: ref;
  var b$reqreads#4: bool;
  var b$reqreads#5: bool;
  var b$reqreads#6: bool;
  var b$reqreads#7: bool;
  var b$reqreads#8: bool;
  var b$reqreads#9: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;
    b$reqreads#3 := true;
    b$reqreads#4 := true;
    b$reqreads#5 := true;
    b$reqreads#6 := true;
    b$reqreads#7 := true;
    b$reqreads#8 := true;
    b$reqreads#9 := true;

    // AddWellformednessCheck for function StartsWith
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(156,19): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.Node.Repr)[$Box($o)]
           || (if that#0 == null
             then Set#Empty(): Set Box
             else read($Heap, that#0, _module.Node.Repr))[$Box($o)]);
    b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && read($Heap, $o, alloc)
           && ($o == this || read($Heap, this, _module.Node.Repr)[$Box($o)])
         ==> $_Frame[$o, $f]);
    assume _module.Node.Valid#canCall($Heap, this);
    assume _module.Node.Valid($LS($LZ), $Heap, this);
    if (that#0 != null)
    {
        assert that#0 != null;
        b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null
               && read($Heap, $o, alloc)
               && ($o == that#0 || read($Heap, that#0, _module.Node.Repr)[$Box($o)])
             ==> $_Frame[$o, $f]);
        assume _module.Node.Valid#canCall($Heap, that#0);
    }

    assume that#0 != null ==> _module.Node.Valid($LS($LZ), $Heap, that#0);
    assert b$reqreads#0;
    assert b$reqreads#1;
    b$reqreads#2 := $_Frame[this, _module.Node.Repr];
    if (that#0 == null)
    {
    }
    else
    {
        assert that#0 != null;
        b$reqreads#3 := $_Frame[that#0, _module.Node.Repr];
    }

    assert b$reqreads#2;
    assert b$reqreads#3;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc)
             ==> read($Heap, this, _module.Node.Repr)[$Box($o)]
               || (if that#0 == null
                 then Set#Empty(): Set Box
                 else read($Heap, that#0, _module.Node.Repr))[$Box($o)]);
        if (that#0 != null)
        {
            b$reqreads#4 := $_Frame[this, _module.Node.val];
            assert that#0 != null;
            b$reqreads#5 := $_Frame[that#0, _module.Node.val];
            if (read($Heap, this, _module.Node.val) == read($Heap, that#0, _module.Node.val))
            {
                b$reqreads#6 := $_Frame[this, _module.Node.next];
            }

            if (read($Heap, this, _module.Node.val) == read($Heap, that#0, _module.Node.val)
               && read($Heap, this, _module.Node.next) != null)
            {
                b$reqreads#7 := $_Frame[this, _module.Node.next];
                assert read($Heap, this, _module.Node.next) != null;
                assert that#0 != null;
                b$reqreads#8 := $_Frame[that#0, _module.Node.next];
                ##that#0 := read($Heap, that#0, _module.Node.next);
                // assume allocatedness for argument to function
                assume $IsAlloc(##that#0, Tclass._module.Node?(), $Heap);
                assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.Node.next))
                   ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.next))
                     || read($Heap, read($Heap, this, _module.Node.next), _module.Node.Repr)[$Box(read($Heap, this, _module.Node.next))];
                assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.Node.next))
                   ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.next))
                     || (read($Heap, read($Heap, this, _module.Node.next), _module.Node.next) != null
                       ==> read($Heap, read($Heap, this, _module.Node.next), _module.Node.Repr)[$Box(read($Heap, read($Heap, this, _module.Node.next), _module.Node.next))]);
                assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.Node.next))
                   ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.next))
                     || (read($Heap, read($Heap, this, _module.Node.next), _module.Node.next) != null
                       ==> Set#Subset(read($Heap, 
                          read($Heap, read($Heap, this, _module.Node.next), _module.Node.next), 
                          _module.Node.Repr), 
                        read($Heap, read($Heap, this, _module.Node.next), _module.Node.Repr)));
                assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.Node.next))
                   ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.next))
                     || (read($Heap, read($Heap, this, _module.Node.next), _module.Node.next) != null
                       ==> !read($Heap, 
                        read($Heap, read($Heap, this, _module.Node.next), _module.Node.next), 
                        _module.Node.Repr)[$Box(read($Heap, this, _module.Node.next))]);
                assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.Node.next))
                   ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.next))
                     || (read($Heap, read($Heap, this, _module.Node.next), _module.Node.next) != null
                       ==> _module.Node.Valid($LS($LS($LZ)), 
                        $Heap, 
                        read($Heap, read($Heap, this, _module.Node.next), _module.Node.next)));
                assert {:subsumption 0} ##that#0 != null
                   ==> 
                  _module.Node.Valid#canCall($Heap, ##that#0)
                   ==> _module.Node.Valid($LS($LZ), $Heap, ##that#0)
                     || read($Heap, ##that#0, _module.Node.Repr)[$Box(##that#0)];
                assert {:subsumption 0} ##that#0 != null
                   ==> 
                  _module.Node.Valid#canCall($Heap, ##that#0)
                   ==> _module.Node.Valid($LS($LZ), $Heap, ##that#0)
                     || (read($Heap, ##that#0, _module.Node.next) != null
                       ==> read($Heap, ##that#0, _module.Node.Repr)[$Box(read($Heap, ##that#0, _module.Node.next))]);
                assert {:subsumption 0} ##that#0 != null
                   ==> 
                  _module.Node.Valid#canCall($Heap, ##that#0)
                   ==> _module.Node.Valid($LS($LZ), $Heap, ##that#0)
                     || (read($Heap, ##that#0, _module.Node.next) != null
                       ==> Set#Subset(read($Heap, read($Heap, ##that#0, _module.Node.next), _module.Node.Repr), 
                        read($Heap, ##that#0, _module.Node.Repr)));
                assert {:subsumption 0} ##that#0 != null
                   ==> 
                  _module.Node.Valid#canCall($Heap, ##that#0)
                   ==> _module.Node.Valid($LS($LZ), $Heap, ##that#0)
                     || (read($Heap, ##that#0, _module.Node.next) != null
                       ==> !read($Heap, read($Heap, ##that#0, _module.Node.next), _module.Node.Repr)[$Box(##that#0)]);
                assert {:subsumption 0} ##that#0 != null
                   ==> 
                  _module.Node.Valid#canCall($Heap, ##that#0)
                   ==> _module.Node.Valid($LS($LZ), $Heap, ##that#0)
                     || (read($Heap, ##that#0, _module.Node.next) != null
                       ==> _module.Node.Valid($LS($LS($LZ)), $Heap, read($Heap, ##that#0, _module.Node.next)));
                assume _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.next))
                   && (##that#0 != null ==> _module.Node.Valid($LS($LZ), $Heap, ##that#0));
                b$reqreads#9 := (forall<alpha> $o: ref, $f: Field alpha :: 
                  $o != null
                       && read($Heap, $o, alloc)
                       && (read($Heap, read($Heap, this, _module.Node.next), _module.Node.Repr)[$Box($o)]
                         || (if ##that#0 == null
                           then Set#Empty(): Set Box
                           else read($Heap, ##that#0, _module.Node.Repr))[$Box($o)])
                     ==> $_Frame[$o, $f]);
                assert Set#Subset(read($Heap, read($Heap, this, _module.Node.next), _module.Node.Repr), 
                    read($Heap, this, _module.Node.Repr))
                   && !Set#Subset(read($Heap, this, _module.Node.Repr), 
                    read($Heap, read($Heap, this, _module.Node.next), _module.Node.Repr));
                assume _module.Node.StartsWith#canCall($Heap, 
                  read($Heap, this, _module.Node.next), 
                  read($Heap, that#0, _module.Node.next));
            }
        }

        assume _module.Node.StartsWith($LS($LZ), $Heap, this, that#0)
           == (that#0 != null
             ==> read($Heap, this, _module.Node.val) == read($Heap, that#0, _module.Node.val)
               && read($Heap, this, _module.Node.next) != null
               && _module.Node.StartsWith($LS($LZ), 
                $Heap, 
                read($Heap, this, _module.Node.next), 
                read($Heap, that#0, _module.Node.next)));
        assume that#0 != null
           ==> 
          read($Heap, this, _module.Node.val) == read($Heap, that#0, _module.Node.val)
           ==> 
          read($Heap, this, _module.Node.next) != null
           ==> _module.Node.StartsWith#canCall($Heap, 
            read($Heap, this, _module.Node.next), 
            read($Heap, that#0, _module.Node.next));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.Node.StartsWith($LS($LZ), $Heap, this, that#0), TBool);
        assert b$reqreads#4;
        assert b$reqreads#5;
        assert b$reqreads#6;
        assert b$reqreads#7;
        assert b$reqreads#8;
        assert b$reqreads#9;
    }
}



procedure CheckWellformed$$_module.Node.IncEverything(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), $Heap), 
    n#0: int);
  free requires 14 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Node.IncEverything(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), $Heap), 
    n#0: int);
  // user-defined preconditions
  requires _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || read($Heap, this, _module.Node.Repr)[$Box(this)];
  requires _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.next) != null
         ==> read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.next))]);
  requires _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.next) != null
         ==> Set#Subset(read($Heap, read($Heap, this, _module.Node.next), _module.Node.Repr), 
          read($Heap, this, _module.Node.Repr)));
  requires _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.next) != null
         ==> !read($Heap, read($Heap, this, _module.Node.next), _module.Node.Repr)[$Box(this)]);
  requires _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.next) != null
         ==> _module.Node.Valid($LS($LS($LZ)), $Heap, read($Heap, this, _module.Node.next)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Node.Valid#canCall($Heap, this);
  free ensures _module.Node.Valid#canCall($Heap, this)
     && 
    _module.Node.Valid($LS($LZ), $Heap, this)
     && 
    read($Heap, this, _module.Node.Repr)[$Box(this)]
     && (read($Heap, this, _module.Node.next) != null
       ==> read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.next))]
         && Set#Subset(read($Heap, read($Heap, this, _module.Node.next), _module.Node.Repr), 
          read($Heap, this, _module.Node.Repr))
         && !read($Heap, read($Heap, this, _module.Node.next), _module.Node.Repr)[$Box(this)]
         && _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.next)));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || read(old($Heap), this, _module.Node.Repr)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Node.IncEverything(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), $Heap), 
    n#0: int)
   returns ($_reverifyPost: bool);
  free requires 14 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.Node.Valid#canCall($Heap, this)
     && 
    _module.Node.Valid($LS($LZ), $Heap, this)
     && 
    read($Heap, this, _module.Node.Repr)[$Box(this)]
     && (read($Heap, this, _module.Node.next) != null
       ==> read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.next))]
         && Set#Subset(read($Heap, read($Heap, this, _module.Node.next), _module.Node.Repr), 
          read($Heap, this, _module.Node.Repr))
         && !read($Heap, read($Heap, this, _module.Node.next), _module.Node.Repr)[$Box(this)]
         && _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.next)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Node.Valid#canCall($Heap, this);
  ensures _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || read($Heap, this, _module.Node.Repr)[$Box(this)];
  ensures _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.next) != null
         ==> read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.next))]);
  ensures _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.next) != null
         ==> Set#Subset(read($Heap, read($Heap, this, _module.Node.next), _module.Node.Repr), 
          read($Heap, this, _module.Node.Repr)));
  ensures _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.next) != null
         ==> !read($Heap, read($Heap, this, _module.Node.next), _module.Node.Repr)[$Box(this)]);
  ensures _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.next) != null
         ==> _module.Node.Valid($LS($LS($LZ)), $Heap, read($Heap, this, _module.Node.next)));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || read(old($Heap), this, _module.Node.Repr)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Node.IncEverything(this: ref, n#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var d#0: ref;
  var d#1: ref;
  var $prevHeap: Heap;

    // AddMethodImpl: IncEverything, Impl$$_module.Node.IncEverything
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.Node.Repr)[$Box($o)]);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(169,2): initial state"} true;
    $_reverifyPost := false;
    // ----- forall statement (assign) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(170,5)
    if (*)
    {
        // Assume Fuel Constant
        havoc d#0;
        assume $Is(d#0, Tclass._module.Node());
        assume true;
        assume read($Heap, this, _module.Node.Repr)[$Box(d#0)];
        assert {:subsumption 0} d#0 != null;
        assume true;
        assert $_Frame[d#0, _module.Node.val];
        assert {:subsumption 0} d#0 != null;
        assume true;
        havoc d#1;
        assume $Is(d#1, Tclass._module.Node());
        assume read($Heap, this, _module.Node.Repr)[$Box(d#1)];
        assume d#0 != d#1;
        assert d#0 != d#1
           || _module.Node.val != _module.Node.val
           || read($Heap, d#0, _module.Node.val) + n#0
             == read($Heap, d#1, _module.Node.val) + n#0;
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
             || (exists d#2: ref :: 
              $Is(d#2, Tclass._module.Node())
                 && read($prevHeap, this, _module.Node.Repr)[$Box(d#2)]
                 && $o == d#2
                 && $f == _module.Node.val));
        assume (forall d#inv#0: ref :: 
          { read($Heap, d#inv#0, _module.Node.val) } 
          $Is(d#inv#0, Tclass._module.Node())
               && 
              d#inv#0 != null
               && read($prevHeap, this, _module.Node.Repr)[$Box(d#inv#0)]
             ==> read($Heap, d#inv#0, _module.Node.val)
               == read($prevHeap, d#inv#0, _module.Node.val) + n#0);
    }

    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(172,4)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(173,30)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert $IsAlloc(this, Tclass._module.Node(), old($Heap));
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.Node.StillValidAfterValChanges(old($Heap), $Heap, this);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(173,31)"} true;
}



procedure {:_induction this} CheckWellformed$$_module.Node.StillValidAfterValChanges(previous$Heap: Heap, 
    current$Heap: Heap, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), previous$Heap));
  free requires 13 == $FunctionContextHeight;
  free requires previous$Heap == $Heap
     && 
    $HeapSucc(previous$Heap, current$Heap)
     && $IsGoodHeap(current$Heap);
  modifies $Heap, $Tick;



implementation {:_induction this} CheckWellformed$$_module.Node.StillValidAfterValChanges(previous$Heap: Heap, current$Heap: Heap, this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var d#0: ref;

    // AddMethodImpl: StillValidAfterValChanges, CheckWellformed$$_module.Node.StillValidAfterValChanges
    $Heap := current$Heap;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(176,17): initial state"} true;
    assert $IsAlloc(this, Tclass._module.Node(), old($Heap));
    assume _module.Node.Valid#canCall(old($Heap), this);
    assume _module.Node.Valid($LS($LZ), old($Heap), this);
    havoc d#0;
    assume $Is(d#0, Tclass._module.Node());
    if (*)
    {
        assert $IsAlloc(this, Tclass._module.Node(), old($Heap));
        assume read(old($Heap), this, _module.Node.Repr)[$Box(d#0)];
        assume (forall<alpha> $o: ref, $f: Field alpha :: 
          { read($Heap, $o, $f) } 
          $o != null
             ==> 
            ($o == d#0 && ($f == _module.Node.next || $f == alloc))
               || ($o == d#0 && ($f == _module.Node.Repr || $f == alloc))
             ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
    }
    else
    {
        assume read(old($Heap), this, _module.Node.Repr)[$Box(d#0)]
           ==> (forall<alpha> $o: ref, $f: Field alpha :: 
            { read($Heap, $o, $f) } 
            $o != null
               ==> 
              ($o == d#0 && ($f == _module.Node.next || $f == alloc))
                 || ($o == d#0 && ($f == _module.Node.Repr || $f == alloc))
               ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
    }

    assume (forall d#1: ref :: 
      { read(old($Heap), this, _module.Node.Repr)[$Box(d#1)] } 
      $Is(d#1, Tclass._module.Node())
         ==> 
        read(old($Heap), this, _module.Node.Repr)[$Box(d#1)]
         ==> (forall<alpha> $o: ref, $f: Field alpha :: 
          { read($Heap, $o, $f) } 
          $o != null
             ==> 
            ($o == d#1 && ($f == _module.Node.next || $f == alloc))
               || ($o == d#1 && ($f == _module.Node.Repr || $f == alloc))
             ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)));
    assert $IsAlloc(this, Tclass._module.Node(), old($Heap));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(179,17): post-state"} true;
    assume _module.Node.Valid#canCall($Heap, this);
    assume _module.Node.Valid($LS($LZ), $Heap, this);
}



procedure {:_induction this} Call$$_module.Node.StillValidAfterValChanges(previous$Heap: Heap, 
    current$Heap: Heap, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), previous$Heap));
  // user-defined preconditions
  requires _module.Node.Valid#canCall(previous$Heap, this)
     ==> _module.Node.Valid($LS($LZ), previous$Heap, this)
       || read(previous$Heap, this, _module.Node.Repr)[$Box(this)];
  requires _module.Node.Valid#canCall(previous$Heap, this)
     ==> _module.Node.Valid($LS($LZ), previous$Heap, this)
       || (read(previous$Heap, this, _module.Node.next) != null
         ==> read(previous$Heap, this, _module.Node.Repr)[$Box(read(previous$Heap, this, _module.Node.next))]);
  requires _module.Node.Valid#canCall(previous$Heap, this)
     ==> _module.Node.Valid($LS($LZ), previous$Heap, this)
       || (read(previous$Heap, this, _module.Node.next) != null
         ==> Set#Subset(read(previous$Heap, read(previous$Heap, this, _module.Node.next), _module.Node.Repr), 
          read(previous$Heap, this, _module.Node.Repr)));
  requires _module.Node.Valid#canCall(previous$Heap, this)
     ==> _module.Node.Valid($LS($LZ), previous$Heap, this)
       || (read(previous$Heap, this, _module.Node.next) != null
         ==> !read(previous$Heap, read(previous$Heap, this, _module.Node.next), _module.Node.Repr)[$Box(this)]);
  requires _module.Node.Valid#canCall(previous$Heap, this)
     ==> _module.Node.Valid($LS($LZ), previous$Heap, this)
       || (read(previous$Heap, this, _module.Node.next) != null
         ==> _module.Node.Valid($LS($LS($LZ)), previous$Heap, read(previous$Heap, this, _module.Node.next)));
  requires (forall d#1: ref :: 
    { read(previous$Heap, this, _module.Node.Repr)[$Box(d#1)] } 
    $Is(d#1, Tclass._module.Node())
       ==> 
      read(previous$Heap, this, _module.Node.Repr)[$Box(d#1)]
       ==> (forall<alpha> $o: ref, $f: Field alpha :: 
        { read(current$Heap, $o, $f) } 
        $o != null
           ==> 
          ($o == d#1 && ($f == _module.Node.next || $f == alloc))
             || ($o == d#1 && ($f == _module.Node.Repr || $f == alloc))
           ==> read(current$Heap, $o, $f) == read(previous$Heap, $o, $f)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Node.Valid#canCall(current$Heap, this);
  free ensures _module.Node.Valid#canCall(current$Heap, this)
     && 
    _module.Node.Valid($LS($LZ), current$Heap, this)
     && 
    read(current$Heap, this, _module.Node.Repr)[$Box(this)]
     && (read(current$Heap, this, _module.Node.next) != null
       ==> read(current$Heap, this, _module.Node.Repr)[$Box(read(current$Heap, this, _module.Node.next))]
         && Set#Subset(read(current$Heap, read(current$Heap, this, _module.Node.next), _module.Node.Repr), 
          read(current$Heap, this, _module.Node.Repr))
         && !read(current$Heap, read(current$Heap, this, _module.Node.next), _module.Node.Repr)[$Box(this)]
         && _module.Node.Valid($LS($LZ), current$Heap, read(current$Heap, this, _module.Node.next)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction this} Impl$$_module.Node.StillValidAfterValChanges(previous$Heap: Heap, 
    current$Heap: Heap, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), previous$Heap))
   returns ($_reverifyPost: bool);
  free requires 13 == $FunctionContextHeight;
  free requires previous$Heap == $Heap
     && 
    $HeapSucc(previous$Heap, current$Heap)
     && $IsGoodHeap(current$Heap);
  // user-defined preconditions
  free requires _module.Node.Valid#canCall(previous$Heap, this)
     && 
    _module.Node.Valid($LS($LZ), previous$Heap, this)
     && 
    read(previous$Heap, this, _module.Node.Repr)[$Box(this)]
     && (read(previous$Heap, this, _module.Node.next) != null
       ==> read(previous$Heap, this, _module.Node.Repr)[$Box(read(previous$Heap, this, _module.Node.next))]
         && Set#Subset(read(previous$Heap, read(previous$Heap, this, _module.Node.next), _module.Node.Repr), 
          read(previous$Heap, this, _module.Node.Repr))
         && !read(previous$Heap, read(previous$Heap, this, _module.Node.next), _module.Node.Repr)[$Box(this)]
         && _module.Node.Valid($LS($LZ), previous$Heap, read(previous$Heap, this, _module.Node.next)));
  requires (forall d#1: ref :: 
    { read(previous$Heap, this, _module.Node.Repr)[$Box(d#1)] } 
    $Is(d#1, Tclass._module.Node())
       ==> 
      read(previous$Heap, this, _module.Node.Repr)[$Box(d#1)]
       ==> (forall<alpha> $o: ref, $f: Field alpha :: 
        { read(current$Heap, $o, $f) } 
        $o != null
           ==> 
          ($o == d#1 && ($f == _module.Node.next || $f == alloc))
             || ($o == d#1 && ($f == _module.Node.Repr || $f == alloc))
           ==> read(current$Heap, $o, $f) == read(previous$Heap, $o, $f)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Node.Valid#canCall(current$Heap, this);
  ensures _module.Node.Valid#canCall(current$Heap, this)
     ==> _module.Node.Valid($LS($LZ), current$Heap, this)
       || read(current$Heap, this, _module.Node.Repr)[$Box(this)];
  ensures _module.Node.Valid#canCall(current$Heap, this)
     ==> _module.Node.Valid($LS($LZ), current$Heap, this)
       || (read(current$Heap, this, _module.Node.next) != null
         ==> read(current$Heap, this, _module.Node.Repr)[$Box(read(current$Heap, this, _module.Node.next))]);
  ensures _module.Node.Valid#canCall(current$Heap, this)
     ==> _module.Node.Valid($LS($LZ), current$Heap, this)
       || (read(current$Heap, this, _module.Node.next) != null
         ==> Set#Subset(read(current$Heap, read(current$Heap, this, _module.Node.next), _module.Node.Repr), 
          read(current$Heap, this, _module.Node.Repr)));
  ensures _module.Node.Valid#canCall(current$Heap, this)
     ==> _module.Node.Valid($LS($LZ), current$Heap, this)
       || (read(current$Heap, this, _module.Node.next) != null
         ==> !read(current$Heap, read(current$Heap, this, _module.Node.next), _module.Node.Repr)[$Box(this)]);
  ensures _module.Node.Valid#canCall(current$Heap, this)
     ==> _module.Node.Valid($LS($LZ), current$Heap, this)
       || (read(current$Heap, this, _module.Node.next) != null
         ==> _module.Node.Valid($LS($LS($LZ)), current$Heap, read(current$Heap, this, _module.Node.next)));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction this} Impl$$_module.Node.StillValidAfterValChanges(previous$Heap: Heap, current$Heap: Heap, this: ref)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;

    // AddMethodImpl: StillValidAfterValChanges, Impl$$_module.Node.StillValidAfterValChanges
    $Heap := current$Heap;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(181,2): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#this0#0: ref :: 
      $Is($ih#this0#0, Tclass._module.Node())
           && 
          _module.Node.Valid($LS($LZ), old($Heap), $ih#this0#0)
           && (forall d#2: ref :: 
            { read(old($Heap), $ih#this0#0, _module.Node.Repr)[$Box(d#2)] } 
            $Is(d#2, Tclass._module.Node())
               ==> 
              read(old($Heap), $ih#this0#0, _module.Node.Repr)[$Box(d#2)]
               ==> (forall<alpha> $o: ref, $f: Field alpha :: 
                { read($initHeapForallStmt#0, $o, $f) } 
                $o != null
                   ==> 
                  ($o == d#2 && ($f == _module.Node.next || $f == alloc))
                     || ($o == d#2 && ($f == _module.Node.Repr || $f == alloc))
                   ==> read($initHeapForallStmt#0, $o, $f) == read(old($Heap), $o, $f)))
           && 
          Set#Subset(read(old($Heap), $ih#this0#0, _module.Node.Repr), 
            read(old($Heap), this, _module.Node.Repr))
           && !Set#Subset(read(old($Heap), this, _module.Node.Repr), 
            read(old($Heap), $ih#this0#0, _module.Node.Repr))
         ==> _module.Node.Valid($LS($LZ), $Heap, this));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(182,5)
    assume true;
    if (read($Heap, this, _module.Node.next) != null)
    {
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(183,37)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        assert read($Heap, this, _module.Node.next) != null;
        assert $IsAlloc(read($Heap, this, _module.Node.next), Tclass._module.Node?(), old($Heap));
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assert Set#Subset(read(old($Heap), read(old($Heap), this, _module.Node.next), _module.Node.Repr), 
            read(old($Heap), this, _module.Node.Repr))
           && !Set#Subset(read(old($Heap), this, _module.Node.Repr), 
            read(old($Heap), read(old($Heap), this, _module.Node.next), _module.Node.Repr));
        // ProcessCallStmt: Make the call
        call Call$$_module.Node.StillValidAfterValChanges(old($Heap), $Heap, read($Heap, this, _module.Node.next));
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(183,38)"} true;
    }
    else
    {
    }
}



// _module.Node: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.Node()) } 
  $Is(c#0, Tclass._module.Node())
     <==> $Is(c#0, Tclass._module.Node?()) && c#0 != null);

// _module.Node: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.Node(), $h) } 
  $IsAlloc(c#0, Tclass._module.Node(), $h)
     <==> $IsAlloc(c#0, Tclass._module.Node?(), $h));

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
  free requires 18 == $FunctionContextHeight;
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
  free requires 18 == $FunctionContextHeight;
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

    // AddMethodImpl: Main, Impl$$_module.__default._default_Main
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(4,14): initial state"} true;
    $_reverifyPost := false;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(5,27)
    // TrCallStmt: Before ProcessCallStmt
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.TestAggregateArrayUpdate();
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(5,28)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(6,32)
    // TrCallStmt: Before ProcessCallStmt
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.TestAggregateMultiArrayUpdate();
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(6,33)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(7,27)
    // TrCallStmt: Before ProcessCallStmt
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.TestAggregateFieldUpdate();
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(7,28)"} true;
}



procedure CheckWellformed$$_module.__default.TestAggregateArrayUpdate();
  free requires 15 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.TestAggregateArrayUpdate();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.TestAggregateArrayUpdate() returns ($_reverifyPost: bool);
  free requires 15 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.TestAggregateArrayUpdate() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var a#0: ref
     where $Is(a#0, Tclass._System.array(TReal))
       && $IsAlloc(a#0, Tclass._System.array(TReal), $Heap);
  var i#0: int;
  var $oldHeap#0: Heap;
  var $_Frame#l0: <beta>[ref,Field beta]bool;
  var lambdaResult#0: real;
  var $nw: ref;
  var b#0: ref
     where $Is(b#0, Tclass._System.array(TReal))
       && $IsAlloc(b#0, Tclass._System.array(TReal), $Heap);
  var c#0: ref
     where $Is(c#0, Tclass._System.array(TBool))
       && $IsAlloc(c#0, Tclass._System.array(TBool), $Heap);
  var i#1: int;
  var i#2: int;
  var $prevHeap: Heap;
  var i#4: int;
  var i#5: int;
  var a##0: ref;
  var a##1: ref;
  var a##2: ref;

    // AddMethodImpl: TestAggregateArrayUpdate, Impl$$_module.__default.TestAggregateArrayUpdate
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(12,34): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(13,9)
    assume true;
    assert 0 <= LitInt(8);
    // Begin Comprehension WF check
    if (*)
    {
        havoc i#0;
        if (LitInt(0) <= i#0)
        {
            $oldHeap#0 := $Heap;
            havoc $Heap;
            assume $IsGoodHeap($Heap);
            assume $oldHeap#0 == $Heap || $HeapSucc($oldHeap#0, $Heap);
            $_Frame#l0 := (lambda<alpha> $o: ref, $f: Field alpha :: 
              $o != null && read($Heap, $o, alloc) ==> false);
            assume lambdaResult#0 == Real(i#0) - 4e0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(lambdaResult#0, TReal);
        }

        assume false;
    }

    // End Comprehension WF check
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._System.array?(TReal);
    assume !read($Heap, $nw, alloc);
    assume _System.array.Length($nw) == LitInt(8);
    assert {:subsumption 0} (forall arrayinit#0#i0#0: int :: 
      0 <= arrayinit#0#i0#0 && arrayinit#0#i0#0 < LitInt(8)
         ==> Requires1(Tclass._System.nat(), 
          TReal, 
          $Heap, 
          Lit(AtLayer((lambda $l#0#ly#0: LayerType :: 
                Handle1((lambda $l#0#heap#0: Heap, $l#0#i#0: Box :: 
                    $Box(Real($Unbox($l#0#i#0): int) - 4e0)), 
                  (lambda $l#0#heap#0: Heap, $l#0#i#0: Box :: 
                    $IsBox($l#0#i#0, Tclass._System.nat())), 
                  (lambda $l#0#heap#0: Heap, $l#0#i#0: Box :: 
                    SetRef_to_SetBox((lambda $l#0#o#0: ref :: false))))), 
              $LS($LZ))), 
          $Box(arrayinit#0#i0#0)));
    assume (forall arrayinit#0#i0#0: int :: 
      { read($Heap, $nw, IndexField(arrayinit#0#i0#0)) } 
      0 <= arrayinit#0#i0#0 && arrayinit#0#i0#0 < LitInt(8)
         ==> $Unbox(read($Heap, $nw, IndexField(arrayinit#0#i0#0))): real
           == $Unbox(Apply1(Tclass._System.nat(), 
              TReal, 
              $Heap, 
              Lit(AtLayer((lambda $l#0#ly#0: LayerType :: 
                    Handle1((lambda $l#0#heap#0: Heap, $l#0#i#0: Box :: 
                        $Box(Real($Unbox($l#0#i#0): int) - 4e0)), 
                      (lambda $l#0#heap#0: Heap, $l#0#i#0: Box :: 
                        $IsBox($l#0#i#0, Tclass._System.nat())), 
                      (lambda $l#0#heap#0: Heap, $l#0#i#0: Box :: 
                        SetRef_to_SetBox((lambda $l#0#o#0: ref :: false))))), 
                  $LS($LZ))), 
              $Box(arrayinit#0#i0#0))): real);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    a#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(13,44)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(14,9)
    assume true;
    assert 0 <= LitInt(8);
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._System.array?(TReal);
    assume !read($Heap, $nw, alloc);
    assume _System.array.Length($nw) == LitInt(8);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    b#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(14,22)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(15,9)
    assume true;
    assert 0 <= LitInt(8);
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._System.array?(TBool);
    assume !read($Heap, $nw, alloc);
    assume _System.array.Length($nw) == LitInt(8);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    c#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(15,22)"} true;
    // ----- forall statement (assign) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(16,3)
    if (*)
    {
        // Assume Fuel Constant
        havoc i#1;
        assume true;
        if (2 - i#1 <= LitInt(2))
        {
            assert {:subsumption 0} a#0 != null;
        }

        assume true;
        assume 2 - i#1 <= LitInt(2) && i#1 < _System.array.Length(a#0);
        assert b#0 != null;
        assert {:subsumption 0} 0 <= 7 - i#1 && 7 - i#1 < _System.array.Length(b#0);
        assume true;
        assert $_Frame[b#0, IndexField(7 - i#1)];
        assert a#0 != null;
        assert {:subsumption 0} 0 <= i#1 && i#1 < _System.array.Length(a#0);
        assume true;
        havoc i#2;
        assume true;
        assume 2 - i#2 <= LitInt(2) && i#2 < _System.array.Length(a#0);
        assume i#1 != i#2;
        assert b#0 != b#0
           || IndexField(7 - i#1) != IndexField(7 - i#2)
           || $Unbox(read($Heap, a#0, IndexField(i#1))): real + 4e0
             == $Unbox(read($Heap, a#0, IndexField(i#2))): real + 4e0;
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
             || (exists i#3: int :: 
              2 - i#3 <= LitInt(2)
                 && i#3 < _System.array.Length(a#0)
                 && $o == b#0
                 && $f == IndexField(7 - i#3)));
        assume (forall i#inv#0: int :: 
          { read($Heap, b#0, IndexField(i#inv#0)) } 
          2 - (7 - i#inv#0) <= LitInt(2) && 7 - i#inv#0 < _System.array.Length(a#0)
             ==> read($Heap, b#0, IndexField(i#inv#0))
               == $Box($Unbox(read($prevHeap, a#0, IndexField(7 - i#inv#0))): real + 4e0));
    }

    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(18,2)"} true;
    // ----- forall statement (assign) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(19,3)
    if (*)
    {
        // Assume Fuel Constant
        havoc i#4;
        assume true;
        if (LitInt(0) <= i#4)
        {
            assert {:subsumption 0} a#0 != null;
        }

        assume true;
        assume LitInt(0) <= i#4 && i#4 < _System.array.Length(a#0);
        assert c#0 != null;
        assert {:subsumption 0} 0 <= i#4 && i#4 < _System.array.Length(c#0);
        assume true;
        assert $_Frame[c#0, IndexField(i#4)];
        assert a#0 != null;
        assert {:subsumption 0} 0 <= i#4 && i#4 < _System.array.Length(a#0);
        assert b#0 != null;
        assert {:subsumption 0} 0 <= i#4 && i#4 < _System.array.Length(b#0);
        assume true;
        havoc i#5;
        assume true;
        assume LitInt(0) <= i#5 && i#5 < _System.array.Length(a#0);
        assume i#4 != i#5;
        assert c#0 != c#0
           || IndexField(i#4) != IndexField(i#5)
           || ($Unbox(read($Heap, a#0, IndexField(i#4))): real
               < $Unbox(read($Heap, b#0, IndexField(i#4))): real)
             == ($Unbox(read($Heap, a#0, IndexField(i#5))): real
               < $Unbox(read($Heap, b#0, IndexField(i#5))): real);
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
             || (exists i#6: int :: 
              LitInt(0) <= i#6
                 && i#6 < _System.array.Length(a#0)
                 && $o == c#0
                 && $f == IndexField(i#6)));
        assume (forall i#inv#1: int :: 
          { read($Heap, c#0, IndexField(i#inv#1)) } 
          LitInt(0) <= i#inv#1 && i#inv#1 < _System.array.Length(a#0)
             ==> read($Heap, c#0, IndexField(i#inv#1))
               == $Box($Unbox(read($prevHeap, a#0, IndexField(i#inv#1))): real
                   < $Unbox(read($prevHeap, b#0, IndexField(i#inv#1))): real));
    }

    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(21,2)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(22,13)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##0 := a#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.PrintArray(TReal, a##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(22,15)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(23,13)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##1 := b#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.PrintArray(TReal, a##1);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(23,15)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(24,13)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##2 := c#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.PrintArray(TBool, a##2);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(24,15)"} true;
}



procedure CheckWellformed$$_module.__default.PrintArray(_module._default.PrintArray$_T0: Ty, 
    a#0: ref
       where $Is(a#0, Tclass._System.array(_module._default.PrintArray$_T0))
         && $IsAlloc(a#0, Tclass._System.array(_module._default.PrintArray$_T0), $Heap));
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.PrintArray(_module._default.PrintArray$_T0: Ty, 
    a#0: ref
       where $Is(a#0, Tclass._System.array(_module._default.PrintArray$_T0))
         && $IsAlloc(a#0, Tclass._System.array(_module._default.PrintArray$_T0), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.PrintArray(_module._default.PrintArray$_T0: Ty, 
    a#0: ref
       where $Is(a#0, Tclass._System.array(_module._default.PrintArray$_T0))
         && $IsAlloc(a#0, Tclass._System.array(_module._default.PrintArray$_T0), $Heap))
   returns ($_reverifyPost: bool);
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.PrintArray(_module._default.PrintArray$_T0: Ty, a#0: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var i#0: int;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var $decr$loop#00: int;

    // AddMethodImpl: PrintArray, Impl$$_module.__default.PrintArray
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(27,28): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(28,9)
    assume true;
    assume true;
    i#0 := LitInt(0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(28,12)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(29,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := _System.array.Length(a#0) - i#0;
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
      free invariant _System.array.Length(a#0) - i#0 <= $decr_init$loop#00
         && (_System.array.Length(a#0) - i#0 == $decr_init$loop#00 ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(29,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assert a#0 != null;
            assume true;
            assume false;
        }

        assert a#0 != null;
        assume true;
        if (_System.array.Length(a#0) <= i#0)
        {
            break;
        }

        $decr$loop#00 := _System.array.Length(a#0) - i#0;
        // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(30,5)
        assert a#0 != null;
        assert {:subsumption 0} 0 <= i#0 && i#0 < _System.array.Length(a#0);
        assume true;
        assume true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(31,7)
        assume true;
        assume true;
        i#0 := i#0 + 1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(31,14)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(29,3)
        assert 0 <= $decr$loop#00 || _System.array.Length(a#0) - i#0 == $decr$loop#00;
        assert _System.array.Length(a#0) - i#0 < $decr$loop#00;
    }

    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(33,3)
    assume true;
}



procedure CheckWellformed$$_module.__default.TestAggregateMultiArrayUpdate();
  free requires 16 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.TestAggregateMultiArrayUpdate();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.TestAggregateMultiArrayUpdate() returns ($_reverifyPost: bool);
  free requires 16 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.TestAggregateMultiArrayUpdate() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var matrix#0: ref
     where $Is(matrix#0, Tclass._System.array2(TInt))
       && $IsAlloc(matrix#0, Tclass._System.array2(TInt), $Heap);
  var i#0: int;
  var j#0: int;
  var $oldHeap#0: Heap;
  var $_Frame#l0: <beta>[ref,Field beta]bool;
  var lambdaResult#0: int;
  var newtype$check#0: int;
  var $nw: ref;
  var m##0: ref;
  var m'#0: ref
     where $Is(m'#0, Tclass._System.array2(TInt))
       && $IsAlloc(m'#0, Tclass._System.array2(TInt), $Heap);
  var i#1: int;
  var j#1: int;
  var $oldHeap#1: Heap;
  var $_Frame#l1: <beta>[ref,Field beta]bool;
  var lambdaResult#1: int;
  var m0#0: ref
     where $Is(m0#0, Tclass._System.array2(TInt))
       && $IsAlloc(m0#0, Tclass._System.array2(TInt), $Heap);
  var m1#0: ref
     where $Is(m1#0, Tclass._System.array2(TInt))
       && $IsAlloc(m1#0, Tclass._System.array2(TInt), $Heap);
  var m2#0: ref
     where $Is(m2#0, Tclass._System.array2(TInt))
       && $IsAlloc(m2#0, Tclass._System.array2(TInt), $Heap);
  var $rhs##0: ref
     where $Is($rhs##0, Tclass._System.array2(TInt))
       && $IsAlloc($rhs##0, Tclass._System.array2(TInt), $Heap);
  var $rhs##1: ref
     where $Is($rhs##1, Tclass._System.array2(TInt))
       && $IsAlloc($rhs##1, Tclass._System.array2(TInt), $Heap);
  var $rhs##2: ref
     where $Is($rhs##2, Tclass._System.array2(TInt))
       && $IsAlloc($rhs##2, Tclass._System.array2(TInt), $Heap);
  var m##1: ref;
  var m##2: ref;
  var m##3: ref;
  var m##4: ref;
  var m##5: ref;
  var ##m#0: ref;
  var ##m'#0: ref;
  var $rhs#0: int;
  var ##m#1: ref;
  var ##m'#1: ref;

    // AddMethodImpl: TestAggregateMultiArrayUpdate, Impl$$_module.__default.TestAggregateMultiArrayUpdate
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(38,39): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(39,14)
    assume true;
    assert 0 <= LitInt(12);
    assert 0 <= LitInt(3);
    // Begin Comprehension WF check
    if (*)
    {
        havoc i#0;
        havoc j#0;
        if (LitInt(0) <= i#0 && LitInt(0) <= j#0)
        {
            $oldHeap#0 := $Heap;
            havoc $Heap;
            assume $IsGoodHeap($Heap);
            assume $oldHeap#0 == $Heap || $HeapSucc($oldHeap#0, $Heap);
            $_Frame#l0 := (lambda<alpha> $o: ref, $f: Field alpha :: 
              $o != null && read($Heap, $o, alloc) ==> false);
            newtype$check#0 := i#0 + j#0;
            assert LitInt(0) <= newtype$check#0;
            assume lambdaResult#0 == i#0 + j#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(lambdaResult#0, Tclass._System.nat());
        }

        assume false;
    }

    // End Comprehension WF check
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._System.array2?(TInt);
    assume !read($Heap, $nw, alloc);
    assume _System.array2.Length0($nw) == LitInt(12);
    assume _System.array2.Length1($nw) == LitInt(3);
    assert {:subsumption 0} (forall arrayinit#0#i0#0: int, arrayinit#0#i1#0: int :: 
      0 <= arrayinit#0#i0#0
           && arrayinit#0#i0#0 < LitInt(12)
           && 
          0 <= arrayinit#0#i1#0
           && arrayinit#0#i1#0 < LitInt(3)
         ==> Requires2(Tclass._System.nat(), 
          Tclass._System.nat(), 
          Tclass._System.nat(), 
          $Heap, 
          Lit(AtLayer((lambda $l#0#ly#0: LayerType :: 
                Handle2((lambda $l#0#heap#0: Heap, $l#0#i#0: Box, $l#0#j#0: Box :: 
                    $Box($Unbox($l#0#i#0): int + $Unbox($l#0#j#0): int)), 
                  (lambda $l#0#heap#0: Heap, $l#0#i#0: Box, $l#0#j#0: Box :: 
                    $IsBox($l#0#i#0, Tclass._System.nat()) && $IsBox($l#0#j#0, Tclass._System.nat())), 
                  (lambda $l#0#heap#0: Heap, $l#0#i#0: Box, $l#0#j#0: Box :: 
                    SetRef_to_SetBox((lambda $l#0#o#0: ref :: false))))), 
              $LS($LZ))), 
          $Box(arrayinit#0#i0#0), 
          $Box(arrayinit#0#i1#0)));
    assert {:subsumption 0} (forall arrayinit#0#i0#0: int, arrayinit#0#i1#0: int :: 
      0 <= arrayinit#0#i0#0
           && arrayinit#0#i0#0 < LitInt(12)
           && 
          0 <= arrayinit#0#i1#0
           && arrayinit#0#i1#0 < LitInt(3)
         ==> $Is($Unbox(Apply2(Tclass._System.nat(), 
              Tclass._System.nat(), 
              Tclass._System.nat(), 
              $Heap, 
              Lit(AtLayer((lambda $l#0#ly#0: LayerType :: 
                    Handle2((lambda $l#0#heap#0: Heap, $l#0#i#0: Box, $l#0#j#0: Box :: 
                        $Box($Unbox($l#0#i#0): int + $Unbox($l#0#j#0): int)), 
                      (lambda $l#0#heap#0: Heap, $l#0#i#0: Box, $l#0#j#0: Box :: 
                        $IsBox($l#0#i#0, Tclass._System.nat()) && $IsBox($l#0#j#0, Tclass._System.nat())), 
                      (lambda $l#0#heap#0: Heap, $l#0#i#0: Box, $l#0#j#0: Box :: 
                        SetRef_to_SetBox((lambda $l#0#o#0: ref :: false))))), 
                  $LS($LZ))), 
              $Box(arrayinit#0#i0#0), 
              $Box(arrayinit#0#i1#0))): int, 
          TInt));
    assume (forall arrayinit#0#i0#0: int, arrayinit#0#i1#0: int :: 
      { read($Heap, $nw, MultiIndexField(IndexField(arrayinit#0#i0#0), arrayinit#0#i1#0)) } 
      0 <= arrayinit#0#i0#0
           && arrayinit#0#i0#0 < LitInt(12)
           && 
          0 <= arrayinit#0#i1#0
           && arrayinit#0#i1#0 < LitInt(3)
         ==> $Unbox(read($Heap, $nw, MultiIndexField(IndexField(arrayinit#0#i0#0), arrayinit#0#i1#0))): int
           == $Unbox(Apply2(Tclass._System.nat(), 
              Tclass._System.nat(), 
              Tclass._System.nat(), 
              $Heap, 
              Lit(AtLayer((lambda $l#0#ly#0: LayerType :: 
                    Handle2((lambda $l#0#heap#0: Heap, $l#0#i#0: Box, $l#0#j#0: Box :: 
                        $Box($Unbox($l#0#i#0): int + $Unbox($l#0#j#0): int)), 
                      (lambda $l#0#heap#0: Heap, $l#0#i#0: Box, $l#0#j#0: Box :: 
                        $IsBox($l#0#i#0, Tclass._System.nat()) && $IsBox($l#0#j#0, Tclass._System.nat())), 
                      (lambda $l#0#heap#0: Heap, $l#0#i#0: Box, $l#0#j#0: Box :: 
                        SetRef_to_SetBox((lambda $l#0#o#0: ref :: false))))), 
                  $LS($LZ))), 
              $Box(arrayinit#0#i0#0), 
              $Box(arrayinit#0#i1#0))): int);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    matrix#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(39,43)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(40,14)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    m##0 := matrix#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.PrintMatrix(m##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(40,21)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(43,10)
    assume true;
    assert matrix#0 != null;
    assert 0 <= _System.array2.Length1(matrix#0);
    assert matrix#0 != null;
    assert 0 <= _System.array2.Length0(matrix#0);
    // Begin Comprehension WF check
    if (*)
    {
        havoc i#1;
        havoc j#1;
        if (true)
        {
            $oldHeap#1 := $Heap;
            havoc $Heap;
            assume $IsGoodHeap($Heap);
            assume $oldHeap#1 == $Heap || $HeapSucc($oldHeap#1, $Heap);
            $_Frame#l1 := (lambda<alpha> $o: ref, $f: Field alpha :: 
              $o != null && read($Heap, $o, alloc) ==> $o == matrix#0);
            if (LitInt(0) <= i#1)
            {
                assert matrix#0 != null;
            }

            if (LitInt(0) <= i#1 && i#1 < _System.array2.Length1(matrix#0))
            {
                if (LitInt(0) <= j#1)
                {
                    assert matrix#0 != null;
                }
            }

            if (LitInt(0) <= i#1
               && i#1 < _System.array2.Length1(matrix#0)
               && 
              LitInt(0) <= j#1
               && j#1 < _System.array2.Length0(matrix#0))
            {
                assert matrix#0 != null;
                assert 0 <= j#1 && j#1 < _System.array2.Length0(matrix#0);
                assert 0 <= i#1 && i#1 < _System.array2.Length1(matrix#0);
                assert $_Frame#l1[matrix#0, MultiIndexField(IndexField(j#1), i#1)];
                assume lambdaResult#1
                   == $Unbox(read($Heap, matrix#0, MultiIndexField(IndexField(j#1), i#1))): int;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(lambdaResult#1, TInt);
            }
        }

        assume false;
    }

    // End Comprehension WF check
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._System.array2?(TInt);
    assume !read($Heap, $nw, alloc);
    assume _System.array2.Length0($nw) == _System.array2.Length1(matrix#0);
    assume _System.array2.Length1($nw) == _System.array2.Length0(matrix#0);
    assert {:subsumption 0} (forall arrayinit#1#i0#0: int, arrayinit#1#i1#0: int :: 
      0 <= arrayinit#1#i0#0
           && arrayinit#1#i0#0 < _System.array2.Length1(matrix#0)
           && 
          0 <= arrayinit#1#i1#0
           && arrayinit#1#i1#0 < _System.array2.Length0(matrix#0)
         ==> Requires2(TInt, 
          TInt, 
          TInt, 
          $Heap, 
          Lit(AtLayer((lambda $l#1#ly#0: LayerType :: 
                Handle2((lambda $l#1#heap#0: Heap, $l#1#i#0: Box, $l#1#j#0: Box :: 
                    $Box($Unbox(read($l#1#heap#0, 
                          matrix#0, 
                          MultiIndexField(IndexField($Unbox($l#1#j#0): int), $Unbox($l#1#i#0): int))): int)), 
                  (lambda $l#1#heap#0: Heap, $l#1#i#0: Box, $l#1#j#0: Box :: 
                    $IsBox($l#1#i#0, TInt)
                       && $IsBox($l#1#j#0, TInt)
                       && 
                      LitInt(0) <= $Unbox($l#1#i#0): int
                       && $Unbox($l#1#i#0): int < _System.array2.Length1(matrix#0)
                       && 
                      LitInt(0) <= $Unbox($l#1#j#0): int
                       && $Unbox($l#1#j#0): int < _System.array2.Length0(matrix#0)), 
                  (lambda $l#1#heap#0: Heap, $l#1#i#0: Box, $l#1#j#0: Box :: 
                    SetRef_to_SetBox((lambda $l#1#o#0: ref :: $l#1#o#0 == matrix#0))))), 
              $LS($LZ))), 
          $Box(arrayinit#1#i0#0), 
          $Box(arrayinit#1#i1#0)));
    assume (forall arrayinit#1#i0#0: int, arrayinit#1#i1#0: int :: 
      { read($Heap, $nw, MultiIndexField(IndexField(arrayinit#1#i0#0), arrayinit#1#i1#0)) } 
      0 <= arrayinit#1#i0#0
           && arrayinit#1#i0#0 < _System.array2.Length1(matrix#0)
           && 
          0 <= arrayinit#1#i1#0
           && arrayinit#1#i1#0 < _System.array2.Length0(matrix#0)
         ==> $Unbox(read($Heap, $nw, MultiIndexField(IndexField(arrayinit#1#i0#0), arrayinit#1#i1#0))): int
           == $Unbox(Apply2(TInt, 
              TInt, 
              TInt, 
              $Heap, 
              Lit(AtLayer((lambda $l#1#ly#0: LayerType :: 
                    Handle2((lambda $l#1#heap#0: Heap, $l#1#i#0: Box, $l#1#j#0: Box :: 
                        $Box($Unbox(read($l#1#heap#0, 
                              matrix#0, 
                              MultiIndexField(IndexField($Unbox($l#1#j#0): int), $Unbox($l#1#i#0): int))): int)), 
                      (lambda $l#1#heap#0: Heap, $l#1#i#0: Box, $l#1#j#0: Box :: 
                        $IsBox($l#1#i#0, TInt)
                           && $IsBox($l#1#j#0, TInt)
                           && 
                          LitInt(0) <= $Unbox($l#1#i#0): int
                           && $Unbox($l#1#i#0): int < _System.array2.Length1(matrix#0)
                           && 
                          LitInt(0) <= $Unbox($l#1#j#0): int
                           && $Unbox($l#1#j#0): int < _System.array2.Length0(matrix#0)), 
                      (lambda $l#1#heap#0: Heap, $l#1#i#0: Box, $l#1#j#0: Box :: 
                        SetRef_to_SetBox((lambda $l#1#o#0: ref :: $l#1#o#0 == matrix#0))))), 
                  $LS($LZ))), 
              $Box(arrayinit#1#i0#0), 
              $Box(arrayinit#1#i1#0))): int);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    m'#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(44,98)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(45,30)
    assume true;
    assume true;
    assume true;
    // TrCallStmt: Adding lhs with type array2<int>
    // TrCallStmt: Adding lhs with type array2<int>
    // TrCallStmt: Adding lhs with type array2<int>
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    m##1 := matrix#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0, $rhs##1, $rhs##2 := Call$$_module.__default.Transpose(TInt, m##1);
    // TrCallStmt: After ProcessCallStmt
    m0#0 := $rhs##0;
    m1#0 := $rhs##1;
    m2#0 := $rhs##2;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(45,37)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(46,14)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    m##2 := m'#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.PrintMatrix(m##2);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(46,17)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(47,14)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    m##3 := m0#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.PrintMatrix(m##3);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(47,17)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(48,14)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    m##4 := m1#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.PrintMatrix(m##4);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(48,17)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(49,14)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    m##5 := m2#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.PrintMatrix(m##5);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(49,17)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(51,3)
    ##m#0 := m0#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##m#0, Tclass._System.array2(TInt), $Heap);
    ##m'#0 := m'#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##m'#0, Tclass._System.array2(TInt), $Heap);
    assume _module.__default.MatrixEqual#canCall(TInt, $Heap, m0#0, m'#0);
    assume _module.__default.MatrixEqual#canCall(TInt, $Heap, m0#0, m'#0);
    assume true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(52,11)
    assert m'#0 != null;
    assert 0 <= LitInt(2) && LitInt(2) < _System.array2.Length0(m'#0);
    assert 0 <= LitInt(2) && LitInt(2) < _System.array2.Length1(m'#0);
    assume true;
    assert $_Frame[m'#0, MultiIndexField(IndexField(LitInt(2)), LitInt(2))];
    assume true;
    $rhs#0 := LitInt(87);
    $Heap := update($Heap, m'#0, MultiIndexField(IndexField(LitInt(2)), LitInt(2)), $Box($rhs#0));
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(52,15)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(53,3)
    ##m#1 := m0#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##m#1, Tclass._System.array2(TInt), $Heap);
    ##m'#1 := m'#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##m'#1, Tclass._System.array2(TInt), $Heap);
    assume _module.__default.MatrixEqual#canCall(TInt, $Heap, m0#0, m'#0);
    assume _module.__default.MatrixEqual#canCall(TInt, $Heap, m0#0, m'#0);
    assume true;
}



procedure CheckWellformed$$_module.__default.PrintMatrix(m#0: ref
       where $Is(m#0, Tclass._System.array2(TInt))
         && $IsAlloc(m#0, Tclass._System.array2(TInt), $Heap));
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.PrintMatrix(m#0: ref
       where $Is(m#0, Tclass._System.array2(TInt))
         && $IsAlloc(m#0, Tclass._System.array2(TInt), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.PrintMatrix(m#0: ref
       where $Is(m#0, Tclass._System.array2(TInt))
         && $IsAlloc(m#0, Tclass._System.array2(TInt), $Heap))
   returns ($_reverifyPost: bool);
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.PrintMatrix(m#0: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var i#0: int;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var $decr$loop#00: int;
  var j#0_0: int;
  var $PreLoopHeap$loop#0_0: Heap;
  var $decr_init$loop#0_00: int;
  var $w$loop#0_0: bool;
  var $decr$loop#0_00: int;

    // AddMethodImpl: PrintMatrix, Impl$$_module.__default.PrintMatrix
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(56,35): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(57,9)
    assume true;
    assume true;
    i#0 := LitInt(0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(57,12)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(58,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := _System.array2.Length0(m#0) - i#0;
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
      free invariant _System.array2.Length0(m#0) - i#0 <= $decr_init$loop#00
         && (_System.array2.Length0(m#0) - i#0 == $decr_init$loop#00 ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(58,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assert m#0 != null;
            assume true;
            assume false;
        }

        assert m#0 != null;
        assume true;
        if (_System.array2.Length0(m#0) <= i#0)
        {
            break;
        }

        $decr$loop#00 := _System.array2.Length0(m#0) - i#0;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(59,11)
        assume true;
        assume true;
        j#0_0 := LitInt(0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(59,14)"} true;
        // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(60,5)
        // Assume Fuel Constant
        $PreLoopHeap$loop#0_0 := $Heap;
        $decr_init$loop#0_00 := _System.array2.Length1(m#0) - j#0_0;
        havoc $w$loop#0_0;
        while (true)
          free invariant (forall $o: ref :: 
            { $Heap[$o] } 
            $o != null && read(old($Heap), $o, alloc)
               ==> $Heap[$o] == $PreLoopHeap$loop#0_0[$o]);
          free invariant $HeapSucc($PreLoopHeap$loop#0_0, $Heap);
          free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
            { read($Heap, $o, $f) } 
            $o != null && read($PreLoopHeap$loop#0_0, $o, alloc)
               ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0_0, $o, $f) || $_Frame[$o, $f]);
          free invariant _System.array2.Length1(m#0) - j#0_0 <= $decr_init$loop#0_00
             && (_System.array2.Length1(m#0) - j#0_0 == $decr_init$loop#0_00 ==> true);
        {
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(60,4): after some loop iterations"} true;
            if (!$w$loop#0_0)
            {
                assert m#0 != null;
                assume true;
                assume false;
            }

            assert m#0 != null;
            assume true;
            if (_System.array2.Length1(m#0) <= j#0_0)
            {
                break;
            }

            $decr$loop#0_00 := _System.array2.Length1(m#0) - j#0_0;
            // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(61,7)
            assert m#0 != null;
            assert {:subsumption 0} 0 <= i#0 && i#0 < _System.array2.Length0(m#0);
            assert {:subsumption 0} 0 <= j#0_0 && j#0_0 < _System.array2.Length1(m#0);
            assume true;
            assume true;
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(62,9)
            assume true;
            assume true;
            j#0_0 := j#0_0 + 1;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(62,16)"} true;
            // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(60,5)
            assert 0 <= $decr$loop#0_00 || _System.array2.Length1(m#0) - j#0_0 == $decr$loop#0_00;
            assert _System.array2.Length1(m#0) - j#0_0 < $decr$loop#0_00;
        }

        // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(64,5)
        assume true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(65,7)
        assume true;
        assume true;
        i#0 := i#0 + 1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(65,14)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(58,3)
        assert 0 <= $decr$loop#00 || _System.array2.Length0(m#0) - i#0 == $decr$loop#00;
        assert _System.array2.Length0(m#0) - i#0 < $decr$loop#00;
    }
}



procedure CheckWellformed$$_module.__default.Transpose(_module._default.Transpose$T: Ty, 
    m#0: ref
       where $Is(m#0, Tclass._System.array2(_module._default.Transpose$T))
         && $IsAlloc(m#0, Tclass._System.array2(_module._default.Transpose$T), $Heap))
   returns (m0#0: ref
       where $Is(m0#0, Tclass._System.array2(_module._default.Transpose$T))
         && $IsAlloc(m0#0, Tclass._System.array2(_module._default.Transpose$T), $Heap), 
    m1#0: ref
       where $Is(m1#0, Tclass._System.array2(_module._default.Transpose$T))
         && $IsAlloc(m1#0, Tclass._System.array2(_module._default.Transpose$T), $Heap), 
    m2#0: ref
       where $Is(m2#0, Tclass._System.array2(_module._default.Transpose$T))
         && $IsAlloc(m2#0, Tclass._System.array2(_module._default.Transpose$T), $Heap));
  free requires 10 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Transpose(_module._default.Transpose$T: Ty, 
    m#0: ref
       where $Is(m#0, Tclass._System.array2(_module._default.Transpose$T))
         && $IsAlloc(m#0, Tclass._System.array2(_module._default.Transpose$T), $Heap))
   returns (m0#0: ref
       where $Is(m0#0, Tclass._System.array2(_module._default.Transpose$T))
         && $IsAlloc(m0#0, Tclass._System.array2(_module._default.Transpose$T), $Heap), 
    m1#0: ref
       where $Is(m1#0, Tclass._System.array2(_module._default.Transpose$T))
         && $IsAlloc(m1#0, Tclass._System.array2(_module._default.Transpose$T), $Heap), 
    m2#0: ref
       where $Is(m2#0, Tclass._System.array2(_module._default.Transpose$T))
         && $IsAlloc(m2#0, Tclass._System.array2(_module._default.Transpose$T), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures m0#0 != null && !read(old($Heap), m0#0, alloc);
  ensures m1#0 != null && !read(old($Heap), m1#0, alloc);
  ensures m2#0 != null && !read(old($Heap), m2#0, alloc);
  free ensures _module.__default.MatrixEqual#canCall(_module._default.Transpose$T, $Heap, m0#0, m1#0)
     && (_module.__default.MatrixEqual(_module._default.Transpose$T, $Heap, m0#0, m1#0)
       ==> _module.__default.MatrixEqual#canCall(_module._default.Transpose$T, $Heap, m0#0, m2#0));
  free ensures _module.__default.MatrixEqual#canCall(_module._default.Transpose$T, $Heap, m0#0, m1#0)
     && 
    _module.__default.MatrixEqual(_module._default.Transpose$T, $Heap, m0#0, m1#0)
     && 
    _System.Tuple2#Equal(#_System._tuple#2._#Make2($Box(_System.array2.Length0(m0#0)), $Box(_System.array2.Length1(m0#0))), 
      #_System._tuple#2._#Make2($Box(_System.array2.Length0(m1#0)), $Box(_System.array2.Length1(m1#0))))
     && (forall i#0: int, j#0: int :: 
      { read($Heap, m1#0, MultiIndexField(IndexField(i#0), j#0)) } 
        { read($Heap, m0#0, MultiIndexField(IndexField(i#0), j#0)) } 
      true
         ==> 
        LitInt(0) <= i#0
           && i#0 < _System.array2.Length0(m0#0)
           && 
          LitInt(0) <= j#0
           && j#0 < _System.array2.Length1(m0#0)
         ==> read($Heap, m0#0, MultiIndexField(IndexField(i#0), j#0))
           == read($Heap, m1#0, MultiIndexField(IndexField(i#0), j#0)));
  free ensures _module.__default.MatrixEqual#canCall(_module._default.Transpose$T, $Heap, m0#0, m2#0)
     && 
    _module.__default.MatrixEqual(_module._default.Transpose$T, $Heap, m0#0, m2#0)
     && 
    _System.Tuple2#Equal(#_System._tuple#2._#Make2($Box(_System.array2.Length0(m0#0)), $Box(_System.array2.Length1(m0#0))), 
      #_System._tuple#2._#Make2($Box(_System.array2.Length0(m2#0)), $Box(_System.array2.Length1(m2#0))))
     && (forall i#1: int, j#1: int :: 
      { read($Heap, m2#0, MultiIndexField(IndexField(i#1), j#1)) } 
        { read($Heap, m0#0, MultiIndexField(IndexField(i#1), j#1)) } 
      true
         ==> 
        LitInt(0) <= i#1
           && i#1 < _System.array2.Length0(m0#0)
           && 
          LitInt(0) <= j#1
           && j#1 < _System.array2.Length1(m0#0)
         ==> read($Heap, m0#0, MultiIndexField(IndexField(i#1), j#1))
           == read($Heap, m2#0, MultiIndexField(IndexField(i#1), j#1)));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.Transpose(_module._default.Transpose$T: Ty, 
    m#0: ref
       where $Is(m#0, Tclass._System.array2(_module._default.Transpose$T))
         && $IsAlloc(m#0, Tclass._System.array2(_module._default.Transpose$T), $Heap))
   returns (m0#0: ref
       where $Is(m0#0, Tclass._System.array2(_module._default.Transpose$T))
         && $IsAlloc(m0#0, Tclass._System.array2(_module._default.Transpose$T), $Heap), 
    m1#0: ref
       where $Is(m1#0, Tclass._System.array2(_module._default.Transpose$T))
         && $IsAlloc(m1#0, Tclass._System.array2(_module._default.Transpose$T), $Heap), 
    m2#0: ref
       where $Is(m2#0, Tclass._System.array2(_module._default.Transpose$T))
         && $IsAlloc(m2#0, Tclass._System.array2(_module._default.Transpose$T), $Heap), 
    $_reverifyPost: bool);
  free requires 10 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures m0#0 != null && !read(old($Heap), m0#0, alloc);
  ensures m1#0 != null && !read(old($Heap), m1#0, alloc);
  ensures m2#0 != null && !read(old($Heap), m2#0, alloc);
  free ensures _module.__default.MatrixEqual#canCall(_module._default.Transpose$T, $Heap, m0#0, m1#0)
     && (_module.__default.MatrixEqual(_module._default.Transpose$T, $Heap, m0#0, m1#0)
       ==> _module.__default.MatrixEqual#canCall(_module._default.Transpose$T, $Heap, m0#0, m2#0));
  ensures _module.__default.MatrixEqual#canCall(_module._default.Transpose$T, $Heap, m0#0, m1#0)
     ==> _module.__default.MatrixEqual(_module._default.Transpose$T, $Heap, m0#0, m1#0)
       || _System.Tuple2#Equal(#_System._tuple#2._#Make2($Box(_System.array2.Length0(m0#0)), $Box(_System.array2.Length1(m0#0))), 
        #_System._tuple#2._#Make2($Box(_System.array2.Length0(m1#0)), $Box(_System.array2.Length1(m1#0))));
  ensures _module.__default.MatrixEqual#canCall(_module._default.Transpose$T, $Heap, m0#0, m1#0)
     ==> _module.__default.MatrixEqual(_module._default.Transpose$T, $Heap, m0#0, m1#0)
       || (forall i#2: int, j#2: int :: 
        { read($Heap, m1#0, MultiIndexField(IndexField(i#2), j#2)) } 
          { read($Heap, m0#0, MultiIndexField(IndexField(i#2), j#2)) } 
        true
           ==> 
          LitInt(0) <= i#2
             && i#2 < _System.array2.Length0(m0#0)
             && 
            LitInt(0) <= j#2
             && j#2 < _System.array2.Length1(m0#0)
           ==> read($Heap, m0#0, MultiIndexField(IndexField(i#2), j#2))
             == read($Heap, m1#0, MultiIndexField(IndexField(i#2), j#2)));
  ensures _module.__default.MatrixEqual#canCall(_module._default.Transpose$T, $Heap, m0#0, m2#0)
     ==> _module.__default.MatrixEqual(_module._default.Transpose$T, $Heap, m0#0, m2#0)
       || _System.Tuple2#Equal(#_System._tuple#2._#Make2($Box(_System.array2.Length0(m0#0)), $Box(_System.array2.Length1(m0#0))), 
        #_System._tuple#2._#Make2($Box(_System.array2.Length0(m2#0)), $Box(_System.array2.Length1(m2#0))));
  ensures _module.__default.MatrixEqual#canCall(_module._default.Transpose$T, $Heap, m0#0, m2#0)
     ==> _module.__default.MatrixEqual(_module._default.Transpose$T, $Heap, m0#0, m2#0)
       || (forall i#3: int, j#3: int :: 
        { read($Heap, m2#0, MultiIndexField(IndexField(i#3), j#3)) } 
          { read($Heap, m0#0, MultiIndexField(IndexField(i#3), j#3)) } 
        true
           ==> 
          LitInt(0) <= i#3
             && i#3 < _System.array2.Length0(m0#0)
             && 
            LitInt(0) <= j#3
             && j#3 < _System.array2.Length1(m0#0)
           ==> read($Heap, m0#0, MultiIndexField(IndexField(i#3), j#3))
             == read($Heap, m2#0, MultiIndexField(IndexField(i#3), j#3)));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.Transpose(_module._default.Transpose$T: Ty, m#0: ref)
   returns (m0#0: ref, m1#0: ref, m2#0: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var X#0: int;
  var Y#0: int;
  var $rhs#0: int;
  var $rhs#1: int;
  var $rhs#2: ref
     where $Is($rhs#2, Tclass._System.array2(_module._default.Transpose$T));
  var $nw: ref;
  var $rhs#3: ref
     where $Is($rhs#3, Tclass._System.array2(_module._default.Transpose$T));
  var $rhs#4: ref
     where $Is($rhs#4, Tclass._System.array2(_module._default.Transpose$T));
  var i#4: int;
  var j#4: int;
  var i#5: int;
  var j#5: int;
  var $prevHeap: Heap;
  var i#7: int;
  var j#7: int;
  var i#8: int;
  var j#8: int;
  var i#10: int;
  var j#10: int;
  var i#11: int;
  var j#11: int;

    // AddMethodImpl: Transpose, Impl$$_module.__default.Transpose
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(72,0): initial state"} true;
    $_reverifyPost := false;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(73,12)
    assume true;
    assume true;
    assert m#0 != null;
    assume true;
    $rhs#0 := _System.array2.Length1(m#0);
    assert m#0 != null;
    assume true;
    $rhs#1 := _System.array2.Length0(m#0);
    X#0 := $rhs#0;
    Y#0 := $rhs#1;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(73,34)"} true;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(74,14)
    assume true;
    assume true;
    assume true;
    assert 0 <= X#0;
    assert 0 <= Y#0;
    havoc $nw;
    assume $nw != null
       && dtype($nw) == Tclass._System.array2?(_module._default.Transpose$T);
    assume !read($Heap, $nw, alloc);
    assume _System.array2.Length0($nw) == X#0;
    assume _System.array2.Length1($nw) == Y#0;
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    $rhs#2 := $nw;
    assert 0 <= X#0;
    assert 0 <= Y#0;
    havoc $nw;
    assume $nw != null
       && dtype($nw) == Tclass._System.array2?(_module._default.Transpose$T);
    assume !read($Heap, $nw, alloc);
    assume _System.array2.Length0($nw) == X#0;
    assume _System.array2.Length1($nw) == Y#0;
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    $rhs#3 := $nw;
    assert 0 <= X#0;
    assert 0 <= Y#0;
    havoc $nw;
    assume $nw != null
       && dtype($nw) == Tclass._System.array2?(_module._default.Transpose$T);
    assume !read($Heap, $nw, alloc);
    assume _System.array2.Length0($nw) == X#0;
    assume _System.array2.Length1($nw) == Y#0;
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    $rhs#4 := $nw;
    m0#0 := $rhs#2;
    m1#0 := $rhs#3;
    m2#0 := $rhs#4;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(74,53)"} true;
    // ----- forall statement (assign) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(75,3)
    if (*)
    {
        // Assume Fuel Constant
        havoc i#4;
        havoc j#4;
        assume true;
        if (LitInt(0) <= i#4)
        {
        }

        if (LitInt(0) <= i#4 && i#4 < X#0)
        {
            if (LitInt(0) <= j#4)
            {
            }
        }

        assume true;
        assume LitInt(0) <= i#4 && i#4 < X#0 && LitInt(0) <= j#4 && j#4 < Y#0;
        assert m0#0 != null;
        assert {:subsumption 0} 0 <= i#4 && i#4 < _System.array2.Length0(m0#0);
        assert {:subsumption 0} 0 <= j#4 && j#4 < _System.array2.Length1(m0#0);
        assume true;
        assert $_Frame[m0#0, MultiIndexField(IndexField(i#4), j#4)];
        assert m#0 != null;
        assert {:subsumption 0} 0 <= j#4 && j#4 < _System.array2.Length0(m#0);
        assert {:subsumption 0} 0 <= i#4 && i#4 < _System.array2.Length1(m#0);
        assume true;
        havoc i#5;
        havoc j#5;
        assume true;
        assume LitInt(0) <= i#5 && i#5 < X#0 && LitInt(0) <= j#5 && j#5 < Y#0;
        assume !(i#4 == i#5 && j#4 == j#5);
        assert m0#0 != m0#0
           || MultiIndexField(IndexField(i#4), j#4) != MultiIndexField(IndexField(i#5), j#5)
           || read($Heap, m#0, MultiIndexField(IndexField(j#4), i#4))
             == read($Heap, m#0, MultiIndexField(IndexField(j#5), i#5));
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
             || (exists i#6: int, j#6: int :: 
              LitInt(0) <= i#6
                 && i#6 < X#0
                 && 
                LitInt(0) <= j#6
                 && j#6 < Y#0
                 && $o == m0#0
                 && $f == MultiIndexField(IndexField(i#6), j#6)));
        assume (forall i#6: int, j#6: int :: 
          LitInt(0) <= i#6 && i#6 < X#0 && LitInt(0) <= j#6 && j#6 < Y#0
             ==> read($Heap, m0#0, MultiIndexField(IndexField(i#6), j#6))
               == read($prevHeap, m#0, MultiIndexField(IndexField(j#6), i#6)));
    }

    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(77,2)"} true;
    // ----- forall statement (assign) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(78,3)
    if (*)
    {
        // Assume Fuel Constant
        havoc i#7;
        havoc j#7;
        assume LitInt(0) <= i#7 && LitInt(0) <= j#7;
        if (i#7 < X#0)
        {
        }

        assume true;
        assume i#7 < X#0 && j#7 < Y#0;
        assert m1#0 != null;
        assert {:subsumption 0} 0 <= i#7 && i#7 < _System.array2.Length0(m1#0);
        assert {:subsumption 0} 0 <= j#7 && j#7 < _System.array2.Length1(m1#0);
        assume true;
        assert $_Frame[m1#0, MultiIndexField(IndexField(i#7), j#7)];
        assert m#0 != null;
        assert {:subsumption 0} 0 <= j#7 && j#7 < _System.array2.Length0(m#0);
        assert {:subsumption 0} 0 <= i#7 && i#7 < _System.array2.Length1(m#0);
        assume true;
        havoc i#8;
        havoc j#8;
        assume LitInt(0) <= i#8 && LitInt(0) <= j#8;
        assume i#8 < X#0 && j#8 < Y#0;
        assume !(i#7 == i#8 && j#7 == j#8);
        assert m1#0 != m1#0
           || MultiIndexField(IndexField(i#7), j#7) != MultiIndexField(IndexField(i#8), j#8)
           || read($Heap, m#0, MultiIndexField(IndexField(j#7), i#7))
             == read($Heap, m#0, MultiIndexField(IndexField(j#8), i#8));
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
             || (exists i#9: int, j#9: int :: 
              LitInt(0) <= i#9
                 && LitInt(0) <= j#9
                 && 
                i#9 < X#0
                 && j#9 < Y#0
                 && $o == m1#0
                 && $f == MultiIndexField(IndexField(i#9), j#9)));
        assume (forall i#9: int, j#9: int :: 
          LitInt(0) <= i#9 && LitInt(0) <= j#9 && i#9 < X#0 && j#9 < Y#0
             ==> read($Heap, m1#0, MultiIndexField(IndexField(i#9), j#9))
               == read($prevHeap, m#0, MultiIndexField(IndexField(j#9), i#9)));
    }

    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(80,2)"} true;
    // ----- forall statement (assign) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(81,3)
    if (*)
    {
        // Assume Fuel Constant
        havoc i#10;
        havoc j#10;
        assume LitInt(0) <= i#10;
        if (0 - Y#0 < 0 - j#10)
        {
        }

        if (0 - Y#0 < 0 - j#10 && 3 + i#10 < X#0 + 3)
        {
        }

        assume true;
        assume 0 - Y#0 < 0 - j#10 && 3 + i#10 < X#0 + 3 && j#10 >= LitInt(0);
        assert m2#0 != null;
        assert {:subsumption 0} 0 <= i#10 && i#10 < _System.array2.Length0(m2#0);
        assert {:subsumption 0} 0 <= j#10 && j#10 < _System.array2.Length1(m2#0);
        assume true;
        assert $_Frame[m2#0, MultiIndexField(IndexField(i#10), j#10)];
        assert m#0 != null;
        assert {:subsumption 0} 0 <= j#10 && j#10 < _System.array2.Length0(m#0);
        assert {:subsumption 0} 0 <= i#10 && i#10 < _System.array2.Length1(m#0);
        assume true;
        havoc i#11;
        havoc j#11;
        assume LitInt(0) <= i#11;
        assume 0 - Y#0 < 0 - j#11 && 3 + i#11 < X#0 + 3 && j#11 >= LitInt(0);
        assume !(i#10 == i#11 && j#10 == j#11);
        assert m2#0 != m2#0
           || MultiIndexField(IndexField(i#10), j#10)
             != MultiIndexField(IndexField(i#11), j#11)
           || read($Heap, m#0, MultiIndexField(IndexField(j#10), i#10))
             == read($Heap, m#0, MultiIndexField(IndexField(j#11), i#11));
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
             || (exists i#12: int, j#12: int :: 
              LitInt(0) <= i#12
                 && 
                0 - Y#0 < 0 - j#12
                 && 3 + i#12 < X#0 + 3
                 && j#12 >= LitInt(0)
                 && $o == m2#0
                 && $f == MultiIndexField(IndexField(i#12), j#12)));
        assume (forall i#12: int, j#12: int :: 
          LitInt(0) <= i#12
               && 
              0 - Y#0 < 0 - j#12
               && 3 + i#12 < X#0 + 3
               && j#12 >= LitInt(0)
             ==> read($Heap, m2#0, MultiIndexField(IndexField(i#12), j#12))
               == read($prevHeap, m#0, MultiIndexField(IndexField(j#12), i#12)));
    }

    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(83,2)"} true;
}



// function declaration for _module._default.MatrixEqual
function _module.__default.MatrixEqual(_module._default.MatrixEqual$T: Ty, $heap: Heap, m#0: ref, m'#0: ref) : bool;

function _module.__default.MatrixEqual#canCall(_module._default.MatrixEqual$T: Ty, $heap: Heap, m#0: ref, m'#0: ref) : bool;

// frame axiom for _module.__default.MatrixEqual
axiom (forall _module._default.MatrixEqual$T: Ty, $h0: Heap, $h1: Heap, m#0: ref, m'#0: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.__default.MatrixEqual(_module._default.MatrixEqual$T, $h1, m#0, m'#0) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && (_module.__default.MatrixEqual#canCall(_module._default.MatrixEqual$T, $h0, m#0, m'#0)
         || ($Is(m#0, Tclass._System.array2(_module._default.MatrixEqual$T))
           && $Is(m'#0, Tclass._System.array2(_module._default.MatrixEqual$T))))
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && ($o == m#0 || $o == m'#0)
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.__default.MatrixEqual(_module._default.MatrixEqual$T, $h0, m#0, m'#0)
       == _module.__default.MatrixEqual(_module._default.MatrixEqual$T, $h1, m#0, m'#0));

// consequence axiom for _module.__default.MatrixEqual
axiom 9 <= $FunctionContextHeight
   ==> (forall _module._default.MatrixEqual$T: Ty, $Heap: Heap, m#0: ref, m'#0: ref :: 
    { _module.__default.MatrixEqual(_module._default.MatrixEqual$T, $Heap, m#0, m'#0) } 
    _module.__default.MatrixEqual#canCall(_module._default.MatrixEqual$T, $Heap, m#0, m'#0)
         || (9 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(m#0, Tclass._System.array2(_module._default.MatrixEqual$T))
           && $Is(m'#0, Tclass._System.array2(_module._default.MatrixEqual$T)))
       ==> true);

function _module.__default.MatrixEqual#requires(Ty, Heap, ref, ref) : bool;

// #requires axiom for _module.__default.MatrixEqual
axiom (forall _module._default.MatrixEqual$T: Ty, $Heap: Heap, m#0: ref, m'#0: ref :: 
  { _module.__default.MatrixEqual#requires(_module._default.MatrixEqual$T, $Heap, m#0, m'#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && $Is(m#0, Tclass._System.array2(_module._default.MatrixEqual$T))
       && $Is(m'#0, Tclass._System.array2(_module._default.MatrixEqual$T))
     ==> _module.__default.MatrixEqual#requires(_module._default.MatrixEqual$T, $Heap, m#0, m'#0)
       == true);

// definition axiom for _module.__default.MatrixEqual (revealed)
axiom 9 <= $FunctionContextHeight
   ==> (forall _module._default.MatrixEqual$T: Ty, $Heap: Heap, m#0: ref, m'#0: ref :: 
    { _module.__default.MatrixEqual(_module._default.MatrixEqual$T, $Heap, m#0, m'#0), $IsGoodHeap($Heap) } 
    _module.__default.MatrixEqual#canCall(_module._default.MatrixEqual$T, $Heap, m#0, m'#0)
         || (9 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(m#0, Tclass._System.array2(_module._default.MatrixEqual$T))
           && $Is(m'#0, Tclass._System.array2(_module._default.MatrixEqual$T)))
       ==> _module.__default.MatrixEqual(_module._default.MatrixEqual$T, $Heap, m#0, m'#0)
         == (_System.Tuple2#Equal(#_System._tuple#2._#Make2($Box(_System.array2.Length0(m#0)), $Box(_System.array2.Length1(m#0))), 
            #_System._tuple#2._#Make2($Box(_System.array2.Length0(m'#0)), $Box(_System.array2.Length1(m'#0))))
           && (forall i#0: int, j#0: int :: 
            { read($Heap, m'#0, MultiIndexField(IndexField(i#0), j#0)) } 
              { read($Heap, m#0, MultiIndexField(IndexField(i#0), j#0)) } 
            true
               ==> 
              LitInt(0) <= i#0
                 && i#0 < _System.array2.Length0(m#0)
                 && 
                LitInt(0) <= j#0
                 && j#0 < _System.array2.Length1(m#0)
               ==> read($Heap, m#0, MultiIndexField(IndexField(i#0), j#0))
                 == read($Heap, m'#0, MultiIndexField(IndexField(i#0), j#0)))));

procedure CheckWellformed$$_module.__default.MatrixEqual(_module._default.MatrixEqual$T: Ty, 
    m#0: ref where $Is(m#0, Tclass._System.array2(_module._default.MatrixEqual$T)), 
    m'#0: ref where $Is(m'#0, Tclass._System.array2(_module._default.MatrixEqual$T)));
  free requires 9 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.MatrixEqual(_module._default.MatrixEqual$T: Ty, m#0: ref, m'#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var i#1: int;
  var j#1: int;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function MatrixEqual
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(86,17): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == m#0 || $o == m'#0);
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> $o == m#0 || $o == m'#0);
        assert m#0 != null;
        assert m#0 != null;
        assert m'#0 != null;
        assert m'#0 != null;
        if (_System.Tuple2#Equal(#_System._tuple#2._#Make2($Box(_System.array2.Length0(m#0)), $Box(_System.array2.Length1(m#0))), 
          #_System._tuple#2._#Make2($Box(_System.array2.Length0(m'#0)), $Box(_System.array2.Length1(m'#0)))))
        {
            // Begin Comprehension WF check
            havoc i#1;
            havoc j#1;
            if (true)
            {
                if (LitInt(0) <= i#1)
                {
                    assert m#0 != null;
                }

                if (LitInt(0) <= i#1 && i#1 < _System.array2.Length0(m#0))
                {
                    if (LitInt(0) <= j#1)
                    {
                        assert m#0 != null;
                    }
                }

                if (LitInt(0) <= i#1
                   && i#1 < _System.array2.Length0(m#0)
                   && 
                  LitInt(0) <= j#1
                   && j#1 < _System.array2.Length1(m#0))
                {
                    assert m#0 != null;
                    assert 0 <= i#1 && i#1 < _System.array2.Length0(m#0);
                    assert 0 <= j#1 && j#1 < _System.array2.Length1(m#0);
                    b$reqreads#0 := $_Frame[m#0, MultiIndexField(IndexField(i#1), j#1)];
                    assert m'#0 != null;
                    assert 0 <= i#1 && i#1 < _System.array2.Length0(m'#0);
                    assert 0 <= j#1 && j#1 < _System.array2.Length1(m'#0);
                    b$reqreads#1 := $_Frame[m'#0, MultiIndexField(IndexField(i#1), j#1)];
                }
            }

            // End Comprehension WF check
        }

        assume _module.__default.MatrixEqual(_module._default.MatrixEqual$T, $Heap, m#0, m'#0)
           == (_System.Tuple2#Equal(#_System._tuple#2._#Make2($Box(_System.array2.Length0(m#0)), $Box(_System.array2.Length1(m#0))), 
              #_System._tuple#2._#Make2($Box(_System.array2.Length0(m'#0)), $Box(_System.array2.Length1(m'#0))))
             && (forall i#2: int, j#2: int :: 
              { read($Heap, m'#0, MultiIndexField(IndexField(i#2), j#2)) } 
                { read($Heap, m#0, MultiIndexField(IndexField(i#2), j#2)) } 
              true
                 ==> 
                LitInt(0) <= i#2
                   && i#2 < _System.array2.Length0(m#0)
                   && 
                  LitInt(0) <= j#2
                   && j#2 < _System.array2.Length1(m#0)
                 ==> read($Heap, m#0, MultiIndexField(IndexField(i#2), j#2))
                   == read($Heap, m'#0, MultiIndexField(IndexField(i#2), j#2))));
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.MatrixEqual(_module._default.MatrixEqual$T, $Heap, m#0, m'#0), 
          TBool);
        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



procedure CheckWellformed$$_module.__default.TestAggregateFieldUpdate();
  free requires 17 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.TestAggregateFieldUpdate();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.TestAggregateFieldUpdate() returns ($_reverifyPost: bool);
  free requires 17 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.TestAggregateFieldUpdate() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var a#0: ref
     where $Is(a#0, Tclass._module.Node()) && $IsAlloc(a#0, Tclass._module.Node(), $Heap);
  var $rhs##0: ref
     where $Is($rhs##0, Tclass._module.Node())
       && $IsAlloc($rhs##0, Tclass._module.Node(), $Heap);
  var n##0: int;
  var b#0: ref
     where $Is(b#0, Tclass._module.Node()) && $IsAlloc(b#0, Tclass._module.Node(), $Heap);
  var $rhs##1: ref
     where $Is($rhs##1, Tclass._module.Node())
       && $IsAlloc($rhs##1, Tclass._module.Node(), $Heap);
  var n##1: int;
  var ##that#0: ref;
  var n##2: int;
  var ##that#1: ref;

    // AddMethodImpl: TestAggregateFieldUpdate, Impl$$_module.__default.TestAggregateFieldUpdate
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(95,34): initial state"} true;
    $_reverifyPost := false;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(96,23)
    assume true;
    // TrCallStmt: Adding lhs with type Node
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    assert $Is(LitInt(4), Tclass._System.nat());
    n##0 := LitInt(4);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0 := Call$$_module.Node.Create(n##0);
    // TrCallStmt: After ProcessCallStmt
    a#0 := $rhs##0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(96,25)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(97,23)
    assume true;
    // TrCallStmt: Adding lhs with type Node
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    assert $Is(LitInt(7), Tclass._System.nat());
    n##1 := LitInt(7);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##1 := Call$$_module.Node.Create(n##1);
    // TrCallStmt: After ProcessCallStmt
    b#0 := $rhs##1;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(97,25)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(98,10)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert a#0 != null;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.Node.Print(a#0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(98,11)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(99,10)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert b#0 != null;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.Node.Print(b#0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(99,11)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(101,3)
    assert {:subsumption 0} b#0 != null;
    ##that#0 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##that#0, Tclass._module.Node?(), $Heap);
    assert {:subsumption 0} _module.Node.Valid#canCall($Heap, b#0)
       ==> _module.Node.Valid($LS($LZ), $Heap, b#0)
         || read($Heap, b#0, _module.Node.Repr)[$Box(b#0)];
    assert {:subsumption 0} _module.Node.Valid#canCall($Heap, b#0)
       ==> _module.Node.Valid($LS($LZ), $Heap, b#0)
         || (read($Heap, b#0, _module.Node.next) != null
           ==> read($Heap, b#0, _module.Node.Repr)[$Box(read($Heap, b#0, _module.Node.next))]);
    assert {:subsumption 0} _module.Node.Valid#canCall($Heap, b#0)
       ==> _module.Node.Valid($LS($LZ), $Heap, b#0)
         || (read($Heap, b#0, _module.Node.next) != null
           ==> Set#Subset(read($Heap, read($Heap, b#0, _module.Node.next), _module.Node.Repr), 
            read($Heap, b#0, _module.Node.Repr)));
    assert {:subsumption 0} _module.Node.Valid#canCall($Heap, b#0)
       ==> _module.Node.Valid($LS($LZ), $Heap, b#0)
         || (read($Heap, b#0, _module.Node.next) != null
           ==> !read($Heap, read($Heap, b#0, _module.Node.next), _module.Node.Repr)[$Box(b#0)]);
    assert {:subsumption 0} _module.Node.Valid#canCall($Heap, b#0)
       ==> _module.Node.Valid($LS($LZ), $Heap, b#0)
         || (read($Heap, b#0, _module.Node.next) != null
           ==> _module.Node.Valid($LS($LS($LZ)), $Heap, read($Heap, b#0, _module.Node.next)));
    assert {:subsumption 0} ##that#0 != null
       ==> 
      _module.Node.Valid#canCall($Heap, ##that#0)
       ==> _module.Node.Valid($LS($LZ), $Heap, ##that#0)
         || read($Heap, ##that#0, _module.Node.Repr)[$Box(##that#0)];
    assert {:subsumption 0} ##that#0 != null
       ==> 
      _module.Node.Valid#canCall($Heap, ##that#0)
       ==> _module.Node.Valid($LS($LZ), $Heap, ##that#0)
         || (read($Heap, ##that#0, _module.Node.next) != null
           ==> read($Heap, ##that#0, _module.Node.Repr)[$Box(read($Heap, ##that#0, _module.Node.next))]);
    assert {:subsumption 0} ##that#0 != null
       ==> 
      _module.Node.Valid#canCall($Heap, ##that#0)
       ==> _module.Node.Valid($LS($LZ), $Heap, ##that#0)
         || (read($Heap, ##that#0, _module.Node.next) != null
           ==> Set#Subset(read($Heap, read($Heap, ##that#0, _module.Node.next), _module.Node.Repr), 
            read($Heap, ##that#0, _module.Node.Repr)));
    assert {:subsumption 0} ##that#0 != null
       ==> 
      _module.Node.Valid#canCall($Heap, ##that#0)
       ==> _module.Node.Valid($LS($LZ), $Heap, ##that#0)
         || (read($Heap, ##that#0, _module.Node.next) != null
           ==> !read($Heap, read($Heap, ##that#0, _module.Node.next), _module.Node.Repr)[$Box(##that#0)]);
    assert {:subsumption 0} ##that#0 != null
       ==> 
      _module.Node.Valid#canCall($Heap, ##that#0)
       ==> _module.Node.Valid($LS($LZ), $Heap, ##that#0)
         || (read($Heap, ##that#0, _module.Node.next) != null
           ==> _module.Node.Valid($LS($LS($LZ)), $Heap, read($Heap, ##that#0, _module.Node.next)));
    assume _module.Node.StartsWith#canCall($Heap, b#0, a#0);
    assume _module.Node.StartsWith#canCall($Heap, b#0, a#0);
    assume true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(103,18)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert a#0 != null;
    assume true;
    // ProcessCallStmt: CheckSubrange
    n##2 := LitInt(3);
    assert (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && read($Heap, $o, alloc)
           && read($Heap, a#0, _module.Node.Repr)[$Box($o)]
         ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.Node.IncEverything(a#0, n##2);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(103,20)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(104,10)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert a#0 != null;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.Node.Print(a#0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(104,11)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/MoForallCompilation.dfy(105,3)
    assert {:subsumption 0} b#0 != null;
    ##that#1 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##that#1, Tclass._module.Node?(), $Heap);
    assert {:subsumption 0} _module.Node.Valid#canCall($Heap, b#0)
       ==> _module.Node.Valid($LS($LZ), $Heap, b#0)
         || read($Heap, b#0, _module.Node.Repr)[$Box(b#0)];
    assert {:subsumption 0} _module.Node.Valid#canCall($Heap, b#0)
       ==> _module.Node.Valid($LS($LZ), $Heap, b#0)
         || (read($Heap, b#0, _module.Node.next) != null
           ==> read($Heap, b#0, _module.Node.Repr)[$Box(read($Heap, b#0, _module.Node.next))]);
    assert {:subsumption 0} _module.Node.Valid#canCall($Heap, b#0)
       ==> _module.Node.Valid($LS($LZ), $Heap, b#0)
         || (read($Heap, b#0, _module.Node.next) != null
           ==> Set#Subset(read($Heap, read($Heap, b#0, _module.Node.next), _module.Node.Repr), 
            read($Heap, b#0, _module.Node.Repr)));
    assert {:subsumption 0} _module.Node.Valid#canCall($Heap, b#0)
       ==> _module.Node.Valid($LS($LZ), $Heap, b#0)
         || (read($Heap, b#0, _module.Node.next) != null
           ==> !read($Heap, read($Heap, b#0, _module.Node.next), _module.Node.Repr)[$Box(b#0)]);
    assert {:subsumption 0} _module.Node.Valid#canCall($Heap, b#0)
       ==> _module.Node.Valid($LS($LZ), $Heap, b#0)
         || (read($Heap, b#0, _module.Node.next) != null
           ==> _module.Node.Valid($LS($LS($LZ)), $Heap, read($Heap, b#0, _module.Node.next)));
    assert {:subsumption 0} ##that#1 != null
       ==> 
      _module.Node.Valid#canCall($Heap, ##that#1)
       ==> _module.Node.Valid($LS($LZ), $Heap, ##that#1)
         || read($Heap, ##that#1, _module.Node.Repr)[$Box(##that#1)];
    assert {:subsumption 0} ##that#1 != null
       ==> 
      _module.Node.Valid#canCall($Heap, ##that#1)
       ==> _module.Node.Valid($LS($LZ), $Heap, ##that#1)
         || (read($Heap, ##that#1, _module.Node.next) != null
           ==> read($Heap, ##that#1, _module.Node.Repr)[$Box(read($Heap, ##that#1, _module.Node.next))]);
    assert {:subsumption 0} ##that#1 != null
       ==> 
      _module.Node.Valid#canCall($Heap, ##that#1)
       ==> _module.Node.Valid($LS($LZ), $Heap, ##that#1)
         || (read($Heap, ##that#1, _module.Node.next) != null
           ==> Set#Subset(read($Heap, read($Heap, ##that#1, _module.Node.next), _module.Node.Repr), 
            read($Heap, ##that#1, _module.Node.Repr)));
    assert {:subsumption 0} ##that#1 != null
       ==> 
      _module.Node.Valid#canCall($Heap, ##that#1)
       ==> _module.Node.Valid($LS($LZ), $Heap, ##that#1)
         || (read($Heap, ##that#1, _module.Node.next) != null
           ==> !read($Heap, read($Heap, ##that#1, _module.Node.next), _module.Node.Repr)[$Box(##that#1)]);
    assert {:subsumption 0} ##that#1 != null
       ==> 
      _module.Node.Valid#canCall($Heap, ##that#1)
       ==> _module.Node.Valid($LS($LZ), $Heap, ##that#1)
         || (read($Heap, ##that#1, _module.Node.next) != null
           ==> _module.Node.Valid($LS($LS($LZ)), $Heap, read($Heap, ##that#1, _module.Node.next)));
    assume _module.Node.StartsWith#canCall($Heap, b#0, a#0);
    assume _module.Node.StartsWith#canCall($Heap, b#0, a#0);
    assume true;
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

const unique tytagFamily$array2: TyTagFamily;

const unique tytagFamily$_#Func2: TyTagFamily;

const unique tytagFamily$_#PartialFunc2: TyTagFamily;

const unique tytagFamily$_#TotalFunc2: TyTagFamily;

const unique tytagFamily$_tuple#2: TyTagFamily;

const unique tytagFamily$_tuple#0: TyTagFamily;

const unique tytagFamily$Node: TyTagFamily;

const unique tytagFamily$_default: TyTagFamily;

const unique field$Repr: NameFamily;

const unique field$next: NameFamily;

const unique field$val: NameFamily;
