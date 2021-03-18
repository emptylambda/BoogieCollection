// Dafny 3.0.0.30204
// Command Line Options: -compile:0 -noVerify /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy -print:./SoftwareFoundations-Basics.bpl

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
function #_module.day.monday() : DatatypeType;

const unique ##_module.day.monday: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#_module.day.monday()) == ##_module.day.monday;

function _module.day.monday_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.day.monday_q(d) } 
  _module.day.monday_q(d) <==> DatatypeCtorId(d) == ##_module.day.monday);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.day.monday_q(d) } 
  _module.day.monday_q(d) ==> d == #_module.day.monday());

function Tclass._module.day() : Ty;

const unique Tagclass._module.day: TyTag;

// Tclass._module.day Tag
axiom Tag(Tclass._module.day()) == Tagclass._module.day
   && TagFamily(Tclass._module.day()) == tytagFamily$day;

// Box/unbox axiom for Tclass._module.day
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.day()) } 
  $IsBox(bx, Tclass._module.day())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.day()));

// Constructor $Is
axiom $Is(#_module.day.monday(), Tclass._module.day());

// Constructor $IsAlloc
axiom (forall $h: Heap :: 
  { $IsAlloc(#_module.day.monday(), Tclass._module.day(), $h) } 
  $IsGoodHeap($h) ==> $IsAlloc(#_module.day.monday(), Tclass._module.day(), $h));

// Constructor literal
axiom #_module.day.monday() == Lit(#_module.day.monday());

// Constructor function declaration
function #_module.day.tuesday() : DatatypeType;

const unique ##_module.day.tuesday: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#_module.day.tuesday()) == ##_module.day.tuesday;

function _module.day.tuesday_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.day.tuesday_q(d) } 
  _module.day.tuesday_q(d) <==> DatatypeCtorId(d) == ##_module.day.tuesday);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.day.tuesday_q(d) } 
  _module.day.tuesday_q(d) ==> d == #_module.day.tuesday());

// Constructor $Is
axiom $Is(#_module.day.tuesday(), Tclass._module.day());

// Constructor $IsAlloc
axiom (forall $h: Heap :: 
  { $IsAlloc(#_module.day.tuesday(), Tclass._module.day(), $h) } 
  $IsGoodHeap($h) ==> $IsAlloc(#_module.day.tuesday(), Tclass._module.day(), $h));

// Constructor literal
axiom #_module.day.tuesday() == Lit(#_module.day.tuesday());

// Constructor function declaration
function #_module.day.wednesday() : DatatypeType;

const unique ##_module.day.wednesday: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#_module.day.wednesday()) == ##_module.day.wednesday;

function _module.day.wednesday_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.day.wednesday_q(d) } 
  _module.day.wednesday_q(d) <==> DatatypeCtorId(d) == ##_module.day.wednesday);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.day.wednesday_q(d) } 
  _module.day.wednesday_q(d) ==> d == #_module.day.wednesday());

// Constructor $Is
axiom $Is(#_module.day.wednesday(), Tclass._module.day());

// Constructor $IsAlloc
axiom (forall $h: Heap :: 
  { $IsAlloc(#_module.day.wednesday(), Tclass._module.day(), $h) } 
  $IsGoodHeap($h) ==> $IsAlloc(#_module.day.wednesday(), Tclass._module.day(), $h));

// Constructor literal
axiom #_module.day.wednesday() == Lit(#_module.day.wednesday());

// Constructor function declaration
function #_module.day.thursday() : DatatypeType;

const unique ##_module.day.thursday: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#_module.day.thursday()) == ##_module.day.thursday;

function _module.day.thursday_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.day.thursday_q(d) } 
  _module.day.thursday_q(d) <==> DatatypeCtorId(d) == ##_module.day.thursday);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.day.thursday_q(d) } 
  _module.day.thursday_q(d) ==> d == #_module.day.thursday());

// Constructor $Is
axiom $Is(#_module.day.thursday(), Tclass._module.day());

// Constructor $IsAlloc
axiom (forall $h: Heap :: 
  { $IsAlloc(#_module.day.thursday(), Tclass._module.day(), $h) } 
  $IsGoodHeap($h) ==> $IsAlloc(#_module.day.thursday(), Tclass._module.day(), $h));

// Constructor literal
axiom #_module.day.thursday() == Lit(#_module.day.thursday());

// Constructor function declaration
function #_module.day.friday() : DatatypeType;

const unique ##_module.day.friday: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#_module.day.friday()) == ##_module.day.friday;

function _module.day.friday_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.day.friday_q(d) } 
  _module.day.friday_q(d) <==> DatatypeCtorId(d) == ##_module.day.friday);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.day.friday_q(d) } 
  _module.day.friday_q(d) ==> d == #_module.day.friday());

// Constructor $Is
axiom $Is(#_module.day.friday(), Tclass._module.day());

// Constructor $IsAlloc
axiom (forall $h: Heap :: 
  { $IsAlloc(#_module.day.friday(), Tclass._module.day(), $h) } 
  $IsGoodHeap($h) ==> $IsAlloc(#_module.day.friday(), Tclass._module.day(), $h));

// Constructor literal
axiom #_module.day.friday() == Lit(#_module.day.friday());

// Constructor function declaration
function #_module.day.saturday() : DatatypeType;

const unique ##_module.day.saturday: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#_module.day.saturday()) == ##_module.day.saturday;

function _module.day.saturday_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.day.saturday_q(d) } 
  _module.day.saturday_q(d) <==> DatatypeCtorId(d) == ##_module.day.saturday);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.day.saturday_q(d) } 
  _module.day.saturday_q(d) ==> d == #_module.day.saturday());

// Constructor $Is
axiom $Is(#_module.day.saturday(), Tclass._module.day());

// Constructor $IsAlloc
axiom (forall $h: Heap :: 
  { $IsAlloc(#_module.day.saturday(), Tclass._module.day(), $h) } 
  $IsGoodHeap($h) ==> $IsAlloc(#_module.day.saturday(), Tclass._module.day(), $h));

// Constructor literal
axiom #_module.day.saturday() == Lit(#_module.day.saturday());

// Constructor function declaration
function #_module.day.sunday() : DatatypeType;

const unique ##_module.day.sunday: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#_module.day.sunday()) == ##_module.day.sunday;

function _module.day.sunday_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.day.sunday_q(d) } 
  _module.day.sunday_q(d) <==> DatatypeCtorId(d) == ##_module.day.sunday);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.day.sunday_q(d) } 
  _module.day.sunday_q(d) ==> d == #_module.day.sunday());

// Constructor $Is
axiom $Is(#_module.day.sunday(), Tclass._module.day());

// Constructor $IsAlloc
axiom (forall $h: Heap :: 
  { $IsAlloc(#_module.day.sunday(), Tclass._module.day(), $h) } 
  $IsGoodHeap($h) ==> $IsAlloc(#_module.day.sunday(), Tclass._module.day(), $h));

// Constructor literal
axiom #_module.day.sunday() == Lit(#_module.day.sunday());

// Depth-one case-split function
function $IsA#_module.day(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.day(d) } 
  $IsA#_module.day(d)
     ==> _module.day.monday_q(d)
       || _module.day.tuesday_q(d)
       || _module.day.wednesday_q(d)
       || _module.day.thursday_q(d)
       || _module.day.friday_q(d)
       || _module.day.saturday_q(d)
       || _module.day.sunday_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.day.sunday_q(d), $Is(d, Tclass._module.day()) } 
    { _module.day.saturday_q(d), $Is(d, Tclass._module.day()) } 
    { _module.day.friday_q(d), $Is(d, Tclass._module.day()) } 
    { _module.day.thursday_q(d), $Is(d, Tclass._module.day()) } 
    { _module.day.wednesday_q(d), $Is(d, Tclass._module.day()) } 
    { _module.day.tuesday_q(d), $Is(d, Tclass._module.day()) } 
    { _module.day.monday_q(d), $Is(d, Tclass._module.day()) } 
  $Is(d, Tclass._module.day())
     ==> _module.day.monday_q(d)
       || _module.day.tuesday_q(d)
       || _module.day.wednesday_q(d)
       || _module.day.thursday_q(d)
       || _module.day.friday_q(d)
       || _module.day.saturday_q(d)
       || _module.day.sunday_q(d));

// Datatype extensional equality declaration
function _module.day#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.day.monday
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.day#Equal(a, b), _module.day.monday_q(a) } 
    { _module.day#Equal(a, b), _module.day.monday_q(b) } 
  _module.day.monday_q(a) && _module.day.monday_q(b)
     ==> (_module.day#Equal(a, b) <==> true));

// Datatype extensional equality definition: #_module.day.tuesday
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.day#Equal(a, b), _module.day.tuesday_q(a) } 
    { _module.day#Equal(a, b), _module.day.tuesday_q(b) } 
  _module.day.tuesday_q(a) && _module.day.tuesday_q(b)
     ==> (_module.day#Equal(a, b) <==> true));

// Datatype extensional equality definition: #_module.day.wednesday
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.day#Equal(a, b), _module.day.wednesday_q(a) } 
    { _module.day#Equal(a, b), _module.day.wednesday_q(b) } 
  _module.day.wednesday_q(a) && _module.day.wednesday_q(b)
     ==> (_module.day#Equal(a, b) <==> true));

// Datatype extensional equality definition: #_module.day.thursday
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.day#Equal(a, b), _module.day.thursday_q(a) } 
    { _module.day#Equal(a, b), _module.day.thursday_q(b) } 
  _module.day.thursday_q(a) && _module.day.thursday_q(b)
     ==> (_module.day#Equal(a, b) <==> true));

// Datatype extensional equality definition: #_module.day.friday
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.day#Equal(a, b), _module.day.friday_q(a) } 
    { _module.day#Equal(a, b), _module.day.friday_q(b) } 
  _module.day.friday_q(a) && _module.day.friday_q(b)
     ==> (_module.day#Equal(a, b) <==> true));

// Datatype extensional equality definition: #_module.day.saturday
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.day#Equal(a, b), _module.day.saturday_q(a) } 
    { _module.day#Equal(a, b), _module.day.saturday_q(b) } 
  _module.day.saturday_q(a) && _module.day.saturday_q(b)
     ==> (_module.day#Equal(a, b) <==> true));

// Datatype extensional equality definition: #_module.day.sunday
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.day#Equal(a, b), _module.day.sunday_q(a) } 
    { _module.day#Equal(a, b), _module.day.sunday_q(b) } 
  _module.day.sunday_q(a) && _module.day.sunday_q(b)
     ==> (_module.day#Equal(a, b) <==> true));

// Datatype extensionality axiom: _module.day
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.day#Equal(a, b) } 
  _module.day#Equal(a, b) <==> a == b);

const unique class._module.day: ClassName;

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
axiom $Is(#_module.Bool.True(), Tclass._module.Bool());

// Constructor $IsAlloc
axiom (forall $h: Heap :: 
  { $IsAlloc(#_module.Bool.True(), Tclass._module.Bool(), $h) } 
  $IsGoodHeap($h) ==> $IsAlloc(#_module.Bool.True(), Tclass._module.Bool(), $h));

// Constructor literal
axiom #_module.Bool.True() == Lit(#_module.Bool.True());

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

// Constructor $Is
axiom $Is(#_module.Bool.False(), Tclass._module.Bool());

// Constructor $IsAlloc
axiom (forall $h: Heap :: 
  { $IsAlloc(#_module.Bool.False(), Tclass._module.Bool(), $h) } 
  $IsGoodHeap($h) ==> $IsAlloc(#_module.Bool.False(), Tclass._module.Bool(), $h));

// Constructor literal
axiom #_module.Bool.False() == Lit(#_module.Bool.False());

// Depth-one case-split function
function $IsA#_module.Bool(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.Bool(d) } 
  $IsA#_module.Bool(d) ==> _module.Bool.True_q(d) || _module.Bool.False_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.Bool.False_q(d), $Is(d, Tclass._module.Bool()) } 
    { _module.Bool.True_q(d), $Is(d, Tclass._module.Bool()) } 
  $Is(d, Tclass._module.Bool())
     ==> _module.Bool.True_q(d) || _module.Bool.False_q(d));

// Datatype extensional equality declaration
function _module.Bool#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.Bool.True
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Bool#Equal(a, b), _module.Bool.True_q(a) } 
    { _module.Bool#Equal(a, b), _module.Bool.True_q(b) } 
  _module.Bool.True_q(a) && _module.Bool.True_q(b)
     ==> (_module.Bool#Equal(a, b) <==> true));

// Datatype extensional equality definition: #_module.Bool.False
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Bool#Equal(a, b), _module.Bool.False_q(a) } 
    { _module.Bool#Equal(a, b), _module.Bool.False_q(b) } 
  _module.Bool.False_q(a) && _module.Bool.False_q(b)
     ==> (_module.Bool#Equal(a, b) <==> true));

// Datatype extensionality axiom: _module.Bool
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Bool#Equal(a, b) } 
  _module.Bool#Equal(a, b) <==> a == b);

const unique class._module.Bool: ClassName;

// Constructor function declaration
function #_module.Nat.O() : DatatypeType;

const unique ##_module.Nat.O: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#_module.Nat.O()) == ##_module.Nat.O;

function _module.Nat.O_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Nat.O_q(d) } 
  _module.Nat.O_q(d) <==> DatatypeCtorId(d) == ##_module.Nat.O);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Nat.O_q(d) } 
  _module.Nat.O_q(d) ==> d == #_module.Nat.O());

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
axiom $Is(#_module.Nat.O(), Tclass._module.Nat());

// Constructor $IsAlloc
axiom (forall $h: Heap :: 
  { $IsAlloc(#_module.Nat.O(), Tclass._module.Nat(), $h) } 
  $IsGoodHeap($h) ==> $IsAlloc(#_module.Nat.O(), Tclass._module.Nat(), $h));

// Constructor literal
axiom #_module.Nat.O() == Lit(#_module.Nat.O());

// Constructor function declaration
function #_module.Nat.S(DatatypeType) : DatatypeType;

const unique ##_module.Nat.S: DtCtorId;

// Constructor identifier
axiom (forall a#64#0#0: DatatypeType :: 
  { #_module.Nat.S(a#64#0#0) } 
  DatatypeCtorId(#_module.Nat.S(a#64#0#0)) == ##_module.Nat.S);

function _module.Nat.S_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Nat.S_q(d) } 
  _module.Nat.S_q(d) <==> DatatypeCtorId(d) == ##_module.Nat.S);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Nat.S_q(d) } 
  _module.Nat.S_q(d)
     ==> (exists a#65#0#0: DatatypeType :: d == #_module.Nat.S(a#65#0#0)));

// Constructor $Is
axiom (forall a#66#0#0: DatatypeType :: 
  { $Is(#_module.Nat.S(a#66#0#0), Tclass._module.Nat()) } 
  $Is(#_module.Nat.S(a#66#0#0), Tclass._module.Nat())
     <==> $Is(a#66#0#0, Tclass._module.Nat()));

// Constructor $IsAlloc
axiom (forall a#67#0#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#_module.Nat.S(a#67#0#0), Tclass._module.Nat(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Nat.S(a#67#0#0), Tclass._module.Nat(), $h)
       <==> $IsAlloc(a#67#0#0, Tclass._module.Nat(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Nat._h0(d), Tclass._module.Nat(), $h) } 
  $IsGoodHeap($h) && _module.Nat.S_q(d) && $IsAlloc(d, Tclass._module.Nat(), $h)
     ==> $IsAlloc(_module.Nat._h0(d), Tclass._module.Nat(), $h));

// Constructor literal
axiom (forall a#68#0#0: DatatypeType :: 
  { #_module.Nat.S(Lit(a#68#0#0)) } 
  #_module.Nat.S(Lit(a#68#0#0)) == Lit(#_module.Nat.S(a#68#0#0)));

function _module.Nat._h0(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#69#0#0: DatatypeType :: 
  { #_module.Nat.S(a#69#0#0) } 
  _module.Nat._h0(#_module.Nat.S(a#69#0#0)) == a#69#0#0);

// Inductive rank
axiom (forall a#70#0#0: DatatypeType :: 
  { #_module.Nat.S(a#70#0#0) } 
  DtRank(a#70#0#0) < DtRank(#_module.Nat.S(a#70#0#0)));

// Depth-one case-split function
function $IsA#_module.Nat(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.Nat(d) } 
  $IsA#_module.Nat(d) ==> _module.Nat.O_q(d) || _module.Nat.S_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.Nat.S_q(d), $Is(d, Tclass._module.Nat()) } 
    { _module.Nat.O_q(d), $Is(d, Tclass._module.Nat()) } 
  $Is(d, Tclass._module.Nat()) ==> _module.Nat.O_q(d) || _module.Nat.S_q(d));

// Datatype extensional equality declaration
function _module.Nat#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.Nat.O
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Nat#Equal(a, b), _module.Nat.O_q(a) } 
    { _module.Nat#Equal(a, b), _module.Nat.O_q(b) } 
  _module.Nat.O_q(a) && _module.Nat.O_q(b) ==> (_module.Nat#Equal(a, b) <==> true));

// Datatype extensional equality definition: #_module.Nat.S
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Nat#Equal(a, b), _module.Nat.S_q(a) } 
    { _module.Nat#Equal(a, b), _module.Nat.S_q(b) } 
  _module.Nat.S_q(a) && _module.Nat.S_q(b)
     ==> (_module.Nat#Equal(a, b)
       <==> _module.Nat#Equal(_module.Nat._h0(a), _module.Nat._h0(b))));

// Datatype extensionality axiom: _module.Nat
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Nat#Equal(a, b) } 
  _module.Nat#Equal(a, b) <==> a == b);

const unique class._module.Nat: ClassName;

// Constructor function declaration
function #_module.bin.Zero() : DatatypeType;

const unique ##_module.bin.Zero: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#_module.bin.Zero()) == ##_module.bin.Zero;

function _module.bin.Zero_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.bin.Zero_q(d) } 
  _module.bin.Zero_q(d) <==> DatatypeCtorId(d) == ##_module.bin.Zero);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.bin.Zero_q(d) } 
  _module.bin.Zero_q(d) ==> d == #_module.bin.Zero());

function Tclass._module.bin() : Ty;

const unique Tagclass._module.bin: TyTag;

// Tclass._module.bin Tag
axiom Tag(Tclass._module.bin()) == Tagclass._module.bin
   && TagFamily(Tclass._module.bin()) == tytagFamily$bin;

// Box/unbox axiom for Tclass._module.bin
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.bin()) } 
  $IsBox(bx, Tclass._module.bin())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.bin()));

// Constructor $Is
axiom $Is(#_module.bin.Zero(), Tclass._module.bin());

// Constructor $IsAlloc
axiom (forall $h: Heap :: 
  { $IsAlloc(#_module.bin.Zero(), Tclass._module.bin(), $h) } 
  $IsGoodHeap($h) ==> $IsAlloc(#_module.bin.Zero(), Tclass._module.bin(), $h));

// Constructor literal
axiom #_module.bin.Zero() == Lit(#_module.bin.Zero());

// Constructor function declaration
function #_module.bin.Twice(DatatypeType) : DatatypeType;

const unique ##_module.bin.Twice: DtCtorId;

// Constructor identifier
axiom (forall a#76#0#0: DatatypeType :: 
  { #_module.bin.Twice(a#76#0#0) } 
  DatatypeCtorId(#_module.bin.Twice(a#76#0#0)) == ##_module.bin.Twice);

function _module.bin.Twice_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.bin.Twice_q(d) } 
  _module.bin.Twice_q(d) <==> DatatypeCtorId(d) == ##_module.bin.Twice);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.bin.Twice_q(d) } 
  _module.bin.Twice_q(d)
     ==> (exists a#77#0#0: DatatypeType :: d == #_module.bin.Twice(a#77#0#0)));

// Constructor $Is
axiom (forall a#78#0#0: DatatypeType :: 
  { $Is(#_module.bin.Twice(a#78#0#0), Tclass._module.bin()) } 
  $Is(#_module.bin.Twice(a#78#0#0), Tclass._module.bin())
     <==> $Is(a#78#0#0, Tclass._module.bin()));

// Constructor $IsAlloc
axiom (forall a#79#0#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#_module.bin.Twice(a#79#0#0), Tclass._module.bin(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.bin.Twice(a#79#0#0), Tclass._module.bin(), $h)
       <==> $IsAlloc(a#79#0#0, Tclass._module.bin(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.bin._h1(d), Tclass._module.bin(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.bin.Twice_q(d)
       && $IsAlloc(d, Tclass._module.bin(), $h)
     ==> $IsAlloc(_module.bin._h1(d), Tclass._module.bin(), $h));

// Constructor literal
axiom (forall a#80#0#0: DatatypeType :: 
  { #_module.bin.Twice(Lit(a#80#0#0)) } 
  #_module.bin.Twice(Lit(a#80#0#0)) == Lit(#_module.bin.Twice(a#80#0#0)));

function _module.bin._h1(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#81#0#0: DatatypeType :: 
  { #_module.bin.Twice(a#81#0#0) } 
  _module.bin._h1(#_module.bin.Twice(a#81#0#0)) == a#81#0#0);

// Inductive rank
axiom (forall a#82#0#0: DatatypeType :: 
  { #_module.bin.Twice(a#82#0#0) } 
  DtRank(a#82#0#0) < DtRank(#_module.bin.Twice(a#82#0#0)));

// Constructor function declaration
function #_module.bin.TwicePlusOne(DatatypeType) : DatatypeType;

const unique ##_module.bin.TwicePlusOne: DtCtorId;

// Constructor identifier
axiom (forall a#83#0#0: DatatypeType :: 
  { #_module.bin.TwicePlusOne(a#83#0#0) } 
  DatatypeCtorId(#_module.bin.TwicePlusOne(a#83#0#0))
     == ##_module.bin.TwicePlusOne);

function _module.bin.TwicePlusOne_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.bin.TwicePlusOne_q(d) } 
  _module.bin.TwicePlusOne_q(d)
     <==> DatatypeCtorId(d) == ##_module.bin.TwicePlusOne);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.bin.TwicePlusOne_q(d) } 
  _module.bin.TwicePlusOne_q(d)
     ==> (exists a#84#0#0: DatatypeType :: d == #_module.bin.TwicePlusOne(a#84#0#0)));

// Constructor $Is
axiom (forall a#85#0#0: DatatypeType :: 
  { $Is(#_module.bin.TwicePlusOne(a#85#0#0), Tclass._module.bin()) } 
  $Is(#_module.bin.TwicePlusOne(a#85#0#0), Tclass._module.bin())
     <==> $Is(a#85#0#0, Tclass._module.bin()));

// Constructor $IsAlloc
axiom (forall a#86#0#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#_module.bin.TwicePlusOne(a#86#0#0), Tclass._module.bin(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.bin.TwicePlusOne(a#86#0#0), Tclass._module.bin(), $h)
       <==> $IsAlloc(a#86#0#0, Tclass._module.bin(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.bin._h2(d), Tclass._module.bin(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.bin.TwicePlusOne_q(d)
       && $IsAlloc(d, Tclass._module.bin(), $h)
     ==> $IsAlloc(_module.bin._h2(d), Tclass._module.bin(), $h));

// Constructor literal
axiom (forall a#87#0#0: DatatypeType :: 
  { #_module.bin.TwicePlusOne(Lit(a#87#0#0)) } 
  #_module.bin.TwicePlusOne(Lit(a#87#0#0))
     == Lit(#_module.bin.TwicePlusOne(a#87#0#0)));

function _module.bin._h2(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#88#0#0: DatatypeType :: 
  { #_module.bin.TwicePlusOne(a#88#0#0) } 
  _module.bin._h2(#_module.bin.TwicePlusOne(a#88#0#0)) == a#88#0#0);

// Inductive rank
axiom (forall a#89#0#0: DatatypeType :: 
  { #_module.bin.TwicePlusOne(a#89#0#0) } 
  DtRank(a#89#0#0) < DtRank(#_module.bin.TwicePlusOne(a#89#0#0)));

// Depth-one case-split function
function $IsA#_module.bin(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.bin(d) } 
  $IsA#_module.bin(d)
     ==> _module.bin.Zero_q(d) || _module.bin.Twice_q(d) || _module.bin.TwicePlusOne_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.bin.TwicePlusOne_q(d), $Is(d, Tclass._module.bin()) } 
    { _module.bin.Twice_q(d), $Is(d, Tclass._module.bin()) } 
    { _module.bin.Zero_q(d), $Is(d, Tclass._module.bin()) } 
  $Is(d, Tclass._module.bin())
     ==> _module.bin.Zero_q(d) || _module.bin.Twice_q(d) || _module.bin.TwicePlusOne_q(d));

// Datatype extensional equality declaration
function _module.bin#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.bin.Zero
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.bin#Equal(a, b), _module.bin.Zero_q(a) } 
    { _module.bin#Equal(a, b), _module.bin.Zero_q(b) } 
  _module.bin.Zero_q(a) && _module.bin.Zero_q(b)
     ==> (_module.bin#Equal(a, b) <==> true));

// Datatype extensional equality definition: #_module.bin.Twice
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.bin#Equal(a, b), _module.bin.Twice_q(a) } 
    { _module.bin#Equal(a, b), _module.bin.Twice_q(b) } 
  _module.bin.Twice_q(a) && _module.bin.Twice_q(b)
     ==> (_module.bin#Equal(a, b)
       <==> _module.bin#Equal(_module.bin._h1(a), _module.bin._h1(b))));

// Datatype extensional equality definition: #_module.bin.TwicePlusOne
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.bin#Equal(a, b), _module.bin.TwicePlusOne_q(a) } 
    { _module.bin#Equal(a, b), _module.bin.TwicePlusOne_q(b) } 
  _module.bin.TwicePlusOne_q(a) && _module.bin.TwicePlusOne_q(b)
     ==> (_module.bin#Equal(a, b)
       <==> _module.bin#Equal(_module.bin._h2(a), _module.bin._h2(b))));

// Datatype extensionality axiom: _module.bin
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.bin#Equal(a, b) } 
  _module.bin#Equal(a, b) <==> a == b);

const unique class._module.bin: ClassName;

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

// function declaration for _module._default.next_weekday
function _module.__default.next__weekday(d#0: DatatypeType) : DatatypeType;

function _module.__default.next__weekday#canCall(d#0: DatatypeType) : bool;

// consequence axiom for _module.__default.next__weekday
axiom 3 <= $FunctionContextHeight
   ==> (forall d#0: DatatypeType :: 
    { _module.__default.next__weekday(d#0) } 
    _module.__default.next__weekday#canCall(d#0)
         || (3 != $FunctionContextHeight && $Is(d#0, Tclass._module.day()))
       ==> $Is(_module.__default.next__weekday(d#0), Tclass._module.day()));

function _module.__default.next__weekday#requires(DatatypeType) : bool;

// #requires axiom for _module.__default.next__weekday
axiom (forall d#0: DatatypeType :: 
  { _module.__default.next__weekday#requires(d#0) } 
  $Is(d#0, Tclass._module.day())
     ==> _module.__default.next__weekday#requires(d#0) == true);

// definition axiom for _module.__default.next__weekday (revealed)
axiom 3 <= $FunctionContextHeight
   ==> (forall d#0: DatatypeType :: 
    { _module.__default.next__weekday(d#0) } 
    _module.__default.next__weekday#canCall(d#0)
         || (3 != $FunctionContextHeight && $Is(d#0, Tclass._module.day()))
       ==> _module.__default.next__weekday(d#0)
         == (if _module.day.monday_q(d#0)
           then #_module.day.tuesday()
           else (if _module.day.tuesday_q(d#0)
             then #_module.day.wednesday()
             else (if _module.day.wednesday_q(d#0)
               then #_module.day.thursday()
               else (if _module.day.thursday_q(d#0)
                 then #_module.day.friday()
                 else (if _module.day.friday_q(d#0)
                   then #_module.day.monday()
                   else (if _module.day.saturday_q(d#0)
                     then #_module.day.monday()
                     else #_module.day.monday())))))));

// definition axiom for _module.__default.next__weekday for all literals (revealed)
axiom 3 <= $FunctionContextHeight
   ==> (forall d#0: DatatypeType :: 
    {:weight 3} { _module.__default.next__weekday(Lit(d#0)) } 
    _module.__default.next__weekday#canCall(Lit(d#0))
         || (3 != $FunctionContextHeight && $Is(d#0, Tclass._module.day()))
       ==> _module.__default.next__weekday(Lit(d#0))
         == (if _module.day.monday_q(Lit(d#0))
           then #_module.day.tuesday()
           else (if _module.day.tuesday_q(Lit(d#0))
             then #_module.day.wednesday()
             else (if _module.day.wednesday_q(Lit(d#0))
               then #_module.day.thursday()
               else (if _module.day.thursday_q(Lit(d#0))
                 then #_module.day.friday()
                 else (if _module.day.friday_q(Lit(d#0))
                   then #_module.day.monday()
                   else (if _module.day.saturday_q(Lit(d#0))
                     then #_module.day.monday()
                     else #_module.day.monday())))))));

procedure CheckWellformed$$_module.__default.next__weekday(d#0: DatatypeType where $Is(d#0, Tclass._module.day()));
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure CheckWellformed$$_module.__default.test__next__weekday();
  free requires 44 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.test__next__weekday();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.test__next__weekday() returns ($_reverifyPost: bool);
  free requires 44 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.test__next__weekday() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##d#0: DatatypeType;
  var ##d#1: DatatypeType;
  var ##d#2: DatatypeType;
  var d#0: DatatypeType
     where $Is(d#0, Tclass._module.day()) && $IsAlloc(d#0, Tclass._module.day(), $Heap);
  var ##d#3: DatatypeType;
  var ##d#4: DatatypeType;
  var ##d#5: DatatypeType;

    // AddMethodImpl: test_next_weekday, Impl$$_module.__default.test__next__weekday
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(34,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(35,3)
    ##d#0 := Lit(#_module.day.friday());
    // assume allocatedness for argument to function
    assume $IsAlloc(##d#0, Tclass._module.day(), $Heap);
    assume _module.__default.next__weekday#canCall(Lit(#_module.day.friday()));
    assume $IsA#_module.day(Lit(_module.__default.next__weekday(Lit(#_module.day.friday()))))
       && _module.__default.next__weekday#canCall(Lit(#_module.day.friday()));
    assert _module.day#Equal(_module.__default.next__weekday(Lit(#_module.day.friday())), 
      #_module.day.monday());
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(36,3)
    ##d#1 := Lit(#_module.day.saturday());
    // assume allocatedness for argument to function
    assume $IsAlloc(##d#1, Tclass._module.day(), $Heap);
    assume _module.__default.next__weekday#canCall(Lit(#_module.day.saturday()));
    ##d#2 := Lit(_module.__default.next__weekday(Lit(#_module.day.saturday())));
    // assume allocatedness for argument to function
    assume $IsAlloc(##d#2, Tclass._module.day(), $Heap);
    assume _module.__default.next__weekday#canCall(Lit(_module.__default.next__weekday(Lit(#_module.day.saturday()))));
    assume $IsA#_module.day(Lit(_module.__default.next__weekday(Lit(_module.__default.next__weekday(Lit(#_module.day.saturday()))))))
       && 
      _module.__default.next__weekday#canCall(Lit(#_module.day.saturday()))
       && _module.__default.next__weekday#canCall(Lit(_module.__default.next__weekday(Lit(#_module.day.saturday()))));
    assert _module.day#Equal(_module.__default.next__weekday(Lit(_module.__default.next__weekday(Lit(#_module.day.saturday())))), 
      #_module.day.tuesday());
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(40,9)
    assume true;
    ##d#3 := Lit(#_module.day.tuesday());
    // assume allocatedness for argument to function
    assume $IsAlloc(##d#3, Tclass._module.day(), $Heap);
    assume _module.__default.next__weekday#canCall(Lit(#_module.day.tuesday()));
    ##d#4 := Lit(_module.__default.next__weekday(Lit(#_module.day.tuesday())));
    // assume allocatedness for argument to function
    assume $IsAlloc(##d#4, Tclass._module.day(), $Heap);
    assume _module.__default.next__weekday#canCall(Lit(_module.__default.next__weekday(Lit(#_module.day.tuesday()))));
    assume _module.__default.next__weekday#canCall(Lit(#_module.day.tuesday()))
       && _module.__default.next__weekday#canCall(Lit(_module.__default.next__weekday(Lit(#_module.day.tuesday()))));
    d#0 := Lit(_module.__default.next__weekday(Lit(_module.__default.next__weekday(Lit(#_module.day.tuesday())))));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(40,46)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(41,3)
    assume $IsA#_module.day(d#0);
    assert _module.day#Equal(d#0, #_module.day.friday());
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(61,3)
    ##d#5 := Lit(#_module.day.wednesday());
    // assume allocatedness for argument to function
    assume $IsAlloc(##d#5, Tclass._module.day(), $Heap);
    assume _module.__default.next__weekday#canCall(Lit(#_module.day.wednesday()));
    assume _module.__default.next__weekday#canCall(Lit(#_module.day.wednesday()));
}



// function declaration for _module._default.negb
function _module.__default.negb(b#0: DatatypeType) : DatatypeType;

function _module.__default.negb#canCall(b#0: DatatypeType) : bool;

// consequence axiom for _module.__default.negb
axiom 5 <= $FunctionContextHeight
   ==> (forall b#0: DatatypeType :: 
    { _module.__default.negb(b#0) } 
    _module.__default.negb#canCall(b#0)
         || (5 != $FunctionContextHeight && $Is(b#0, Tclass._module.Bool()))
       ==> $Is(_module.__default.negb(b#0), Tclass._module.Bool()));

function _module.__default.negb#requires(DatatypeType) : bool;

// #requires axiom for _module.__default.negb
axiom (forall b#0: DatatypeType :: 
  { _module.__default.negb#requires(b#0) } 
  $Is(b#0, Tclass._module.Bool()) ==> _module.__default.negb#requires(b#0) == true);

// definition axiom for _module.__default.negb (revealed)
axiom 5 <= $FunctionContextHeight
   ==> (forall b#0: DatatypeType :: 
    { _module.__default.negb(b#0) } 
    _module.__default.negb#canCall(b#0)
         || (5 != $FunctionContextHeight && $Is(b#0, Tclass._module.Bool()))
       ==> _module.__default.negb(b#0)
         == (if _module.Bool.True_q(b#0)
           then #_module.Bool.False()
           else #_module.Bool.True()));

// definition axiom for _module.__default.negb for all literals (revealed)
axiom 5 <= $FunctionContextHeight
   ==> (forall b#0: DatatypeType :: 
    {:weight 3} { _module.__default.negb(Lit(b#0)) } 
    _module.__default.negb#canCall(Lit(b#0))
         || (5 != $FunctionContextHeight && $Is(b#0, Tclass._module.Bool()))
       ==> _module.__default.negb(Lit(b#0))
         == (if _module.Bool.True_q(Lit(b#0))
           then #_module.Bool.False()
           else #_module.Bool.True()));

procedure CheckWellformed$$_module.__default.negb(b#0: DatatypeType where $Is(b#0, Tclass._module.Bool()));
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;



// function declaration for _module._default.andb
function _module.__default.andb(b1#0: DatatypeType, b2#0: DatatypeType) : DatatypeType;

function _module.__default.andb#canCall(b1#0: DatatypeType, b2#0: DatatypeType) : bool;

// consequence axiom for _module.__default.andb
axiom 6 <= $FunctionContextHeight
   ==> (forall b1#0: DatatypeType, b2#0: DatatypeType :: 
    { _module.__default.andb(b1#0, b2#0) } 
    _module.__default.andb#canCall(b1#0, b2#0)
         || (6 != $FunctionContextHeight
           && 
          $Is(b1#0, Tclass._module.Bool())
           && $Is(b2#0, Tclass._module.Bool()))
       ==> $Is(_module.__default.andb(b1#0, b2#0), Tclass._module.Bool()));

function _module.__default.andb#requires(DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.andb
axiom (forall b1#0: DatatypeType, b2#0: DatatypeType :: 
  { _module.__default.andb#requires(b1#0, b2#0) } 
  $Is(b1#0, Tclass._module.Bool()) && $Is(b2#0, Tclass._module.Bool())
     ==> _module.__default.andb#requires(b1#0, b2#0) == true);

// definition axiom for _module.__default.andb (revealed)
axiom 6 <= $FunctionContextHeight
   ==> (forall b1#0: DatatypeType, b2#0: DatatypeType :: 
    { _module.__default.andb(b1#0, b2#0) } 
    _module.__default.andb#canCall(b1#0, b2#0)
         || (6 != $FunctionContextHeight
           && 
          $Is(b1#0, Tclass._module.Bool())
           && $Is(b2#0, Tclass._module.Bool()))
       ==> _module.__default.andb(b1#0, b2#0)
         == (if _module.Bool.True_q(b1#0) then b2#0 else #_module.Bool.False()));

// definition axiom for _module.__default.andb for all literals (revealed)
axiom 6 <= $FunctionContextHeight
   ==> (forall b1#0: DatatypeType, b2#0: DatatypeType :: 
    {:weight 3} { _module.__default.andb(Lit(b1#0), Lit(b2#0)) } 
    _module.__default.andb#canCall(Lit(b1#0), Lit(b2#0))
         || (6 != $FunctionContextHeight
           && 
          $Is(b1#0, Tclass._module.Bool())
           && $Is(b2#0, Tclass._module.Bool()))
       ==> _module.__default.andb(Lit(b1#0), Lit(b2#0))
         == (if _module.Bool.True_q(Lit(b1#0)) then b2#0 else #_module.Bool.False()));

procedure CheckWellformed$$_module.__default.andb(b1#0: DatatypeType where $Is(b1#0, Tclass._module.Bool()), 
    b2#0: DatatypeType where $Is(b2#0, Tclass._module.Bool()));
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;



// function declaration for _module._default.orb
function _module.__default.orb(b1#0: DatatypeType, b2#0: DatatypeType) : DatatypeType;

function _module.__default.orb#canCall(b1#0: DatatypeType, b2#0: DatatypeType) : bool;

// consequence axiom for _module.__default.orb
axiom 7 <= $FunctionContextHeight
   ==> (forall b1#0: DatatypeType, b2#0: DatatypeType :: 
    { _module.__default.orb(b1#0, b2#0) } 
    _module.__default.orb#canCall(b1#0, b2#0)
         || (7 != $FunctionContextHeight
           && 
          $Is(b1#0, Tclass._module.Bool())
           && $Is(b2#0, Tclass._module.Bool()))
       ==> $Is(_module.__default.orb(b1#0, b2#0), Tclass._module.Bool()));

function _module.__default.orb#requires(DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.orb
axiom (forall b1#0: DatatypeType, b2#0: DatatypeType :: 
  { _module.__default.orb#requires(b1#0, b2#0) } 
  $Is(b1#0, Tclass._module.Bool()) && $Is(b2#0, Tclass._module.Bool())
     ==> _module.__default.orb#requires(b1#0, b2#0) == true);

// definition axiom for _module.__default.orb (revealed)
axiom 7 <= $FunctionContextHeight
   ==> (forall b1#0: DatatypeType, b2#0: DatatypeType :: 
    { _module.__default.orb(b1#0, b2#0) } 
    _module.__default.orb#canCall(b1#0, b2#0)
         || (7 != $FunctionContextHeight
           && 
          $Is(b1#0, Tclass._module.Bool())
           && $Is(b2#0, Tclass._module.Bool()))
       ==> _module.__default.orb(b1#0, b2#0)
         == (if _module.Bool.True_q(b1#0) then #_module.Bool.True() else b2#0));

// definition axiom for _module.__default.orb for all literals (revealed)
axiom 7 <= $FunctionContextHeight
   ==> (forall b1#0: DatatypeType, b2#0: DatatypeType :: 
    {:weight 3} { _module.__default.orb(Lit(b1#0), Lit(b2#0)) } 
    _module.__default.orb#canCall(Lit(b1#0), Lit(b2#0))
         || (7 != $FunctionContextHeight
           && 
          $Is(b1#0, Tclass._module.Bool())
           && $Is(b2#0, Tclass._module.Bool()))
       ==> _module.__default.orb(Lit(b1#0), Lit(b2#0))
         == (if _module.Bool.True_q(Lit(b1#0)) then #_module.Bool.True() else b2#0));

procedure CheckWellformed$$_module.__default.orb(b1#0: DatatypeType where $Is(b1#0, Tclass._module.Bool()), 
    b2#0: DatatypeType where $Is(b2#0, Tclass._module.Bool()));
  free requires 7 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure CheckWellformed$$_module.__default.test__orb();
  free requires 45 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.test__orb();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.test__orb() returns ($_reverifyPost: bool);
  free requires 45 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.test__orb() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##b1#0: DatatypeType;
  var ##b2#0: DatatypeType;
  var ##b1#1: DatatypeType;
  var ##b2#1: DatatypeType;
  var ##b1#2: DatatypeType;
  var ##b2#2: DatatypeType;
  var ##b1#3: DatatypeType;
  var ##b2#3: DatatypeType;

    // AddMethodImpl: test_orb, Impl$$_module.__default.test__orb
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(95,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(96,3)
    ##b1#0 := Lit(#_module.Bool.True());
    // assume allocatedness for argument to function
    assume $IsAlloc(##b1#0, Tclass._module.Bool(), $Heap);
    ##b2#0 := Lit(#_module.Bool.False());
    // assume allocatedness for argument to function
    assume $IsAlloc(##b2#0, Tclass._module.Bool(), $Heap);
    assume _module.__default.orb#canCall(Lit(#_module.Bool.True()), Lit(#_module.Bool.False()));
    assume $IsA#_module.Bool(Lit(_module.__default.orb(Lit(#_module.Bool.True()), Lit(#_module.Bool.False()))))
       && _module.__default.orb#canCall(Lit(#_module.Bool.True()), Lit(#_module.Bool.False()));
    assert _module.Bool#Equal(_module.__default.orb(Lit(#_module.Bool.True()), Lit(#_module.Bool.False())), 
      #_module.Bool.True());
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(97,3)
    ##b1#1 := Lit(#_module.Bool.False());
    // assume allocatedness for argument to function
    assume $IsAlloc(##b1#1, Tclass._module.Bool(), $Heap);
    ##b2#1 := Lit(#_module.Bool.False());
    // assume allocatedness for argument to function
    assume $IsAlloc(##b2#1, Tclass._module.Bool(), $Heap);
    assume _module.__default.orb#canCall(Lit(#_module.Bool.False()), Lit(#_module.Bool.False()));
    assume $IsA#_module.Bool(Lit(_module.__default.orb(Lit(#_module.Bool.False()), Lit(#_module.Bool.False()))))
       && _module.__default.orb#canCall(Lit(#_module.Bool.False()), Lit(#_module.Bool.False()));
    assert _module.Bool#Equal(_module.__default.orb(Lit(#_module.Bool.False()), Lit(#_module.Bool.False())), 
      #_module.Bool.False());
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(98,3)
    ##b1#2 := Lit(#_module.Bool.False());
    // assume allocatedness for argument to function
    assume $IsAlloc(##b1#2, Tclass._module.Bool(), $Heap);
    ##b2#2 := Lit(#_module.Bool.True());
    // assume allocatedness for argument to function
    assume $IsAlloc(##b2#2, Tclass._module.Bool(), $Heap);
    assume _module.__default.orb#canCall(Lit(#_module.Bool.False()), Lit(#_module.Bool.True()));
    assume $IsA#_module.Bool(Lit(_module.__default.orb(Lit(#_module.Bool.False()), Lit(#_module.Bool.True()))))
       && _module.__default.orb#canCall(Lit(#_module.Bool.False()), Lit(#_module.Bool.True()));
    assert _module.Bool#Equal(_module.__default.orb(Lit(#_module.Bool.False()), Lit(#_module.Bool.True())), 
      #_module.Bool.True());
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(99,3)
    ##b1#3 := Lit(#_module.Bool.True());
    // assume allocatedness for argument to function
    assume $IsAlloc(##b1#3, Tclass._module.Bool(), $Heap);
    ##b2#3 := Lit(#_module.Bool.True());
    // assume allocatedness for argument to function
    assume $IsAlloc(##b2#3, Tclass._module.Bool(), $Heap);
    assume _module.__default.orb#canCall(Lit(#_module.Bool.True()), Lit(#_module.Bool.True()));
    assume $IsA#_module.Bool(Lit(_module.__default.orb(Lit(#_module.Bool.True()), Lit(#_module.Bool.True()))))
       && _module.__default.orb#canCall(Lit(#_module.Bool.True()), Lit(#_module.Bool.True()));
    assert _module.Bool#Equal(_module.__default.orb(Lit(#_module.Bool.True()), Lit(#_module.Bool.True())), 
      #_module.Bool.True());
}



// function declaration for _module._default.nandb
function _module.__default.nandb(b1#0: DatatypeType, b2#0: DatatypeType) : DatatypeType;

function _module.__default.nandb#canCall(b1#0: DatatypeType, b2#0: DatatypeType) : bool;

// consequence axiom for _module.__default.nandb
axiom 8 <= $FunctionContextHeight
   ==> (forall b1#0: DatatypeType, b2#0: DatatypeType :: 
    { _module.__default.nandb(b1#0, b2#0) } 
    _module.__default.nandb#canCall(b1#0, b2#0)
         || (8 != $FunctionContextHeight
           && 
          $Is(b1#0, Tclass._module.Bool())
           && $Is(b2#0, Tclass._module.Bool()))
       ==> $Is(_module.__default.nandb(b1#0, b2#0), Tclass._module.Bool()));

function _module.__default.nandb#requires(DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.nandb
axiom (forall b1#0: DatatypeType, b2#0: DatatypeType :: 
  { _module.__default.nandb#requires(b1#0, b2#0) } 
  $Is(b1#0, Tclass._module.Bool()) && $Is(b2#0, Tclass._module.Bool())
     ==> _module.__default.nandb#requires(b1#0, b2#0) == true);

// definition axiom for _module.__default.nandb (revealed)
axiom 8 <= $FunctionContextHeight
   ==> (forall b1#0: DatatypeType, b2#0: DatatypeType :: 
    { _module.__default.nandb(b1#0, b2#0) } 
    _module.__default.nandb#canCall(b1#0, b2#0)
         || (8 != $FunctionContextHeight
           && 
          $Is(b1#0, Tclass._module.Bool())
           && $Is(b2#0, Tclass._module.Bool()))
       ==> _module.__default.andb#canCall(b1#0, b2#0)
         && _module.__default.negb#canCall(_module.__default.andb(b1#0, b2#0))
         && _module.__default.nandb(b1#0, b2#0)
           == _module.__default.negb(_module.__default.andb(b1#0, b2#0)));

// definition axiom for _module.__default.nandb for all literals (revealed)
axiom 8 <= $FunctionContextHeight
   ==> (forall b1#0: DatatypeType, b2#0: DatatypeType :: 
    {:weight 3} { _module.__default.nandb(Lit(b1#0), Lit(b2#0)) } 
    _module.__default.nandb#canCall(Lit(b1#0), Lit(b2#0))
         || (8 != $FunctionContextHeight
           && 
          $Is(b1#0, Tclass._module.Bool())
           && $Is(b2#0, Tclass._module.Bool()))
       ==> _module.__default.andb#canCall(Lit(b1#0), Lit(b2#0))
         && _module.__default.negb#canCall(Lit(_module.__default.andb(Lit(b1#0), Lit(b2#0))))
         && _module.__default.nandb(Lit(b1#0), Lit(b2#0))
           == Lit(_module.__default.negb(Lit(_module.__default.andb(Lit(b1#0), Lit(b2#0))))));

procedure CheckWellformed$$_module.__default.nandb(b1#0: DatatypeType where $Is(b1#0, Tclass._module.Bool()), 
    b2#0: DatatypeType where $Is(b2#0, Tclass._module.Bool()));
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.nandb(b1#0: DatatypeType, b2#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##b1#0: DatatypeType;
  var ##b2#0: DatatypeType;
  var ##b#0: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function nandb
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(104,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.nandb(b1#0, b2#0), Tclass._module.Bool());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        ##b1#0 := b1#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##b1#0, Tclass._module.Bool(), $Heap);
        ##b2#0 := b2#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##b2#0, Tclass._module.Bool(), $Heap);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.andb#canCall(b1#0, b2#0);
        ##b#0 := _module.__default.andb(b1#0, b2#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##b#0, Tclass._module.Bool(), $Heap);
        b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.negb#canCall(_module.__default.andb(b1#0, b2#0));
        assume _module.__default.nandb(b1#0, b2#0)
           == _module.__default.negb(_module.__default.andb(b1#0, b2#0));
        assume _module.__default.andb#canCall(b1#0, b2#0)
           && _module.__default.negb#canCall(_module.__default.andb(b1#0, b2#0));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.nandb(b1#0, b2#0), Tclass._module.Bool());
        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



procedure CheckWellformed$$_module.__default.test__nandb();
  free requires 46 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.test__nandb();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.test__nandb() returns ($_reverifyPost: bool);
  free requires 46 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.test__nandb() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##b1#0: DatatypeType;
  var ##b2#0: DatatypeType;
  var ##b1#1: DatatypeType;
  var ##b2#1: DatatypeType;
  var ##b1#2: DatatypeType;
  var ##b2#2: DatatypeType;
  var ##b1#3: DatatypeType;
  var ##b2#3: DatatypeType;

    // AddMethodImpl: test_nandb, Impl$$_module.__default.test__nandb
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(110,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(111,3)
    ##b1#0 := Lit(#_module.Bool.True());
    // assume allocatedness for argument to function
    assume $IsAlloc(##b1#0, Tclass._module.Bool(), $Heap);
    ##b2#0 := Lit(#_module.Bool.False());
    // assume allocatedness for argument to function
    assume $IsAlloc(##b2#0, Tclass._module.Bool(), $Heap);
    assume _module.__default.nandb#canCall(Lit(#_module.Bool.True()), Lit(#_module.Bool.False()));
    assume $IsA#_module.Bool(Lit(_module.__default.nandb(Lit(#_module.Bool.True()), Lit(#_module.Bool.False()))))
       && _module.__default.nandb#canCall(Lit(#_module.Bool.True()), Lit(#_module.Bool.False()));
    assert _module.Bool#Equal(_module.__default.nandb(Lit(#_module.Bool.True()), Lit(#_module.Bool.False())), 
      #_module.Bool.True());
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(112,3)
    ##b1#1 := Lit(#_module.Bool.False());
    // assume allocatedness for argument to function
    assume $IsAlloc(##b1#1, Tclass._module.Bool(), $Heap);
    ##b2#1 := Lit(#_module.Bool.False());
    // assume allocatedness for argument to function
    assume $IsAlloc(##b2#1, Tclass._module.Bool(), $Heap);
    assume _module.__default.nandb#canCall(Lit(#_module.Bool.False()), Lit(#_module.Bool.False()));
    assume $IsA#_module.Bool(Lit(_module.__default.nandb(Lit(#_module.Bool.False()), Lit(#_module.Bool.False()))))
       && _module.__default.nandb#canCall(Lit(#_module.Bool.False()), Lit(#_module.Bool.False()));
    assert _module.Bool#Equal(_module.__default.nandb(Lit(#_module.Bool.False()), Lit(#_module.Bool.False())), 
      #_module.Bool.True());
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(113,3)
    ##b1#2 := Lit(#_module.Bool.False());
    // assume allocatedness for argument to function
    assume $IsAlloc(##b1#2, Tclass._module.Bool(), $Heap);
    ##b2#2 := Lit(#_module.Bool.True());
    // assume allocatedness for argument to function
    assume $IsAlloc(##b2#2, Tclass._module.Bool(), $Heap);
    assume _module.__default.nandb#canCall(Lit(#_module.Bool.False()), Lit(#_module.Bool.True()));
    assume $IsA#_module.Bool(Lit(_module.__default.nandb(Lit(#_module.Bool.False()), Lit(#_module.Bool.True()))))
       && _module.__default.nandb#canCall(Lit(#_module.Bool.False()), Lit(#_module.Bool.True()));
    assert _module.Bool#Equal(_module.__default.nandb(Lit(#_module.Bool.False()), Lit(#_module.Bool.True())), 
      #_module.Bool.True());
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(114,3)
    ##b1#3 := Lit(#_module.Bool.True());
    // assume allocatedness for argument to function
    assume $IsAlloc(##b1#3, Tclass._module.Bool(), $Heap);
    ##b2#3 := Lit(#_module.Bool.True());
    // assume allocatedness for argument to function
    assume $IsAlloc(##b2#3, Tclass._module.Bool(), $Heap);
    assume _module.__default.nandb#canCall(Lit(#_module.Bool.True()), Lit(#_module.Bool.True()));
    assume $IsA#_module.Bool(Lit(_module.__default.nandb(Lit(#_module.Bool.True()), Lit(#_module.Bool.True()))))
       && _module.__default.nandb#canCall(Lit(#_module.Bool.True()), Lit(#_module.Bool.True()));
    assert _module.Bool#Equal(_module.__default.nandb(Lit(#_module.Bool.True()), Lit(#_module.Bool.True())), 
      #_module.Bool.False());
}



// function declaration for _module._default.andb3
function _module.__default.andb3(b1#0: DatatypeType, b2#0: DatatypeType, b3#0: DatatypeType) : DatatypeType;

function _module.__default.andb3#canCall(b1#0: DatatypeType, b2#0: DatatypeType, b3#0: DatatypeType) : bool;

// consequence axiom for _module.__default.andb3
axiom 9 <= $FunctionContextHeight
   ==> (forall b1#0: DatatypeType, b2#0: DatatypeType, b3#0: DatatypeType :: 
    { _module.__default.andb3(b1#0, b2#0, b3#0) } 
    _module.__default.andb3#canCall(b1#0, b2#0, b3#0)
         || (9 != $FunctionContextHeight
           && 
          $Is(b1#0, Tclass._module.Bool())
           && $Is(b2#0, Tclass._module.Bool())
           && $Is(b3#0, Tclass._module.Bool()))
       ==> $Is(_module.__default.andb3(b1#0, b2#0, b3#0), Tclass._module.Bool()));

function _module.__default.andb3#requires(DatatypeType, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.andb3
axiom (forall b1#0: DatatypeType, b2#0: DatatypeType, b3#0: DatatypeType :: 
  { _module.__default.andb3#requires(b1#0, b2#0, b3#0) } 
  $Is(b1#0, Tclass._module.Bool())
       && $Is(b2#0, Tclass._module.Bool())
       && $Is(b3#0, Tclass._module.Bool())
     ==> _module.__default.andb3#requires(b1#0, b2#0, b3#0) == true);

// definition axiom for _module.__default.andb3 (revealed)
axiom 9 <= $FunctionContextHeight
   ==> (forall b1#0: DatatypeType, b2#0: DatatypeType, b3#0: DatatypeType :: 
    { _module.__default.andb3(b1#0, b2#0, b3#0) } 
    _module.__default.andb3#canCall(b1#0, b2#0, b3#0)
         || (9 != $FunctionContextHeight
           && 
          $Is(b1#0, Tclass._module.Bool())
           && $Is(b2#0, Tclass._module.Bool())
           && $Is(b3#0, Tclass._module.Bool()))
       ==> _module.__default.andb#canCall(b1#0, b2#0)
         && _module.__default.andb#canCall(_module.__default.andb(b1#0, b2#0), b3#0)
         && _module.__default.andb3(b1#0, b2#0, b3#0)
           == _module.__default.andb(_module.__default.andb(b1#0, b2#0), b3#0));

// definition axiom for _module.__default.andb3 for all literals (revealed)
axiom 9 <= $FunctionContextHeight
   ==> (forall b1#0: DatatypeType, b2#0: DatatypeType, b3#0: DatatypeType :: 
    {:weight 3} { _module.__default.andb3(Lit(b1#0), Lit(b2#0), Lit(b3#0)) } 
    _module.__default.andb3#canCall(Lit(b1#0), Lit(b2#0), Lit(b3#0))
         || (9 != $FunctionContextHeight
           && 
          $Is(b1#0, Tclass._module.Bool())
           && $Is(b2#0, Tclass._module.Bool())
           && $Is(b3#0, Tclass._module.Bool()))
       ==> _module.__default.andb#canCall(Lit(b1#0), Lit(b2#0))
         && _module.__default.andb#canCall(Lit(_module.__default.andb(Lit(b1#0), Lit(b2#0))), Lit(b3#0))
         && _module.__default.andb3(Lit(b1#0), Lit(b2#0), Lit(b3#0))
           == Lit(_module.__default.andb(Lit(_module.__default.andb(Lit(b1#0), Lit(b2#0))), Lit(b3#0))));

procedure CheckWellformed$$_module.__default.andb3(b1#0: DatatypeType where $Is(b1#0, Tclass._module.Bool()), 
    b2#0: DatatypeType where $Is(b2#0, Tclass._module.Bool()), 
    b3#0: DatatypeType where $Is(b3#0, Tclass._module.Bool()));
  free requires 9 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.andb3(b1#0: DatatypeType, b2#0: DatatypeType, b3#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##b1#0: DatatypeType;
  var ##b2#0: DatatypeType;
  var ##b1#1: DatatypeType;
  var ##b2#1: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function andb3
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(119,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.andb3(b1#0, b2#0, b3#0), Tclass._module.Bool());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        ##b1#0 := b1#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##b1#0, Tclass._module.Bool(), $Heap);
        ##b2#0 := b2#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##b2#0, Tclass._module.Bool(), $Heap);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.andb#canCall(b1#0, b2#0);
        ##b1#1 := _module.__default.andb(b1#0, b2#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##b1#1, Tclass._module.Bool(), $Heap);
        ##b2#1 := b3#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##b2#1, Tclass._module.Bool(), $Heap);
        b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.andb#canCall(_module.__default.andb(b1#0, b2#0), b3#0);
        assume _module.__default.andb3(b1#0, b2#0, b3#0)
           == _module.__default.andb(_module.__default.andb(b1#0, b2#0), b3#0);
        assume _module.__default.andb#canCall(b1#0, b2#0)
           && _module.__default.andb#canCall(_module.__default.andb(b1#0, b2#0), b3#0);
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.andb3(b1#0, b2#0, b3#0), Tclass._module.Bool());
        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



procedure CheckWellformed$$_module.__default.test__andb3();
  free requires 47 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.test__andb3();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.test__andb3() returns ($_reverifyPost: bool);
  free requires 47 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.test__andb3() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##b1#0: DatatypeType;
  var ##b2#0: DatatypeType;
  var ##b3#0: DatatypeType;
  var ##b1#1: DatatypeType;
  var ##b2#1: DatatypeType;
  var ##b3#1: DatatypeType;
  var ##b1#2: DatatypeType;
  var ##b2#2: DatatypeType;
  var ##b3#2: DatatypeType;
  var ##b1#3: DatatypeType;
  var ##b2#3: DatatypeType;
  var ##b3#3: DatatypeType;

    // AddMethodImpl: test_andb3, Impl$$_module.__default.test__andb3
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(125,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(126,3)
    ##b1#0 := Lit(#_module.Bool.True());
    // assume allocatedness for argument to function
    assume $IsAlloc(##b1#0, Tclass._module.Bool(), $Heap);
    ##b2#0 := Lit(#_module.Bool.True());
    // assume allocatedness for argument to function
    assume $IsAlloc(##b2#0, Tclass._module.Bool(), $Heap);
    ##b3#0 := Lit(#_module.Bool.True());
    // assume allocatedness for argument to function
    assume $IsAlloc(##b3#0, Tclass._module.Bool(), $Heap);
    assume _module.__default.andb3#canCall(Lit(#_module.Bool.True()), Lit(#_module.Bool.True()), Lit(#_module.Bool.True()));
    assume $IsA#_module.Bool(Lit(_module.__default.andb3(Lit(#_module.Bool.True()), Lit(#_module.Bool.True()), Lit(#_module.Bool.True()))))
       && _module.__default.andb3#canCall(Lit(#_module.Bool.True()), Lit(#_module.Bool.True()), Lit(#_module.Bool.True()));
    assert _module.Bool#Equal(_module.__default.andb3(Lit(#_module.Bool.True()), Lit(#_module.Bool.True()), Lit(#_module.Bool.True())), 
      #_module.Bool.True());
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(127,3)
    ##b1#1 := Lit(#_module.Bool.False());
    // assume allocatedness for argument to function
    assume $IsAlloc(##b1#1, Tclass._module.Bool(), $Heap);
    ##b2#1 := Lit(#_module.Bool.True());
    // assume allocatedness for argument to function
    assume $IsAlloc(##b2#1, Tclass._module.Bool(), $Heap);
    ##b3#1 := Lit(#_module.Bool.True());
    // assume allocatedness for argument to function
    assume $IsAlloc(##b3#1, Tclass._module.Bool(), $Heap);
    assume _module.__default.andb3#canCall(Lit(#_module.Bool.False()), Lit(#_module.Bool.True()), Lit(#_module.Bool.True()));
    assume $IsA#_module.Bool(Lit(_module.__default.andb3(Lit(#_module.Bool.False()), Lit(#_module.Bool.True()), Lit(#_module.Bool.True()))))
       && _module.__default.andb3#canCall(Lit(#_module.Bool.False()), Lit(#_module.Bool.True()), Lit(#_module.Bool.True()));
    assert _module.Bool#Equal(_module.__default.andb3(Lit(#_module.Bool.False()), Lit(#_module.Bool.True()), Lit(#_module.Bool.True())), 
      #_module.Bool.False());
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(128,3)
    ##b1#2 := Lit(#_module.Bool.True());
    // assume allocatedness for argument to function
    assume $IsAlloc(##b1#2, Tclass._module.Bool(), $Heap);
    ##b2#2 := Lit(#_module.Bool.False());
    // assume allocatedness for argument to function
    assume $IsAlloc(##b2#2, Tclass._module.Bool(), $Heap);
    ##b3#2 := Lit(#_module.Bool.True());
    // assume allocatedness for argument to function
    assume $IsAlloc(##b3#2, Tclass._module.Bool(), $Heap);
    assume _module.__default.andb3#canCall(Lit(#_module.Bool.True()), Lit(#_module.Bool.False()), Lit(#_module.Bool.True()));
    assume $IsA#_module.Bool(Lit(_module.__default.andb3(Lit(#_module.Bool.True()), Lit(#_module.Bool.False()), Lit(#_module.Bool.True()))))
       && _module.__default.andb3#canCall(Lit(#_module.Bool.True()), Lit(#_module.Bool.False()), Lit(#_module.Bool.True()));
    assert _module.Bool#Equal(_module.__default.andb3(Lit(#_module.Bool.True()), Lit(#_module.Bool.False()), Lit(#_module.Bool.True())), 
      #_module.Bool.False());
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(129,3)
    ##b1#3 := Lit(#_module.Bool.True());
    // assume allocatedness for argument to function
    assume $IsAlloc(##b1#3, Tclass._module.Bool(), $Heap);
    ##b2#3 := Lit(#_module.Bool.True());
    // assume allocatedness for argument to function
    assume $IsAlloc(##b2#3, Tclass._module.Bool(), $Heap);
    ##b3#3 := Lit(#_module.Bool.False());
    // assume allocatedness for argument to function
    assume $IsAlloc(##b3#3, Tclass._module.Bool(), $Heap);
    assume _module.__default.andb3#canCall(Lit(#_module.Bool.True()), Lit(#_module.Bool.True()), Lit(#_module.Bool.False()));
    assume $IsA#_module.Bool(Lit(_module.__default.andb3(Lit(#_module.Bool.True()), Lit(#_module.Bool.True()), Lit(#_module.Bool.False()))))
       && _module.__default.andb3#canCall(Lit(#_module.Bool.True()), Lit(#_module.Bool.True()), Lit(#_module.Bool.False()));
    assert _module.Bool#Equal(_module.__default.andb3(Lit(#_module.Bool.True()), Lit(#_module.Bool.True()), Lit(#_module.Bool.False())), 
      #_module.Bool.False());
}



// function declaration for _module._default.pred
function _module.__default.pred(n#0: DatatypeType) : DatatypeType;

function _module.__default.pred#canCall(n#0: DatatypeType) : bool;

// consequence axiom for _module.__default.pred
axiom 10 <= $FunctionContextHeight
   ==> (forall n#0: DatatypeType :: 
    { _module.__default.pred(n#0) } 
    _module.__default.pred#canCall(n#0)
         || (10 != $FunctionContextHeight && $Is(n#0, Tclass._module.Nat()))
       ==> $Is(_module.__default.pred(n#0), Tclass._module.Nat()));

function _module.__default.pred#requires(DatatypeType) : bool;

// #requires axiom for _module.__default.pred
axiom (forall n#0: DatatypeType :: 
  { _module.__default.pred#requires(n#0) } 
  $Is(n#0, Tclass._module.Nat()) ==> _module.__default.pred#requires(n#0) == true);

// definition axiom for _module.__default.pred (revealed)
axiom 10 <= $FunctionContextHeight
   ==> (forall n#0: DatatypeType :: 
    { _module.__default.pred(n#0) } 
    _module.__default.pred#canCall(n#0)
         || (10 != $FunctionContextHeight && $Is(n#0, Tclass._module.Nat()))
       ==> _module.__default.pred(n#0)
         == (if _module.Nat.O_q(n#0)
           then #_module.Nat.O()
           else (var n'#0 := _module.Nat._h0(n#0); n'#0)));

// definition axiom for _module.__default.pred for all literals (revealed)
axiom 10 <= $FunctionContextHeight
   ==> (forall n#0: DatatypeType :: 
    {:weight 3} { _module.__default.pred(Lit(n#0)) } 
    _module.__default.pred#canCall(Lit(n#0))
         || (10 != $FunctionContextHeight && $Is(n#0, Tclass._module.Nat()))
       ==> _module.__default.pred(Lit(n#0))
         == (if _module.Nat.O_q(Lit(n#0))
           then #_module.Nat.O()
           else (var n'#2 := Lit(_module.Nat._h0(Lit(n#0))); n'#2)));

procedure CheckWellformed$$_module.__default.pred(n#0: DatatypeType where $Is(n#0, Tclass._module.Nat()));
  free requires 10 == $FunctionContextHeight;
  modifies $Heap, $Tick;



// function declaration for _module._default.minustwo
function _module.__default.minustwo(n#0: DatatypeType) : DatatypeType;

function _module.__default.minustwo#canCall(n#0: DatatypeType) : bool;

// consequence axiom for _module.__default.minustwo
axiom 11 <= $FunctionContextHeight
   ==> (forall n#0: DatatypeType :: 
    { _module.__default.minustwo(n#0) } 
    _module.__default.minustwo#canCall(n#0)
         || (11 != $FunctionContextHeight && $Is(n#0, Tclass._module.Nat()))
       ==> $Is(_module.__default.minustwo(n#0), Tclass._module.Nat()));

function _module.__default.minustwo#requires(DatatypeType) : bool;

// #requires axiom for _module.__default.minustwo
axiom (forall n#0: DatatypeType :: 
  { _module.__default.minustwo#requires(n#0) } 
  $Is(n#0, Tclass._module.Nat())
     ==> _module.__default.minustwo#requires(n#0) == true);

// definition axiom for _module.__default.minustwo (revealed)
axiom 11 <= $FunctionContextHeight
   ==> (forall n#0: DatatypeType :: 
    { _module.__default.minustwo(n#0) } 
    _module.__default.minustwo#canCall(n#0)
         || (11 != $FunctionContextHeight && $Is(n#0, Tclass._module.Nat()))
       ==> _module.__default.minustwo(n#0)
         == (if _module.Nat.O_q(n#0)
           then #_module.Nat.O()
           else (var nn#0 := _module.Nat._h0(n#0); 
            (if _module.Nat.O_q(nn#0)
               then #_module.Nat.O()
               else (var n'#0 := _module.Nat._h0(nn#0); n'#0)))));

// definition axiom for _module.__default.minustwo for all literals (revealed)
axiom 11 <= $FunctionContextHeight
   ==> (forall n#0: DatatypeType :: 
    {:weight 3} { _module.__default.minustwo(Lit(n#0)) } 
    _module.__default.minustwo#canCall(Lit(n#0))
         || (11 != $FunctionContextHeight && $Is(n#0, Tclass._module.Nat()))
       ==> _module.__default.minustwo(Lit(n#0))
         == (if _module.Nat.O_q(Lit(n#0))
           then #_module.Nat.O()
           else (var nn#2 := Lit(_module.Nat._h0(Lit(n#0))); 
            (if _module.Nat.O_q(nn#2)
               then #_module.Nat.O()
               else (var n'#2 := Lit(_module.Nat._h0(nn#2)); n'#2)))));

procedure CheckWellformed$$_module.__default.minustwo(n#0: DatatypeType where $Is(n#0, Tclass._module.Nat()));
  free requires 11 == $FunctionContextHeight;
  modifies $Heap, $Tick;



// function declaration for _module._default.evenb
function _module.__default.evenb($ly: LayerType, n#0: DatatypeType) : DatatypeType;

function _module.__default.evenb#canCall(n#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, n#0: DatatypeType :: 
  { _module.__default.evenb($LS($ly), n#0) } 
  _module.__default.evenb($LS($ly), n#0) == _module.__default.evenb($ly, n#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, n#0: DatatypeType :: 
  { _module.__default.evenb(AsFuelBottom($ly), n#0) } 
  _module.__default.evenb($ly, n#0) == _module.__default.evenb($LZ, n#0));

// consequence axiom for _module.__default.evenb
axiom 12 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: DatatypeType :: 
    { _module.__default.evenb($ly, n#0) } 
    _module.__default.evenb#canCall(n#0)
         || (12 != $FunctionContextHeight && $Is(n#0, Tclass._module.Nat()))
       ==> $Is(_module.__default.evenb($ly, n#0), Tclass._module.Bool()));

function _module.__default.evenb#requires(LayerType, DatatypeType) : bool;

// #requires axiom for _module.__default.evenb
axiom (forall $ly: LayerType, n#0: DatatypeType :: 
  { _module.__default.evenb#requires($ly, n#0) } 
  $Is(n#0, Tclass._module.Nat())
     ==> _module.__default.evenb#requires($ly, n#0) == true);

// definition axiom for _module.__default.evenb (revealed)
axiom 12 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: DatatypeType :: 
    { _module.__default.evenb($LS($ly), n#0) } 
    _module.__default.evenb#canCall(n#0)
         || (12 != $FunctionContextHeight && $Is(n#0, Tclass._module.Nat()))
       ==> (!_module.Nat.O_q(n#0)
           ==> (var nn#1 := _module.Nat._h0(n#0); 
            !_module.Nat.O_q(nn#1)
               ==> (var n'#1 := _module.Nat._h0(nn#1); _module.__default.evenb#canCall(n'#1))))
         && _module.__default.evenb($LS($ly), n#0)
           == (if _module.Nat.O_q(n#0)
             then #_module.Bool.True()
             else (var nn#0 := _module.Nat._h0(n#0); 
              (if _module.Nat.O_q(nn#0)
                 then #_module.Bool.False()
                 else (var n'#0 := _module.Nat._h0(nn#0); _module.__default.evenb($ly, n'#0))))));

// definition axiom for _module.__default.evenb for all literals (revealed)
axiom 12 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: DatatypeType :: 
    {:weight 3} { _module.__default.evenb($LS($ly), Lit(n#0)) } 
    _module.__default.evenb#canCall(Lit(n#0))
         || (12 != $FunctionContextHeight && $Is(n#0, Tclass._module.Nat()))
       ==> (!Lit(_module.Nat.O_q(Lit(n#0)))
           ==> (var nn#3 := Lit(_module.Nat._h0(Lit(n#0))); 
            !_module.Nat.O_q(nn#3)
               ==> (var n'#3 := _module.Nat._h0(nn#3); _module.__default.evenb#canCall(n'#3))))
         && _module.__default.evenb($LS($ly), Lit(n#0))
           == (if _module.Nat.O_q(Lit(n#0))
             then #_module.Bool.True()
             else (var nn#2 := Lit(_module.Nat._h0(Lit(n#0))); 
              (if _module.Nat.O_q(nn#2)
                 then #_module.Bool.False()
                 else (var n'#2 := Lit(_module.Nat._h0(nn#2)); 
                  Lit(_module.__default.evenb($LS($ly), n'#2)))))));

procedure CheckWellformed$$_module.__default.evenb(n#0: DatatypeType where $Is(n#0, Tclass._module.Nat()));
  free requires 12 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.evenb(n#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: DatatypeType;
  var nn#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var _mcc#1#0: DatatypeType;
  var n'#Z#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var ##n#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function evenb
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(159,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.evenb($LS($LZ), n#0), Tclass._module.Bool());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (n#0 == #_module.Nat.O())
        {
            assume _module.__default.evenb($LS($LZ), n#0) == Lit(#_module.Bool.True());
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.evenb($LS($LZ), n#0), Tclass._module.Bool());
        }
        else if (n#0 == #_module.Nat.S(_mcc#0#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.Nat());
            havoc nn#Z#0;
            assume $Is(nn#Z#0, Tclass._module.Nat());
            assume let#0#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.Nat());
            assume nn#Z#0 == let#0#0#0;
            if (nn#Z#0 == #_module.Nat.O())
            {
                assume _module.__default.evenb($LS($LZ), n#0) == Lit(#_module.Bool.False());
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.evenb($LS($LZ), n#0), Tclass._module.Bool());
            }
            else if (nn#Z#0 == #_module.Nat.S(_mcc#1#0))
            {
                assume $Is(_mcc#1#0, Tclass._module.Nat());
                havoc n'#Z#0;
                assume $Is(n'#Z#0, Tclass._module.Nat());
                assume let#1#0#0 == _mcc#1#0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(let#1#0#0, Tclass._module.Nat());
                assume n'#Z#0 == let#1#0#0;
                ##n#0 := n'#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#0, Tclass._module.Nat(), $Heap);
                b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assert DtRank(##n#0) < DtRank(n#0);
                assume _module.__default.evenb#canCall(n'#Z#0);
                assume _module.__default.evenb($LS($LZ), n#0)
                   == _module.__default.evenb($LS($LZ), n'#Z#0);
                assume _module.__default.evenb#canCall(n'#Z#0);
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.evenb($LS($LZ), n#0), Tclass._module.Bool());
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



// function declaration for _module._default.oddb
function _module.__default.oddb(n#0: DatatypeType) : DatatypeType;

function _module.__default.oddb#canCall(n#0: DatatypeType) : bool;

// consequence axiom for _module.__default.oddb
axiom 13 <= $FunctionContextHeight
   ==> (forall n#0: DatatypeType :: 
    { _module.__default.oddb(n#0) } 
    _module.__default.oddb#canCall(n#0)
         || (13 != $FunctionContextHeight && $Is(n#0, Tclass._module.Nat()))
       ==> $Is(_module.__default.oddb(n#0), Tclass._module.Bool()));

function _module.__default.oddb#requires(DatatypeType) : bool;

// #requires axiom for _module.__default.oddb
axiom (forall n#0: DatatypeType :: 
  { _module.__default.oddb#requires(n#0) } 
  $Is(n#0, Tclass._module.Nat()) ==> _module.__default.oddb#requires(n#0) == true);

// definition axiom for _module.__default.oddb (revealed)
axiom 13 <= $FunctionContextHeight
   ==> (forall n#0: DatatypeType :: 
    { _module.__default.oddb(n#0) } 
    _module.__default.oddb#canCall(n#0)
         || (13 != $FunctionContextHeight && $Is(n#0, Tclass._module.Nat()))
       ==> _module.__default.evenb#canCall(n#0)
         && _module.__default.negb#canCall(_module.__default.evenb($LS($LZ), n#0))
         && _module.__default.oddb(n#0)
           == _module.__default.negb(_module.__default.evenb($LS($LZ), n#0)));

// definition axiom for _module.__default.oddb for all literals (revealed)
axiom 13 <= $FunctionContextHeight
   ==> (forall n#0: DatatypeType :: 
    {:weight 3} { _module.__default.oddb(Lit(n#0)) } 
    _module.__default.oddb#canCall(Lit(n#0))
         || (13 != $FunctionContextHeight && $Is(n#0, Tclass._module.Nat()))
       ==> _module.__default.evenb#canCall(Lit(n#0))
         && _module.__default.negb#canCall(Lit(_module.__default.evenb($LS($LZ), Lit(n#0))))
         && _module.__default.oddb(Lit(n#0))
           == Lit(_module.__default.negb(Lit(_module.__default.evenb($LS($LZ), Lit(n#0))))));

procedure CheckWellformed$$_module.__default.oddb(n#0: DatatypeType where $Is(n#0, Tclass._module.Nat()));
  free requires 13 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.oddb(n#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##n#0: DatatypeType;
  var ##b#0: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function oddb
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(169,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.oddb(n#0), Tclass._module.Bool());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        ##n#0 := n#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#0, Tclass._module.Nat(), $Heap);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.evenb#canCall(n#0);
        ##b#0 := _module.__default.evenb($LS($LZ), n#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##b#0, Tclass._module.Bool(), $Heap);
        b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.negb#canCall(_module.__default.evenb($LS($LZ), n#0));
        assume _module.__default.oddb(n#0)
           == _module.__default.negb(_module.__default.evenb($LS($LZ), n#0));
        assume _module.__default.evenb#canCall(n#0)
           && _module.__default.negb#canCall(_module.__default.evenb($LS($LZ), n#0));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.oddb(n#0), Tclass._module.Bool());
        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



procedure CheckWellformed$$_module.__default.test__oddb();
  free requires 48 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.test__oddb();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.test__oddb() returns ($_reverifyPost: bool);
  free requires 48 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.test__oddb() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##n#0: DatatypeType;
  var ##n#1: DatatypeType;

    // AddMethodImpl: test_oddb, Impl$$_module.__default.test__oddb
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(175,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(176,3)
    ##n#0 := Lit(#_module.Nat.S(Lit(#_module.Nat.O())));
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#0, Tclass._module.Nat(), $Heap);
    assume _module.__default.oddb#canCall(Lit(#_module.Nat.S(Lit(#_module.Nat.O()))));
    assume $IsA#_module.Bool(Lit(_module.__default.oddb(Lit(#_module.Nat.S(Lit(#_module.Nat.O()))))))
       && _module.__default.oddb#canCall(Lit(#_module.Nat.S(Lit(#_module.Nat.O()))));
    assert _module.Bool#Equal(_module.__default.oddb(Lit(#_module.Nat.S(Lit(#_module.Nat.O())))), 
      #_module.Bool.True());
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(177,3)
    ##n#1 := Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.O())))))))));
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#1, Tclass._module.Nat(), $Heap);
    assume _module.__default.oddb#canCall(Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.O()))))))))));
    assume $IsA#_module.Bool(Lit(_module.__default.oddb(Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.O()))))))))))))
       && _module.__default.oddb#canCall(Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.O()))))))))));
    assert _module.Bool#Equal(_module.__default.oddb(Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.O())))))))))), 
      #_module.Bool.False());
}



// function declaration for _module._default.plus
function _module.__default.plus($ly: LayerType, n#0: DatatypeType, m#0: DatatypeType) : DatatypeType;

function _module.__default.plus#canCall(n#0: DatatypeType, m#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType :: 
  { _module.__default.plus($LS($ly), n#0, m#0) } 
  _module.__default.plus($LS($ly), n#0, m#0)
     == _module.__default.plus($ly, n#0, m#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType :: 
  { _module.__default.plus(AsFuelBottom($ly), n#0, m#0) } 
  _module.__default.plus($ly, n#0, m#0) == _module.__default.plus($LZ, n#0, m#0));

// consequence axiom for _module.__default.plus
axiom 14 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType :: 
    { _module.__default.plus($ly, n#0, m#0) } 
    _module.__default.plus#canCall(n#0, m#0)
         || (14 != $FunctionContextHeight
           && 
          $Is(n#0, Tclass._module.Nat())
           && $Is(m#0, Tclass._module.Nat()))
       ==> $Is(_module.__default.plus($ly, n#0, m#0), Tclass._module.Nat()));

function _module.__default.plus#requires(LayerType, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.plus
axiom (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType :: 
  { _module.__default.plus#requires($ly, n#0, m#0) } 
  $Is(n#0, Tclass._module.Nat()) && $Is(m#0, Tclass._module.Nat())
     ==> _module.__default.plus#requires($ly, n#0, m#0) == true);

// definition axiom for _module.__default.plus (revealed)
axiom 14 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType :: 
    { _module.__default.plus($LS($ly), n#0, m#0) } 
    _module.__default.plus#canCall(n#0, m#0)
         || (14 != $FunctionContextHeight
           && 
          $Is(n#0, Tclass._module.Nat())
           && $Is(m#0, Tclass._module.Nat()))
       ==> (!_module.Nat.O_q(n#0)
           ==> (var n'#1 := _module.Nat._h0(n#0); _module.__default.plus#canCall(n'#1, m#0)))
         && _module.__default.plus($LS($ly), n#0, m#0)
           == (if _module.Nat.O_q(n#0)
             then m#0
             else (var n'#0 := _module.Nat._h0(n#0); 
              #_module.Nat.S(_module.__default.plus($ly, n'#0, m#0)))));

// definition axiom for _module.__default.plus for all literals (revealed)
axiom 14 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType :: 
    {:weight 3} { _module.__default.plus($LS($ly), Lit(n#0), Lit(m#0)) } 
    _module.__default.plus#canCall(Lit(n#0), Lit(m#0))
         || (14 != $FunctionContextHeight
           && 
          $Is(n#0, Tclass._module.Nat())
           && $Is(m#0, Tclass._module.Nat()))
       ==> (!Lit(_module.Nat.O_q(Lit(n#0)))
           ==> (var n'#3 := Lit(_module.Nat._h0(Lit(n#0))); 
            _module.__default.plus#canCall(n'#3, Lit(m#0))))
         && _module.__default.plus($LS($ly), Lit(n#0), Lit(m#0))
           == (if _module.Nat.O_q(Lit(n#0))
             then m#0
             else (var n'#2 := Lit(_module.Nat._h0(Lit(n#0))); 
              Lit(#_module.Nat.S(Lit(_module.__default.plus($LS($ly), n'#2, Lit(m#0))))))));

procedure CheckWellformed$$_module.__default.plus(n#0: DatatypeType where $Is(n#0, Tclass._module.Nat()), 
    m#0: DatatypeType where $Is(m#0, Tclass._module.Nat()));
  free requires 14 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.plus(n#0: DatatypeType, m#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: DatatypeType;
  var n'#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var ##n#0: DatatypeType;
  var ##m#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function plus
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(180,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.plus($LS($LZ), n#0, m#0), Tclass._module.Nat());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (n#0 == #_module.Nat.O())
        {
            assume _module.__default.plus($LS($LZ), n#0, m#0) == m#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.plus($LS($LZ), n#0, m#0), Tclass._module.Nat());
        }
        else if (n#0 == #_module.Nat.S(_mcc#0#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.Nat());
            havoc n'#Z#0;
            assume $Is(n'#Z#0, Tclass._module.Nat());
            assume let#0#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.Nat());
            assume n'#Z#0 == let#0#0#0;
            ##n#0 := n'#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0, Tclass._module.Nat(), $Heap);
            ##m#0 := m#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#0, Tclass._module.Nat(), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(##n#0) < DtRank(n#0)
               || (DtRank(##n#0) == DtRank(n#0) && DtRank(##m#0) < DtRank(m#0));
            assume _module.__default.plus#canCall(n'#Z#0, m#0);
            assume _module.__default.plus($LS($LZ), n#0, m#0)
               == #_module.Nat.S(_module.__default.plus($LS($LZ), n'#Z#0, m#0));
            assume _module.__default.plus#canCall(n'#Z#0, m#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.plus($LS($LZ), n#0, m#0), Tclass._module.Nat());
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
    }
}



procedure CheckWellformed$$_module.__default.test__plus();
  free requires 49 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.test__plus();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.test__plus() returns ($_reverifyPost: bool);
  free requires 49 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.test__plus() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##n#0: DatatypeType;
  var ##m#0: DatatypeType;

    // AddMethodImpl: test_plus, Impl$$_module.__default.test__plus
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(188,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(189,3)
    ##n#0 := Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.O())))))));
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#0, Tclass._module.Nat(), $Heap);
    ##m#0 := Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.O())))));
    // assume allocatedness for argument to function
    assume $IsAlloc(##m#0, Tclass._module.Nat(), $Heap);
    assume _module.__default.plus#canCall(Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.O()))))))), 
      Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.O()))))));
    assume $IsA#_module.Nat(Lit(_module.__default.plus($LS($LZ), 
            Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.O()))))))), 
            Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.O()))))))))
       && _module.__default.plus#canCall(Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.O()))))))), 
        Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.O()))))));
    assert {:subsumption 0} _module.Nat#Equal(_module.__default.plus($LS($LS($LZ)), 
        Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.O()))))))), 
        Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.O())))))), 
      #_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.O())))))))))));
    assume _module.Nat#Equal(_module.__default.plus($LS($LZ), 
        Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.O()))))))), 
        Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.O())))))), 
      #_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.O())))))))))));
}



// function declaration for _module._default.mult
function _module.__default.mult($ly: LayerType, n#0: DatatypeType, m#0: DatatypeType) : DatatypeType;

function _module.__default.mult#canCall(n#0: DatatypeType, m#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType :: 
  { _module.__default.mult($LS($ly), n#0, m#0) } 
  _module.__default.mult($LS($ly), n#0, m#0)
     == _module.__default.mult($ly, n#0, m#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType :: 
  { _module.__default.mult(AsFuelBottom($ly), n#0, m#0) } 
  _module.__default.mult($ly, n#0, m#0) == _module.__default.mult($LZ, n#0, m#0));

// consequence axiom for _module.__default.mult
axiom 15 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType :: 
    { _module.__default.mult($ly, n#0, m#0) } 
    _module.__default.mult#canCall(n#0, m#0)
         || (15 != $FunctionContextHeight
           && 
          $Is(n#0, Tclass._module.Nat())
           && $Is(m#0, Tclass._module.Nat()))
       ==> $Is(_module.__default.mult($ly, n#0, m#0), Tclass._module.Nat()));

function _module.__default.mult#requires(LayerType, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.mult
axiom (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType :: 
  { _module.__default.mult#requires($ly, n#0, m#0) } 
  $Is(n#0, Tclass._module.Nat()) && $Is(m#0, Tclass._module.Nat())
     ==> _module.__default.mult#requires($ly, n#0, m#0) == true);

// definition axiom for _module.__default.mult (revealed)
axiom 15 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType :: 
    { _module.__default.mult($LS($ly), n#0, m#0) } 
    _module.__default.mult#canCall(n#0, m#0)
         || (15 != $FunctionContextHeight
           && 
          $Is(n#0, Tclass._module.Nat())
           && $Is(m#0, Tclass._module.Nat()))
       ==> (!_module.Nat.O_q(n#0)
           ==> (var n'#1 := _module.Nat._h0(n#0); 
            _module.__default.mult#canCall(n'#1, m#0)
               && _module.__default.plus#canCall(m#0, _module.__default.mult($ly, n'#1, m#0))))
         && _module.__default.mult($LS($ly), n#0, m#0)
           == (if _module.Nat.O_q(n#0)
             then #_module.Nat.O()
             else (var n'#0 := _module.Nat._h0(n#0); 
              _module.__default.plus($LS($LZ), m#0, _module.__default.mult($ly, n'#0, m#0)))));

// definition axiom for _module.__default.mult for all literals (revealed)
axiom 15 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType :: 
    {:weight 3} { _module.__default.mult($LS($ly), Lit(n#0), Lit(m#0)) } 
    _module.__default.mult#canCall(Lit(n#0), Lit(m#0))
         || (15 != $FunctionContextHeight
           && 
          $Is(n#0, Tclass._module.Nat())
           && $Is(m#0, Tclass._module.Nat()))
       ==> (!Lit(_module.Nat.O_q(Lit(n#0)))
           ==> (var n'#3 := Lit(_module.Nat._h0(Lit(n#0))); 
            _module.__default.mult#canCall(n'#3, Lit(m#0))
               && _module.__default.plus#canCall(Lit(m#0), _module.__default.mult($LS($ly), n'#3, Lit(m#0)))))
         && _module.__default.mult($LS($ly), Lit(n#0), Lit(m#0))
           == (if _module.Nat.O_q(Lit(n#0))
             then #_module.Nat.O()
             else (var n'#2 := Lit(_module.Nat._h0(Lit(n#0))); 
              Lit(_module.__default.plus($LS($LZ), Lit(m#0), Lit(_module.__default.mult($LS($ly), n'#2, Lit(m#0))))))));

procedure CheckWellformed$$_module.__default.mult(n#0: DatatypeType where $Is(n#0, Tclass._module.Nat()), 
    m#0: DatatypeType where $Is(m#0, Tclass._module.Nat()));
  free requires 15 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.mult(n#0: DatatypeType, m#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: DatatypeType;
  var n'#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var ##n#0: DatatypeType;
  var ##m#0: DatatypeType;
  var ##n#1: DatatypeType;
  var ##m#1: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function mult
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(192,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.mult($LS($LZ), n#0, m#0), Tclass._module.Nat());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (n#0 == #_module.Nat.O())
        {
            assume _module.__default.mult($LS($LZ), n#0, m#0) == Lit(#_module.Nat.O());
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.mult($LS($LZ), n#0, m#0), Tclass._module.Nat());
        }
        else if (n#0 == #_module.Nat.S(_mcc#0#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.Nat());
            havoc n'#Z#0;
            assume $Is(n'#Z#0, Tclass._module.Nat());
            assume let#0#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.Nat());
            assume n'#Z#0 == let#0#0#0;
            ##n#0 := n'#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0, Tclass._module.Nat(), $Heap);
            ##m#0 := m#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#0, Tclass._module.Nat(), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(##n#0) < DtRank(n#0)
               || (DtRank(##n#0) == DtRank(n#0) && DtRank(##m#0) < DtRank(m#0));
            assume _module.__default.mult#canCall(n'#Z#0, m#0);
            ##n#1 := m#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#1, Tclass._module.Nat(), $Heap);
            ##m#1 := _module.__default.mult($LS($LZ), n'#Z#0, m#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#1, Tclass._module.Nat(), $Heap);
            b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.plus#canCall(m#0, _module.__default.mult($LS($LZ), n'#Z#0, m#0));
            assume _module.__default.mult($LS($LZ), n#0, m#0)
               == _module.__default.plus($LS($LZ), m#0, _module.__default.mult($LS($LZ), n'#Z#0, m#0));
            assume _module.__default.mult#canCall(n'#Z#0, m#0)
               && _module.__default.plus#canCall(m#0, _module.__default.mult($LS($LZ), n'#Z#0, m#0));
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.mult($LS($LZ), n#0, m#0), Tclass._module.Nat());
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



procedure CheckWellformed$$_module.__default.test__mult();
  free requires 50 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.test__mult();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.test__mult() returns ($_reverifyPost: bool);
  free requires 50 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.test__mult() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var n3#0: DatatypeType
     where $Is(n3#0, Tclass._module.Nat()) && $IsAlloc(n3#0, Tclass._module.Nat(), $Heap);
  var n9#0: DatatypeType
     where $Is(n9#0, Tclass._module.Nat()) && $IsAlloc(n9#0, Tclass._module.Nat(), $Heap);
  var ##n#0: DatatypeType;
  var ##m#0: DatatypeType;

    // AddMethodImpl: test_mult, Impl$$_module.__default.test__mult
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(200,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(201,10)
    assume true;
    assume true;
    n3#0 := Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.O())))))));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(201,22)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(202,10)
    assume true;
    assume true;
    n9#0 := Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.O())))))))))))))))))));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(202,40)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(203,3)
    ##n#0 := n3#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#0, Tclass._module.Nat(), $Heap);
    ##m#0 := n3#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##m#0, Tclass._module.Nat(), $Heap);
    assume _module.__default.mult#canCall(n3#0, n3#0);
    assume $IsA#_module.Nat(_module.__default.mult($LS($LZ), n3#0, n3#0))
       && $IsA#_module.Nat(n9#0)
       && _module.__default.mult#canCall(n3#0, n3#0);
    assert {:subsumption 0} _module.Nat#Equal(_module.__default.mult($LS($LS($LZ)), n3#0, n3#0), n9#0);
    assume _module.Nat#Equal(_module.__default.mult($LS($LZ), n3#0, n3#0), n9#0);
}



// function declaration for _module._default.minus
function _module.__default.minus($ly: LayerType, n#0: DatatypeType, m#0: DatatypeType) : DatatypeType;

function _module.__default.minus#canCall(n#0: DatatypeType, m#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType :: 
  { _module.__default.minus($LS($ly), n#0, m#0) } 
  _module.__default.minus($LS($ly), n#0, m#0)
     == _module.__default.minus($ly, n#0, m#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType :: 
  { _module.__default.minus(AsFuelBottom($ly), n#0, m#0) } 
  _module.__default.minus($ly, n#0, m#0) == _module.__default.minus($LZ, n#0, m#0));

// consequence axiom for _module.__default.minus
axiom 16 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType :: 
    { _module.__default.minus($ly, n#0, m#0) } 
    _module.__default.minus#canCall(n#0, m#0)
         || (16 != $FunctionContextHeight
           && 
          $Is(n#0, Tclass._module.Nat())
           && $Is(m#0, Tclass._module.Nat()))
       ==> $Is(_module.__default.minus($ly, n#0, m#0), Tclass._module.Nat()));

function _module.__default.minus#requires(LayerType, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.minus
axiom (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType :: 
  { _module.__default.minus#requires($ly, n#0, m#0) } 
  $Is(n#0, Tclass._module.Nat()) && $Is(m#0, Tclass._module.Nat())
     ==> _module.__default.minus#requires($ly, n#0, m#0) == true);

// definition axiom for _module.__default.minus (revealed)
axiom 16 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType :: 
    { _module.__default.minus($LS($ly), n#0, m#0) } 
    _module.__default.minus#canCall(n#0, m#0)
         || (16 != $FunctionContextHeight
           && 
          $Is(n#0, Tclass._module.Nat())
           && $Is(m#0, Tclass._module.Nat()))
       ==> (!_module.Nat.O_q(n#0)
           ==> (var n'#1 := _module.Nat._h0(n#0); 
            !_module.Nat.O_q(m#0)
               ==> (var m'#1 := _module.Nat._h0(m#0); _module.__default.minus#canCall(n'#1, m'#1))))
         && _module.__default.minus($LS($ly), n#0, m#0)
           == (if _module.Nat.O_q(n#0)
             then #_module.Nat.O()
             else (var n'#0 := _module.Nat._h0(n#0); 
              (if _module.Nat.O_q(m#0)
                 then n#0
                 else (var m'#0 := _module.Nat._h0(m#0); _module.__default.minus($ly, n'#0, m'#0))))));

// definition axiom for _module.__default.minus for all literals (revealed)
axiom 16 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType :: 
    {:weight 3} { _module.__default.minus($LS($ly), Lit(n#0), Lit(m#0)) } 
    _module.__default.minus#canCall(Lit(n#0), Lit(m#0))
         || (16 != $FunctionContextHeight
           && 
          $Is(n#0, Tclass._module.Nat())
           && $Is(m#0, Tclass._module.Nat()))
       ==> (!Lit(_module.Nat.O_q(Lit(n#0)))
           ==> (var n'#3 := Lit(_module.Nat._h0(Lit(n#0))); 
            !Lit(_module.Nat.O_q(Lit(m#0)))
               ==> (var m'#3 := Lit(_module.Nat._h0(Lit(m#0))); 
                _module.__default.minus#canCall(n'#3, m'#3))))
         && _module.__default.minus($LS($ly), Lit(n#0), Lit(m#0))
           == (if _module.Nat.O_q(Lit(n#0))
             then #_module.Nat.O()
             else (var n'#2 := Lit(_module.Nat._h0(Lit(n#0))); 
              (if _module.Nat.O_q(Lit(m#0))
                 then n#0
                 else (var m'#2 := Lit(_module.Nat._h0(Lit(m#0))); 
                  Lit(_module.__default.minus($LS($ly), n'#2, m'#2)))))));

procedure CheckWellformed$$_module.__default.minus(n#0: DatatypeType where $Is(n#0, Tclass._module.Nat()), 
    m#0: DatatypeType where $Is(m#0, Tclass._module.Nat()));
  free requires 16 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.minus(n#0: DatatypeType, m#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: DatatypeType;
  var n'#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var _mcc#1#0: DatatypeType;
  var m'#Z#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var ##n#0: DatatypeType;
  var ##m#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function minus
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(206,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.minus($LS($LZ), n#0, m#0), Tclass._module.Nat());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (n#0 == #_module.Nat.O())
        {
            assume _module.__default.minus($LS($LZ), n#0, m#0) == Lit(#_module.Nat.O());
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.minus($LS($LZ), n#0, m#0), Tclass._module.Nat());
        }
        else if (n#0 == #_module.Nat.S(_mcc#0#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.Nat());
            havoc n'#Z#0;
            assume $Is(n'#Z#0, Tclass._module.Nat());
            assume let#0#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.Nat());
            assume n'#Z#0 == let#0#0#0;
            if (m#0 == #_module.Nat.O())
            {
                assume _module.__default.minus($LS($LZ), n#0, m#0) == n#0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.minus($LS($LZ), n#0, m#0), Tclass._module.Nat());
            }
            else if (m#0 == #_module.Nat.S(_mcc#1#0))
            {
                assume $Is(_mcc#1#0, Tclass._module.Nat());
                havoc m'#Z#0;
                assume $Is(m'#Z#0, Tclass._module.Nat());
                assume let#1#0#0 == _mcc#1#0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(let#1#0#0, Tclass._module.Nat());
                assume m'#Z#0 == let#1#0#0;
                ##n#0 := n'#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#0, Tclass._module.Nat(), $Heap);
                ##m#0 := m'#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##m#0, Tclass._module.Nat(), $Heap);
                b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assert DtRank(##n#0) < DtRank(n#0)
                   || (DtRank(##n#0) == DtRank(n#0) && DtRank(##m#0) < DtRank(m#0));
                assume _module.__default.minus#canCall(n'#Z#0, m'#Z#0);
                assume _module.__default.minus($LS($LZ), n#0, m#0)
                   == _module.__default.minus($LS($LZ), n'#Z#0, m'#Z#0);
                assume _module.__default.minus#canCall(n'#Z#0, m'#Z#0);
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.minus($LS($LZ), n#0, m#0), Tclass._module.Nat());
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



// function declaration for _module._default.exp
function _module.__default.exp($ly: LayerType, base#0: DatatypeType, power#0: DatatypeType) : DatatypeType;

function _module.__default.exp#canCall(base#0: DatatypeType, power#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, base#0: DatatypeType, power#0: DatatypeType :: 
  { _module.__default.exp($LS($ly), base#0, power#0) } 
  _module.__default.exp($LS($ly), base#0, power#0)
     == _module.__default.exp($ly, base#0, power#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, base#0: DatatypeType, power#0: DatatypeType :: 
  { _module.__default.exp(AsFuelBottom($ly), base#0, power#0) } 
  _module.__default.exp($ly, base#0, power#0)
     == _module.__default.exp($LZ, base#0, power#0));

// consequence axiom for _module.__default.exp
axiom 17 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, base#0: DatatypeType, power#0: DatatypeType :: 
    { _module.__default.exp($ly, base#0, power#0) } 
    _module.__default.exp#canCall(base#0, power#0)
         || (17 != $FunctionContextHeight
           && 
          $Is(base#0, Tclass._module.Nat())
           && $Is(power#0, Tclass._module.Nat()))
       ==> $Is(_module.__default.exp($ly, base#0, power#0), Tclass._module.Nat()));

function _module.__default.exp#requires(LayerType, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.exp
axiom (forall $ly: LayerType, base#0: DatatypeType, power#0: DatatypeType :: 
  { _module.__default.exp#requires($ly, base#0, power#0) } 
  $Is(base#0, Tclass._module.Nat()) && $Is(power#0, Tclass._module.Nat())
     ==> _module.__default.exp#requires($ly, base#0, power#0) == true);

// definition axiom for _module.__default.exp (revealed)
axiom 17 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, base#0: DatatypeType, power#0: DatatypeType :: 
    { _module.__default.exp($LS($ly), base#0, power#0) } 
    _module.__default.exp#canCall(base#0, power#0)
         || (17 != $FunctionContextHeight
           && 
          $Is(base#0, Tclass._module.Nat())
           && $Is(power#0, Tclass._module.Nat()))
       ==> (!_module.Nat.O_q(power#0)
           ==> (var p#1 := _module.Nat._h0(power#0); 
            _module.__default.exp#canCall(base#0, p#1)
               && _module.__default.mult#canCall(base#0, _module.__default.exp($ly, base#0, p#1))))
         && _module.__default.exp($LS($ly), base#0, power#0)
           == (if _module.Nat.O_q(power#0)
             then #_module.Nat.S(Lit(#_module.Nat.O()))
             else (var p#0 := _module.Nat._h0(power#0); 
              _module.__default.mult($LS($LZ), base#0, _module.__default.exp($ly, base#0, p#0)))));

// definition axiom for _module.__default.exp for all literals (revealed)
axiom 17 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, base#0: DatatypeType, power#0: DatatypeType :: 
    {:weight 3} { _module.__default.exp($LS($ly), Lit(base#0), Lit(power#0)) } 
    _module.__default.exp#canCall(Lit(base#0), Lit(power#0))
         || (17 != $FunctionContextHeight
           && 
          $Is(base#0, Tclass._module.Nat())
           && $Is(power#0, Tclass._module.Nat()))
       ==> (!Lit(_module.Nat.O_q(Lit(power#0)))
           ==> (var p#3 := Lit(_module.Nat._h0(Lit(power#0))); 
            _module.__default.exp#canCall(Lit(base#0), p#3)
               && _module.__default.mult#canCall(Lit(base#0), _module.__default.exp($LS($ly), Lit(base#0), p#3))))
         && _module.__default.exp($LS($ly), Lit(base#0), Lit(power#0))
           == (if _module.Nat.O_q(Lit(power#0))
             then #_module.Nat.S(Lit(#_module.Nat.O()))
             else (var p#2 := Lit(_module.Nat._h0(Lit(power#0))); 
              Lit(_module.__default.mult($LS($LZ), Lit(base#0), Lit(_module.__default.exp($LS($ly), Lit(base#0), p#2)))))));

procedure CheckWellformed$$_module.__default.exp(base#0: DatatypeType where $Is(base#0, Tclass._module.Nat()), 
    power#0: DatatypeType where $Is(power#0, Tclass._module.Nat()));
  free requires 17 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.exp(base#0: DatatypeType, power#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: DatatypeType;
  var p#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var ##base#0: DatatypeType;
  var ##power#0: DatatypeType;
  var ##n#0: DatatypeType;
  var ##m#0: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function exp
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(216,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.exp($LS($LZ), base#0, power#0), Tclass._module.Nat());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (power#0 == #_module.Nat.O())
        {
            assume _module.__default.exp($LS($LZ), base#0, power#0)
               == Lit(#_module.Nat.S(Lit(#_module.Nat.O())));
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.exp($LS($LZ), base#0, power#0), Tclass._module.Nat());
        }
        else if (power#0 == #_module.Nat.S(_mcc#0#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.Nat());
            havoc p#Z#0;
            assume $Is(p#Z#0, Tclass._module.Nat());
            assume let#0#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.Nat());
            assume p#Z#0 == let#0#0#0;
            ##base#0 := base#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##base#0, Tclass._module.Nat(), $Heap);
            ##power#0 := p#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##power#0, Tclass._module.Nat(), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(##base#0) < DtRank(base#0)
               || (DtRank(##base#0) == DtRank(base#0) && DtRank(##power#0) < DtRank(power#0));
            assume _module.__default.exp#canCall(base#0, p#Z#0);
            ##n#0 := base#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0, Tclass._module.Nat(), $Heap);
            ##m#0 := _module.__default.exp($LS($LZ), base#0, p#Z#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#0, Tclass._module.Nat(), $Heap);
            b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.mult#canCall(base#0, _module.__default.exp($LS($LZ), base#0, p#Z#0));
            assume _module.__default.exp($LS($LZ), base#0, power#0)
               == _module.__default.mult($LS($LZ), base#0, _module.__default.exp($LS($LZ), base#0, p#Z#0));
            assume _module.__default.exp#canCall(base#0, p#Z#0)
               && _module.__default.mult#canCall(base#0, _module.__default.exp($LS($LZ), base#0, p#Z#0));
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.exp($LS($LZ), base#0, power#0), Tclass._module.Nat());
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



// function declaration for _module._default.factorial
function _module.__default.factorial($ly: LayerType, n#0: DatatypeType) : DatatypeType;

function _module.__default.factorial#canCall(n#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, n#0: DatatypeType :: 
  { _module.__default.factorial($LS($ly), n#0) } 
  _module.__default.factorial($LS($ly), n#0)
     == _module.__default.factorial($ly, n#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, n#0: DatatypeType :: 
  { _module.__default.factorial(AsFuelBottom($ly), n#0) } 
  _module.__default.factorial($ly, n#0) == _module.__default.factorial($LZ, n#0));

// consequence axiom for _module.__default.factorial
axiom 18 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: DatatypeType :: 
    { _module.__default.factorial($ly, n#0) } 
    _module.__default.factorial#canCall(n#0)
         || (18 != $FunctionContextHeight && $Is(n#0, Tclass._module.Nat()))
       ==> $Is(_module.__default.factorial($ly, n#0), Tclass._module.Nat()));

function _module.__default.factorial#requires(LayerType, DatatypeType) : bool;

// #requires axiom for _module.__default.factorial
axiom (forall $ly: LayerType, n#0: DatatypeType :: 
  { _module.__default.factorial#requires($ly, n#0) } 
  $Is(n#0, Tclass._module.Nat())
     ==> _module.__default.factorial#requires($ly, n#0) == true);

// definition axiom for _module.__default.factorial (revealed)
axiom 18 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: DatatypeType :: 
    { _module.__default.factorial($LS($ly), n#0) } 
    _module.__default.factorial#canCall(n#0)
         || (18 != $FunctionContextHeight && $Is(n#0, Tclass._module.Nat()))
       ==> (!_module.Nat.O_q(n#0)
           ==> (var n'#1 := _module.Nat._h0(n#0); 
            _module.__default.factorial#canCall(n'#1)
               && _module.__default.mult#canCall(n#0, _module.__default.factorial($ly, n'#1))))
         && _module.__default.factorial($LS($ly), n#0)
           == (if _module.Nat.O_q(n#0)
             then #_module.Nat.S(Lit(#_module.Nat.O()))
             else (var n'#0 := _module.Nat._h0(n#0); 
              _module.__default.mult($LS($LZ), n#0, _module.__default.factorial($ly, n'#0)))));

// definition axiom for _module.__default.factorial for all literals (revealed)
axiom 18 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: DatatypeType :: 
    {:weight 3} { _module.__default.factorial($LS($ly), Lit(n#0)) } 
    _module.__default.factorial#canCall(Lit(n#0))
         || (18 != $FunctionContextHeight && $Is(n#0, Tclass._module.Nat()))
       ==> (!Lit(_module.Nat.O_q(Lit(n#0)))
           ==> (var n'#3 := Lit(_module.Nat._h0(Lit(n#0))); 
            _module.__default.factorial#canCall(n'#3)
               && _module.__default.mult#canCall(Lit(n#0), _module.__default.factorial($LS($ly), n'#3))))
         && _module.__default.factorial($LS($ly), Lit(n#0))
           == (if _module.Nat.O_q(Lit(n#0))
             then #_module.Nat.S(Lit(#_module.Nat.O()))
             else (var n'#2 := Lit(_module.Nat._h0(Lit(n#0))); 
              Lit(_module.__default.mult($LS($LZ), Lit(n#0), Lit(_module.__default.factorial($LS($ly), n'#2)))))));

procedure CheckWellformed$$_module.__default.factorial(n#0: DatatypeType where $Is(n#0, Tclass._module.Nat()));
  free requires 18 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.factorial(n#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: DatatypeType;
  var n'#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var ##n#0: DatatypeType;
  var ##n#1: DatatypeType;
  var ##m#0: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function factorial
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(225,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.factorial($LS($LZ), n#0), Tclass._module.Nat());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (n#0 == #_module.Nat.O())
        {
            assume _module.__default.factorial($LS($LZ), n#0)
               == Lit(#_module.Nat.S(Lit(#_module.Nat.O())));
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.factorial($LS($LZ), n#0), Tclass._module.Nat());
        }
        else if (n#0 == #_module.Nat.S(_mcc#0#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.Nat());
            havoc n'#Z#0;
            assume $Is(n'#Z#0, Tclass._module.Nat());
            assume let#0#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.Nat());
            assume n'#Z#0 == let#0#0#0;
            ##n#0 := n'#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0, Tclass._module.Nat(), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(##n#0) < DtRank(n#0);
            assume _module.__default.factorial#canCall(n'#Z#0);
            ##n#1 := n#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#1, Tclass._module.Nat(), $Heap);
            ##m#0 := _module.__default.factorial($LS($LZ), n'#Z#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#0, Tclass._module.Nat(), $Heap);
            b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.mult#canCall(n#0, _module.__default.factorial($LS($LZ), n'#Z#0));
            assume _module.__default.factorial($LS($LZ), n#0)
               == _module.__default.mult($LS($LZ), n#0, _module.__default.factorial($LS($LZ), n'#Z#0));
            assume _module.__default.factorial#canCall(n'#Z#0)
               && _module.__default.mult#canCall(n#0, _module.__default.factorial($LS($LZ), n'#Z#0));
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.factorial($LS($LZ), n#0), Tclass._module.Nat());
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



procedure CheckWellformed$$_module.__default.test__factorial1();
  free requires 51 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.test__factorial1();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.test__factorial1() returns ($_reverifyPost: bool);
  free requires 51 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.test__factorial1() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var n2#0: DatatypeType
     where $Is(n2#0, Tclass._module.Nat()) && $IsAlloc(n2#0, Tclass._module.Nat(), $Heap);
  var n3#0: DatatypeType
     where $Is(n3#0, Tclass._module.Nat()) && $IsAlloc(n3#0, Tclass._module.Nat(), $Heap);
  var n5#0: DatatypeType
     where $Is(n5#0, Tclass._module.Nat()) && $IsAlloc(n5#0, Tclass._module.Nat(), $Heap);
  var n6#0: DatatypeType
     where $Is(n6#0, Tclass._module.Nat()) && $IsAlloc(n6#0, Tclass._module.Nat(), $Heap);
  var ##n#0: DatatypeType;
  var n10#0: DatatypeType
     where $Is(n10#0, Tclass._module.Nat()) && $IsAlloc(n10#0, Tclass._module.Nat(), $Heap);
  var n12#0: DatatypeType
     where $Is(n12#0, Tclass._module.Nat()) && $IsAlloc(n12#0, Tclass._module.Nat(), $Heap);
  var ##n#1: DatatypeType;
  var ##n#2: DatatypeType;
  var ##m#0: DatatypeType;

    // AddMethodImpl: test_factorial1, Impl$$_module.__default.test__factorial1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(233,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(234,10)
    assume true;
    assume true;
    n2#0 := Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.O())))));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(234,19)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(235,10)
    assume true;
    assume true;
    n3#0 := #_module.Nat.S(n2#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(235,17)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(236,10)
    assume true;
    assume true;
    n5#0 := #_module.Nat.S(#_module.Nat.S(n3#0));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(236,20)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(237,10)
    assume true;
    assume true;
    n6#0 := #_module.Nat.S(n5#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(237,17)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(238,3)
    ##n#0 := n3#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#0, Tclass._module.Nat(), $Heap);
    assume _module.__default.factorial#canCall(n3#0);
    assume $IsA#_module.Nat(_module.__default.factorial($LS($LZ), n3#0))
       && $IsA#_module.Nat(n6#0)
       && _module.__default.factorial#canCall(n3#0);
    assert {:subsumption 0} _module.Nat#Equal(_module.__default.factorial($LS($LS($LZ)), n3#0), n6#0);
    assume _module.Nat#Equal(_module.__default.factorial($LS($LZ), n3#0), n6#0);
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(240,11)
    assume true;
    assume true;
    n10#0 := #_module.Nat.S(#_module.Nat.S(#_module.Nat.S(#_module.Nat.S(n6#0))));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(240,27)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(241,11)
    assume true;
    assume true;
    n12#0 := #_module.Nat.S(#_module.Nat.S(n10#0));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(241,22)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(243,3)
    ##n#1 := n5#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#1, Tclass._module.Nat(), $Heap);
    assume _module.__default.factorial#canCall(n5#0);
    ##n#2 := n10#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#2, Tclass._module.Nat(), $Heap);
    ##m#0 := n12#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##m#0, Tclass._module.Nat(), $Heap);
    assume _module.__default.mult#canCall(n10#0, n12#0);
    assume $IsA#_module.Nat(_module.__default.factorial($LS($LZ), n5#0))
       && $IsA#_module.Nat(_module.__default.mult($LS($LZ), n10#0, n12#0))
       && 
      _module.__default.factorial#canCall(n5#0)
       && _module.__default.mult#canCall(n10#0, n12#0);
    assert {:subsumption 0} _module.Nat#Equal(_module.__default.factorial($LS($LS($LZ)), n5#0), 
      _module.__default.mult($LS($LS($LZ)), n10#0, n12#0));
    assume _module.Nat#Equal(_module.__default.factorial($LS($LZ), n5#0), 
      _module.__default.mult($LS($LZ), n10#0, n12#0));
}



procedure CheckWellformed$$_module.__default.test__factorial1__old();
  free requires 52 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.test__factorial1__old();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.test__factorial1__old() returns ($_reverifyPost: bool);
  free requires 52 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.test__factorial1__old() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var n2#0: DatatypeType
     where $Is(n2#0, Tclass._module.Nat()) && $IsAlloc(n2#0, Tclass._module.Nat(), $Heap);
  var n3#0: DatatypeType
     where $Is(n3#0, Tclass._module.Nat()) && $IsAlloc(n3#0, Tclass._module.Nat(), $Heap);
  var n5#0: DatatypeType
     where $Is(n5#0, Tclass._module.Nat()) && $IsAlloc(n5#0, Tclass._module.Nat(), $Heap);
  var n6#0: DatatypeType
     where $Is(n6#0, Tclass._module.Nat()) && $IsAlloc(n6#0, Tclass._module.Nat(), $Heap);
  var ##n#0: DatatypeType;
  var n10#0: DatatypeType
     where $Is(n10#0, Tclass._module.Nat()) && $IsAlloc(n10#0, Tclass._module.Nat(), $Heap);
  var n12#0: DatatypeType
     where $Is(n12#0, Tclass._module.Nat()) && $IsAlloc(n12#0, Tclass._module.Nat(), $Heap);
  var ##n#0_0_0: DatatypeType;
  var ##m#0_0_0: DatatypeType;
  var ##n#0_0_1: DatatypeType;
  var ##m#0_0_1: DatatypeType;
  var ##n#0_0_2: DatatypeType;
  var ##m#0_0_2: DatatypeType;
  var ##n#0_0_3: DatatypeType;
  var ##m#0_0_3: DatatypeType;
  var ##n#0_0_4: DatatypeType;
  var ##m#0_0_4: DatatypeType;
  var m##0_0_0: DatatypeType;
  var n##0_0_0: DatatypeType;
  var ##n#0_0_5: DatatypeType;
  var ##m#0_0_5: DatatypeType;
  var ##n#0_0_6: DatatypeType;
  var ##m#0_0_6: DatatypeType;
  var ##n#0_1_0: DatatypeType;
  var m##0_1_0: DatatypeType;
  var n##0_1_0: DatatypeType;
  var ##n#0_1_1: DatatypeType;
  var ##m#0_1_0: DatatypeType;
  var ##n#0_1_2: DatatypeType;
  var ##m#0_1_1: DatatypeType;
  var ##n#0_1_3: DatatypeType;
  var ##m#0_1_2: DatatypeType;
  var ##n#0_1_4: DatatypeType;
  var ##m#0_1_3: DatatypeType;
  var ##n#0_1_5: DatatypeType;
  var ##m#0_1_4: DatatypeType;
  var ##n#0_0: DatatypeType;

    // AddMethodImpl: test_factorial1_old, Impl$$_module.__default.test__factorial1__old
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(247,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(248,10)
    assume true;
    assume true;
    n2#0 := Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.O())))));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(248,19)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(249,10)
    assume true;
    assume true;
    n3#0 := #_module.Nat.S(n2#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(249,17)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(250,10)
    assume true;
    assume true;
    n5#0 := #_module.Nat.S(#_module.Nat.S(n3#0));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(250,20)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(251,10)
    assume true;
    assume true;
    n6#0 := #_module.Nat.S(n5#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(251,17)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(252,3)
    ##n#0 := n3#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#0, Tclass._module.Nat(), $Heap);
    assume _module.__default.factorial#canCall(n3#0);
    assume $IsA#_module.Nat(_module.__default.factorial($LS($LZ), n3#0))
       && $IsA#_module.Nat(n6#0)
       && _module.__default.factorial#canCall(n3#0);
    assert {:subsumption 0} _module.Nat#Equal(_module.__default.factorial($LS($LS($LZ)), n3#0), n6#0);
    assume _module.Nat#Equal(_module.__default.factorial($LS($LZ), n3#0), n6#0);
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(254,11)
    assume true;
    assume true;
    n10#0 := #_module.Nat.S(#_module.Nat.S(#_module.Nat.S(#_module.Nat.S(n6#0))));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(254,27)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(255,11)
    assume true;
    assume true;
    n12#0 := #_module.Nat.S(#_module.Nat.S(n10#0));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(255,22)"} true;
    // ----- calc statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(258,3)
    // Assume Fuel Constant
    if (*)
    {
        // ----- assert wf[initial] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(258,3)
        ##n#0_0 := n5#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#0_0, Tclass._module.Nat(), $Heap);
        assume _module.__default.factorial#canCall(n5#0);
        assume _module.__default.factorial#canCall(n5#0);
        assume false;
    }
    else if (*)
    {
        // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(258,3)
        ##n#0_1_0 := n5#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#0_1_0, Tclass._module.Nat(), $Heap);
        assume _module.__default.factorial#canCall(n5#0);
        assume _module.__default.factorial#canCall(n5#0);
        // ----- Hint0 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(258,3)
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(260,19)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        m##0_1_0 := n2#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        n##0_1_0 := n6#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.mult__lemma(m##0_1_0, n##0_1_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(260,26)"} true;
        // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(258,3)
        ##n#0_1_1 := n6#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#0_1_1, Tclass._module.Nat(), $Heap);
        ##m#0_1_0 := n6#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##m#0_1_0, Tclass._module.Nat(), $Heap);
        assume _module.__default.plus#canCall(n6#0, n6#0);
        ##n#0_1_2 := n6#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#0_1_2, Tclass._module.Nat(), $Heap);
        ##m#0_1_1 := n6#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##m#0_1_1, Tclass._module.Nat(), $Heap);
        assume _module.__default.plus#canCall(n6#0, n6#0);
        ##n#0_1_3 := _module.__default.plus($LS($LZ), n6#0, n6#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#0_1_3, Tclass._module.Nat(), $Heap);
        ##m#0_1_2 := Lit(#_module.Nat.O());
        // assume allocatedness for argument to function
        assume $IsAlloc(##m#0_1_2, Tclass._module.Nat(), $Heap);
        assume _module.__default.plus#canCall(_module.__default.plus($LS($LZ), n6#0, n6#0), Lit(#_module.Nat.O()));
        ##n#0_1_4 := _module.__default.plus($LS($LZ), n6#0, n6#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#0_1_4, Tclass._module.Nat(), $Heap);
        ##m#0_1_3 := _module.__default.plus($LS($LZ), _module.__default.plus($LS($LZ), n6#0, n6#0), Lit(#_module.Nat.O()));
        // assume allocatedness for argument to function
        assume $IsAlloc(##m#0_1_3, Tclass._module.Nat(), $Heap);
        assume _module.__default.plus#canCall(_module.__default.plus($LS($LZ), n6#0, n6#0), 
          _module.__default.plus($LS($LZ), _module.__default.plus($LS($LZ), n6#0, n6#0), Lit(#_module.Nat.O())));
        ##n#0_1_5 := n5#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#0_1_5, Tclass._module.Nat(), $Heap);
        ##m#0_1_4 := _module.__default.plus($LS($LZ), 
          _module.__default.plus($LS($LZ), n6#0, n6#0), 
          _module.__default.plus($LS($LZ), _module.__default.plus($LS($LZ), n6#0, n6#0), Lit(#_module.Nat.O())));
        // assume allocatedness for argument to function
        assume $IsAlloc(##m#0_1_4, Tclass._module.Nat(), $Heap);
        assume _module.__default.mult#canCall(n5#0, 
          _module.__default.plus($LS($LZ), 
            _module.__default.plus($LS($LZ), n6#0, n6#0), 
            _module.__default.plus($LS($LZ), _module.__default.plus($LS($LZ), n6#0, n6#0), Lit(#_module.Nat.O()))));
        assume _module.__default.plus#canCall(n6#0, n6#0)
           && 
          _module.__default.plus#canCall(n6#0, n6#0)
           && _module.__default.plus#canCall(_module.__default.plus($LS($LZ), n6#0, n6#0), Lit(#_module.Nat.O()))
           && _module.__default.plus#canCall(_module.__default.plus($LS($LZ), n6#0, n6#0), 
            _module.__default.plus($LS($LZ), _module.__default.plus($LS($LZ), n6#0, n6#0), Lit(#_module.Nat.O())))
           && _module.__default.mult#canCall(n5#0, 
            _module.__default.plus($LS($LZ), 
              _module.__default.plus($LS($LZ), n6#0, n6#0), 
              _module.__default.plus($LS($LZ), _module.__default.plus($LS($LZ), n6#0, n6#0), Lit(#_module.Nat.O()))));
        // ----- assert line0 == line1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(258,3)
        assert {:subsumption 0} _module.Nat#Equal(_module.__default.factorial($LS($LS($LZ)), n5#0), 
          _module.__default.mult($LS($LS($LZ)), 
            n5#0, 
            _module.__default.plus($LS($LS($LZ)), 
              _module.__default.plus($LS($LS($LZ)), n6#0, n6#0), 
              _module.__default.plus($LS($LS($LZ)), 
                _module.__default.plus($LS($LS($LZ)), n6#0, n6#0), 
                Lit(#_module.Nat.O())))));
        assume false;
    }
    else if (*)
    {
        // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(258,3)
        ##n#0_0_0 := n6#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#0_0_0, Tclass._module.Nat(), $Heap);
        ##m#0_0_0 := n6#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##m#0_0_0, Tclass._module.Nat(), $Heap);
        assume _module.__default.plus#canCall(n6#0, n6#0);
        ##n#0_0_1 := n6#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#0_0_1, Tclass._module.Nat(), $Heap);
        ##m#0_0_1 := n6#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##m#0_0_1, Tclass._module.Nat(), $Heap);
        assume _module.__default.plus#canCall(n6#0, n6#0);
        ##n#0_0_2 := _module.__default.plus($LS($LZ), n6#0, n6#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#0_0_2, Tclass._module.Nat(), $Heap);
        ##m#0_0_2 := Lit(#_module.Nat.O());
        // assume allocatedness for argument to function
        assume $IsAlloc(##m#0_0_2, Tclass._module.Nat(), $Heap);
        assume _module.__default.plus#canCall(_module.__default.plus($LS($LZ), n6#0, n6#0), Lit(#_module.Nat.O()));
        ##n#0_0_3 := _module.__default.plus($LS($LZ), n6#0, n6#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#0_0_3, Tclass._module.Nat(), $Heap);
        ##m#0_0_3 := _module.__default.plus($LS($LZ), _module.__default.plus($LS($LZ), n6#0, n6#0), Lit(#_module.Nat.O()));
        // assume allocatedness for argument to function
        assume $IsAlloc(##m#0_0_3, Tclass._module.Nat(), $Heap);
        assume _module.__default.plus#canCall(_module.__default.plus($LS($LZ), n6#0, n6#0), 
          _module.__default.plus($LS($LZ), _module.__default.plus($LS($LZ), n6#0, n6#0), Lit(#_module.Nat.O())));
        ##n#0_0_4 := n5#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#0_0_4, Tclass._module.Nat(), $Heap);
        ##m#0_0_4 := _module.__default.plus($LS($LZ), 
          _module.__default.plus($LS($LZ), n6#0, n6#0), 
          _module.__default.plus($LS($LZ), _module.__default.plus($LS($LZ), n6#0, n6#0), Lit(#_module.Nat.O())));
        // assume allocatedness for argument to function
        assume $IsAlloc(##m#0_0_4, Tclass._module.Nat(), $Heap);
        assume _module.__default.mult#canCall(n5#0, 
          _module.__default.plus($LS($LZ), 
            _module.__default.plus($LS($LZ), n6#0, n6#0), 
            _module.__default.plus($LS($LZ), _module.__default.plus($LS($LZ), n6#0, n6#0), Lit(#_module.Nat.O()))));
        assume _module.__default.plus#canCall(n6#0, n6#0)
           && 
          _module.__default.plus#canCall(n6#0, n6#0)
           && _module.__default.plus#canCall(_module.__default.plus($LS($LZ), n6#0, n6#0), Lit(#_module.Nat.O()))
           && _module.__default.plus#canCall(_module.__default.plus($LS($LZ), n6#0, n6#0), 
            _module.__default.plus($LS($LZ), _module.__default.plus($LS($LZ), n6#0, n6#0), Lit(#_module.Nat.O())))
           && _module.__default.mult#canCall(n5#0, 
            _module.__default.plus($LS($LZ), 
              _module.__default.plus($LS($LZ), n6#0, n6#0), 
              _module.__default.plus($LS($LZ), _module.__default.plus($LS($LZ), n6#0, n6#0), Lit(#_module.Nat.O()))));
        // ----- Hint1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(258,3)
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(262,19)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        m##0_0_0 := n5#0;
        ##n#0_0_5 := n6#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#0_0_5, Tclass._module.Nat(), $Heap);
        ##m#0_0_5 := n6#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##m#0_0_5, Tclass._module.Nat(), $Heap);
        assume _module.__default.plus#canCall(n6#0, n6#0);
        assume _module.__default.plus#canCall(n6#0, n6#0);
        // ProcessCallStmt: CheckSubrange
        n##0_0_0 := _module.__default.plus($LS($LZ), n6#0, n6#0);
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.mult__lemma(m##0_0_0, n##0_0_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(262,36)"} true;
        // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(258,3)
        ##n#0_0_6 := n10#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#0_0_6, Tclass._module.Nat(), $Heap);
        ##m#0_0_6 := n12#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##m#0_0_6, Tclass._module.Nat(), $Heap);
        assume _module.__default.mult#canCall(n10#0, n12#0);
        assume _module.__default.mult#canCall(n10#0, n12#0);
        // ----- assert line1 == line2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(258,3)
        assert {:subsumption 0} _module.Nat#Equal(_module.__default.mult($LS($LS($LZ)), 
            n5#0, 
            _module.__default.plus($LS($LS($LZ)), 
              _module.__default.plus($LS($LS($LZ)), n6#0, n6#0), 
              _module.__default.plus($LS($LS($LZ)), 
                _module.__default.plus($LS($LS($LZ)), n6#0, n6#0), 
                Lit(#_module.Nat.O())))), 
          _module.__default.mult($LS($LS($LZ)), n10#0, n12#0));
        assume false;
    }

    assume _module.Nat#Equal(_module.__default.factorial($LS($LZ), n5#0), 
      _module.__default.mult($LS($LZ), n10#0, n12#0));
}



procedure {:_induction m#0, n#0} CheckWellformed$$_module.__default.mult__lemma(m#0: DatatypeType
       where $Is(m#0, Tclass._module.Nat())
         && $IsAlloc(m#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(m#0), 
    n#0: DatatypeType
       where $Is(n#0, Tclass._module.Nat())
         && $IsAlloc(n#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(n#0));
  free requires 19 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction m#0, n#0} Call$$_module.__default.mult__lemma(m#0: DatatypeType
       where $Is(m#0, Tclass._module.Nat())
         && $IsAlloc(m#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(m#0), 
    n#0: DatatypeType
       where $Is(n#0, Tclass._module.Nat())
         && $IsAlloc(n#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(n#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Nat(_module.__default.mult($LS($LZ), m#0, _module.__default.plus($LS($LZ), n#0, n#0)))
     && $IsA#_module.Nat(_module.__default.mult($LS($LZ), _module.__default.plus($LS($LZ), m#0, m#0), n#0))
     && 
    _module.__default.plus#canCall(n#0, n#0)
     && _module.__default.mult#canCall(m#0, _module.__default.plus($LS($LZ), n#0, n#0))
     && 
    _module.__default.plus#canCall(m#0, m#0)
     && _module.__default.mult#canCall(_module.__default.plus($LS($LZ), m#0, m#0), n#0);
  ensures _module.Nat#Equal(_module.__default.mult($LS($LS($LZ)), m#0, _module.__default.plus($LS($LS($LZ)), n#0, n#0)), 
    _module.__default.mult($LS($LS($LZ)), _module.__default.plus($LS($LS($LZ)), m#0, m#0), n#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction m#0, n#0} Impl$$_module.__default.mult__lemma(m#0: DatatypeType
       where $Is(m#0, Tclass._module.Nat())
         && $IsAlloc(m#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(m#0), 
    n#0: DatatypeType
       where $Is(n#0, Tclass._module.Nat())
         && $IsAlloc(n#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(n#0))
   returns ($_reverifyPost: bool);
  free requires 19 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Nat(_module.__default.mult($LS($LZ), m#0, _module.__default.plus($LS($LZ), n#0, n#0)))
     && $IsA#_module.Nat(_module.__default.mult($LS($LZ), _module.__default.plus($LS($LZ), m#0, m#0), n#0))
     && 
    _module.__default.plus#canCall(n#0, n#0)
     && _module.__default.mult#canCall(m#0, _module.__default.plus($LS($LZ), n#0, n#0))
     && 
    _module.__default.plus#canCall(m#0, m#0)
     && _module.__default.mult#canCall(_module.__default.plus($LS($LZ), m#0, m#0), n#0);
  ensures _module.Nat#Equal(_module.__default.mult($LS($LS($LZ)), m#0, _module.__default.plus($LS($LS($LZ)), n#0, n#0)), 
    _module.__default.mult($LS($LS($LZ)), _module.__default.plus($LS($LS($LZ)), m#0, m#0), n#0));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction m#0, n#0} Impl$$_module.__default.mult__lemma(m#0: DatatypeType, n#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var _mcc#0#0_0: DatatypeType;
  var m'#0_0: DatatypeType;
  var let#0_0#0#0: DatatypeType;
  var ##n#0_0_0_0: DatatypeType;
  var ##m#0_0_0_0: DatatypeType;
  var ##n#0_0_0_1: DatatypeType;
  var ##m#0_0_0_1: DatatypeType;
  var a#0_0_0_0: DatatypeType;
  var b#0_0_0_0: DatatypeType;
  var ##n#0_0_0_2: DatatypeType;
  var ##m#0_0_0_2: DatatypeType;
  var ##n#0_0_0_3: DatatypeType;
  var ##m#0_0_0_3: DatatypeType;
  var ##n#0_0_0_4: DatatypeType;
  var ##m#0_0_0_4: DatatypeType;
  var ##n#0_0_0_5: DatatypeType;
  var ##m#0_0_0_5: DatatypeType;
  var ##n#0_0_1_0: DatatypeType;
  var ##m#0_0_1_0: DatatypeType;
  var ##n#0_0_1_1: DatatypeType;
  var ##m#0_0_1_1: DatatypeType;
  var ##n#0_0_1_2: DatatypeType;
  var ##m#0_0_1_2: DatatypeType;
  var ##n#0_0_1_3: DatatypeType;
  var ##m#0_0_1_3: DatatypeType;
  var ##n#0_0_2_0: DatatypeType;
  var ##m#0_0_2_0: DatatypeType;
  var ##n#0_0_2_1: DatatypeType;
  var ##m#0_0_2_1: DatatypeType;
  var ##n#0_0_2_2: DatatypeType;
  var ##m#0_0_2_2: DatatypeType;
  var ##n#0_0_2_3: DatatypeType;
  var ##m#0_0_2_3: DatatypeType;
  var ##n#0_0_2_4: DatatypeType;
  var ##m#0_0_2_4: DatatypeType;
  var ##n#0_0_2_5: DatatypeType;
  var ##m#0_0_2_5: DatatypeType;
  var ##n#0_0_3_0: DatatypeType;
  var ##m#0_0_3_0: DatatypeType;
  var ##n#0_0_3_1: DatatypeType;
  var ##m#0_0_3_1: DatatypeType;
  var ##n#0_0_3_2: DatatypeType;
  var ##m#0_0_3_2: DatatypeType;
  var ##n#0_0_3_3: DatatypeType;
  var ##m#0_0_3_3: DatatypeType;
  var a#0_0_3_0: DatatypeType;
  var b#0_0_3_0: DatatypeType;
  var c#0_0_3_0: DatatypeType;
  var ##n#0_0_3_4: DatatypeType;
  var ##m#0_0_3_4: DatatypeType;
  var ##n#0_0_3_5: DatatypeType;
  var ##m#0_0_3_5: DatatypeType;
  var ##n#0_0_3_6: DatatypeType;
  var ##m#0_0_3_6: DatatypeType;
  var ##n#0_0_3_7: DatatypeType;
  var ##m#0_0_3_7: DatatypeType;
  var ##n#0_0_3_8: DatatypeType;
  var ##m#0_0_3_8: DatatypeType;
  var ##n#0_0_3_9: DatatypeType;
  var ##m#0_0_3_9: DatatypeType;
  var ##n#0_0_3_10: DatatypeType;
  var ##m#0_0_3_10: DatatypeType;
  var ##n#0_0_3_11: DatatypeType;
  var ##m#0_0_3_11: DatatypeType;
  var ##n#0_0_4_0: DatatypeType;
  var ##m#0_0_4_0: DatatypeType;
  var ##n#0_0_4_1: DatatypeType;
  var ##m#0_0_4_1: DatatypeType;
  var ##n#0_0_4_2: DatatypeType;
  var ##m#0_0_4_2: DatatypeType;
  var ##n#0_0_4_3: DatatypeType;
  var ##m#0_0_4_3: DatatypeType;
  var ##n#0_0_4_4: DatatypeType;
  var ##m#0_0_4_4: DatatypeType;
  var ##n#0_0_4_5: DatatypeType;
  var ##m#0_0_4_5: DatatypeType;
  var ##n#0_0_4_6: DatatypeType;
  var ##m#0_0_4_6: DatatypeType;
  var ##n#0_0_4_7: DatatypeType;
  var ##m#0_0_4_7: DatatypeType;
  var ##n#0_0_5_0: DatatypeType;
  var ##m#0_0_5_0: DatatypeType;
  var ##n#0_0_5_1: DatatypeType;
  var ##m#0_0_5_1: DatatypeType;
  var ##n#0_0_5_2: DatatypeType;
  var ##m#0_0_5_2: DatatypeType;
  var ##n#0_0_5_3: DatatypeType;
  var ##m#0_0_5_3: DatatypeType;
  var ##n#0_0_5_4: DatatypeType;
  var ##m#0_0_5_4: DatatypeType;
  var ##n#0_0_5_5: DatatypeType;
  var ##m#0_0_5_5: DatatypeType;
  var ##n#0_0_0: DatatypeType;
  var ##m#0_0_0: DatatypeType;
  var ##n#0_0_1: DatatypeType;
  var ##m#0_0_1: DatatypeType;

    // AddMethodImpl: mult_lemma, Impl$$_module.__default.mult__lemma
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(270,0): initial state"} true;
    assume $IsA#_module.Nat(m#0);
    assume $IsA#_module.Nat(n#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#m0#0: DatatypeType, $ih#n0#0: DatatypeType :: 
      $Is($ih#m0#0, Tclass._module.Nat())
           && $Is($ih#n0#0, Tclass._module.Nat())
           && Lit(true)
           && (DtRank($ih#m0#0) < DtRank(m#0)
             || (DtRank($ih#m0#0) == DtRank(m#0) && DtRank($ih#n0#0) < DtRank(n#0)))
         ==> _module.Nat#Equal(_module.__default.mult($LS($LZ), $ih#m0#0, _module.__default.plus($LS($LZ), $ih#n0#0, $ih#n0#0)), 
          _module.__default.mult($LS($LZ), _module.__default.plus($LS($LZ), $ih#m0#0, $ih#m0#0), $ih#n0#0)));
    $_reverifyPost := false;
    assume true;
    havoc _mcc#0#0_0;
    if (m#0 == #_module.Nat.O())
    {
    }
    else if (m#0 == #_module.Nat.S(_mcc#0#0_0))
    {
        assume $Is(_mcc#0#0_0, Tclass._module.Nat());
        havoc m'#0_0;
        assume $Is(m'#0_0, Tclass._module.Nat())
           && $IsAlloc(m'#0_0, Tclass._module.Nat(), $Heap);
        assume let#0_0#0#0 == _mcc#0#0_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_0#0#0, Tclass._module.Nat());
        assume m'#0_0 == let#0_0#0#0;
        // ----- calc statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(274,7)
        // Assume Fuel Constant
        if (*)
        {
            // ----- assert wf[initial] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(274,7)
            ##n#0_0_0 := n#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0_0_0, Tclass._module.Nat(), $Heap);
            ##m#0_0_0 := n#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#0_0_0, Tclass._module.Nat(), $Heap);
            assume _module.__default.plus#canCall(n#0, n#0);
            ##n#0_0_1 := m#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0_0_1, Tclass._module.Nat(), $Heap);
            ##m#0_0_1 := _module.__default.plus($LS($LZ), n#0, n#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#0_0_1, Tclass._module.Nat(), $Heap);
            assume _module.__default.mult#canCall(m#0, _module.__default.plus($LS($LZ), n#0, n#0));
            assume _module.__default.plus#canCall(n#0, n#0)
               && _module.__default.mult#canCall(m#0, _module.__default.plus($LS($LZ), n#0, n#0));
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(274,7)
            ##n#0_0_5_0 := n#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0_0_5_0, Tclass._module.Nat(), $Heap);
            ##m#0_0_5_0 := n#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#0_0_5_0, Tclass._module.Nat(), $Heap);
            assume _module.__default.plus#canCall(n#0, n#0);
            ##n#0_0_5_1 := m#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0_0_5_1, Tclass._module.Nat(), $Heap);
            ##m#0_0_5_1 := _module.__default.plus($LS($LZ), n#0, n#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#0_0_5_1, Tclass._module.Nat(), $Heap);
            assume _module.__default.mult#canCall(m#0, _module.__default.plus($LS($LZ), n#0, n#0));
            assume _module.__default.plus#canCall(n#0, n#0)
               && _module.__default.mult#canCall(m#0, _module.__default.plus($LS($LZ), n#0, n#0));
            // ----- Hint0 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(274,7)
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(274,7)
            ##n#0_0_5_2 := n#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0_0_5_2, Tclass._module.Nat(), $Heap);
            ##m#0_0_5_2 := n#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#0_0_5_2, Tclass._module.Nat(), $Heap);
            assume _module.__default.plus#canCall(n#0, n#0);
            ##n#0_0_5_3 := n#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0_0_5_3, Tclass._module.Nat(), $Heap);
            ##m#0_0_5_3 := n#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#0_0_5_3, Tclass._module.Nat(), $Heap);
            assume _module.__default.plus#canCall(n#0, n#0);
            ##n#0_0_5_4 := m'#0_0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0_0_5_4, Tclass._module.Nat(), $Heap);
            ##m#0_0_5_4 := _module.__default.plus($LS($LZ), n#0, n#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#0_0_5_4, Tclass._module.Nat(), $Heap);
            assume _module.__default.mult#canCall(m'#0_0, _module.__default.plus($LS($LZ), n#0, n#0));
            ##n#0_0_5_5 := _module.__default.plus($LS($LZ), n#0, n#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0_0_5_5, Tclass._module.Nat(), $Heap);
            ##m#0_0_5_5 := _module.__default.mult($LS($LZ), m'#0_0, _module.__default.plus($LS($LZ), n#0, n#0));
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#0_0_5_5, Tclass._module.Nat(), $Heap);
            assume _module.__default.plus#canCall(_module.__default.plus($LS($LZ), n#0, n#0), 
              _module.__default.mult($LS($LZ), m'#0_0, _module.__default.plus($LS($LZ), n#0, n#0)));
            assume _module.__default.plus#canCall(n#0, n#0)
               && 
              _module.__default.plus#canCall(n#0, n#0)
               && _module.__default.mult#canCall(m'#0_0, _module.__default.plus($LS($LZ), n#0, n#0))
               && _module.__default.plus#canCall(_module.__default.plus($LS($LZ), n#0, n#0), 
                _module.__default.mult($LS($LZ), m'#0_0, _module.__default.plus($LS($LZ), n#0, n#0)));
            // ----- assert line0 == line1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(274,7)
            assert {:subsumption 0} _module.Nat#Equal(_module.__default.mult($LS($LS($LZ)), m#0, _module.__default.plus($LS($LS($LZ)), n#0, n#0)), 
              _module.__default.plus($LS($LS($LZ)), 
                _module.__default.plus($LS($LS($LZ)), n#0, n#0), 
                _module.__default.mult($LS($LS($LZ)), m'#0_0, _module.__default.plus($LS($LS($LZ)), n#0, n#0))));
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(274,7)
            ##n#0_0_4_0 := n#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0_0_4_0, Tclass._module.Nat(), $Heap);
            ##m#0_0_4_0 := n#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#0_0_4_0, Tclass._module.Nat(), $Heap);
            assume _module.__default.plus#canCall(n#0, n#0);
            ##n#0_0_4_1 := n#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0_0_4_1, Tclass._module.Nat(), $Heap);
            ##m#0_0_4_1 := n#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#0_0_4_1, Tclass._module.Nat(), $Heap);
            assume _module.__default.plus#canCall(n#0, n#0);
            ##n#0_0_4_2 := m'#0_0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0_0_4_2, Tclass._module.Nat(), $Heap);
            ##m#0_0_4_2 := _module.__default.plus($LS($LZ), n#0, n#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#0_0_4_2, Tclass._module.Nat(), $Heap);
            assume _module.__default.mult#canCall(m'#0_0, _module.__default.plus($LS($LZ), n#0, n#0));
            ##n#0_0_4_3 := _module.__default.plus($LS($LZ), n#0, n#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0_0_4_3, Tclass._module.Nat(), $Heap);
            ##m#0_0_4_3 := _module.__default.mult($LS($LZ), m'#0_0, _module.__default.plus($LS($LZ), n#0, n#0));
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#0_0_4_3, Tclass._module.Nat(), $Heap);
            assume _module.__default.plus#canCall(_module.__default.plus($LS($LZ), n#0, n#0), 
              _module.__default.mult($LS($LZ), m'#0_0, _module.__default.plus($LS($LZ), n#0, n#0)));
            assume _module.__default.plus#canCall(n#0, n#0)
               && 
              _module.__default.plus#canCall(n#0, n#0)
               && _module.__default.mult#canCall(m'#0_0, _module.__default.plus($LS($LZ), n#0, n#0))
               && _module.__default.plus#canCall(_module.__default.plus($LS($LZ), n#0, n#0), 
                _module.__default.mult($LS($LZ), m'#0_0, _module.__default.plus($LS($LZ), n#0, n#0)));
            // ----- Hint1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(274,7)
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(274,7)
            ##n#0_0_4_4 := n#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0_0_4_4, Tclass._module.Nat(), $Heap);
            ##m#0_0_4_4 := n#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#0_0_4_4, Tclass._module.Nat(), $Heap);
            assume _module.__default.plus#canCall(n#0, n#0);
            ##n#0_0_4_5 := m'#0_0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0_0_4_5, Tclass._module.Nat(), $Heap);
            ##m#0_0_4_5 := m'#0_0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#0_0_4_5, Tclass._module.Nat(), $Heap);
            assume _module.__default.plus#canCall(m'#0_0, m'#0_0);
            ##n#0_0_4_6 := _module.__default.plus($LS($LZ), m'#0_0, m'#0_0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0_0_4_6, Tclass._module.Nat(), $Heap);
            ##m#0_0_4_6 := n#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#0_0_4_6, Tclass._module.Nat(), $Heap);
            assume _module.__default.mult#canCall(_module.__default.plus($LS($LZ), m'#0_0, m'#0_0), n#0);
            ##n#0_0_4_7 := _module.__default.plus($LS($LZ), n#0, n#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0_0_4_7, Tclass._module.Nat(), $Heap);
            ##m#0_0_4_7 := _module.__default.mult($LS($LZ), _module.__default.plus($LS($LZ), m'#0_0, m'#0_0), n#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#0_0_4_7, Tclass._module.Nat(), $Heap);
            assume _module.__default.plus#canCall(_module.__default.plus($LS($LZ), n#0, n#0), 
              _module.__default.mult($LS($LZ), _module.__default.plus($LS($LZ), m'#0_0, m'#0_0), n#0));
            assume _module.__default.plus#canCall(n#0, n#0)
               && 
              _module.__default.plus#canCall(m'#0_0, m'#0_0)
               && _module.__default.mult#canCall(_module.__default.plus($LS($LZ), m'#0_0, m'#0_0), n#0)
               && _module.__default.plus#canCall(_module.__default.plus($LS($LZ), n#0, n#0), 
                _module.__default.mult($LS($LZ), _module.__default.plus($LS($LZ), m'#0_0, m'#0_0), n#0));
            // ----- assert line1 == line2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(274,7)
            assert {:subsumption 0} _module.Nat#Equal(_module.__default.plus($LS($LS($LZ)), 
                _module.__default.plus($LS($LS($LZ)), n#0, n#0), 
                _module.__default.mult($LS($LS($LZ)), m'#0_0, _module.__default.plus($LS($LS($LZ)), n#0, n#0))), 
              _module.__default.plus($LS($LS($LZ)), 
                _module.__default.plus($LS($LS($LZ)), n#0, n#0), 
                _module.__default.mult($LS($LS($LZ)), _module.__default.plus($LS($LS($LZ)), m'#0_0, m'#0_0), n#0)));
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(274,7)
            ##n#0_0_3_0 := n#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0_0_3_0, Tclass._module.Nat(), $Heap);
            ##m#0_0_3_0 := n#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#0_0_3_0, Tclass._module.Nat(), $Heap);
            assume _module.__default.plus#canCall(n#0, n#0);
            ##n#0_0_3_1 := m'#0_0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0_0_3_1, Tclass._module.Nat(), $Heap);
            ##m#0_0_3_1 := m'#0_0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#0_0_3_1, Tclass._module.Nat(), $Heap);
            assume _module.__default.plus#canCall(m'#0_0, m'#0_0);
            ##n#0_0_3_2 := _module.__default.plus($LS($LZ), m'#0_0, m'#0_0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0_0_3_2, Tclass._module.Nat(), $Heap);
            ##m#0_0_3_2 := n#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#0_0_3_2, Tclass._module.Nat(), $Heap);
            assume _module.__default.mult#canCall(_module.__default.plus($LS($LZ), m'#0_0, m'#0_0), n#0);
            ##n#0_0_3_3 := _module.__default.plus($LS($LZ), n#0, n#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0_0_3_3, Tclass._module.Nat(), $Heap);
            ##m#0_0_3_3 := _module.__default.mult($LS($LZ), _module.__default.plus($LS($LZ), m'#0_0, m'#0_0), n#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#0_0_3_3, Tclass._module.Nat(), $Heap);
            assume _module.__default.plus#canCall(_module.__default.plus($LS($LZ), n#0, n#0), 
              _module.__default.mult($LS($LZ), _module.__default.plus($LS($LZ), m'#0_0, m'#0_0), n#0));
            assume _module.__default.plus#canCall(n#0, n#0)
               && 
              _module.__default.plus#canCall(m'#0_0, m'#0_0)
               && _module.__default.mult#canCall(_module.__default.plus($LS($LZ), m'#0_0, m'#0_0), n#0)
               && _module.__default.plus#canCall(_module.__default.plus($LS($LZ), n#0, n#0), 
                _module.__default.mult($LS($LZ), _module.__default.plus($LS($LZ), m'#0_0, m'#0_0), n#0));
            // ----- Hint2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(274,7)
            // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(280,13)
            // Begin Comprehension WF check
            havoc a#0_0_3_0;
            havoc b#0_0_3_0;
            havoc c#0_0_3_0;
            if ($Is(a#0_0_3_0, Tclass._module.Nat())
               && $Is(b#0_0_3_0, Tclass._module.Nat())
               && $Is(c#0_0_3_0, Tclass._module.Nat()))
            {
                ##n#0_0_3_4 := a#0_0_3_0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#0_0_3_4, Tclass._module.Nat(), $Heap);
                ##m#0_0_3_4 := b#0_0_3_0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##m#0_0_3_4, Tclass._module.Nat(), $Heap);
                assume _module.__default.plus#canCall(a#0_0_3_0, b#0_0_3_0);
                ##n#0_0_3_5 := _module.__default.plus($LS($LZ), a#0_0_3_0, b#0_0_3_0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#0_0_3_5, Tclass._module.Nat(), $Heap);
                ##m#0_0_3_5 := c#0_0_3_0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##m#0_0_3_5, Tclass._module.Nat(), $Heap);
                assume _module.__default.plus#canCall(_module.__default.plus($LS($LZ), a#0_0_3_0, b#0_0_3_0), c#0_0_3_0);
                ##n#0_0_3_6 := b#0_0_3_0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#0_0_3_6, Tclass._module.Nat(), $Heap);
                ##m#0_0_3_6 := c#0_0_3_0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##m#0_0_3_6, Tclass._module.Nat(), $Heap);
                assume _module.__default.plus#canCall(b#0_0_3_0, c#0_0_3_0);
                ##n#0_0_3_7 := a#0_0_3_0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#0_0_3_7, Tclass._module.Nat(), $Heap);
                ##m#0_0_3_7 := _module.__default.plus($LS($LZ), b#0_0_3_0, c#0_0_3_0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##m#0_0_3_7, Tclass._module.Nat(), $Heap);
                assume _module.__default.plus#canCall(a#0_0_3_0, _module.__default.plus($LS($LZ), b#0_0_3_0, c#0_0_3_0));
            }

            // End Comprehension WF check
            assume (forall a#0_0_3_1: DatatypeType, b#0_0_3_1: DatatypeType, c#0_0_3_1: DatatypeType :: 
              { _module.__default.plus($LS($LZ), a#0_0_3_1, _module.__default.plus($LS($LZ), b#0_0_3_1, c#0_0_3_1)) } 
                { _module.__default.plus($LS($LZ), _module.__default.plus($LS($LZ), a#0_0_3_1, b#0_0_3_1), c#0_0_3_1) } 
              $Is(a#0_0_3_1, Tclass._module.Nat())
                   && $Is(b#0_0_3_1, Tclass._module.Nat())
                   && $Is(c#0_0_3_1, Tclass._module.Nat())
                 ==> $IsA#_module.Nat(_module.__default.plus($LS($LZ), _module.__default.plus($LS($LZ), a#0_0_3_1, b#0_0_3_1), c#0_0_3_1))
                   && $IsA#_module.Nat(_module.__default.plus($LS($LZ), a#0_0_3_1, _module.__default.plus($LS($LZ), b#0_0_3_1, c#0_0_3_1)))
                   && 
                  _module.__default.plus#canCall(a#0_0_3_1, b#0_0_3_1)
                   && _module.__default.plus#canCall(_module.__default.plus($LS($LZ), a#0_0_3_1, b#0_0_3_1), c#0_0_3_1)
                   && 
                  _module.__default.plus#canCall(b#0_0_3_1, c#0_0_3_1)
                   && _module.__default.plus#canCall(a#0_0_3_1, _module.__default.plus($LS($LZ), b#0_0_3_1, c#0_0_3_1)));
            assert {:subsumption 0} (forall a#0_0_3_1: DatatypeType, b#0_0_3_1: DatatypeType, c#0_0_3_1: DatatypeType :: 
              { _module.__default.plus($LS($LS($LZ)), 
                  a#0_0_3_1, 
                  _module.__default.plus($LS($LS($LZ)), b#0_0_3_1, c#0_0_3_1)) } 
                { _module.__default.plus($LS($LS($LZ)), 
                  _module.__default.plus($LS($LS($LZ)), a#0_0_3_1, b#0_0_3_1), 
                  c#0_0_3_1) } 
              $Is(a#0_0_3_1, Tclass._module.Nat())
                   && $Is(b#0_0_3_1, Tclass._module.Nat())
                   && $Is(c#0_0_3_1, Tclass._module.Nat())
                   && (forall a$ih#0_0_3_0#0_0_3_0: DatatypeType, 
                      b$ih#0_0_3_0#0_0_3_0: DatatypeType, 
                      c$ih#0_0_3_0#0_0_3_0: DatatypeType :: 
                    { _module.__default.plus($LS($LZ), 
                        a$ih#0_0_3_0#0_0_3_0, 
                        _module.__default.plus($LS($LZ), b$ih#0_0_3_0#0_0_3_0, c$ih#0_0_3_0#0_0_3_0)) } 
                      { _module.__default.plus($LS($LZ), 
                        _module.__default.plus($LS($LZ), a$ih#0_0_3_0#0_0_3_0, b$ih#0_0_3_0#0_0_3_0), 
                        c$ih#0_0_3_0#0_0_3_0) } 
                    $Is(a$ih#0_0_3_0#0_0_3_0, Tclass._module.Nat())
                         && $Is(b$ih#0_0_3_0#0_0_3_0, Tclass._module.Nat())
                         && $Is(c$ih#0_0_3_0#0_0_3_0, Tclass._module.Nat())
                       ==> 
                      DtRank(a$ih#0_0_3_0#0_0_3_0) < DtRank(a#0_0_3_1)
                         || (DtRank(a$ih#0_0_3_0#0_0_3_0) == DtRank(a#0_0_3_1)
                           && (DtRank(b$ih#0_0_3_0#0_0_3_0) < DtRank(b#0_0_3_1)
                             || (DtRank(b$ih#0_0_3_0#0_0_3_0) == DtRank(b#0_0_3_1)
                               && DtRank(c$ih#0_0_3_0#0_0_3_0) < DtRank(c#0_0_3_1))))
                       ==> _module.Nat#Equal(_module.__default.plus($LS($LZ), 
                          _module.__default.plus($LS($LZ), a$ih#0_0_3_0#0_0_3_0, b$ih#0_0_3_0#0_0_3_0), 
                          c$ih#0_0_3_0#0_0_3_0), 
                        _module.__default.plus($LS($LZ), 
                          a$ih#0_0_3_0#0_0_3_0, 
                          _module.__default.plus($LS($LZ), b$ih#0_0_3_0#0_0_3_0, c$ih#0_0_3_0#0_0_3_0))))
                   && 
                  true
                   && #_module.Nat.O() == a#0_0_3_1
                   && #_module.Nat.O() == b#0_0_3_1
                   && #_module.Nat.O() == c#0_0_3_1
                 ==> _module.Nat#Equal(_module.__default.plus($LS($LS($LZ)), 
                    _module.__default.plus($LS($LS($LZ)), a#0_0_3_1, b#0_0_3_1), 
                    c#0_0_3_1), 
                  _module.__default.plus($LS($LS($LZ)), 
                    a#0_0_3_1, 
                    _module.__default.plus($LS($LS($LZ)), b#0_0_3_1, c#0_0_3_1))));
            assert {:subsumption 0} (forall a#0_0_3_1: DatatypeType, b#0_0_3_1: DatatypeType, c#0_0_3_1: DatatypeType :: 
              { _module.__default.plus($LS($LS($LZ)), 
                  a#0_0_3_1, 
                  _module.__default.plus($LS($LS($LZ)), b#0_0_3_1, c#0_0_3_1)) } 
                { _module.__default.plus($LS($LS($LZ)), 
                  _module.__default.plus($LS($LS($LZ)), a#0_0_3_1, b#0_0_3_1), 
                  c#0_0_3_1) } 
              $Is(a#0_0_3_1, Tclass._module.Nat())
                   && $Is(b#0_0_3_1, Tclass._module.Nat())
                   && $Is(c#0_0_3_1, Tclass._module.Nat())
                   && (forall a$ih#0_0_3_0#0_0_3_0: DatatypeType, 
                      b$ih#0_0_3_0#0_0_3_0: DatatypeType, 
                      c$ih#0_0_3_0#0_0_3_0: DatatypeType :: 
                    { _module.__default.plus($LS($LZ), 
                        a$ih#0_0_3_0#0_0_3_0, 
                        _module.__default.plus($LS($LZ), b$ih#0_0_3_0#0_0_3_0, c$ih#0_0_3_0#0_0_3_0)) } 
                      { _module.__default.plus($LS($LZ), 
                        _module.__default.plus($LS($LZ), a$ih#0_0_3_0#0_0_3_0, b$ih#0_0_3_0#0_0_3_0), 
                        c$ih#0_0_3_0#0_0_3_0) } 
                    $Is(a$ih#0_0_3_0#0_0_3_0, Tclass._module.Nat())
                         && $Is(b$ih#0_0_3_0#0_0_3_0, Tclass._module.Nat())
                         && $Is(c$ih#0_0_3_0#0_0_3_0, Tclass._module.Nat())
                       ==> 
                      DtRank(a$ih#0_0_3_0#0_0_3_0) < DtRank(a#0_0_3_1)
                         || (DtRank(a$ih#0_0_3_0#0_0_3_0) == DtRank(a#0_0_3_1)
                           && (DtRank(b$ih#0_0_3_0#0_0_3_0) < DtRank(b#0_0_3_1)
                             || (DtRank(b$ih#0_0_3_0#0_0_3_0) == DtRank(b#0_0_3_1)
                               && DtRank(c$ih#0_0_3_0#0_0_3_0) < DtRank(c#0_0_3_1))))
                       ==> _module.Nat#Equal(_module.__default.plus($LS($LZ), 
                          _module.__default.plus($LS($LZ), a$ih#0_0_3_0#0_0_3_0, b$ih#0_0_3_0#0_0_3_0), 
                          c$ih#0_0_3_0#0_0_3_0), 
                        _module.__default.plus($LS($LZ), 
                          a$ih#0_0_3_0#0_0_3_0, 
                          _module.__default.plus($LS($LZ), b$ih#0_0_3_0#0_0_3_0, c$ih#0_0_3_0#0_0_3_0))))
                   && 
                  true
                   && (exists a#0_0_3_3#0#0: DatatypeType :: 
                    { #_module.Nat.S(a#0_0_3_3#0#0) } 
                    $Is(a#0_0_3_3#0#0, Tclass._module.Nat())
                       && #_module.Nat.S(a#0_0_3_3#0#0) == a#0_0_3_1)
                   && #_module.Nat.O() == b#0_0_3_1
                   && #_module.Nat.O() == c#0_0_3_1
                 ==> _module.Nat#Equal(_module.__default.plus($LS($LS($LZ)), 
                    _module.__default.plus($LS($LS($LZ)), a#0_0_3_1, b#0_0_3_1), 
                    c#0_0_3_1), 
                  _module.__default.plus($LS($LS($LZ)), 
                    a#0_0_3_1, 
                    _module.__default.plus($LS($LS($LZ)), b#0_0_3_1, c#0_0_3_1))));
            assert {:subsumption 0} (forall a#0_0_3_1: DatatypeType, b#0_0_3_1: DatatypeType, c#0_0_3_1: DatatypeType :: 
              { _module.__default.plus($LS($LS($LZ)), 
                  a#0_0_3_1, 
                  _module.__default.plus($LS($LS($LZ)), b#0_0_3_1, c#0_0_3_1)) } 
                { _module.__default.plus($LS($LS($LZ)), 
                  _module.__default.plus($LS($LS($LZ)), a#0_0_3_1, b#0_0_3_1), 
                  c#0_0_3_1) } 
              $Is(a#0_0_3_1, Tclass._module.Nat())
                   && $Is(b#0_0_3_1, Tclass._module.Nat())
                   && $Is(c#0_0_3_1, Tclass._module.Nat())
                   && (forall a$ih#0_0_3_0#0_0_3_0: DatatypeType, 
                      b$ih#0_0_3_0#0_0_3_0: DatatypeType, 
                      c$ih#0_0_3_0#0_0_3_0: DatatypeType :: 
                    { _module.__default.plus($LS($LZ), 
                        a$ih#0_0_3_0#0_0_3_0, 
                        _module.__default.plus($LS($LZ), b$ih#0_0_3_0#0_0_3_0, c$ih#0_0_3_0#0_0_3_0)) } 
                      { _module.__default.plus($LS($LZ), 
                        _module.__default.plus($LS($LZ), a$ih#0_0_3_0#0_0_3_0, b$ih#0_0_3_0#0_0_3_0), 
                        c$ih#0_0_3_0#0_0_3_0) } 
                    $Is(a$ih#0_0_3_0#0_0_3_0, Tclass._module.Nat())
                         && $Is(b$ih#0_0_3_0#0_0_3_0, Tclass._module.Nat())
                         && $Is(c$ih#0_0_3_0#0_0_3_0, Tclass._module.Nat())
                       ==> 
                      DtRank(a$ih#0_0_3_0#0_0_3_0) < DtRank(a#0_0_3_1)
                         || (DtRank(a$ih#0_0_3_0#0_0_3_0) == DtRank(a#0_0_3_1)
                           && (DtRank(b$ih#0_0_3_0#0_0_3_0) < DtRank(b#0_0_3_1)
                             || (DtRank(b$ih#0_0_3_0#0_0_3_0) == DtRank(b#0_0_3_1)
                               && DtRank(c$ih#0_0_3_0#0_0_3_0) < DtRank(c#0_0_3_1))))
                       ==> _module.Nat#Equal(_module.__default.plus($LS($LZ), 
                          _module.__default.plus($LS($LZ), a$ih#0_0_3_0#0_0_3_0, b$ih#0_0_3_0#0_0_3_0), 
                          c$ih#0_0_3_0#0_0_3_0), 
                        _module.__default.plus($LS($LZ), 
                          a$ih#0_0_3_0#0_0_3_0, 
                          _module.__default.plus($LS($LZ), b$ih#0_0_3_0#0_0_3_0, c$ih#0_0_3_0#0_0_3_0))))
                   && 
                  true
                   && #_module.Nat.O() == a#0_0_3_1
                   && (exists a#0_0_3_5#0#0: DatatypeType :: 
                    { #_module.Nat.S(a#0_0_3_5#0#0) } 
                    $Is(a#0_0_3_5#0#0, Tclass._module.Nat())
                       && #_module.Nat.S(a#0_0_3_5#0#0) == b#0_0_3_1)
                   && #_module.Nat.O() == c#0_0_3_1
                 ==> _module.Nat#Equal(_module.__default.plus($LS($LS($LZ)), 
                    _module.__default.plus($LS($LS($LZ)), a#0_0_3_1, b#0_0_3_1), 
                    c#0_0_3_1), 
                  _module.__default.plus($LS($LS($LZ)), 
                    a#0_0_3_1, 
                    _module.__default.plus($LS($LS($LZ)), b#0_0_3_1, c#0_0_3_1))));
            assert {:subsumption 0} (forall a#0_0_3_1: DatatypeType, b#0_0_3_1: DatatypeType, c#0_0_3_1: DatatypeType :: 
              { _module.__default.plus($LS($LS($LZ)), 
                  a#0_0_3_1, 
                  _module.__default.plus($LS($LS($LZ)), b#0_0_3_1, c#0_0_3_1)) } 
                { _module.__default.plus($LS($LS($LZ)), 
                  _module.__default.plus($LS($LS($LZ)), a#0_0_3_1, b#0_0_3_1), 
                  c#0_0_3_1) } 
              $Is(a#0_0_3_1, Tclass._module.Nat())
                   && $Is(b#0_0_3_1, Tclass._module.Nat())
                   && $Is(c#0_0_3_1, Tclass._module.Nat())
                   && (forall a$ih#0_0_3_0#0_0_3_0: DatatypeType, 
                      b$ih#0_0_3_0#0_0_3_0: DatatypeType, 
                      c$ih#0_0_3_0#0_0_3_0: DatatypeType :: 
                    { _module.__default.plus($LS($LZ), 
                        a$ih#0_0_3_0#0_0_3_0, 
                        _module.__default.plus($LS($LZ), b$ih#0_0_3_0#0_0_3_0, c$ih#0_0_3_0#0_0_3_0)) } 
                      { _module.__default.plus($LS($LZ), 
                        _module.__default.plus($LS($LZ), a$ih#0_0_3_0#0_0_3_0, b$ih#0_0_3_0#0_0_3_0), 
                        c$ih#0_0_3_0#0_0_3_0) } 
                    $Is(a$ih#0_0_3_0#0_0_3_0, Tclass._module.Nat())
                         && $Is(b$ih#0_0_3_0#0_0_3_0, Tclass._module.Nat())
                         && $Is(c$ih#0_0_3_0#0_0_3_0, Tclass._module.Nat())
                       ==> 
                      DtRank(a$ih#0_0_3_0#0_0_3_0) < DtRank(a#0_0_3_1)
                         || (DtRank(a$ih#0_0_3_0#0_0_3_0) == DtRank(a#0_0_3_1)
                           && (DtRank(b$ih#0_0_3_0#0_0_3_0) < DtRank(b#0_0_3_1)
                             || (DtRank(b$ih#0_0_3_0#0_0_3_0) == DtRank(b#0_0_3_1)
                               && DtRank(c$ih#0_0_3_0#0_0_3_0) < DtRank(c#0_0_3_1))))
                       ==> _module.Nat#Equal(_module.__default.plus($LS($LZ), 
                          _module.__default.plus($LS($LZ), a$ih#0_0_3_0#0_0_3_0, b$ih#0_0_3_0#0_0_3_0), 
                          c$ih#0_0_3_0#0_0_3_0), 
                        _module.__default.plus($LS($LZ), 
                          a$ih#0_0_3_0#0_0_3_0, 
                          _module.__default.plus($LS($LZ), b$ih#0_0_3_0#0_0_3_0, c$ih#0_0_3_0#0_0_3_0))))
                   && 
                  true
                   && (exists a#0_0_3_3#0#0: DatatypeType :: 
                    { #_module.Nat.S(a#0_0_3_3#0#0) } 
                    $Is(a#0_0_3_3#0#0, Tclass._module.Nat())
                       && #_module.Nat.S(a#0_0_3_3#0#0) == a#0_0_3_1)
                   && (exists a#0_0_3_5#0#0: DatatypeType :: 
                    { #_module.Nat.S(a#0_0_3_5#0#0) } 
                    $Is(a#0_0_3_5#0#0, Tclass._module.Nat())
                       && #_module.Nat.S(a#0_0_3_5#0#0) == b#0_0_3_1)
                   && #_module.Nat.O() == c#0_0_3_1
                 ==> _module.Nat#Equal(_module.__default.plus($LS($LS($LZ)), 
                    _module.__default.plus($LS($LS($LZ)), a#0_0_3_1, b#0_0_3_1), 
                    c#0_0_3_1), 
                  _module.__default.plus($LS($LS($LZ)), 
                    a#0_0_3_1, 
                    _module.__default.plus($LS($LS($LZ)), b#0_0_3_1, c#0_0_3_1))));
            assert {:subsumption 0} (forall a#0_0_3_1: DatatypeType, b#0_0_3_1: DatatypeType, c#0_0_3_1: DatatypeType :: 
              { _module.__default.plus($LS($LS($LZ)), 
                  a#0_0_3_1, 
                  _module.__default.plus($LS($LS($LZ)), b#0_0_3_1, c#0_0_3_1)) } 
                { _module.__default.plus($LS($LS($LZ)), 
                  _module.__default.plus($LS($LS($LZ)), a#0_0_3_1, b#0_0_3_1), 
                  c#0_0_3_1) } 
              $Is(a#0_0_3_1, Tclass._module.Nat())
                   && $Is(b#0_0_3_1, Tclass._module.Nat())
                   && $Is(c#0_0_3_1, Tclass._module.Nat())
                   && (forall a$ih#0_0_3_0#0_0_3_0: DatatypeType, 
                      b$ih#0_0_3_0#0_0_3_0: DatatypeType, 
                      c$ih#0_0_3_0#0_0_3_0: DatatypeType :: 
                    { _module.__default.plus($LS($LZ), 
                        a$ih#0_0_3_0#0_0_3_0, 
                        _module.__default.plus($LS($LZ), b$ih#0_0_3_0#0_0_3_0, c$ih#0_0_3_0#0_0_3_0)) } 
                      { _module.__default.plus($LS($LZ), 
                        _module.__default.plus($LS($LZ), a$ih#0_0_3_0#0_0_3_0, b$ih#0_0_3_0#0_0_3_0), 
                        c$ih#0_0_3_0#0_0_3_0) } 
                    $Is(a$ih#0_0_3_0#0_0_3_0, Tclass._module.Nat())
                         && $Is(b$ih#0_0_3_0#0_0_3_0, Tclass._module.Nat())
                         && $Is(c$ih#0_0_3_0#0_0_3_0, Tclass._module.Nat())
                       ==> 
                      DtRank(a$ih#0_0_3_0#0_0_3_0) < DtRank(a#0_0_3_1)
                         || (DtRank(a$ih#0_0_3_0#0_0_3_0) == DtRank(a#0_0_3_1)
                           && (DtRank(b$ih#0_0_3_0#0_0_3_0) < DtRank(b#0_0_3_1)
                             || (DtRank(b$ih#0_0_3_0#0_0_3_0) == DtRank(b#0_0_3_1)
                               && DtRank(c$ih#0_0_3_0#0_0_3_0) < DtRank(c#0_0_3_1))))
                       ==> _module.Nat#Equal(_module.__default.plus($LS($LZ), 
                          _module.__default.plus($LS($LZ), a$ih#0_0_3_0#0_0_3_0, b$ih#0_0_3_0#0_0_3_0), 
                          c$ih#0_0_3_0#0_0_3_0), 
                        _module.__default.plus($LS($LZ), 
                          a$ih#0_0_3_0#0_0_3_0, 
                          _module.__default.plus($LS($LZ), b$ih#0_0_3_0#0_0_3_0, c$ih#0_0_3_0#0_0_3_0))))
                   && 
                  true
                   && #_module.Nat.O() == a#0_0_3_1
                   && #_module.Nat.O() == b#0_0_3_1
                   && (exists a#0_0_3_7#0#0: DatatypeType :: 
                    { #_module.Nat.S(a#0_0_3_7#0#0) } 
                    $Is(a#0_0_3_7#0#0, Tclass._module.Nat())
                       && #_module.Nat.S(a#0_0_3_7#0#0) == c#0_0_3_1)
                 ==> _module.Nat#Equal(_module.__default.plus($LS($LS($LZ)), 
                    _module.__default.plus($LS($LS($LZ)), a#0_0_3_1, b#0_0_3_1), 
                    c#0_0_3_1), 
                  _module.__default.plus($LS($LS($LZ)), 
                    a#0_0_3_1, 
                    _module.__default.plus($LS($LS($LZ)), b#0_0_3_1, c#0_0_3_1))));
            assert {:subsumption 0} (forall a#0_0_3_1: DatatypeType, b#0_0_3_1: DatatypeType, c#0_0_3_1: DatatypeType :: 
              { _module.__default.plus($LS($LS($LZ)), 
                  a#0_0_3_1, 
                  _module.__default.plus($LS($LS($LZ)), b#0_0_3_1, c#0_0_3_1)) } 
                { _module.__default.plus($LS($LS($LZ)), 
                  _module.__default.plus($LS($LS($LZ)), a#0_0_3_1, b#0_0_3_1), 
                  c#0_0_3_1) } 
              $Is(a#0_0_3_1, Tclass._module.Nat())
                   && $Is(b#0_0_3_1, Tclass._module.Nat())
                   && $Is(c#0_0_3_1, Tclass._module.Nat())
                   && (forall a$ih#0_0_3_0#0_0_3_0: DatatypeType, 
                      b$ih#0_0_3_0#0_0_3_0: DatatypeType, 
                      c$ih#0_0_3_0#0_0_3_0: DatatypeType :: 
                    { _module.__default.plus($LS($LZ), 
                        a$ih#0_0_3_0#0_0_3_0, 
                        _module.__default.plus($LS($LZ), b$ih#0_0_3_0#0_0_3_0, c$ih#0_0_3_0#0_0_3_0)) } 
                      { _module.__default.plus($LS($LZ), 
                        _module.__default.plus($LS($LZ), a$ih#0_0_3_0#0_0_3_0, b$ih#0_0_3_0#0_0_3_0), 
                        c$ih#0_0_3_0#0_0_3_0) } 
                    $Is(a$ih#0_0_3_0#0_0_3_0, Tclass._module.Nat())
                         && $Is(b$ih#0_0_3_0#0_0_3_0, Tclass._module.Nat())
                         && $Is(c$ih#0_0_3_0#0_0_3_0, Tclass._module.Nat())
                       ==> 
                      DtRank(a$ih#0_0_3_0#0_0_3_0) < DtRank(a#0_0_3_1)
                         || (DtRank(a$ih#0_0_3_0#0_0_3_0) == DtRank(a#0_0_3_1)
                           && (DtRank(b$ih#0_0_3_0#0_0_3_0) < DtRank(b#0_0_3_1)
                             || (DtRank(b$ih#0_0_3_0#0_0_3_0) == DtRank(b#0_0_3_1)
                               && DtRank(c$ih#0_0_3_0#0_0_3_0) < DtRank(c#0_0_3_1))))
                       ==> _module.Nat#Equal(_module.__default.plus($LS($LZ), 
                          _module.__default.plus($LS($LZ), a$ih#0_0_3_0#0_0_3_0, b$ih#0_0_3_0#0_0_3_0), 
                          c$ih#0_0_3_0#0_0_3_0), 
                        _module.__default.plus($LS($LZ), 
                          a$ih#0_0_3_0#0_0_3_0, 
                          _module.__default.plus($LS($LZ), b$ih#0_0_3_0#0_0_3_0, c$ih#0_0_3_0#0_0_3_0))))
                   && 
                  true
                   && (exists a#0_0_3_3#0#0: DatatypeType :: 
                    { #_module.Nat.S(a#0_0_3_3#0#0) } 
                    $Is(a#0_0_3_3#0#0, Tclass._module.Nat())
                       && #_module.Nat.S(a#0_0_3_3#0#0) == a#0_0_3_1)
                   && #_module.Nat.O() == b#0_0_3_1
                   && (exists a#0_0_3_7#0#0: DatatypeType :: 
                    { #_module.Nat.S(a#0_0_3_7#0#0) } 
                    $Is(a#0_0_3_7#0#0, Tclass._module.Nat())
                       && #_module.Nat.S(a#0_0_3_7#0#0) == c#0_0_3_1)
                 ==> _module.Nat#Equal(_module.__default.plus($LS($LS($LZ)), 
                    _module.__default.plus($LS($LS($LZ)), a#0_0_3_1, b#0_0_3_1), 
                    c#0_0_3_1), 
                  _module.__default.plus($LS($LS($LZ)), 
                    a#0_0_3_1, 
                    _module.__default.plus($LS($LS($LZ)), b#0_0_3_1, c#0_0_3_1))));
            assert {:subsumption 0} (forall a#0_0_3_1: DatatypeType, b#0_0_3_1: DatatypeType, c#0_0_3_1: DatatypeType :: 
              { _module.__default.plus($LS($LS($LZ)), 
                  a#0_0_3_1, 
                  _module.__default.plus($LS($LS($LZ)), b#0_0_3_1, c#0_0_3_1)) } 
                { _module.__default.plus($LS($LS($LZ)), 
                  _module.__default.plus($LS($LS($LZ)), a#0_0_3_1, b#0_0_3_1), 
                  c#0_0_3_1) } 
              $Is(a#0_0_3_1, Tclass._module.Nat())
                   && $Is(b#0_0_3_1, Tclass._module.Nat())
                   && $Is(c#0_0_3_1, Tclass._module.Nat())
                   && (forall a$ih#0_0_3_0#0_0_3_0: DatatypeType, 
                      b$ih#0_0_3_0#0_0_3_0: DatatypeType, 
                      c$ih#0_0_3_0#0_0_3_0: DatatypeType :: 
                    { _module.__default.plus($LS($LZ), 
                        a$ih#0_0_3_0#0_0_3_0, 
                        _module.__default.plus($LS($LZ), b$ih#0_0_3_0#0_0_3_0, c$ih#0_0_3_0#0_0_3_0)) } 
                      { _module.__default.plus($LS($LZ), 
                        _module.__default.plus($LS($LZ), a$ih#0_0_3_0#0_0_3_0, b$ih#0_0_3_0#0_0_3_0), 
                        c$ih#0_0_3_0#0_0_3_0) } 
                    $Is(a$ih#0_0_3_0#0_0_3_0, Tclass._module.Nat())
                         && $Is(b$ih#0_0_3_0#0_0_3_0, Tclass._module.Nat())
                         && $Is(c$ih#0_0_3_0#0_0_3_0, Tclass._module.Nat())
                       ==> 
                      DtRank(a$ih#0_0_3_0#0_0_3_0) < DtRank(a#0_0_3_1)
                         || (DtRank(a$ih#0_0_3_0#0_0_3_0) == DtRank(a#0_0_3_1)
                           && (DtRank(b$ih#0_0_3_0#0_0_3_0) < DtRank(b#0_0_3_1)
                             || (DtRank(b$ih#0_0_3_0#0_0_3_0) == DtRank(b#0_0_3_1)
                               && DtRank(c$ih#0_0_3_0#0_0_3_0) < DtRank(c#0_0_3_1))))
                       ==> _module.Nat#Equal(_module.__default.plus($LS($LZ), 
                          _module.__default.plus($LS($LZ), a$ih#0_0_3_0#0_0_3_0, b$ih#0_0_3_0#0_0_3_0), 
                          c$ih#0_0_3_0#0_0_3_0), 
                        _module.__default.plus($LS($LZ), 
                          a$ih#0_0_3_0#0_0_3_0, 
                          _module.__default.plus($LS($LZ), b$ih#0_0_3_0#0_0_3_0, c$ih#0_0_3_0#0_0_3_0))))
                   && 
                  true
                   && #_module.Nat.O() == a#0_0_3_1
                   && (exists a#0_0_3_5#0#0: DatatypeType :: 
                    { #_module.Nat.S(a#0_0_3_5#0#0) } 
                    $Is(a#0_0_3_5#0#0, Tclass._module.Nat())
                       && #_module.Nat.S(a#0_0_3_5#0#0) == b#0_0_3_1)
                   && (exists a#0_0_3_7#0#0: DatatypeType :: 
                    { #_module.Nat.S(a#0_0_3_7#0#0) } 
                    $Is(a#0_0_3_7#0#0, Tclass._module.Nat())
                       && #_module.Nat.S(a#0_0_3_7#0#0) == c#0_0_3_1)
                 ==> _module.Nat#Equal(_module.__default.plus($LS($LS($LZ)), 
                    _module.__default.plus($LS($LS($LZ)), a#0_0_3_1, b#0_0_3_1), 
                    c#0_0_3_1), 
                  _module.__default.plus($LS($LS($LZ)), 
                    a#0_0_3_1, 
                    _module.__default.plus($LS($LS($LZ)), b#0_0_3_1, c#0_0_3_1))));
            assert {:subsumption 0} (forall a#0_0_3_1: DatatypeType, b#0_0_3_1: DatatypeType, c#0_0_3_1: DatatypeType :: 
              { _module.__default.plus($LS($LS($LZ)), 
                  a#0_0_3_1, 
                  _module.__default.plus($LS($LS($LZ)), b#0_0_3_1, c#0_0_3_1)) } 
                { _module.__default.plus($LS($LS($LZ)), 
                  _module.__default.plus($LS($LS($LZ)), a#0_0_3_1, b#0_0_3_1), 
                  c#0_0_3_1) } 
              $Is(a#0_0_3_1, Tclass._module.Nat())
                   && $Is(b#0_0_3_1, Tclass._module.Nat())
                   && $Is(c#0_0_3_1, Tclass._module.Nat())
                   && (forall a$ih#0_0_3_0#0_0_3_0: DatatypeType, 
                      b$ih#0_0_3_0#0_0_3_0: DatatypeType, 
                      c$ih#0_0_3_0#0_0_3_0: DatatypeType :: 
                    { _module.__default.plus($LS($LZ), 
                        a$ih#0_0_3_0#0_0_3_0, 
                        _module.__default.plus($LS($LZ), b$ih#0_0_3_0#0_0_3_0, c$ih#0_0_3_0#0_0_3_0)) } 
                      { _module.__default.plus($LS($LZ), 
                        _module.__default.plus($LS($LZ), a$ih#0_0_3_0#0_0_3_0, b$ih#0_0_3_0#0_0_3_0), 
                        c$ih#0_0_3_0#0_0_3_0) } 
                    $Is(a$ih#0_0_3_0#0_0_3_0, Tclass._module.Nat())
                         && $Is(b$ih#0_0_3_0#0_0_3_0, Tclass._module.Nat())
                         && $Is(c$ih#0_0_3_0#0_0_3_0, Tclass._module.Nat())
                       ==> 
                      DtRank(a$ih#0_0_3_0#0_0_3_0) < DtRank(a#0_0_3_1)
                         || (DtRank(a$ih#0_0_3_0#0_0_3_0) == DtRank(a#0_0_3_1)
                           && (DtRank(b$ih#0_0_3_0#0_0_3_0) < DtRank(b#0_0_3_1)
                             || (DtRank(b$ih#0_0_3_0#0_0_3_0) == DtRank(b#0_0_3_1)
                               && DtRank(c$ih#0_0_3_0#0_0_3_0) < DtRank(c#0_0_3_1))))
                       ==> _module.Nat#Equal(_module.__default.plus($LS($LZ), 
                          _module.__default.plus($LS($LZ), a$ih#0_0_3_0#0_0_3_0, b$ih#0_0_3_0#0_0_3_0), 
                          c$ih#0_0_3_0#0_0_3_0), 
                        _module.__default.plus($LS($LZ), 
                          a$ih#0_0_3_0#0_0_3_0, 
                          _module.__default.plus($LS($LZ), b$ih#0_0_3_0#0_0_3_0, c$ih#0_0_3_0#0_0_3_0))))
                   && 
                  true
                   && (exists a#0_0_3_3#0#0: DatatypeType :: 
                    { #_module.Nat.S(a#0_0_3_3#0#0) } 
                    $Is(a#0_0_3_3#0#0, Tclass._module.Nat())
                       && #_module.Nat.S(a#0_0_3_3#0#0) == a#0_0_3_1)
                   && (exists a#0_0_3_5#0#0: DatatypeType :: 
                    { #_module.Nat.S(a#0_0_3_5#0#0) } 
                    $Is(a#0_0_3_5#0#0, Tclass._module.Nat())
                       && #_module.Nat.S(a#0_0_3_5#0#0) == b#0_0_3_1)
                   && (exists a#0_0_3_7#0#0: DatatypeType :: 
                    { #_module.Nat.S(a#0_0_3_7#0#0) } 
                    $Is(a#0_0_3_7#0#0, Tclass._module.Nat())
                       && #_module.Nat.S(a#0_0_3_7#0#0) == c#0_0_3_1)
                 ==> _module.Nat#Equal(_module.__default.plus($LS($LS($LZ)), 
                    _module.__default.plus($LS($LS($LZ)), a#0_0_3_1, b#0_0_3_1), 
                    c#0_0_3_1), 
                  _module.__default.plus($LS($LS($LZ)), 
                    a#0_0_3_1, 
                    _module.__default.plus($LS($LS($LZ)), b#0_0_3_1, c#0_0_3_1))));
            assume (forall a#0_0_3_1: DatatypeType, b#0_0_3_1: DatatypeType, c#0_0_3_1: DatatypeType :: 
              {:induction} {:_induction a#0_0_3_1, b#0_0_3_1, c#0_0_3_1} { _module.__default.plus($LS($LZ), a#0_0_3_1, _module.__default.plus($LS($LZ), b#0_0_3_1, c#0_0_3_1)) } 
                { _module.__default.plus($LS($LZ), _module.__default.plus($LS($LZ), a#0_0_3_1, b#0_0_3_1), c#0_0_3_1) } 
              $Is(a#0_0_3_1, Tclass._module.Nat())
                   && $Is(b#0_0_3_1, Tclass._module.Nat())
                   && $Is(c#0_0_3_1, Tclass._module.Nat())
                 ==> _module.Nat#Equal(_module.__default.plus($LS($LZ), _module.__default.plus($LS($LZ), a#0_0_3_1, b#0_0_3_1), c#0_0_3_1), 
                  _module.__default.plus($LS($LZ), a#0_0_3_1, _module.__default.plus($LS($LZ), b#0_0_3_1, c#0_0_3_1))));
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(274,7)
            ##n#0_0_3_8 := m'#0_0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0_0_3_8, Tclass._module.Nat(), $Heap);
            ##m#0_0_3_8 := m'#0_0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#0_0_3_8, Tclass._module.Nat(), $Heap);
            assume _module.__default.plus#canCall(m'#0_0, m'#0_0);
            ##n#0_0_3_9 := _module.__default.plus($LS($LZ), m'#0_0, m'#0_0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0_0_3_9, Tclass._module.Nat(), $Heap);
            ##m#0_0_3_9 := n#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#0_0_3_9, Tclass._module.Nat(), $Heap);
            assume _module.__default.mult#canCall(_module.__default.plus($LS($LZ), m'#0_0, m'#0_0), n#0);
            ##n#0_0_3_10 := n#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0_0_3_10, Tclass._module.Nat(), $Heap);
            ##m#0_0_3_10 := _module.__default.mult($LS($LZ), _module.__default.plus($LS($LZ), m'#0_0, m'#0_0), n#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#0_0_3_10, Tclass._module.Nat(), $Heap);
            assume _module.__default.plus#canCall(n#0, 
              _module.__default.mult($LS($LZ), _module.__default.plus($LS($LZ), m'#0_0, m'#0_0), n#0));
            ##n#0_0_3_11 := n#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0_0_3_11, Tclass._module.Nat(), $Heap);
            ##m#0_0_3_11 := _module.__default.plus($LS($LZ), 
              n#0, 
              _module.__default.mult($LS($LZ), _module.__default.plus($LS($LZ), m'#0_0, m'#0_0), n#0));
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#0_0_3_11, Tclass._module.Nat(), $Heap);
            assume _module.__default.plus#canCall(n#0, 
              _module.__default.plus($LS($LZ), 
                n#0, 
                _module.__default.mult($LS($LZ), _module.__default.plus($LS($LZ), m'#0_0, m'#0_0), n#0)));
            assume _module.__default.plus#canCall(m'#0_0, m'#0_0)
               && _module.__default.mult#canCall(_module.__default.plus($LS($LZ), m'#0_0, m'#0_0), n#0)
               && _module.__default.plus#canCall(n#0, 
                _module.__default.mult($LS($LZ), _module.__default.plus($LS($LZ), m'#0_0, m'#0_0), n#0))
               && _module.__default.plus#canCall(n#0, 
                _module.__default.plus($LS($LZ), 
                  n#0, 
                  _module.__default.mult($LS($LZ), _module.__default.plus($LS($LZ), m'#0_0, m'#0_0), n#0)));
            // ----- assert line2 == line3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(274,7)
            assert {:subsumption 0} _module.Nat#Equal(_module.__default.plus($LS($LS($LZ)), 
                _module.__default.plus($LS($LS($LZ)), n#0, n#0), 
                _module.__default.mult($LS($LS($LZ)), _module.__default.plus($LS($LS($LZ)), m'#0_0, m'#0_0), n#0)), 
              _module.__default.plus($LS($LS($LZ)), 
                n#0, 
                _module.__default.plus($LS($LS($LZ)), 
                  n#0, 
                  _module.__default.mult($LS($LS($LZ)), _module.__default.plus($LS($LS($LZ)), m'#0_0, m'#0_0), n#0))));
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(274,7)
            ##n#0_0_2_0 := m'#0_0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0_0_2_0, Tclass._module.Nat(), $Heap);
            ##m#0_0_2_0 := m'#0_0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#0_0_2_0, Tclass._module.Nat(), $Heap);
            assume _module.__default.plus#canCall(m'#0_0, m'#0_0);
            ##n#0_0_2_1 := _module.__default.plus($LS($LZ), m'#0_0, m'#0_0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0_0_2_1, Tclass._module.Nat(), $Heap);
            ##m#0_0_2_1 := n#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#0_0_2_1, Tclass._module.Nat(), $Heap);
            assume _module.__default.mult#canCall(_module.__default.plus($LS($LZ), m'#0_0, m'#0_0), n#0);
            ##n#0_0_2_2 := n#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0_0_2_2, Tclass._module.Nat(), $Heap);
            ##m#0_0_2_2 := _module.__default.mult($LS($LZ), _module.__default.plus($LS($LZ), m'#0_0, m'#0_0), n#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#0_0_2_2, Tclass._module.Nat(), $Heap);
            assume _module.__default.plus#canCall(n#0, 
              _module.__default.mult($LS($LZ), _module.__default.plus($LS($LZ), m'#0_0, m'#0_0), n#0));
            ##n#0_0_2_3 := n#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0_0_2_3, Tclass._module.Nat(), $Heap);
            ##m#0_0_2_3 := _module.__default.plus($LS($LZ), 
              n#0, 
              _module.__default.mult($LS($LZ), _module.__default.plus($LS($LZ), m'#0_0, m'#0_0), n#0));
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#0_0_2_3, Tclass._module.Nat(), $Heap);
            assume _module.__default.plus#canCall(n#0, 
              _module.__default.plus($LS($LZ), 
                n#0, 
                _module.__default.mult($LS($LZ), _module.__default.plus($LS($LZ), m'#0_0, m'#0_0), n#0)));
            assume _module.__default.plus#canCall(m'#0_0, m'#0_0)
               && _module.__default.mult#canCall(_module.__default.plus($LS($LZ), m'#0_0, m'#0_0), n#0)
               && _module.__default.plus#canCall(n#0, 
                _module.__default.mult($LS($LZ), _module.__default.plus($LS($LZ), m'#0_0, m'#0_0), n#0))
               && _module.__default.plus#canCall(n#0, 
                _module.__default.plus($LS($LZ), 
                  n#0, 
                  _module.__default.mult($LS($LZ), _module.__default.plus($LS($LZ), m'#0_0, m'#0_0), n#0)));
            // ----- Hint3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(274,7)
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(274,7)
            ##n#0_0_2_4 := m'#0_0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0_0_2_4, Tclass._module.Nat(), $Heap);
            ##m#0_0_2_4 := m'#0_0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#0_0_2_4, Tclass._module.Nat(), $Heap);
            assume _module.__default.plus#canCall(m'#0_0, m'#0_0);
            ##n#0_0_2_5 := #_module.Nat.S(#_module.Nat.S(_module.__default.plus($LS($LZ), m'#0_0, m'#0_0)));
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0_0_2_5, Tclass._module.Nat(), $Heap);
            ##m#0_0_2_5 := n#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#0_0_2_5, Tclass._module.Nat(), $Heap);
            assume _module.__default.mult#canCall(#_module.Nat.S(#_module.Nat.S(_module.__default.plus($LS($LZ), m'#0_0, m'#0_0))), 
              n#0);
            assume _module.__default.plus#canCall(m'#0_0, m'#0_0)
               && _module.__default.mult#canCall(#_module.Nat.S(#_module.Nat.S(_module.__default.plus($LS($LZ), m'#0_0, m'#0_0))), 
                n#0);
            // ----- assert line3 == line4 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(274,7)
            assert {:subsumption 0} _module.Nat#Equal(_module.__default.plus($LS($LS($LZ)), 
                n#0, 
                _module.__default.plus($LS($LS($LZ)), 
                  n#0, 
                  _module.__default.mult($LS($LS($LZ)), _module.__default.plus($LS($LS($LZ)), m'#0_0, m'#0_0), n#0))), 
              _module.__default.mult($LS($LS($LZ)), 
                #_module.Nat.S(#_module.Nat.S(_module.__default.plus($LS($LS($LZ)), m'#0_0, m'#0_0))), 
                n#0));
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(274,7)
            ##n#0_0_1_0 := m'#0_0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0_0_1_0, Tclass._module.Nat(), $Heap);
            ##m#0_0_1_0 := m'#0_0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#0_0_1_0, Tclass._module.Nat(), $Heap);
            assume _module.__default.plus#canCall(m'#0_0, m'#0_0);
            ##n#0_0_1_1 := #_module.Nat.S(#_module.Nat.S(_module.__default.plus($LS($LZ), m'#0_0, m'#0_0)));
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0_0_1_1, Tclass._module.Nat(), $Heap);
            ##m#0_0_1_1 := n#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#0_0_1_1, Tclass._module.Nat(), $Heap);
            assume _module.__default.mult#canCall(#_module.Nat.S(#_module.Nat.S(_module.__default.plus($LS($LZ), m'#0_0, m'#0_0))), 
              n#0);
            assume _module.__default.plus#canCall(m'#0_0, m'#0_0)
               && _module.__default.mult#canCall(#_module.Nat.S(#_module.Nat.S(_module.__default.plus($LS($LZ), m'#0_0, m'#0_0))), 
                n#0);
            // ----- Hint4 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(274,7)
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(274,7)
            ##n#0_0_1_2 := #_module.Nat.S(m'#0_0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0_0_1_2, Tclass._module.Nat(), $Heap);
            ##m#0_0_1_2 := m'#0_0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#0_0_1_2, Tclass._module.Nat(), $Heap);
            assume _module.__default.plus#canCall(#_module.Nat.S(m'#0_0), m'#0_0);
            ##n#0_0_1_3 := #_module.Nat.S(_module.__default.plus($LS($LZ), #_module.Nat.S(m'#0_0), m'#0_0));
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0_0_1_3, Tclass._module.Nat(), $Heap);
            ##m#0_0_1_3 := n#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#0_0_1_3, Tclass._module.Nat(), $Heap);
            assume _module.__default.mult#canCall(#_module.Nat.S(_module.__default.plus($LS($LZ), #_module.Nat.S(m'#0_0), m'#0_0)), 
              n#0);
            assume _module.__default.plus#canCall(#_module.Nat.S(m'#0_0), m'#0_0)
               && _module.__default.mult#canCall(#_module.Nat.S(_module.__default.plus($LS($LZ), #_module.Nat.S(m'#0_0), m'#0_0)), 
                n#0);
            // ----- assert line4 == line5 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(274,7)
            assert {:subsumption 0} _module.Nat#Equal(_module.__default.mult($LS($LS($LZ)), 
                #_module.Nat.S(#_module.Nat.S(_module.__default.plus($LS($LS($LZ)), m'#0_0, m'#0_0))), 
                n#0), 
              _module.__default.mult($LS($LS($LZ)), 
                #_module.Nat.S(_module.__default.plus($LS($LS($LZ)), #_module.Nat.S(m'#0_0), m'#0_0)), 
                n#0));
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(274,7)
            ##n#0_0_0_0 := #_module.Nat.S(m'#0_0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0_0_0_0, Tclass._module.Nat(), $Heap);
            ##m#0_0_0_0 := m'#0_0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#0_0_0_0, Tclass._module.Nat(), $Heap);
            assume _module.__default.plus#canCall(#_module.Nat.S(m'#0_0), m'#0_0);
            ##n#0_0_0_1 := #_module.Nat.S(_module.__default.plus($LS($LZ), #_module.Nat.S(m'#0_0), m'#0_0));
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0_0_0_1, Tclass._module.Nat(), $Heap);
            ##m#0_0_0_1 := n#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#0_0_0_1, Tclass._module.Nat(), $Heap);
            assume _module.__default.mult#canCall(#_module.Nat.S(_module.__default.plus($LS($LZ), #_module.Nat.S(m'#0_0), m'#0_0)), 
              n#0);
            assume _module.__default.plus#canCall(#_module.Nat.S(m'#0_0), m'#0_0)
               && _module.__default.mult#canCall(#_module.Nat.S(_module.__default.plus($LS($LZ), #_module.Nat.S(m'#0_0), m'#0_0)), 
                n#0);
            // ----- Hint5 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(274,7)
            // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(286,13)
            // Begin Comprehension WF check
            havoc a#0_0_0_0;
            havoc b#0_0_0_0;
            if ($Is(a#0_0_0_0, Tclass._module.Nat()) && $Is(b#0_0_0_0, Tclass._module.Nat()))
            {
                ##n#0_0_0_2 := a#0_0_0_0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#0_0_0_2, Tclass._module.Nat(), $Heap);
                ##m#0_0_0_2 := b#0_0_0_0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##m#0_0_0_2, Tclass._module.Nat(), $Heap);
                assume _module.__default.plus#canCall(a#0_0_0_0, b#0_0_0_0);
                ##n#0_0_0_3 := a#0_0_0_0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#0_0_0_3, Tclass._module.Nat(), $Heap);
                ##m#0_0_0_3 := #_module.Nat.S(b#0_0_0_0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##m#0_0_0_3, Tclass._module.Nat(), $Heap);
                assume _module.__default.plus#canCall(a#0_0_0_0, #_module.Nat.S(b#0_0_0_0));
            }

            // End Comprehension WF check
            assume (forall a#0_0_0_1: DatatypeType, b#0_0_0_1: DatatypeType :: 
              { _module.__default.plus($LS($LZ), a#0_0_0_1, #_module.Nat.S(b#0_0_0_1)) } 
                { #_module.Nat.S(_module.__default.plus($LS($LZ), a#0_0_0_1, b#0_0_0_1)) } 
              $Is(a#0_0_0_1, Tclass._module.Nat()) && $Is(b#0_0_0_1, Tclass._module.Nat())
                 ==> $IsA#_module.Nat(_module.__default.plus($LS($LZ), a#0_0_0_1, #_module.Nat.S(b#0_0_0_1)))
                   && 
                  _module.__default.plus#canCall(a#0_0_0_1, b#0_0_0_1)
                   && _module.__default.plus#canCall(a#0_0_0_1, #_module.Nat.S(b#0_0_0_1)));
            assert {:subsumption 0} (forall a#0_0_0_1: DatatypeType, b#0_0_0_1: DatatypeType :: 
              { _module.__default.plus($LS($LS($LZ)), a#0_0_0_1, #_module.Nat.S(b#0_0_0_1)) } 
                { #_module.Nat.S(_module.__default.plus($LS($LS($LZ)), a#0_0_0_1, b#0_0_0_1)) } 
              $Is(a#0_0_0_1, Tclass._module.Nat())
                   && $Is(b#0_0_0_1, Tclass._module.Nat())
                   && (forall a$ih#0_0_0_0#0_0_0_0: DatatypeType, b$ih#0_0_0_0#0_0_0_0: DatatypeType :: 
                    { _module.__default.plus($LS($LZ), a$ih#0_0_0_0#0_0_0_0, #_module.Nat.S(b$ih#0_0_0_0#0_0_0_0)) } 
                      { #_module.Nat.S(_module.__default.plus($LS($LZ), a$ih#0_0_0_0#0_0_0_0, b$ih#0_0_0_0#0_0_0_0)) } 
                    $Is(a$ih#0_0_0_0#0_0_0_0, Tclass._module.Nat())
                         && $Is(b$ih#0_0_0_0#0_0_0_0, Tclass._module.Nat())
                       ==> 
                      DtRank(a$ih#0_0_0_0#0_0_0_0) < DtRank(a#0_0_0_1)
                         || (DtRank(a$ih#0_0_0_0#0_0_0_0) == DtRank(a#0_0_0_1)
                           && DtRank(b$ih#0_0_0_0#0_0_0_0) < DtRank(b#0_0_0_1))
                       ==> _module.Nat#Equal(#_module.Nat.S(_module.__default.plus($LS($LZ), a$ih#0_0_0_0#0_0_0_0, b$ih#0_0_0_0#0_0_0_0)), 
                        _module.__default.plus($LS($LZ), a$ih#0_0_0_0#0_0_0_0, #_module.Nat.S(b$ih#0_0_0_0#0_0_0_0))))
                   && 
                  true
                   && #_module.Nat.O() == a#0_0_0_1
                   && #_module.Nat.O() == b#0_0_0_1
                 ==> _module.Nat#Equal(#_module.Nat.S(_module.__default.plus($LS($LS($LZ)), a#0_0_0_1, b#0_0_0_1)), 
                  _module.__default.plus($LS($LS($LZ)), a#0_0_0_1, #_module.Nat.S(b#0_0_0_1))));
            assert {:subsumption 0} (forall a#0_0_0_1: DatatypeType, b#0_0_0_1: DatatypeType :: 
              { _module.__default.plus($LS($LS($LZ)), a#0_0_0_1, #_module.Nat.S(b#0_0_0_1)) } 
                { #_module.Nat.S(_module.__default.plus($LS($LS($LZ)), a#0_0_0_1, b#0_0_0_1)) } 
              $Is(a#0_0_0_1, Tclass._module.Nat())
                   && $Is(b#0_0_0_1, Tclass._module.Nat())
                   && (forall a$ih#0_0_0_0#0_0_0_0: DatatypeType, b$ih#0_0_0_0#0_0_0_0: DatatypeType :: 
                    { _module.__default.plus($LS($LZ), a$ih#0_0_0_0#0_0_0_0, #_module.Nat.S(b$ih#0_0_0_0#0_0_0_0)) } 
                      { #_module.Nat.S(_module.__default.plus($LS($LZ), a$ih#0_0_0_0#0_0_0_0, b$ih#0_0_0_0#0_0_0_0)) } 
                    $Is(a$ih#0_0_0_0#0_0_0_0, Tclass._module.Nat())
                         && $Is(b$ih#0_0_0_0#0_0_0_0, Tclass._module.Nat())
                       ==> 
                      DtRank(a$ih#0_0_0_0#0_0_0_0) < DtRank(a#0_0_0_1)
                         || (DtRank(a$ih#0_0_0_0#0_0_0_0) == DtRank(a#0_0_0_1)
                           && DtRank(b$ih#0_0_0_0#0_0_0_0) < DtRank(b#0_0_0_1))
                       ==> _module.Nat#Equal(#_module.Nat.S(_module.__default.plus($LS($LZ), a$ih#0_0_0_0#0_0_0_0, b$ih#0_0_0_0#0_0_0_0)), 
                        _module.__default.plus($LS($LZ), a$ih#0_0_0_0#0_0_0_0, #_module.Nat.S(b$ih#0_0_0_0#0_0_0_0))))
                   && 
                  true
                   && (exists a#0_0_0_3#0#0: DatatypeType :: 
                    { #_module.Nat.S(a#0_0_0_3#0#0) } 
                    $Is(a#0_0_0_3#0#0, Tclass._module.Nat())
                       && #_module.Nat.S(a#0_0_0_3#0#0) == a#0_0_0_1)
                   && #_module.Nat.O() == b#0_0_0_1
                 ==> _module.Nat#Equal(#_module.Nat.S(_module.__default.plus($LS($LS($LZ)), a#0_0_0_1, b#0_0_0_1)), 
                  _module.__default.plus($LS($LS($LZ)), a#0_0_0_1, #_module.Nat.S(b#0_0_0_1))));
            assert {:subsumption 0} (forall a#0_0_0_1: DatatypeType, b#0_0_0_1: DatatypeType :: 
              { _module.__default.plus($LS($LS($LZ)), a#0_0_0_1, #_module.Nat.S(b#0_0_0_1)) } 
                { #_module.Nat.S(_module.__default.plus($LS($LS($LZ)), a#0_0_0_1, b#0_0_0_1)) } 
              $Is(a#0_0_0_1, Tclass._module.Nat())
                   && $Is(b#0_0_0_1, Tclass._module.Nat())
                   && (forall a$ih#0_0_0_0#0_0_0_0: DatatypeType, b$ih#0_0_0_0#0_0_0_0: DatatypeType :: 
                    { _module.__default.plus($LS($LZ), a$ih#0_0_0_0#0_0_0_0, #_module.Nat.S(b$ih#0_0_0_0#0_0_0_0)) } 
                      { #_module.Nat.S(_module.__default.plus($LS($LZ), a$ih#0_0_0_0#0_0_0_0, b$ih#0_0_0_0#0_0_0_0)) } 
                    $Is(a$ih#0_0_0_0#0_0_0_0, Tclass._module.Nat())
                         && $Is(b$ih#0_0_0_0#0_0_0_0, Tclass._module.Nat())
                       ==> 
                      DtRank(a$ih#0_0_0_0#0_0_0_0) < DtRank(a#0_0_0_1)
                         || (DtRank(a$ih#0_0_0_0#0_0_0_0) == DtRank(a#0_0_0_1)
                           && DtRank(b$ih#0_0_0_0#0_0_0_0) < DtRank(b#0_0_0_1))
                       ==> _module.Nat#Equal(#_module.Nat.S(_module.__default.plus($LS($LZ), a$ih#0_0_0_0#0_0_0_0, b$ih#0_0_0_0#0_0_0_0)), 
                        _module.__default.plus($LS($LZ), a$ih#0_0_0_0#0_0_0_0, #_module.Nat.S(b$ih#0_0_0_0#0_0_0_0))))
                   && 
                  true
                   && #_module.Nat.O() == a#0_0_0_1
                   && (exists a#0_0_0_5#0#0: DatatypeType :: 
                    { #_module.Nat.S(a#0_0_0_5#0#0) } 
                    $Is(a#0_0_0_5#0#0, Tclass._module.Nat())
                       && #_module.Nat.S(a#0_0_0_5#0#0) == b#0_0_0_1)
                 ==> _module.Nat#Equal(#_module.Nat.S(_module.__default.plus($LS($LS($LZ)), a#0_0_0_1, b#0_0_0_1)), 
                  _module.__default.plus($LS($LS($LZ)), a#0_0_0_1, #_module.Nat.S(b#0_0_0_1))));
            assert {:subsumption 0} (forall a#0_0_0_1: DatatypeType, b#0_0_0_1: DatatypeType :: 
              { _module.__default.plus($LS($LS($LZ)), a#0_0_0_1, #_module.Nat.S(b#0_0_0_1)) } 
                { #_module.Nat.S(_module.__default.plus($LS($LS($LZ)), a#0_0_0_1, b#0_0_0_1)) } 
              $Is(a#0_0_0_1, Tclass._module.Nat())
                   && $Is(b#0_0_0_1, Tclass._module.Nat())
                   && (forall a$ih#0_0_0_0#0_0_0_0: DatatypeType, b$ih#0_0_0_0#0_0_0_0: DatatypeType :: 
                    { _module.__default.plus($LS($LZ), a$ih#0_0_0_0#0_0_0_0, #_module.Nat.S(b$ih#0_0_0_0#0_0_0_0)) } 
                      { #_module.Nat.S(_module.__default.plus($LS($LZ), a$ih#0_0_0_0#0_0_0_0, b$ih#0_0_0_0#0_0_0_0)) } 
                    $Is(a$ih#0_0_0_0#0_0_0_0, Tclass._module.Nat())
                         && $Is(b$ih#0_0_0_0#0_0_0_0, Tclass._module.Nat())
                       ==> 
                      DtRank(a$ih#0_0_0_0#0_0_0_0) < DtRank(a#0_0_0_1)
                         || (DtRank(a$ih#0_0_0_0#0_0_0_0) == DtRank(a#0_0_0_1)
                           && DtRank(b$ih#0_0_0_0#0_0_0_0) < DtRank(b#0_0_0_1))
                       ==> _module.Nat#Equal(#_module.Nat.S(_module.__default.plus($LS($LZ), a$ih#0_0_0_0#0_0_0_0, b$ih#0_0_0_0#0_0_0_0)), 
                        _module.__default.plus($LS($LZ), a$ih#0_0_0_0#0_0_0_0, #_module.Nat.S(b$ih#0_0_0_0#0_0_0_0))))
                   && 
                  true
                   && (exists a#0_0_0_3#0#0: DatatypeType :: 
                    { #_module.Nat.S(a#0_0_0_3#0#0) } 
                    $Is(a#0_0_0_3#0#0, Tclass._module.Nat())
                       && #_module.Nat.S(a#0_0_0_3#0#0) == a#0_0_0_1)
                   && (exists a#0_0_0_5#0#0: DatatypeType :: 
                    { #_module.Nat.S(a#0_0_0_5#0#0) } 
                    $Is(a#0_0_0_5#0#0, Tclass._module.Nat())
                       && #_module.Nat.S(a#0_0_0_5#0#0) == b#0_0_0_1)
                 ==> _module.Nat#Equal(#_module.Nat.S(_module.__default.plus($LS($LS($LZ)), a#0_0_0_1, b#0_0_0_1)), 
                  _module.__default.plus($LS($LS($LZ)), a#0_0_0_1, #_module.Nat.S(b#0_0_0_1))));
            assume (forall a#0_0_0_1: DatatypeType, b#0_0_0_1: DatatypeType :: 
              {:induction} {:_induction a#0_0_0_1, b#0_0_0_1} { _module.__default.plus($LS($LZ), a#0_0_0_1, #_module.Nat.S(b#0_0_0_1)) } 
                { #_module.Nat.S(_module.__default.plus($LS($LZ), a#0_0_0_1, b#0_0_0_1)) } 
              $Is(a#0_0_0_1, Tclass._module.Nat()) && $Is(b#0_0_0_1, Tclass._module.Nat())
                 ==> _module.Nat#Equal(#_module.Nat.S(_module.__default.plus($LS($LZ), a#0_0_0_1, b#0_0_0_1)), 
                  _module.__default.plus($LS($LZ), a#0_0_0_1, #_module.Nat.S(b#0_0_0_1))));
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(274,7)
            ##n#0_0_0_4 := #_module.Nat.S(m'#0_0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0_0_0_4, Tclass._module.Nat(), $Heap);
            ##m#0_0_0_4 := #_module.Nat.S(m'#0_0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#0_0_0_4, Tclass._module.Nat(), $Heap);
            assume _module.__default.plus#canCall(#_module.Nat.S(m'#0_0), #_module.Nat.S(m'#0_0));
            ##n#0_0_0_5 := _module.__default.plus($LS($LZ), #_module.Nat.S(m'#0_0), #_module.Nat.S(m'#0_0));
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0_0_0_5, Tclass._module.Nat(), $Heap);
            ##m#0_0_0_5 := n#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#0_0_0_5, Tclass._module.Nat(), $Heap);
            assume _module.__default.mult#canCall(_module.__default.plus($LS($LZ), #_module.Nat.S(m'#0_0), #_module.Nat.S(m'#0_0)), 
              n#0);
            assume _module.__default.plus#canCall(#_module.Nat.S(m'#0_0), #_module.Nat.S(m'#0_0))
               && _module.__default.mult#canCall(_module.__default.plus($LS($LZ), #_module.Nat.S(m'#0_0), #_module.Nat.S(m'#0_0)), 
                n#0);
            // ----- assert line5 == line6 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(274,7)
            assert {:subsumption 0} _module.Nat#Equal(_module.__default.mult($LS($LS($LZ)), 
                #_module.Nat.S(_module.__default.plus($LS($LS($LZ)), #_module.Nat.S(m'#0_0), m'#0_0)), 
                n#0), 
              _module.__default.mult($LS($LS($LZ)), 
                _module.__default.plus($LS($LS($LZ)), #_module.Nat.S(m'#0_0), #_module.Nat.S(m'#0_0)), 
                n#0));
            assume false;
        }

        assume _module.Nat#Equal(_module.__default.mult($LS($LZ), m#0, _module.__default.plus($LS($LZ), n#0, n#0)), 
          _module.__default.mult($LS($LZ), 
            _module.__default.plus($LS($LZ), #_module.Nat.S(m'#0_0), #_module.Nat.S(m'#0_0)), 
            n#0));
    }
    else
    {
        assume false;
    }
}



// function declaration for _module._default.beq_nat
function _module.__default.beq__nat($ly: LayerType, n#0: DatatypeType, m#0: DatatypeType) : DatatypeType;

function _module.__default.beq__nat#canCall(n#0: DatatypeType, m#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType :: 
  { _module.__default.beq__nat($LS($ly), n#0, m#0) } 
  _module.__default.beq__nat($LS($ly), n#0, m#0)
     == _module.__default.beq__nat($ly, n#0, m#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType :: 
  { _module.__default.beq__nat(AsFuelBottom($ly), n#0, m#0) } 
  _module.__default.beq__nat($ly, n#0, m#0)
     == _module.__default.beq__nat($LZ, n#0, m#0));

// consequence axiom for _module.__default.beq__nat
axiom 20 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType :: 
    { _module.__default.beq__nat($ly, n#0, m#0) } 
    _module.__default.beq__nat#canCall(n#0, m#0)
         || (20 != $FunctionContextHeight
           && 
          $Is(n#0, Tclass._module.Nat())
           && $Is(m#0, Tclass._module.Nat()))
       ==> $Is(_module.__default.beq__nat($ly, n#0, m#0), Tclass._module.Bool()));

function _module.__default.beq__nat#requires(LayerType, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.beq__nat
axiom (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType :: 
  { _module.__default.beq__nat#requires($ly, n#0, m#0) } 
  $Is(n#0, Tclass._module.Nat()) && $Is(m#0, Tclass._module.Nat())
     ==> _module.__default.beq__nat#requires($ly, n#0, m#0) == true);

// definition axiom for _module.__default.beq__nat (revealed)
axiom 20 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType :: 
    { _module.__default.beq__nat($LS($ly), n#0, m#0) } 
    _module.__default.beq__nat#canCall(n#0, m#0)
         || (20 != $FunctionContextHeight
           && 
          $Is(n#0, Tclass._module.Nat())
           && $Is(m#0, Tclass._module.Nat()))
       ==> (!_module.Nat.O_q(n#0)
           ==> (var n'#1 := _module.Nat._h0(n#0); 
            !_module.Nat.O_q(m#0)
               ==> (var m'#3 := _module.Nat._h0(m#0); 
                _module.__default.beq__nat#canCall(n'#1, m'#3))))
         && _module.__default.beq__nat($LS($ly), n#0, m#0)
           == (if _module.Nat.O_q(n#0)
             then (if _module.Nat.O_q(m#0)
               then #_module.Bool.True()
               else (var m'#0 := _module.Nat._h0(m#0); Lit(#_module.Bool.False())))
             else (var n'#0 := _module.Nat._h0(n#0); 
              (if _module.Nat.O_q(m#0)
                 then #_module.Bool.False()
                 else (var m'#1 := _module.Nat._h0(m#0); _module.__default.beq__nat($ly, n'#0, m'#1))))));

// definition axiom for _module.__default.beq__nat for all literals (revealed)
axiom 20 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType :: 
    {:weight 3} { _module.__default.beq__nat($LS($ly), Lit(n#0), Lit(m#0)) } 
    _module.__default.beq__nat#canCall(Lit(n#0), Lit(m#0))
         || (20 != $FunctionContextHeight
           && 
          $Is(n#0, Tclass._module.Nat())
           && $Is(m#0, Tclass._module.Nat()))
       ==> (!Lit(_module.Nat.O_q(Lit(n#0)))
           ==> (var n'#3 := Lit(_module.Nat._h0(Lit(n#0))); 
            !Lit(_module.Nat.O_q(Lit(m#0)))
               ==> (var m'#7 := Lit(_module.Nat._h0(Lit(m#0))); 
                _module.__default.beq__nat#canCall(n'#3, m'#7))))
         && _module.__default.beq__nat($LS($ly), Lit(n#0), Lit(m#0))
           == (if _module.Nat.O_q(Lit(n#0))
             then (if _module.Nat.O_q(Lit(m#0))
               then #_module.Bool.True()
               else (var m'#4 := Lit(_module.Nat._h0(Lit(m#0))); Lit(#_module.Bool.False())))
             else (var n'#2 := Lit(_module.Nat._h0(Lit(n#0))); 
              (if _module.Nat.O_q(Lit(m#0))
                 then #_module.Bool.False()
                 else (var m'#5 := Lit(_module.Nat._h0(Lit(m#0))); 
                  Lit(_module.__default.beq__nat($LS($ly), n'#2, m'#5)))))));

procedure CheckWellformed$$_module.__default.beq__nat(n#0: DatatypeType where $Is(n#0, Tclass._module.Nat()), 
    m#0: DatatypeType where $Is(m#0, Tclass._module.Nat()));
  free requires 20 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.beq__nat(n#0: DatatypeType, m#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: DatatypeType;
  var n'#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var _mcc#2#0: DatatypeType;
  var m'#Z#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var ##n#0: DatatypeType;
  var ##m#0: DatatypeType;
  var _mcc#1#0: DatatypeType;
  var m'#Z#1: DatatypeType;
  var let#2#0#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function beq_nat
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(292,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.beq__nat($LS($LZ), n#0, m#0), Tclass._module.Bool());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (n#0 == #_module.Nat.O())
        {
            if (m#0 == #_module.Nat.O())
            {
                assume _module.__default.beq__nat($LS($LZ), n#0, m#0) == Lit(#_module.Bool.True());
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.beq__nat($LS($LZ), n#0, m#0), Tclass._module.Bool());
            }
            else if (m#0 == #_module.Nat.S(_mcc#1#0))
            {
                assume $Is(_mcc#1#0, Tclass._module.Nat());
                havoc m'#Z#1;
                assume $Is(m'#Z#1, Tclass._module.Nat());
                assume let#2#0#0 == _mcc#1#0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(let#2#0#0, Tclass._module.Nat());
                assume m'#Z#1 == let#2#0#0;
                assume _module.__default.beq__nat($LS($LZ), n#0, m#0) == Lit(#_module.Bool.False());
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.beq__nat($LS($LZ), n#0, m#0), Tclass._module.Bool());
            }
            else
            {
                assume false;
            }
        }
        else if (n#0 == #_module.Nat.S(_mcc#0#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.Nat());
            havoc n'#Z#0;
            assume $Is(n'#Z#0, Tclass._module.Nat());
            assume let#0#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.Nat());
            assume n'#Z#0 == let#0#0#0;
            if (m#0 == #_module.Nat.O())
            {
                assume _module.__default.beq__nat($LS($LZ), n#0, m#0) == Lit(#_module.Bool.False());
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.beq__nat($LS($LZ), n#0, m#0), Tclass._module.Bool());
            }
            else if (m#0 == #_module.Nat.S(_mcc#2#0))
            {
                assume $Is(_mcc#2#0, Tclass._module.Nat());
                havoc m'#Z#0;
                assume $Is(m'#Z#0, Tclass._module.Nat());
                assume let#1#0#0 == _mcc#2#0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(let#1#0#0, Tclass._module.Nat());
                assume m'#Z#0 == let#1#0#0;
                ##n#0 := n'#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#0, Tclass._module.Nat(), $Heap);
                ##m#0 := m'#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##m#0, Tclass._module.Nat(), $Heap);
                b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assert DtRank(##n#0) < DtRank(n#0)
                   || (DtRank(##n#0) == DtRank(n#0) && DtRank(##m#0) < DtRank(m#0));
                assume _module.__default.beq__nat#canCall(n'#Z#0, m'#Z#0);
                assume _module.__default.beq__nat($LS($LZ), n#0, m#0)
                   == _module.__default.beq__nat($LS($LZ), n'#Z#0, m'#Z#0);
                assume _module.__default.beq__nat#canCall(n'#Z#0, m'#Z#0);
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.beq__nat($LS($LZ), n#0, m#0), Tclass._module.Bool());
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



// function declaration for _module._default.ble_nat
function _module.__default.ble__nat($ly: LayerType, n#0: DatatypeType, m#0: DatatypeType) : DatatypeType;

function _module.__default.ble__nat#canCall(n#0: DatatypeType, m#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType :: 
  { _module.__default.ble__nat($LS($ly), n#0, m#0) } 
  _module.__default.ble__nat($LS($ly), n#0, m#0)
     == _module.__default.ble__nat($ly, n#0, m#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType :: 
  { _module.__default.ble__nat(AsFuelBottom($ly), n#0, m#0) } 
  _module.__default.ble__nat($ly, n#0, m#0)
     == _module.__default.ble__nat($LZ, n#0, m#0));

// consequence axiom for _module.__default.ble__nat
axiom 21 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType :: 
    { _module.__default.ble__nat($ly, n#0, m#0) } 
    _module.__default.ble__nat#canCall(n#0, m#0)
         || (21 != $FunctionContextHeight
           && 
          $Is(n#0, Tclass._module.Nat())
           && $Is(m#0, Tclass._module.Nat()))
       ==> $Is(_module.__default.ble__nat($ly, n#0, m#0), Tclass._module.Bool()));

function _module.__default.ble__nat#requires(LayerType, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.ble__nat
axiom (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType :: 
  { _module.__default.ble__nat#requires($ly, n#0, m#0) } 
  $Is(n#0, Tclass._module.Nat()) && $Is(m#0, Tclass._module.Nat())
     ==> _module.__default.ble__nat#requires($ly, n#0, m#0) == true);

// definition axiom for _module.__default.ble__nat (revealed)
axiom 21 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType :: 
    { _module.__default.ble__nat($LS($ly), n#0, m#0) } 
    _module.__default.ble__nat#canCall(n#0, m#0)
         || (21 != $FunctionContextHeight
           && 
          $Is(n#0, Tclass._module.Nat())
           && $Is(m#0, Tclass._module.Nat()))
       ==> (!_module.Nat.O_q(n#0)
           ==> (var n'#1 := _module.Nat._h0(n#0); 
            !_module.Nat.O_q(m#0)
               ==> (var m'#1 := _module.Nat._h0(m#0); 
                _module.__default.ble__nat#canCall(n'#1, m'#1))))
         && _module.__default.ble__nat($LS($ly), n#0, m#0)
           == (if _module.Nat.O_q(n#0)
             then #_module.Bool.True()
             else (var n'#0 := _module.Nat._h0(n#0); 
              (if _module.Nat.O_q(m#0)
                 then #_module.Bool.False()
                 else (var m'#0 := _module.Nat._h0(m#0); _module.__default.ble__nat($ly, n'#0, m'#0))))));

// definition axiom for _module.__default.ble__nat for all literals (revealed)
axiom 21 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType :: 
    {:weight 3} { _module.__default.ble__nat($LS($ly), Lit(n#0), Lit(m#0)) } 
    _module.__default.ble__nat#canCall(Lit(n#0), Lit(m#0))
         || (21 != $FunctionContextHeight
           && 
          $Is(n#0, Tclass._module.Nat())
           && $Is(m#0, Tclass._module.Nat()))
       ==> (!Lit(_module.Nat.O_q(Lit(n#0)))
           ==> (var n'#3 := Lit(_module.Nat._h0(Lit(n#0))); 
            !Lit(_module.Nat.O_q(Lit(m#0)))
               ==> (var m'#3 := Lit(_module.Nat._h0(Lit(m#0))); 
                _module.__default.ble__nat#canCall(n'#3, m'#3))))
         && _module.__default.ble__nat($LS($ly), Lit(n#0), Lit(m#0))
           == (if _module.Nat.O_q(Lit(n#0))
             then #_module.Bool.True()
             else (var n'#2 := Lit(_module.Nat._h0(Lit(n#0))); 
              (if _module.Nat.O_q(Lit(m#0))
                 then #_module.Bool.False()
                 else (var m'#2 := Lit(_module.Nat._h0(Lit(m#0))); 
                  Lit(_module.__default.ble__nat($LS($ly), n'#2, m'#2)))))));

procedure CheckWellformed$$_module.__default.ble__nat(n#0: DatatypeType where $Is(n#0, Tclass._module.Nat()), 
    m#0: DatatypeType where $Is(m#0, Tclass._module.Nat()));
  free requires 21 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.ble__nat(n#0: DatatypeType, m#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: DatatypeType;
  var n'#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var _mcc#1#0: DatatypeType;
  var m'#Z#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var ##n#0: DatatypeType;
  var ##m#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function ble_nat
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(306,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.ble__nat($LS($LZ), n#0, m#0), Tclass._module.Bool());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (n#0 == #_module.Nat.O())
        {
            assume _module.__default.ble__nat($LS($LZ), n#0, m#0) == Lit(#_module.Bool.True());
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.ble__nat($LS($LZ), n#0, m#0), Tclass._module.Bool());
        }
        else if (n#0 == #_module.Nat.S(_mcc#0#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.Nat());
            havoc n'#Z#0;
            assume $Is(n'#Z#0, Tclass._module.Nat());
            assume let#0#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.Nat());
            assume n'#Z#0 == let#0#0#0;
            if (m#0 == #_module.Nat.O())
            {
                assume _module.__default.ble__nat($LS($LZ), n#0, m#0) == Lit(#_module.Bool.False());
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.ble__nat($LS($LZ), n#0, m#0), Tclass._module.Bool());
            }
            else if (m#0 == #_module.Nat.S(_mcc#1#0))
            {
                assume $Is(_mcc#1#0, Tclass._module.Nat());
                havoc m'#Z#0;
                assume $Is(m'#Z#0, Tclass._module.Nat());
                assume let#1#0#0 == _mcc#1#0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(let#1#0#0, Tclass._module.Nat());
                assume m'#Z#0 == let#1#0#0;
                ##n#0 := n'#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#0, Tclass._module.Nat(), $Heap);
                ##m#0 := m'#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##m#0, Tclass._module.Nat(), $Heap);
                b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assert DtRank(##n#0) < DtRank(n#0)
                   || (DtRank(##n#0) == DtRank(n#0) && DtRank(##m#0) < DtRank(m#0));
                assume _module.__default.ble__nat#canCall(n'#Z#0, m'#Z#0);
                assume _module.__default.ble__nat($LS($LZ), n#0, m#0)
                   == _module.__default.ble__nat($LS($LZ), n'#Z#0, m'#Z#0);
                assume _module.__default.ble__nat#canCall(n'#Z#0, m'#Z#0);
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.ble__nat($LS($LZ), n#0, m#0), Tclass._module.Bool());
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



procedure CheckWellformed$$_module.__default.test__ble__nat1();
  free requires 53 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.test__ble__nat1();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.test__ble__nat1() returns ($_reverifyPost: bool);
  free requires 53 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.test__ble__nat1() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var n2#0: DatatypeType
     where $Is(n2#0, Tclass._module.Nat()) && $IsAlloc(n2#0, Tclass._module.Nat(), $Heap);
  var n4#0: DatatypeType
     where $Is(n4#0, Tclass._module.Nat()) && $IsAlloc(n4#0, Tclass._module.Nat(), $Heap);
  var ##n#0: DatatypeType;
  var ##m#0: DatatypeType;
  var ##n#1: DatatypeType;
  var ##m#1: DatatypeType;
  var ##n#2: DatatypeType;
  var ##m#2: DatatypeType;

    // AddMethodImpl: test_ble_nat1, Impl$$_module.__default.test__ble__nat1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(317,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(318,10)
    assume true;
    assume true;
    n2#0 := Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.O())))));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(318,19)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(319,10)
    assume true;
    assume true;
    n4#0 := #_module.Nat.S(#_module.Nat.S(n2#0));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(319,20)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(320,3)
    ##n#0 := n2#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#0, Tclass._module.Nat(), $Heap);
    ##m#0 := n2#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##m#0, Tclass._module.Nat(), $Heap);
    assume _module.__default.ble__nat#canCall(n2#0, n2#0);
    assume $IsA#_module.Bool(_module.__default.ble__nat($LS($LZ), n2#0, n2#0))
       && _module.__default.ble__nat#canCall(n2#0, n2#0);
    assert {:subsumption 0} _module.Bool#Equal(_module.__default.ble__nat($LS($LS($LZ)), n2#0, n2#0), #_module.Bool.True());
    assume _module.Bool#Equal(_module.__default.ble__nat($LS($LZ), n2#0, n2#0), #_module.Bool.True());
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(321,3)
    ##n#1 := n2#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#1, Tclass._module.Nat(), $Heap);
    ##m#1 := n4#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##m#1, Tclass._module.Nat(), $Heap);
    assume _module.__default.ble__nat#canCall(n2#0, n4#0);
    assume $IsA#_module.Bool(_module.__default.ble__nat($LS($LZ), n2#0, n4#0))
       && _module.__default.ble__nat#canCall(n2#0, n4#0);
    assert {:subsumption 0} _module.Bool#Equal(_module.__default.ble__nat($LS($LS($LZ)), n2#0, n4#0), #_module.Bool.True());
    assume _module.Bool#Equal(_module.__default.ble__nat($LS($LZ), n2#0, n4#0), #_module.Bool.True());
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(322,3)
    ##n#2 := n4#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#2, Tclass._module.Nat(), $Heap);
    ##m#2 := n2#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##m#2, Tclass._module.Nat(), $Heap);
    assume _module.__default.ble__nat#canCall(n4#0, n2#0);
    assume $IsA#_module.Bool(_module.__default.ble__nat($LS($LZ), n4#0, n2#0))
       && _module.__default.ble__nat#canCall(n4#0, n2#0);
    assert {:subsumption 0} _module.Bool#Equal(_module.__default.ble__nat($LS($LS($LZ)), n4#0, n2#0), #_module.Bool.False());
    assume _module.Bool#Equal(_module.__default.ble__nat($LS($LZ), n4#0, n2#0), #_module.Bool.False());
}



// function declaration for _module._default.blt_nat
function _module.__default.blt__nat(n#0: DatatypeType, m#0: DatatypeType) : DatatypeType;

function _module.__default.blt__nat#canCall(n#0: DatatypeType, m#0: DatatypeType) : bool;

// consequence axiom for _module.__default.blt__nat
axiom 22 <= $FunctionContextHeight
   ==> (forall n#0: DatatypeType, m#0: DatatypeType :: 
    { _module.__default.blt__nat(n#0, m#0) } 
    _module.__default.blt__nat#canCall(n#0, m#0)
         || (22 != $FunctionContextHeight
           && 
          $Is(n#0, Tclass._module.Nat())
           && $Is(m#0, Tclass._module.Nat()))
       ==> $Is(_module.__default.blt__nat(n#0, m#0), Tclass._module.Bool()));

function _module.__default.blt__nat#requires(DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.blt__nat
axiom (forall n#0: DatatypeType, m#0: DatatypeType :: 
  { _module.__default.blt__nat#requires(n#0, m#0) } 
  $Is(n#0, Tclass._module.Nat()) && $Is(m#0, Tclass._module.Nat())
     ==> _module.__default.blt__nat#requires(n#0, m#0) == true);

// definition axiom for _module.__default.blt__nat (revealed)
axiom 22 <= $FunctionContextHeight
   ==> (forall n#0: DatatypeType, m#0: DatatypeType :: 
    { _module.__default.blt__nat(n#0, m#0) } 
    _module.__default.blt__nat#canCall(n#0, m#0)
         || (22 != $FunctionContextHeight
           && 
          $Is(n#0, Tclass._module.Nat())
           && $Is(m#0, Tclass._module.Nat()))
       ==> _module.__default.ble__nat#canCall(n#0, m#0)
         && 
        _module.__default.beq__nat#canCall(n#0, m#0)
         && _module.__default.negb#canCall(_module.__default.beq__nat($LS($LZ), n#0, m#0))
         && _module.__default.andb#canCall(_module.__default.ble__nat($LS($LZ), n#0, m#0), 
          _module.__default.negb(_module.__default.beq__nat($LS($LZ), n#0, m#0)))
         && _module.__default.blt__nat(n#0, m#0)
           == _module.__default.andb(_module.__default.ble__nat($LS($LZ), n#0, m#0), 
            _module.__default.negb(_module.__default.beq__nat($LS($LZ), n#0, m#0))));

// definition axiom for _module.__default.blt__nat for all literals (revealed)
axiom 22 <= $FunctionContextHeight
   ==> (forall n#0: DatatypeType, m#0: DatatypeType :: 
    {:weight 3} { _module.__default.blt__nat(Lit(n#0), Lit(m#0)) } 
    _module.__default.blt__nat#canCall(Lit(n#0), Lit(m#0))
         || (22 != $FunctionContextHeight
           && 
          $Is(n#0, Tclass._module.Nat())
           && $Is(m#0, Tclass._module.Nat()))
       ==> _module.__default.ble__nat#canCall(Lit(n#0), Lit(m#0))
         && 
        _module.__default.beq__nat#canCall(Lit(n#0), Lit(m#0))
         && _module.__default.negb#canCall(Lit(_module.__default.beq__nat($LS($LZ), Lit(n#0), Lit(m#0))))
         && _module.__default.andb#canCall(Lit(_module.__default.ble__nat($LS($LZ), Lit(n#0), Lit(m#0))), 
          Lit(_module.__default.negb(Lit(_module.__default.beq__nat($LS($LZ), Lit(n#0), Lit(m#0))))))
         && _module.__default.blt__nat(Lit(n#0), Lit(m#0))
           == Lit(_module.__default.andb(Lit(_module.__default.ble__nat($LS($LZ), Lit(n#0), Lit(m#0))), 
              Lit(_module.__default.negb(Lit(_module.__default.beq__nat($LS($LZ), Lit(n#0), Lit(m#0))))))));

procedure CheckWellformed$$_module.__default.blt__nat(n#0: DatatypeType where $Is(n#0, Tclass._module.Nat()), 
    m#0: DatatypeType where $Is(m#0, Tclass._module.Nat()));
  free requires 22 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.blt__nat(n#0: DatatypeType, m#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##n#0: DatatypeType;
  var ##m#0: DatatypeType;
  var ##n#1: DatatypeType;
  var ##m#1: DatatypeType;
  var ##b#0: DatatypeType;
  var ##b1#0: DatatypeType;
  var ##b2#0: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;
  var b$reqreads#2: bool;
  var b$reqreads#3: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;
    b$reqreads#3 := true;

    // AddWellformednessCheck for function blt_nat
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(327,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.blt__nat(n#0, m#0), Tclass._module.Bool());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        ##n#0 := n#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#0, Tclass._module.Nat(), $Heap);
        ##m#0 := m#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##m#0, Tclass._module.Nat(), $Heap);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.ble__nat#canCall(n#0, m#0);
        ##n#1 := n#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#1, Tclass._module.Nat(), $Heap);
        ##m#1 := m#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##m#1, Tclass._module.Nat(), $Heap);
        b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.beq__nat#canCall(n#0, m#0);
        ##b#0 := _module.__default.beq__nat($LS($LZ), n#0, m#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##b#0, Tclass._module.Bool(), $Heap);
        b$reqreads#2 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.negb#canCall(_module.__default.beq__nat($LS($LZ), n#0, m#0));
        ##b1#0 := _module.__default.ble__nat($LS($LZ), n#0, m#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##b1#0, Tclass._module.Bool(), $Heap);
        ##b2#0 := _module.__default.negb(_module.__default.beq__nat($LS($LZ), n#0, m#0));
        // assume allocatedness for argument to function
        assume $IsAlloc(##b2#0, Tclass._module.Bool(), $Heap);
        b$reqreads#3 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.andb#canCall(_module.__default.ble__nat($LS($LZ), n#0, m#0), 
          _module.__default.negb(_module.__default.beq__nat($LS($LZ), n#0, m#0)));
        assume _module.__default.blt__nat(n#0, m#0)
           == _module.__default.andb(_module.__default.ble__nat($LS($LZ), n#0, m#0), 
            _module.__default.negb(_module.__default.beq__nat($LS($LZ), n#0, m#0)));
        assume _module.__default.ble__nat#canCall(n#0, m#0)
           && 
          _module.__default.beq__nat#canCall(n#0, m#0)
           && _module.__default.negb#canCall(_module.__default.beq__nat($LS($LZ), n#0, m#0))
           && _module.__default.andb#canCall(_module.__default.ble__nat($LS($LZ), n#0, m#0), 
            _module.__default.negb(_module.__default.beq__nat($LS($LZ), n#0, m#0)));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.blt__nat(n#0, m#0), Tclass._module.Bool());
        assert b$reqreads#0;
        assert b$reqreads#1;
        assert b$reqreads#2;
        assert b$reqreads#3;
    }
}



procedure CheckWellformed$$_module.__default.test__blt__nat1();
  free requires 54 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.test__blt__nat1();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.test__blt__nat1() returns ($_reverifyPost: bool);
  free requires 54 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.test__blt__nat1() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var n2#0: DatatypeType
     where $Is(n2#0, Tclass._module.Nat()) && $IsAlloc(n2#0, Tclass._module.Nat(), $Heap);
  var n4#0: DatatypeType
     where $Is(n4#0, Tclass._module.Nat()) && $IsAlloc(n4#0, Tclass._module.Nat(), $Heap);
  var ##n#0: DatatypeType;
  var ##m#0: DatatypeType;
  var ##n#1: DatatypeType;
  var ##m#1: DatatypeType;
  var ##n#2: DatatypeType;
  var ##m#2: DatatypeType;

    // AddMethodImpl: test_blt_nat1, Impl$$_module.__default.test__blt__nat1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(333,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(334,10)
    assume true;
    assume true;
    n2#0 := Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.O())))));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(334,19)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(335,10)
    assume true;
    assume true;
    n4#0 := #_module.Nat.S(#_module.Nat.S(n2#0));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(335,20)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(336,3)
    ##n#0 := n2#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#0, Tclass._module.Nat(), $Heap);
    ##m#0 := n2#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##m#0, Tclass._module.Nat(), $Heap);
    assume _module.__default.blt__nat#canCall(n2#0, n2#0);
    assume $IsA#_module.Bool(_module.__default.blt__nat(n2#0, n2#0))
       && _module.__default.blt__nat#canCall(n2#0, n2#0);
    assert _module.Bool#Equal(_module.__default.blt__nat(n2#0, n2#0), #_module.Bool.False());
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(337,3)
    ##n#1 := n2#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#1, Tclass._module.Nat(), $Heap);
    ##m#1 := n4#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##m#1, Tclass._module.Nat(), $Heap);
    assume _module.__default.blt__nat#canCall(n2#0, n4#0);
    assume $IsA#_module.Bool(_module.__default.blt__nat(n2#0, n4#0))
       && _module.__default.blt__nat#canCall(n2#0, n4#0);
    assert _module.Bool#Equal(_module.__default.blt__nat(n2#0, n4#0), #_module.Bool.True());
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(338,3)
    ##n#2 := n4#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#2, Tclass._module.Nat(), $Heap);
    ##m#2 := n2#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##m#2, Tclass._module.Nat(), $Heap);
    assume _module.__default.blt__nat#canCall(n4#0, n2#0);
    assume $IsA#_module.Bool(_module.__default.blt__nat(n4#0, n2#0))
       && _module.__default.blt__nat#canCall(n4#0, n2#0);
    assert _module.Bool#Equal(_module.__default.blt__nat(n4#0, n2#0), #_module.Bool.False());
}



procedure {:_induction n#0} CheckWellformed$$_module.__default.plus__O__n(n#0: DatatypeType
       where $Is(n#0, Tclass._module.Nat())
         && $IsAlloc(n#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(n#0));
  free requires 23 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction n#0} Call$$_module.__default.plus__O__n(n#0: DatatypeType
       where $Is(n#0, Tclass._module.Nat())
         && $IsAlloc(n#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(n#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Nat(_module.__default.plus($LS($LZ), Lit(#_module.Nat.O()), n#0))
     && $IsA#_module.Nat(n#0)
     && _module.__default.plus#canCall(Lit(#_module.Nat.O()), n#0);
  ensures _module.Nat#Equal(_module.__default.plus($LS($LS($LZ)), Lit(#_module.Nat.O()), n#0), n#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction n#0} Impl$$_module.__default.plus__O__n(n#0: DatatypeType
       where $Is(n#0, Tclass._module.Nat())
         && $IsAlloc(n#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(n#0))
   returns ($_reverifyPost: bool);
  free requires 23 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Nat(_module.__default.plus($LS($LZ), Lit(#_module.Nat.O()), n#0))
     && $IsA#_module.Nat(n#0)
     && _module.__default.plus#canCall(Lit(#_module.Nat.O()), n#0);
  ensures _module.Nat#Equal(_module.__default.plus($LS($LS($LZ)), Lit(#_module.Nat.O()), n#0), n#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction n#0} Impl$$_module.__default.plus__O__n(n#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;

    // AddMethodImpl: plus_O_n, Impl$$_module.__default.plus__O__n
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(345,0): initial state"} true;
    assume $IsA#_module.Nat(n#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#n0#0: DatatypeType :: 
      $Is($ih#n0#0, Tclass._module.Nat())
           && Lit(true)
           && DtRank($ih#n0#0) < DtRank(n#0)
         ==> _module.Nat#Equal(_module.__default.plus($LS($LZ), Lit(#_module.Nat.O()), $ih#n0#0), $ih#n0#0));
    $_reverifyPost := false;
}



procedure {:_induction n#0} CheckWellformed$$_module.__default.plus__1__l(n#0: DatatypeType
       where $Is(n#0, Tclass._module.Nat())
         && $IsAlloc(n#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(n#0));
  free requires 24 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction n#0} Call$$_module.__default.plus__1__l(n#0: DatatypeType
       where $Is(n#0, Tclass._module.Nat())
         && $IsAlloc(n#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(n#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Nat(_module.__default.plus($LS($LZ), Lit(#_module.Nat.S(Lit(#_module.Nat.O()))), n#0))
     && _module.__default.plus#canCall(Lit(#_module.Nat.S(Lit(#_module.Nat.O()))), n#0);
  ensures _module.Nat#Equal(_module.__default.plus($LS($LS($LZ)), Lit(#_module.Nat.S(Lit(#_module.Nat.O()))), n#0), 
    #_module.Nat.S(n#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction n#0} Impl$$_module.__default.plus__1__l(n#0: DatatypeType
       where $Is(n#0, Tclass._module.Nat())
         && $IsAlloc(n#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(n#0))
   returns ($_reverifyPost: bool);
  free requires 24 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Nat(_module.__default.plus($LS($LZ), Lit(#_module.Nat.S(Lit(#_module.Nat.O()))), n#0))
     && _module.__default.plus#canCall(Lit(#_module.Nat.S(Lit(#_module.Nat.O()))), n#0);
  ensures _module.Nat#Equal(_module.__default.plus($LS($LS($LZ)), Lit(#_module.Nat.S(Lit(#_module.Nat.O()))), n#0), 
    #_module.Nat.S(n#0));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction n#0} Impl$$_module.__default.plus__1__l(n#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;

    // AddMethodImpl: plus_1_l, Impl$$_module.__default.plus__1__l
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(350,0): initial state"} true;
    assume $IsA#_module.Nat(n#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#n0#0: DatatypeType :: 
      $Is($ih#n0#0, Tclass._module.Nat())
           && Lit(true)
           && DtRank($ih#n0#0) < DtRank(n#0)
         ==> _module.Nat#Equal(_module.__default.plus($LS($LZ), Lit(#_module.Nat.S(Lit(#_module.Nat.O()))), $ih#n0#0), 
          #_module.Nat.S($ih#n0#0)));
    $_reverifyPost := false;
}



procedure {:_induction n#0} CheckWellformed$$_module.__default.mult__0__l(n#0: DatatypeType
       where $Is(n#0, Tclass._module.Nat())
         && $IsAlloc(n#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(n#0));
  free requires 25 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction n#0} Call$$_module.__default.mult__0__l(n#0: DatatypeType
       where $Is(n#0, Tclass._module.Nat())
         && $IsAlloc(n#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(n#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Nat(_module.__default.mult($LS($LZ), Lit(#_module.Nat.O()), n#0))
     && _module.__default.mult#canCall(Lit(#_module.Nat.O()), n#0);
  ensures _module.Nat#Equal(_module.__default.mult($LS($LS($LZ)), Lit(#_module.Nat.O()), n#0), 
    #_module.Nat.O());
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction n#0} Impl$$_module.__default.mult__0__l(n#0: DatatypeType
       where $Is(n#0, Tclass._module.Nat())
         && $IsAlloc(n#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(n#0))
   returns ($_reverifyPost: bool);
  free requires 25 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Nat(_module.__default.mult($LS($LZ), Lit(#_module.Nat.O()), n#0))
     && _module.__default.mult#canCall(Lit(#_module.Nat.O()), n#0);
  ensures _module.Nat#Equal(_module.__default.mult($LS($LS($LZ)), Lit(#_module.Nat.O()), n#0), 
    #_module.Nat.O());
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction n#0} Impl$$_module.__default.mult__0__l(n#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;

    // AddMethodImpl: mult_0_l, Impl$$_module.__default.mult__0__l
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(355,0): initial state"} true;
    assume $IsA#_module.Nat(n#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#n0#0: DatatypeType :: 
      $Is($ih#n0#0, Tclass._module.Nat())
           && Lit(true)
           && DtRank($ih#n0#0) < DtRank(n#0)
         ==> _module.Nat#Equal(_module.__default.mult($LS($LZ), Lit(#_module.Nat.O()), $ih#n0#0), 
          #_module.Nat.O()));
    $_reverifyPost := false;
}



procedure {:_induction n#0, m#0} CheckWellformed$$_module.__default.plus__id__example(n#0: DatatypeType
       where $Is(n#0, Tclass._module.Nat())
         && $IsAlloc(n#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(n#0), 
    m#0: DatatypeType
       where $Is(m#0, Tclass._module.Nat())
         && $IsAlloc(m#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(m#0));
  free requires 26 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction n#0, m#0} Call$$_module.__default.plus__id__example(n#0: DatatypeType
       where $Is(n#0, Tclass._module.Nat())
         && $IsAlloc(n#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(n#0), 
    m#0: DatatypeType
       where $Is(m#0, Tclass._module.Nat())
         && $IsAlloc(m#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(m#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Nat(n#0)
     && $IsA#_module.Nat(m#0)
     && (_module.Nat#Equal(n#0, m#0)
       ==> $IsA#_module.Nat(_module.__default.plus($LS($LZ), n#0, n#0))
         && $IsA#_module.Nat(_module.__default.plus($LS($LZ), m#0, m#0))
         && 
        _module.__default.plus#canCall(n#0, n#0)
         && _module.__default.plus#canCall(m#0, m#0));
  ensures _module.Nat#Equal(n#0, m#0)
     ==> _module.Nat#Equal(_module.__default.plus($LS($LS($LZ)), n#0, n#0), 
      _module.__default.plus($LS($LS($LZ)), m#0, m#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction n#0, m#0} Impl$$_module.__default.plus__id__example(n#0: DatatypeType
       where $Is(n#0, Tclass._module.Nat())
         && $IsAlloc(n#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(n#0), 
    m#0: DatatypeType
       where $Is(m#0, Tclass._module.Nat())
         && $IsAlloc(m#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(m#0))
   returns ($_reverifyPost: bool);
  free requires 26 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Nat(n#0)
     && $IsA#_module.Nat(m#0)
     && (_module.Nat#Equal(n#0, m#0)
       ==> $IsA#_module.Nat(_module.__default.plus($LS($LZ), n#0, n#0))
         && $IsA#_module.Nat(_module.__default.plus($LS($LZ), m#0, m#0))
         && 
        _module.__default.plus#canCall(n#0, n#0)
         && _module.__default.plus#canCall(m#0, m#0));
  ensures _module.Nat#Equal(n#0, m#0)
     ==> _module.Nat#Equal(_module.__default.plus($LS($LS($LZ)), n#0, n#0), 
      _module.__default.plus($LS($LS($LZ)), m#0, m#0));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction n#0, m#0} Impl$$_module.__default.plus__id__example(n#0: DatatypeType, m#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;

    // AddMethodImpl: plus_id_example, Impl$$_module.__default.plus__id__example
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(362,0): initial state"} true;
    assume $IsA#_module.Nat(n#0);
    assume $IsA#_module.Nat(m#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#n0#0: DatatypeType, $ih#m0#0: DatatypeType :: 
      $Is($ih#n0#0, Tclass._module.Nat())
           && $Is($ih#m0#0, Tclass._module.Nat())
           && Lit(true)
           && (DtRank($ih#n0#0) < DtRank(n#0)
             || (DtRank($ih#n0#0) == DtRank(n#0) && DtRank($ih#m0#0) < DtRank(m#0)))
         ==> 
        _module.Nat#Equal($ih#n0#0, $ih#m0#0)
         ==> _module.Nat#Equal(_module.__default.plus($LS($LZ), $ih#n0#0, $ih#n0#0), 
          _module.__default.plus($LS($LZ), $ih#m0#0, $ih#m0#0)));
    $_reverifyPost := false;
}



procedure {:_induction n#0, m#0, o#0} CheckWellformed$$_module.__default.plus__id__exercise(n#0: DatatypeType
       where $Is(n#0, Tclass._module.Nat())
         && $IsAlloc(n#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(n#0), 
    m#0: DatatypeType
       where $Is(m#0, Tclass._module.Nat())
         && $IsAlloc(m#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(m#0), 
    o#0: DatatypeType
       where $Is(o#0, Tclass._module.Nat())
         && $IsAlloc(o#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(o#0));
  free requires 27 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction n#0, m#0, o#0} Call$$_module.__default.plus__id__exercise(n#0: DatatypeType
       where $Is(n#0, Tclass._module.Nat())
         && $IsAlloc(n#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(n#0), 
    m#0: DatatypeType
       where $Is(m#0, Tclass._module.Nat())
         && $IsAlloc(m#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(m#0), 
    o#0: DatatypeType
       where $Is(o#0, Tclass._module.Nat())
         && $IsAlloc(o#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(o#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Nat(n#0)
     && $IsA#_module.Nat(m#0)
     && (_module.Nat#Equal(n#0, m#0)
       ==> $IsA#_module.Nat(m#0)
         && $IsA#_module.Nat(o#0)
         && (_module.Nat#Equal(m#0, o#0)
           ==> $IsA#_module.Nat(_module.__default.plus($LS($LZ), n#0, m#0))
             && $IsA#_module.Nat(_module.__default.plus($LS($LZ), m#0, o#0))
             && 
            _module.__default.plus#canCall(n#0, m#0)
             && _module.__default.plus#canCall(m#0, o#0)));
  ensures _module.Nat#Equal(n#0, m#0)
     ==> 
    _module.Nat#Equal(m#0, o#0)
     ==> _module.Nat#Equal(_module.__default.plus($LS($LS($LZ)), n#0, m#0), 
      _module.__default.plus($LS($LS($LZ)), m#0, o#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction n#0, m#0, o#0} Impl$$_module.__default.plus__id__exercise(n#0: DatatypeType
       where $Is(n#0, Tclass._module.Nat())
         && $IsAlloc(n#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(n#0), 
    m#0: DatatypeType
       where $Is(m#0, Tclass._module.Nat())
         && $IsAlloc(m#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(m#0), 
    o#0: DatatypeType
       where $Is(o#0, Tclass._module.Nat())
         && $IsAlloc(o#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(o#0))
   returns ($_reverifyPost: bool);
  free requires 27 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Nat(n#0)
     && $IsA#_module.Nat(m#0)
     && (_module.Nat#Equal(n#0, m#0)
       ==> $IsA#_module.Nat(m#0)
         && $IsA#_module.Nat(o#0)
         && (_module.Nat#Equal(m#0, o#0)
           ==> $IsA#_module.Nat(_module.__default.plus($LS($LZ), n#0, m#0))
             && $IsA#_module.Nat(_module.__default.plus($LS($LZ), m#0, o#0))
             && 
            _module.__default.plus#canCall(n#0, m#0)
             && _module.__default.plus#canCall(m#0, o#0)));
  ensures _module.Nat#Equal(n#0, m#0)
     ==> 
    _module.Nat#Equal(m#0, o#0)
     ==> _module.Nat#Equal(_module.__default.plus($LS($LS($LZ)), n#0, m#0), 
      _module.__default.plus($LS($LS($LZ)), m#0, o#0));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction n#0, m#0, o#0} Impl$$_module.__default.plus__id__exercise(n#0: DatatypeType, m#0: DatatypeType, o#0: DatatypeType)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;

    // AddMethodImpl: plus_id_exercise, Impl$$_module.__default.plus__id__exercise
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(369,0): initial state"} true;
    assume $IsA#_module.Nat(n#0);
    assume $IsA#_module.Nat(m#0);
    assume $IsA#_module.Nat(o#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#n0#0: DatatypeType, $ih#m0#0: DatatypeType, $ih#o0#0: DatatypeType :: 
      $Is($ih#n0#0, Tclass._module.Nat())
           && $Is($ih#m0#0, Tclass._module.Nat())
           && $Is($ih#o0#0, Tclass._module.Nat())
           && Lit(true)
           && (DtRank($ih#n0#0) < DtRank(n#0)
             || (DtRank($ih#n0#0) == DtRank(n#0)
               && (DtRank($ih#m0#0) < DtRank(m#0)
                 || (DtRank($ih#m0#0) == DtRank(m#0) && DtRank($ih#o0#0) < DtRank(o#0)))))
         ==> 
        _module.Nat#Equal($ih#n0#0, $ih#m0#0)
         ==> 
        _module.Nat#Equal($ih#m0#0, $ih#o0#0)
         ==> _module.Nat#Equal(_module.__default.plus($LS($LZ), $ih#n0#0, $ih#m0#0), 
          _module.__default.plus($LS($LZ), $ih#m0#0, $ih#o0#0)));
    $_reverifyPost := false;
}



procedure {:_induction n#0, m#0} CheckWellformed$$_module.__default.mult__0__plus(n#0: DatatypeType
       where $Is(n#0, Tclass._module.Nat())
         && $IsAlloc(n#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(n#0), 
    m#0: DatatypeType
       where $Is(m#0, Tclass._module.Nat())
         && $IsAlloc(m#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(m#0));
  free requires 28 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction n#0, m#0} Call$$_module.__default.mult__0__plus(n#0: DatatypeType
       where $Is(n#0, Tclass._module.Nat())
         && $IsAlloc(n#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(n#0), 
    m#0: DatatypeType
       where $Is(m#0, Tclass._module.Nat())
         && $IsAlloc(m#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(m#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Nat(_module.__default.mult($LS($LZ), _module.__default.plus($LS($LZ), Lit(#_module.Nat.O()), n#0), m#0))
     && $IsA#_module.Nat(_module.__default.mult($LS($LZ), n#0, m#0))
     && 
    _module.__default.plus#canCall(Lit(#_module.Nat.O()), n#0)
     && _module.__default.mult#canCall(_module.__default.plus($LS($LZ), Lit(#_module.Nat.O()), n#0), m#0)
     && _module.__default.mult#canCall(n#0, m#0);
  ensures _module.Nat#Equal(_module.__default.mult($LS($LS($LZ)), 
      _module.__default.plus($LS($LS($LZ)), Lit(#_module.Nat.O()), n#0), 
      m#0), 
    _module.__default.mult($LS($LS($LZ)), n#0, m#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction n#0, m#0} Impl$$_module.__default.mult__0__plus(n#0: DatatypeType
       where $Is(n#0, Tclass._module.Nat())
         && $IsAlloc(n#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(n#0), 
    m#0: DatatypeType
       where $Is(m#0, Tclass._module.Nat())
         && $IsAlloc(m#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(m#0))
   returns ($_reverifyPost: bool);
  free requires 28 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Nat(_module.__default.mult($LS($LZ), _module.__default.plus($LS($LZ), Lit(#_module.Nat.O()), n#0), m#0))
     && $IsA#_module.Nat(_module.__default.mult($LS($LZ), n#0, m#0))
     && 
    _module.__default.plus#canCall(Lit(#_module.Nat.O()), n#0)
     && _module.__default.mult#canCall(_module.__default.plus($LS($LZ), Lit(#_module.Nat.O()), n#0), m#0)
     && _module.__default.mult#canCall(n#0, m#0);
  ensures _module.Nat#Equal(_module.__default.mult($LS($LS($LZ)), 
      _module.__default.plus($LS($LS($LZ)), Lit(#_module.Nat.O()), n#0), 
      m#0), 
    _module.__default.mult($LS($LS($LZ)), n#0, m#0));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction n#0, m#0} Impl$$_module.__default.mult__0__plus(n#0: DatatypeType, m#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;

    // AddMethodImpl: mult_0_plus, Impl$$_module.__default.mult__0__plus
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(374,0): initial state"} true;
    assume $IsA#_module.Nat(n#0);
    assume $IsA#_module.Nat(m#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#n0#0: DatatypeType, $ih#m0#0: DatatypeType :: 
      $Is($ih#n0#0, Tclass._module.Nat())
           && $Is($ih#m0#0, Tclass._module.Nat())
           && Lit(true)
           && (DtRank($ih#n0#0) < DtRank(n#0)
             || (DtRank($ih#n0#0) == DtRank(n#0) && DtRank($ih#m0#0) < DtRank(m#0)))
         ==> _module.Nat#Equal(_module.__default.mult($LS($LZ), 
            _module.__default.plus($LS($LZ), Lit(#_module.Nat.O()), $ih#n0#0), 
            $ih#m0#0), 
          _module.__default.mult($LS($LZ), $ih#n0#0, $ih#m0#0)));
    $_reverifyPost := false;
}



procedure {:_induction n#0, m#0} CheckWellformed$$_module.__default.mult__S__1(n#0: DatatypeType
       where $Is(n#0, Tclass._module.Nat())
         && $IsAlloc(n#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(n#0), 
    m#0: DatatypeType
       where $Is(m#0, Tclass._module.Nat())
         && $IsAlloc(m#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(m#0));
  free requires 29 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction n#0, m#0} Call$$_module.__default.mult__S__1(n#0: DatatypeType
       where $Is(n#0, Tclass._module.Nat())
         && $IsAlloc(n#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(n#0), 
    m#0: DatatypeType
       where $Is(m#0, Tclass._module.Nat())
         && $IsAlloc(m#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(m#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Nat(m#0)
     && (_module.Nat#Equal(m#0, #_module.Nat.S(n#0))
       ==> $IsA#_module.Nat(_module.__default.mult($LS($LZ), 
            m#0, 
            _module.__default.plus($LS($LZ), Lit(#_module.Nat.S(Lit(#_module.Nat.O()))), n#0)))
         && $IsA#_module.Nat(_module.__default.mult($LS($LZ), m#0, m#0))
         && 
        _module.__default.plus#canCall(Lit(#_module.Nat.S(Lit(#_module.Nat.O()))), n#0)
         && _module.__default.mult#canCall(m#0, 
          _module.__default.plus($LS($LZ), Lit(#_module.Nat.S(Lit(#_module.Nat.O()))), n#0))
         && _module.__default.mult#canCall(m#0, m#0));
  ensures _module.Nat#Equal(m#0, #_module.Nat.S(n#0))
     ==> _module.Nat#Equal(_module.__default.mult($LS($LS($LZ)), 
        m#0, 
        _module.__default.plus($LS($LS($LZ)), Lit(#_module.Nat.S(Lit(#_module.Nat.O()))), n#0)), 
      _module.__default.mult($LS($LS($LZ)), m#0, m#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction n#0, m#0} Impl$$_module.__default.mult__S__1(n#0: DatatypeType
       where $Is(n#0, Tclass._module.Nat())
         && $IsAlloc(n#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(n#0), 
    m#0: DatatypeType
       where $Is(m#0, Tclass._module.Nat())
         && $IsAlloc(m#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(m#0))
   returns ($_reverifyPost: bool);
  free requires 29 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Nat(m#0)
     && (_module.Nat#Equal(m#0, #_module.Nat.S(n#0))
       ==> $IsA#_module.Nat(_module.__default.mult($LS($LZ), 
            m#0, 
            _module.__default.plus($LS($LZ), Lit(#_module.Nat.S(Lit(#_module.Nat.O()))), n#0)))
         && $IsA#_module.Nat(_module.__default.mult($LS($LZ), m#0, m#0))
         && 
        _module.__default.plus#canCall(Lit(#_module.Nat.S(Lit(#_module.Nat.O()))), n#0)
         && _module.__default.mult#canCall(m#0, 
          _module.__default.plus($LS($LZ), Lit(#_module.Nat.S(Lit(#_module.Nat.O()))), n#0))
         && _module.__default.mult#canCall(m#0, m#0));
  ensures _module.Nat#Equal(m#0, #_module.Nat.S(n#0))
     ==> _module.Nat#Equal(_module.__default.mult($LS($LS($LZ)), 
        m#0, 
        _module.__default.plus($LS($LS($LZ)), Lit(#_module.Nat.S(Lit(#_module.Nat.O()))), n#0)), 
      _module.__default.mult($LS($LS($LZ)), m#0, m#0));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction n#0, m#0} Impl$$_module.__default.mult__S__1(n#0: DatatypeType, m#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;

    // AddMethodImpl: mult_S_1, Impl$$_module.__default.mult__S__1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(381,0): initial state"} true;
    assume $IsA#_module.Nat(n#0);
    assume $IsA#_module.Nat(m#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#n0#0: DatatypeType, $ih#m0#0: DatatypeType :: 
      $Is($ih#n0#0, Tclass._module.Nat())
           && $Is($ih#m0#0, Tclass._module.Nat())
           && Lit(true)
           && (DtRank($ih#n0#0) < DtRank(n#0)
             || (DtRank($ih#n0#0) == DtRank(n#0) && DtRank($ih#m0#0) < DtRank(m#0)))
         ==> 
        _module.Nat#Equal($ih#m0#0, #_module.Nat.S($ih#n0#0))
         ==> _module.Nat#Equal(_module.__default.mult($LS($LZ), 
            $ih#m0#0, 
            _module.__default.plus($LS($LZ), Lit(#_module.Nat.S(Lit(#_module.Nat.O()))), $ih#n0#0)), 
          _module.__default.mult($LS($LZ), $ih#m0#0, $ih#m0#0)));
    $_reverifyPost := false;
}



procedure {:_induction n#0} CheckWellformed$$_module.__default.plus__1__neq__0__firsttry(n#0: DatatypeType
       where $Is(n#0, Tclass._module.Nat())
         && $IsAlloc(n#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(n#0));
  free requires 30 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction n#0} Call$$_module.__default.plus__1__neq__0__firsttry(n#0: DatatypeType
       where $Is(n#0, Tclass._module.Nat())
         && $IsAlloc(n#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(n#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Bool(_module.__default.beq__nat($LS($LZ), 
        _module.__default.plus($LS($LZ), n#0, Lit(#_module.Nat.S(Lit(#_module.Nat.O())))), 
        Lit(#_module.Nat.O())))
     && 
    _module.__default.plus#canCall(n#0, Lit(#_module.Nat.S(Lit(#_module.Nat.O()))))
     && _module.__default.beq__nat#canCall(_module.__default.plus($LS($LZ), n#0, Lit(#_module.Nat.S(Lit(#_module.Nat.O())))), 
      Lit(#_module.Nat.O()));
  ensures _module.Bool#Equal(_module.__default.beq__nat($LS($LS($LZ)), 
      _module.__default.plus($LS($LS($LZ)), n#0, Lit(#_module.Nat.S(Lit(#_module.Nat.O())))), 
      Lit(#_module.Nat.O())), 
    #_module.Bool.False());
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction n#0} Impl$$_module.__default.plus__1__neq__0__firsttry(n#0: DatatypeType
       where $Is(n#0, Tclass._module.Nat())
         && $IsAlloc(n#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(n#0))
   returns ($_reverifyPost: bool);
  free requires 30 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Bool(_module.__default.beq__nat($LS($LZ), 
        _module.__default.plus($LS($LZ), n#0, Lit(#_module.Nat.S(Lit(#_module.Nat.O())))), 
        Lit(#_module.Nat.O())))
     && 
    _module.__default.plus#canCall(n#0, Lit(#_module.Nat.S(Lit(#_module.Nat.O()))))
     && _module.__default.beq__nat#canCall(_module.__default.plus($LS($LZ), n#0, Lit(#_module.Nat.S(Lit(#_module.Nat.O())))), 
      Lit(#_module.Nat.O()));
  ensures _module.Bool#Equal(_module.__default.beq__nat($LS($LS($LZ)), 
      _module.__default.plus($LS($LS($LZ)), n#0, Lit(#_module.Nat.S(Lit(#_module.Nat.O())))), 
      Lit(#_module.Nat.O())), 
    #_module.Bool.False());
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction n#0} Impl$$_module.__default.plus__1__neq__0__firsttry(n#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;

    // AddMethodImpl: plus_1_neq_0_firsttry, Impl$$_module.__default.plus__1__neq__0__firsttry
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(389,0): initial state"} true;
    assume $IsA#_module.Nat(n#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#n0#0: DatatypeType :: 
      $Is($ih#n0#0, Tclass._module.Nat())
           && Lit(true)
           && DtRank($ih#n0#0) < DtRank(n#0)
         ==> _module.Bool#Equal(_module.__default.beq__nat($LS($LZ), 
            _module.__default.plus($LS($LZ), $ih#n0#0, Lit(#_module.Nat.S(Lit(#_module.Nat.O())))), 
            Lit(#_module.Nat.O())), 
          #_module.Bool.False()));
    $_reverifyPost := false;
}



procedure {:_induction n#0} CheckWellformed$$_module.__default.plus__1__neq__0(n#0: DatatypeType
       where $Is(n#0, Tclass._module.Nat())
         && $IsAlloc(n#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(n#0));
  free requires 31 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction n#0} Call$$_module.__default.plus__1__neq__0(n#0: DatatypeType
       where $Is(n#0, Tclass._module.Nat())
         && $IsAlloc(n#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(n#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Bool(_module.__default.beq__nat($LS($LZ), 
        _module.__default.plus($LS($LZ), n#0, Lit(#_module.Nat.S(Lit(#_module.Nat.O())))), 
        Lit(#_module.Nat.O())))
     && 
    _module.__default.plus#canCall(n#0, Lit(#_module.Nat.S(Lit(#_module.Nat.O()))))
     && _module.__default.beq__nat#canCall(_module.__default.plus($LS($LZ), n#0, Lit(#_module.Nat.S(Lit(#_module.Nat.O())))), 
      Lit(#_module.Nat.O()));
  ensures _module.Bool#Equal(_module.__default.beq__nat($LS($LS($LZ)), 
      _module.__default.plus($LS($LS($LZ)), n#0, Lit(#_module.Nat.S(Lit(#_module.Nat.O())))), 
      Lit(#_module.Nat.O())), 
    #_module.Bool.False());
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction n#0} Impl$$_module.__default.plus__1__neq__0(n#0: DatatypeType
       where $Is(n#0, Tclass._module.Nat())
         && $IsAlloc(n#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(n#0))
   returns ($_reverifyPost: bool);
  free requires 31 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Bool(_module.__default.beq__nat($LS($LZ), 
        _module.__default.plus($LS($LZ), n#0, Lit(#_module.Nat.S(Lit(#_module.Nat.O())))), 
        Lit(#_module.Nat.O())))
     && 
    _module.__default.plus#canCall(n#0, Lit(#_module.Nat.S(Lit(#_module.Nat.O()))))
     && _module.__default.beq__nat#canCall(_module.__default.plus($LS($LZ), n#0, Lit(#_module.Nat.S(Lit(#_module.Nat.O())))), 
      Lit(#_module.Nat.O()));
  ensures _module.Bool#Equal(_module.__default.beq__nat($LS($LS($LZ)), 
      _module.__default.plus($LS($LS($LZ)), n#0, Lit(#_module.Nat.S(Lit(#_module.Nat.O())))), 
      Lit(#_module.Nat.O())), 
    #_module.Bool.False());
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction n#0} Impl$$_module.__default.plus__1__neq__0(n#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;

    // AddMethodImpl: plus_1_neq_0, Impl$$_module.__default.plus__1__neq__0
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(394,0): initial state"} true;
    assume $IsA#_module.Nat(n#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#n0#0: DatatypeType :: 
      $Is($ih#n0#0, Tclass._module.Nat())
           && Lit(true)
           && DtRank($ih#n0#0) < DtRank(n#0)
         ==> _module.Bool#Equal(_module.__default.beq__nat($LS($LZ), 
            _module.__default.plus($LS($LZ), $ih#n0#0, Lit(#_module.Nat.S(Lit(#_module.Nat.O())))), 
            Lit(#_module.Nat.O())), 
          #_module.Bool.False()));
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.negb__involutive(b#0: DatatypeType
       where $Is(b#0, Tclass._module.Bool())
         && $IsAlloc(b#0, Tclass._module.Bool(), $Heap)
         && $IsA#_module.Bool(b#0));
  free requires 32 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.negb__involutive(b#0: DatatypeType
       where $Is(b#0, Tclass._module.Bool())
         && $IsAlloc(b#0, Tclass._module.Bool(), $Heap)
         && $IsA#_module.Bool(b#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Bool(_module.__default.negb(_module.__default.negb(b#0)))
     && $IsA#_module.Bool(b#0)
     && 
    _module.__default.negb#canCall(b#0)
     && _module.__default.negb#canCall(_module.__default.negb(b#0));
  ensures _module.Bool#Equal(_module.__default.negb(_module.__default.negb(b#0)), b#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.negb__involutive(b#0: DatatypeType
       where $Is(b#0, Tclass._module.Bool())
         && $IsAlloc(b#0, Tclass._module.Bool(), $Heap)
         && $IsA#_module.Bool(b#0))
   returns ($_reverifyPost: bool);
  free requires 32 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Bool(_module.__default.negb(_module.__default.negb(b#0)))
     && $IsA#_module.Bool(b#0)
     && 
    _module.__default.negb#canCall(b#0)
     && _module.__default.negb#canCall(_module.__default.negb(b#0));
  ensures _module.Bool#Equal(_module.__default.negb(_module.__default.negb(b#0)), b#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.negb__involutive(b#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: negb_involutive, Impl$$_module.__default.negb__involutive
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(399,0): initial state"} true;
    $_reverifyPost := false;
}



procedure {:_induction n#0} CheckWellformed$$_module.__default.zero__nbeq__plus__1(n#0: DatatypeType
       where $Is(n#0, Tclass._module.Nat())
         && $IsAlloc(n#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(n#0));
  free requires 33 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction n#0} Call$$_module.__default.zero__nbeq__plus__1(n#0: DatatypeType
       where $Is(n#0, Tclass._module.Nat())
         && $IsAlloc(n#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(n#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Bool(_module.__default.beq__nat($LS($LZ), 
        Lit(#_module.Nat.O()), 
        _module.__default.plus($LS($LZ), n#0, Lit(#_module.Nat.S(Lit(#_module.Nat.O()))))))
     && 
    _module.__default.plus#canCall(n#0, Lit(#_module.Nat.S(Lit(#_module.Nat.O()))))
     && _module.__default.beq__nat#canCall(Lit(#_module.Nat.O()), 
      _module.__default.plus($LS($LZ), n#0, Lit(#_module.Nat.S(Lit(#_module.Nat.O())))));
  ensures _module.Bool#Equal(_module.__default.beq__nat($LS($LS($LZ)), 
      Lit(#_module.Nat.O()), 
      _module.__default.plus($LS($LS($LZ)), n#0, Lit(#_module.Nat.S(Lit(#_module.Nat.O()))))), 
    #_module.Bool.False());
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction n#0} Impl$$_module.__default.zero__nbeq__plus__1(n#0: DatatypeType
       where $Is(n#0, Tclass._module.Nat())
         && $IsAlloc(n#0, Tclass._module.Nat(), $Heap)
         && $IsA#_module.Nat(n#0))
   returns ($_reverifyPost: bool);
  free requires 33 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Bool(_module.__default.beq__nat($LS($LZ), 
        Lit(#_module.Nat.O()), 
        _module.__default.plus($LS($LZ), n#0, Lit(#_module.Nat.S(Lit(#_module.Nat.O()))))))
     && 
    _module.__default.plus#canCall(n#0, Lit(#_module.Nat.S(Lit(#_module.Nat.O()))))
     && _module.__default.beq__nat#canCall(Lit(#_module.Nat.O()), 
      _module.__default.plus($LS($LZ), n#0, Lit(#_module.Nat.S(Lit(#_module.Nat.O())))));
  ensures _module.Bool#Equal(_module.__default.beq__nat($LS($LS($LZ)), 
      Lit(#_module.Nat.O()), 
      _module.__default.plus($LS($LS($LZ)), n#0, Lit(#_module.Nat.S(Lit(#_module.Nat.O()))))), 
    #_module.Bool.False());
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction n#0} Impl$$_module.__default.zero__nbeq__plus__1(n#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;

    // AddMethodImpl: zero_nbeq_plus_1, Impl$$_module.__default.zero__nbeq__plus__1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(406,0): initial state"} true;
    assume $IsA#_module.Nat(n#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#n0#0: DatatypeType :: 
      $Is($ih#n0#0, Tclass._module.Nat())
           && Lit(true)
           && DtRank($ih#n0#0) < DtRank(n#0)
         ==> _module.Bool#Equal(_module.__default.beq__nat($LS($LZ), 
            Lit(#_module.Nat.O()), 
            _module.__default.plus($LS($LZ), $ih#n0#0, Lit(#_module.Nat.S(Lit(#_module.Nat.O()))))), 
          #_module.Bool.False()));
    $_reverifyPost := false;
}



// function declaration for _module._default.f
function _module.__default.f(x#0: DatatypeType) : DatatypeType;

function _module.__default.f#canCall(x#0: DatatypeType) : bool;

// consequence axiom for _module.__default.f
axiom 34 <= $FunctionContextHeight
   ==> (forall x#0: DatatypeType :: 
    { _module.__default.f(x#0) } 
    _module.__default.f#canCall(x#0)
         || (34 != $FunctionContextHeight && $Is(x#0, Tclass._module.Bool()))
       ==> $Is(_module.__default.f(x#0), Tclass._module.Bool()));

function _module.__default.f#requires(DatatypeType) : bool;

// #requires axiom for _module.__default.f
axiom (forall x#0: DatatypeType :: 
  { _module.__default.f#requires(x#0) } 
  $Is(x#0, Tclass._module.Bool()) ==> _module.__default.f#requires(x#0) == true);

procedure CheckWellformed$$_module.__default.f(x#0: DatatypeType where $Is(x#0, Tclass._module.Bool()));
  free requires 34 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure CheckWellformed$$_module.__default.identity__fn__applied__twice(b#0: DatatypeType
       where $Is(b#0, Tclass._module.Bool())
         && $IsAlloc(b#0, Tclass._module.Bool(), $Heap)
         && $IsA#_module.Bool(b#0));
  free requires 35 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.identity__fn__applied__twice(b#0: DatatypeType
       where $Is(b#0, Tclass._module.Bool())
         && $IsAlloc(b#0, Tclass._module.Bool(), $Heap)
         && $IsA#_module.Bool(b#0));
  // user-defined preconditions
  requires (forall x#1: DatatypeType :: 
    { _module.__default.f(x#1) } 
    $Is(x#1, Tclass._module.Bool())
       ==> _module.Bool#Equal(_module.__default.f(x#1), x#1));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Bool(_module.__default.f(_module.__default.f(b#0)))
     && $IsA#_module.Bool(b#0)
     && 
    _module.__default.f#canCall(b#0)
     && _module.__default.f#canCall(_module.__default.f(b#0));
  ensures _module.Bool#Equal(_module.__default.f(_module.__default.f(b#0)), b#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.identity__fn__applied__twice(b#0: DatatypeType
       where $Is(b#0, Tclass._module.Bool())
         && $IsAlloc(b#0, Tclass._module.Bool(), $Heap)
         && $IsA#_module.Bool(b#0))
   returns ($_reverifyPost: bool);
  free requires 35 == $FunctionContextHeight;
  // user-defined preconditions
  requires (forall x#1: DatatypeType :: 
    { _module.__default.f(x#1) } 
    $Is(x#1, Tclass._module.Bool())
       ==> _module.Bool#Equal(_module.__default.f(x#1), x#1));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Bool(_module.__default.f(_module.__default.f(b#0)))
     && $IsA#_module.Bool(b#0)
     && 
    _module.__default.f#canCall(b#0)
     && _module.__default.f#canCall(_module.__default.f(b#0));
  ensures _module.Bool#Equal(_module.__default.f(_module.__default.f(b#0)), b#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.identity__fn__applied__twice(b#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: identity_fn_applied_twice, Impl$$_module.__default.identity__fn__applied__twice
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(425,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.negation__fn__applied__twice(b#0: DatatypeType
       where $Is(b#0, Tclass._module.Bool())
         && $IsAlloc(b#0, Tclass._module.Bool(), $Heap)
         && $IsA#_module.Bool(b#0));
  free requires 36 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.negation__fn__applied__twice(b#0: DatatypeType
       where $Is(b#0, Tclass._module.Bool())
         && $IsAlloc(b#0, Tclass._module.Bool(), $Heap)
         && $IsA#_module.Bool(b#0));
  // user-defined preconditions
  requires (forall x#1: DatatypeType :: 
    { _module.__default.negb(x#1) } { _module.__default.f(x#1) } 
    $Is(x#1, Tclass._module.Bool())
       ==> _module.Bool#Equal(_module.__default.f(x#1), _module.__default.negb(x#1)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Bool(_module.__default.f(_module.__default.f(b#0)))
     && $IsA#_module.Bool(b#0)
     && 
    _module.__default.f#canCall(b#0)
     && _module.__default.f#canCall(_module.__default.f(b#0));
  ensures _module.Bool#Equal(_module.__default.f(_module.__default.f(b#0)), b#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.negation__fn__applied__twice(b#0: DatatypeType
       where $Is(b#0, Tclass._module.Bool())
         && $IsAlloc(b#0, Tclass._module.Bool(), $Heap)
         && $IsA#_module.Bool(b#0))
   returns ($_reverifyPost: bool);
  free requires 36 == $FunctionContextHeight;
  // user-defined preconditions
  requires (forall x#1: DatatypeType :: 
    { _module.__default.negb(x#1) } { _module.__default.f(x#1) } 
    $Is(x#1, Tclass._module.Bool())
       ==> _module.Bool#Equal(_module.__default.f(x#1), _module.__default.negb(x#1)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Bool(_module.__default.f(_module.__default.f(b#0)))
     && $IsA#_module.Bool(b#0)
     && 
    _module.__default.f#canCall(b#0)
     && _module.__default.f#canCall(_module.__default.f(b#0));
  ensures _module.Bool#Equal(_module.__default.f(_module.__default.f(b#0)), b#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.negation__fn__applied__twice(b#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: negation_fn_applied_twice, Impl$$_module.__default.negation__fn__applied__twice
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(432,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.andb__true(b#0: DatatypeType
       where $Is(b#0, Tclass._module.Bool())
         && $IsAlloc(b#0, Tclass._module.Bool(), $Heap)
         && $IsA#_module.Bool(b#0));
  free requires 37 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.andb__true(b#0: DatatypeType
       where $Is(b#0, Tclass._module.Bool())
         && $IsAlloc(b#0, Tclass._module.Bool(), $Heap)
         && $IsA#_module.Bool(b#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Bool(_module.__default.andb(Lit(#_module.Bool.True()), b#0))
     && $IsA#_module.Bool(b#0)
     && _module.__default.andb#canCall(Lit(#_module.Bool.True()), b#0);
  ensures _module.Bool#Equal(_module.__default.andb(Lit(#_module.Bool.True()), b#0), b#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.andb__true(b#0: DatatypeType
       where $Is(b#0, Tclass._module.Bool())
         && $IsAlloc(b#0, Tclass._module.Bool(), $Heap)
         && $IsA#_module.Bool(b#0))
   returns ($_reverifyPost: bool);
  free requires 37 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Bool(_module.__default.andb(Lit(#_module.Bool.True()), b#0))
     && $IsA#_module.Bool(b#0)
     && _module.__default.andb#canCall(Lit(#_module.Bool.True()), b#0);
  ensures _module.Bool#Equal(_module.__default.andb(Lit(#_module.Bool.True()), b#0), b#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.andb__true(b#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: andb_true, Impl$$_module.__default.andb__true
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(439,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.orb__false(b#0: DatatypeType
       where $Is(b#0, Tclass._module.Bool())
         && $IsAlloc(b#0, Tclass._module.Bool(), $Heap)
         && $IsA#_module.Bool(b#0));
  free requires 38 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.orb__false(b#0: DatatypeType
       where $Is(b#0, Tclass._module.Bool())
         && $IsAlloc(b#0, Tclass._module.Bool(), $Heap)
         && $IsA#_module.Bool(b#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Bool(_module.__default.orb(Lit(#_module.Bool.False()), b#0))
     && $IsA#_module.Bool(b#0)
     && _module.__default.orb#canCall(Lit(#_module.Bool.False()), b#0);
  ensures _module.Bool#Equal(_module.__default.orb(Lit(#_module.Bool.False()), b#0), b#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.orb__false(b#0: DatatypeType
       where $Is(b#0, Tclass._module.Bool())
         && $IsAlloc(b#0, Tclass._module.Bool(), $Heap)
         && $IsA#_module.Bool(b#0))
   returns ($_reverifyPost: bool);
  free requires 38 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Bool(_module.__default.orb(Lit(#_module.Bool.False()), b#0))
     && $IsA#_module.Bool(b#0)
     && _module.__default.orb#canCall(Lit(#_module.Bool.False()), b#0);
  ensures _module.Bool#Equal(_module.__default.orb(Lit(#_module.Bool.False()), b#0), b#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.orb__false(b#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: orb_false, Impl$$_module.__default.orb__false
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(444,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.andb__eq__orb(b#0: DatatypeType
       where $Is(b#0, Tclass._module.Bool())
         && $IsAlloc(b#0, Tclass._module.Bool(), $Heap)
         && $IsA#_module.Bool(b#0), 
    c#0: DatatypeType
       where $Is(c#0, Tclass._module.Bool())
         && $IsAlloc(c#0, Tclass._module.Bool(), $Heap)
         && $IsA#_module.Bool(c#0));
  free requires 39 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.andb__eq__orb(b#0: DatatypeType
       where $Is(b#0, Tclass._module.Bool())
         && $IsAlloc(b#0, Tclass._module.Bool(), $Heap)
         && $IsA#_module.Bool(b#0), 
    c#0: DatatypeType
       where $Is(c#0, Tclass._module.Bool())
         && $IsAlloc(c#0, Tclass._module.Bool(), $Heap)
         && $IsA#_module.Bool(c#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Bool(_module.__default.andb(b#0, c#0))
     && $IsA#_module.Bool(_module.__default.orb(b#0, c#0))
     && 
    _module.__default.andb#canCall(b#0, c#0)
     && _module.__default.orb#canCall(b#0, c#0)
     && (_module.Bool#Equal(_module.__default.andb(b#0, c#0), _module.__default.orb(b#0, c#0))
       ==> $IsA#_module.Bool(b#0) && $IsA#_module.Bool(c#0));
  ensures _module.Bool#Equal(_module.__default.andb(b#0, c#0), _module.__default.orb(b#0, c#0))
     ==> _module.Bool#Equal(b#0, c#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.andb__eq__orb(b#0: DatatypeType
       where $Is(b#0, Tclass._module.Bool())
         && $IsAlloc(b#0, Tclass._module.Bool(), $Heap)
         && $IsA#_module.Bool(b#0), 
    c#0: DatatypeType
       where $Is(c#0, Tclass._module.Bool())
         && $IsAlloc(c#0, Tclass._module.Bool(), $Heap)
         && $IsA#_module.Bool(c#0))
   returns ($_reverifyPost: bool);
  free requires 39 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Bool(_module.__default.andb(b#0, c#0))
     && $IsA#_module.Bool(_module.__default.orb(b#0, c#0))
     && 
    _module.__default.andb#canCall(b#0, c#0)
     && _module.__default.orb#canCall(b#0, c#0)
     && (_module.Bool#Equal(_module.__default.andb(b#0, c#0), _module.__default.orb(b#0, c#0))
       ==> $IsA#_module.Bool(b#0) && $IsA#_module.Bool(c#0));
  ensures _module.Bool#Equal(_module.__default.andb(b#0, c#0), _module.__default.orb(b#0, c#0))
     ==> _module.Bool#Equal(b#0, c#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.andb__eq__orb(b#0: DatatypeType, c#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: andb_eq_orb, Impl$$_module.__default.andb__eq__orb
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(449,0): initial state"} true;
    $_reverifyPost := false;
}



// function declaration for _module._default.increment
function _module.__default.increment($ly: LayerType, b#0: DatatypeType) : DatatypeType;

function _module.__default.increment#canCall(b#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, b#0: DatatypeType :: 
  { _module.__default.increment($LS($ly), b#0) } 
  _module.__default.increment($LS($ly), b#0)
     == _module.__default.increment($ly, b#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, b#0: DatatypeType :: 
  { _module.__default.increment(AsFuelBottom($ly), b#0) } 
  _module.__default.increment($ly, b#0) == _module.__default.increment($LZ, b#0));

// consequence axiom for _module.__default.increment
axiom 40 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, b#0: DatatypeType :: 
    { _module.__default.increment($ly, b#0) } 
    _module.__default.increment#canCall(b#0)
         || (40 != $FunctionContextHeight && $Is(b#0, Tclass._module.bin()))
       ==> $Is(_module.__default.increment($ly, b#0), Tclass._module.bin()));

function _module.__default.increment#requires(LayerType, DatatypeType) : bool;

// #requires axiom for _module.__default.increment
axiom (forall $ly: LayerType, b#0: DatatypeType :: 
  { _module.__default.increment#requires($ly, b#0) } 
  $Is(b#0, Tclass._module.bin())
     ==> _module.__default.increment#requires($ly, b#0) == true);

// definition axiom for _module.__default.increment (revealed)
axiom 40 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, b#0: DatatypeType :: 
    { _module.__default.increment($LS($ly), b#0) } 
    _module.__default.increment#canCall(b#0)
         || (40 != $FunctionContextHeight && $Is(b#0, Tclass._module.bin()))
       ==> (!_module.bin.Zero_q(b#0)
           ==> 
          !_module.bin.Twice_q(b#0)
           ==> (var b'#3 := _module.bin._h2(b#0); _module.__default.increment#canCall(b'#3)))
         && _module.__default.increment($LS($ly), b#0)
           == (if _module.bin.Zero_q(b#0)
             then #_module.bin.TwicePlusOne(Lit(#_module.bin.Zero()))
             else (if _module.bin.Twice_q(b#0)
               then (var b'#0 := _module.bin._h1(b#0); #_module.bin.TwicePlusOne(b'#0))
               else (var b'#1 := _module.bin._h2(b#0); 
                #_module.bin.Twice(_module.__default.increment($ly, b'#1))))));

// definition axiom for _module.__default.increment for all literals (revealed)
axiom 40 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, b#0: DatatypeType :: 
    {:weight 3} { _module.__default.increment($LS($ly), Lit(b#0)) } 
    _module.__default.increment#canCall(Lit(b#0))
         || (40 != $FunctionContextHeight && $Is(b#0, Tclass._module.bin()))
       ==> (!Lit(_module.bin.Zero_q(Lit(b#0)))
           ==> 
          !Lit(_module.bin.Twice_q(Lit(b#0)))
           ==> (var b'#7 := Lit(_module.bin._h2(Lit(b#0))); 
            _module.__default.increment#canCall(b'#7)))
         && _module.__default.increment($LS($ly), Lit(b#0))
           == (if _module.bin.Zero_q(Lit(b#0))
             then #_module.bin.TwicePlusOne(Lit(#_module.bin.Zero()))
             else (if _module.bin.Twice_q(Lit(b#0))
               then (var b'#4 := Lit(_module.bin._h1(Lit(b#0))); 
                Lit(#_module.bin.TwicePlusOne(b'#4)))
               else (var b'#5 := Lit(_module.bin._h2(Lit(b#0))); 
                Lit(#_module.bin.Twice(Lit(_module.__default.increment($LS($ly), b'#5))))))));

procedure CheckWellformed$$_module.__default.increment(b#0: DatatypeType where $Is(b#0, Tclass._module.bin()));
  free requires 40 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.increment(b#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#1#0: DatatypeType;
  var b'#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var ##b#0: DatatypeType;
  var _mcc#0#0: DatatypeType;
  var b'#Z#1: DatatypeType;
  var let#1#0#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function increment
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(456,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.increment($LS($LZ), b#0), Tclass._module.bin());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (b#0 == #_module.bin.Zero())
        {
            assume _module.__default.increment($LS($LZ), b#0)
               == Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.Zero())));
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.increment($LS($LZ), b#0), Tclass._module.bin());
        }
        else if (b#0 == #_module.bin.Twice(_mcc#0#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.bin());
            havoc b'#Z#1;
            assume $Is(b'#Z#1, Tclass._module.bin());
            assume let#1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#1#0#0, Tclass._module.bin());
            assume b'#Z#1 == let#1#0#0;
            assume _module.__default.increment($LS($LZ), b#0) == #_module.bin.TwicePlusOne(b'#Z#1);
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.increment($LS($LZ), b#0), Tclass._module.bin());
        }
        else if (b#0 == #_module.bin.TwicePlusOne(_mcc#1#0))
        {
            assume $Is(_mcc#1#0, Tclass._module.bin());
            havoc b'#Z#0;
            assume $Is(b'#Z#0, Tclass._module.bin());
            assume let#0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.bin());
            assume b'#Z#0 == let#0#0#0;
            ##b#0 := b'#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#0, Tclass._module.bin(), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(##b#0) < DtRank(b#0);
            assume _module.__default.increment#canCall(b'#Z#0);
            assume _module.__default.increment($LS($LZ), b#0)
               == #_module.bin.Twice(_module.__default.increment($LS($LZ), b'#Z#0));
            assume _module.__default.increment#canCall(b'#Z#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.increment($LS($LZ), b#0), Tclass._module.bin());
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
    }
}



// function declaration for _module._default.BinToUnary
function _module.__default.BinToUnary($ly: LayerType, b#0: DatatypeType) : DatatypeType;

function _module.__default.BinToUnary#canCall(b#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, b#0: DatatypeType :: 
  { _module.__default.BinToUnary($LS($ly), b#0) } 
  _module.__default.BinToUnary($LS($ly), b#0)
     == _module.__default.BinToUnary($ly, b#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, b#0: DatatypeType :: 
  { _module.__default.BinToUnary(AsFuelBottom($ly), b#0) } 
  _module.__default.BinToUnary($ly, b#0) == _module.__default.BinToUnary($LZ, b#0));

// consequence axiom for _module.__default.BinToUnary
axiom 41 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, b#0: DatatypeType :: 
    { _module.__default.BinToUnary($ly, b#0) } 
    _module.__default.BinToUnary#canCall(b#0)
         || (41 != $FunctionContextHeight && $Is(b#0, Tclass._module.bin()))
       ==> $Is(_module.__default.BinToUnary($ly, b#0), Tclass._module.Nat()));

function _module.__default.BinToUnary#requires(LayerType, DatatypeType) : bool;

// #requires axiom for _module.__default.BinToUnary
axiom (forall $ly: LayerType, b#0: DatatypeType :: 
  { _module.__default.BinToUnary#requires($ly, b#0) } 
  $Is(b#0, Tclass._module.bin())
     ==> _module.__default.BinToUnary#requires($ly, b#0) == true);

// definition axiom for _module.__default.BinToUnary (revealed)
axiom 41 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, b#0: DatatypeType :: 
    { _module.__default.BinToUnary($LS($ly), b#0) } 
    _module.__default.BinToUnary#canCall(b#0)
         || (41 != $FunctionContextHeight && $Is(b#0, Tclass._module.bin()))
       ==> (!_module.bin.Zero_q(b#0)
           ==> (_module.bin.Twice_q(b#0)
               ==> (var b'#2 := _module.bin._h1(b#0); 
                _module.__default.BinToUnary#canCall(b'#2)
                   && (var t#2 := _module.__default.BinToUnary($ly, b'#2); 
                    _module.__default.plus#canCall(t#2, t#2))))
             && (!_module.bin.Twice_q(b#0)
               ==> (var b'#3 := _module.bin._h2(b#0); 
                _module.__default.BinToUnary#canCall(b'#3)
                   && (var t#3 := _module.__default.BinToUnary($ly, b'#3); 
                    _module.__default.plus#canCall(t#3, Lit(#_module.Nat.S(Lit(#_module.Nat.O()))))
                       && _module.__default.plus#canCall(t#3, 
                        _module.__default.plus($LS($LZ), t#3, Lit(#_module.Nat.S(Lit(#_module.Nat.O())))))))))
         && _module.__default.BinToUnary($LS($ly), b#0)
           == (if _module.bin.Zero_q(b#0)
             then #_module.Nat.O()
             else (if _module.bin.Twice_q(b#0)
               then (var b'#0 := _module.bin._h1(b#0); 
                (var t#0 := _module.__default.BinToUnary($ly, b'#0); 
                  _module.__default.plus($LS($LZ), t#0, t#0)))
               else (var b'#1 := _module.bin._h2(b#0); 
                (var t#1 := _module.__default.BinToUnary($ly, b'#1); 
                  _module.__default.plus($LS($LZ), 
                    t#1, 
                    _module.__default.plus($LS($LZ), t#1, Lit(#_module.Nat.S(Lit(#_module.Nat.O()))))))))));

// definition axiom for _module.__default.BinToUnary for all literals (revealed)
axiom 41 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, b#0: DatatypeType :: 
    {:weight 3} { _module.__default.BinToUnary($LS($ly), Lit(b#0)) } 
    _module.__default.BinToUnary#canCall(Lit(b#0))
         || (41 != $FunctionContextHeight && $Is(b#0, Tclass._module.bin()))
       ==> (!Lit(_module.bin.Zero_q(Lit(b#0)))
           ==> (Lit(_module.bin.Twice_q(Lit(b#0)))
               ==> (var b'#6 := Lit(_module.bin._h1(Lit(b#0))); 
                _module.__default.BinToUnary#canCall(b'#6)
                   && (var t#6 := _module.__default.BinToUnary($LS($ly), b'#6); 
                    _module.__default.plus#canCall(t#6, t#6))))
             && (!Lit(_module.bin.Twice_q(Lit(b#0)))
               ==> (var b'#7 := Lit(_module.bin._h2(Lit(b#0))); 
                _module.__default.BinToUnary#canCall(b'#7)
                   && (var t#7 := _module.__default.BinToUnary($LS($ly), b'#7); 
                    _module.__default.plus#canCall(t#7, Lit(#_module.Nat.S(Lit(#_module.Nat.O()))))
                       && _module.__default.plus#canCall(t#7, 
                        _module.__default.plus($LS($LZ), t#7, Lit(#_module.Nat.S(Lit(#_module.Nat.O())))))))))
         && _module.__default.BinToUnary($LS($ly), Lit(b#0))
           == (if _module.bin.Zero_q(Lit(b#0))
             then #_module.Nat.O()
             else (if _module.bin.Twice_q(Lit(b#0))
               then (var b'#4 := Lit(_module.bin._h1(Lit(b#0))); 
                (var t#4 := Lit(_module.__default.BinToUnary($LS($ly), b'#4)); 
                  Lit(_module.__default.plus($LS($LZ), t#4, t#4))))
               else (var b'#5 := Lit(_module.bin._h2(Lit(b#0))); 
                (var t#5 := Lit(_module.__default.BinToUnary($LS($ly), b'#5)); 
                  Lit(_module.__default.plus($LS($LZ), 
                      t#5, 
                      Lit(_module.__default.plus($LS($LZ), t#5, Lit(#_module.Nat.S(Lit(#_module.Nat.O()))))))))))));

procedure CheckWellformed$$_module.__default.BinToUnary(b#0: DatatypeType where $Is(b#0, Tclass._module.bin()));
  free requires 41 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.BinToUnary(b#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#1#0: DatatypeType;
  var b'#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var t#Z#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var ##b#0: DatatypeType;
  var ##n#0: DatatypeType;
  var ##m#0: DatatypeType;
  var ##n#1: DatatypeType;
  var ##m#1: DatatypeType;
  var _mcc#0#0: DatatypeType;
  var b'#Z#1: DatatypeType;
  var let#2#0#0: DatatypeType;
  var t#Z#1: DatatypeType;
  var let#3#0#0: DatatypeType;
  var ##b#1: DatatypeType;
  var ##n#2: DatatypeType;
  var ##m#2: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;
  var b$reqreads#2: bool;
  var b$reqreads#3: bool;
  var b$reqreads#4: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;
    b$reqreads#3 := true;
    b$reqreads#4 := true;

    // AddWellformednessCheck for function BinToUnary
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(464,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.BinToUnary($LS($LZ), b#0), Tclass._module.Nat());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (b#0 == #_module.bin.Zero())
        {
            assume _module.__default.BinToUnary($LS($LZ), b#0) == Lit(#_module.Nat.O());
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.BinToUnary($LS($LZ), b#0), Tclass._module.Nat());
        }
        else if (b#0 == #_module.bin.Twice(_mcc#0#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.bin());
            havoc b'#Z#1;
            assume $Is(b'#Z#1, Tclass._module.bin());
            assume let#2#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#2#0#0, Tclass._module.bin());
            assume b'#Z#1 == let#2#0#0;
            havoc t#Z#1;
            assume $Is(t#Z#1, Tclass._module.Nat());
            ##b#1 := b'#Z#1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#1, Tclass._module.bin(), $Heap);
            b$reqreads#3 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(##b#1) < DtRank(b#0);
            assume _module.__default.BinToUnary#canCall(b'#Z#1);
            assume let#3#0#0 == _module.__default.BinToUnary($LS($LZ), b'#Z#1);
            assume _module.__default.BinToUnary#canCall(b'#Z#1);
            // CheckWellformedWithResult: any expression
            assume $Is(let#3#0#0, Tclass._module.Nat());
            assume t#Z#1 == let#3#0#0;
            ##n#2 := t#Z#1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#2, Tclass._module.Nat(), $Heap);
            ##m#2 := t#Z#1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#2, Tclass._module.Nat(), $Heap);
            b$reqreads#4 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.plus#canCall(t#Z#1, t#Z#1);
            assume _module.__default.BinToUnary($LS($LZ), b#0)
               == _module.__default.plus($LS($LZ), t#Z#1, t#Z#1);
            assume _module.__default.plus#canCall(t#Z#1, t#Z#1);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.BinToUnary($LS($LZ), b#0), Tclass._module.Nat());
        }
        else if (b#0 == #_module.bin.TwicePlusOne(_mcc#1#0))
        {
            assume $Is(_mcc#1#0, Tclass._module.bin());
            havoc b'#Z#0;
            assume $Is(b'#Z#0, Tclass._module.bin());
            assume let#0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.bin());
            assume b'#Z#0 == let#0#0#0;
            havoc t#Z#0;
            assume $Is(t#Z#0, Tclass._module.Nat());
            ##b#0 := b'#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#0, Tclass._module.bin(), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(##b#0) < DtRank(b#0);
            assume _module.__default.BinToUnary#canCall(b'#Z#0);
            assume let#1#0#0 == _module.__default.BinToUnary($LS($LZ), b'#Z#0);
            assume _module.__default.BinToUnary#canCall(b'#Z#0);
            // CheckWellformedWithResult: any expression
            assume $Is(let#1#0#0, Tclass._module.Nat());
            assume t#Z#0 == let#1#0#0;
            ##n#0 := t#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0, Tclass._module.Nat(), $Heap);
            ##m#0 := Lit(#_module.Nat.S(Lit(#_module.Nat.O())));
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#0, Tclass._module.Nat(), $Heap);
            b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.plus#canCall(t#Z#0, Lit(#_module.Nat.S(Lit(#_module.Nat.O()))));
            ##n#1 := t#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#1, Tclass._module.Nat(), $Heap);
            ##m#1 := _module.__default.plus($LS($LZ), t#Z#0, Lit(#_module.Nat.S(Lit(#_module.Nat.O()))));
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#1, Tclass._module.Nat(), $Heap);
            b$reqreads#2 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.plus#canCall(t#Z#0, 
              _module.__default.plus($LS($LZ), t#Z#0, Lit(#_module.Nat.S(Lit(#_module.Nat.O())))));
            assume _module.__default.BinToUnary($LS($LZ), b#0)
               == _module.__default.plus($LS($LZ), 
                t#Z#0, 
                _module.__default.plus($LS($LZ), t#Z#0, Lit(#_module.Nat.S(Lit(#_module.Nat.O())))));
            assume _module.__default.plus#canCall(t#Z#0, Lit(#_module.Nat.S(Lit(#_module.Nat.O()))))
               && _module.__default.plus#canCall(t#Z#0, 
                _module.__default.plus($LS($LZ), t#Z#0, Lit(#_module.Nat.S(Lit(#_module.Nat.O())))));
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.BinToUnary($LS($LZ), b#0), Tclass._module.Nat());
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
        assert b$reqreads#1;
        assert b$reqreads#2;
        assert b$reqreads#3;
        assert b$reqreads#4;
    }
}



procedure CheckWellformed$$_module.__default.test__bin();
  free requires 55 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.test__bin();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.test__bin() returns ($_reverifyPost: bool);
  free requires 55 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.test__bin() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var n6#0: DatatypeType
     where $Is(n6#0, Tclass._module.Nat()) && $IsAlloc(n6#0, Tclass._module.Nat(), $Heap);
  var n13#0: DatatypeType
     where $Is(n13#0, Tclass._module.Nat()) && $IsAlloc(n13#0, Tclass._module.Nat(), $Heap);
  var ##b#0: DatatypeType;
  var ##b#1: DatatypeType;

    // AddMethodImpl: test_bin, Impl$$_module.__default.test__bin
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(477,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(478,10)
    assume true;
    assume true;
    n6#0 := Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.O())))))))))))));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(478,31)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(479,11)
    assume true;
    assume true;
    n13#0 := #_module.Nat.S(#_module.Nat.S(#_module.Nat.S(#_module.Nat.S(#_module.Nat.S(#_module.Nat.S(#_module.Nat.S(n6#0)))))));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(479,36)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(480,3)
    ##b#0 := Lit(#_module.bin.Twice(Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.Zero())))))));
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#0, Tclass._module.bin(), $Heap);
    assume _module.__default.BinToUnary#canCall(Lit(#_module.bin.Twice(Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.Zero()))))))));
    assume $IsA#_module.Nat(Lit(_module.__default.BinToUnary($LS($LZ), 
            Lit(#_module.bin.Twice(Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.Zero()))))))))))
       && $IsA#_module.Nat(n6#0)
       && _module.__default.BinToUnary#canCall(Lit(#_module.bin.Twice(Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.Zero()))))))));
    assert {:subsumption 0} _module.Nat#Equal(_module.__default.BinToUnary($LS($LS($LZ)), 
        Lit(#_module.bin.Twice(Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.Zero())))))))), 
      n6#0);
    assume _module.Nat#Equal(_module.__default.BinToUnary($LS($LZ), 
        Lit(#_module.bin.Twice(Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.Zero())))))))), 
      n6#0);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(481,3)
    ##b#1 := Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.Twice(Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.Zero())))))))));
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#1, Tclass._module.bin(), $Heap);
    assume _module.__default.BinToUnary#canCall(Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.Twice(Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.Zero()))))))))));
    assume $IsA#_module.Nat(Lit(_module.__default.BinToUnary($LS($LZ), 
            Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.Twice(Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.Zero()))))))))))))
       && $IsA#_module.Nat(n13#0)
       && _module.__default.BinToUnary#canCall(Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.Twice(Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.Zero()))))))))));
    assert {:subsumption 0} _module.Nat#Equal(_module.__default.BinToUnary($LS($LS($LZ)), 
        Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.Twice(Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.Zero())))))))))), 
      n13#0);
    assume _module.Nat#Equal(_module.__default.BinToUnary($LS($LZ), 
        Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.Twice(Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.Zero())))))))))), 
      n13#0);
}



procedure CheckWellformed$$_module.__default.test__increment();
  free requires 56 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.test__increment();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.test__increment() returns ($_reverifyPost: bool);
  free requires 56 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.test__increment() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b13#0: DatatypeType
     where $Is(b13#0, Tclass._module.bin()) && $IsAlloc(b13#0, Tclass._module.bin(), $Heap);
  var n13#0: DatatypeType
     where $Is(n13#0, Tclass._module.Nat()) && $IsAlloc(n13#0, Tclass._module.Nat(), $Heap);
  var n14#0: DatatypeType
     where $Is(n14#0, Tclass._module.Nat()) && $IsAlloc(n14#0, Tclass._module.Nat(), $Heap);
  var ##b#0: DatatypeType;
  var ##b#1: DatatypeType;
  var ##b#2: DatatypeType;
  var ##b#3: DatatypeType;
  var ##b#4: DatatypeType;
  var ##n#0: DatatypeType;
  var ##m#0: DatatypeType;

    // AddMethodImpl: test_increment, Impl$$_module.__default.test__increment
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(485,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(486,11)
    assume true;
    assume true;
    b13#0 := Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.Twice(Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.Zero())))))))));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(486,66)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(487,11)
    assume true;
    assume true;
    n13#0 := Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.S(Lit(#_module.Nat.O())))))))))))))))))))))))))));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(487,53)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(488,11)
    assume true;
    assume true;
    n14#0 := #_module.Nat.S(n13#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(488,19)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(490,3)
    ##b#0 := Lit(#_module.bin.Twice(Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.Zero())))))));
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#0, Tclass._module.bin(), $Heap);
    assume _module.__default.increment#canCall(Lit(#_module.bin.Twice(Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.Zero()))))))));
    assume $IsA#_module.bin(Lit(_module.__default.increment($LS($LZ), 
            Lit(#_module.bin.Twice(Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.Zero()))))))))))
       && _module.__default.increment#canCall(Lit(#_module.bin.Twice(Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.Zero()))))))));
    assert {:subsumption 0} _module.bin#Equal(_module.__default.increment($LS($LS($LZ)), 
        Lit(#_module.bin.Twice(Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.Zero())))))))), 
      #_module.bin.TwicePlusOne(Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.Zero())))))));
    assume _module.bin#Equal(_module.__default.increment($LS($LZ), 
        Lit(#_module.bin.Twice(Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.Zero())))))))), 
      #_module.bin.TwicePlusOne(Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.Zero())))))));
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(491,3)
    ##b#1 := b13#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#1, Tclass._module.bin(), $Heap);
    assume _module.__default.increment#canCall(b13#0);
    assume $IsA#_module.bin(_module.__default.increment($LS($LZ), b13#0))
       && _module.__default.increment#canCall(b13#0);
    assert {:subsumption 0} _module.bin#Equal(_module.__default.increment($LS($LS($LZ)), b13#0), 
      #_module.bin.Twice(Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.Zero())))))))));
    assume _module.bin#Equal(_module.__default.increment($LS($LZ), b13#0), 
      #_module.bin.Twice(Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.TwicePlusOne(Lit(#_module.bin.Zero())))))))));
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(493,3)
    ##b#2 := b13#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#2, Tclass._module.bin(), $Heap);
    assume _module.__default.increment#canCall(b13#0);
    ##b#3 := _module.__default.increment($LS($LZ), b13#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#3, Tclass._module.bin(), $Heap);
    assume _module.__default.BinToUnary#canCall(_module.__default.increment($LS($LZ), b13#0));
    ##b#4 := b13#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#4, Tclass._module.bin(), $Heap);
    assume _module.__default.BinToUnary#canCall(b13#0);
    ##n#0 := _module.__default.BinToUnary($LS($LZ), b13#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#0, Tclass._module.Nat(), $Heap);
    ##m#0 := Lit(#_module.Nat.S(Lit(#_module.Nat.O())));
    // assume allocatedness for argument to function
    assume $IsAlloc(##m#0, Tclass._module.Nat(), $Heap);
    assume _module.__default.plus#canCall(_module.__default.BinToUnary($LS($LZ), b13#0), 
      Lit(#_module.Nat.S(Lit(#_module.Nat.O()))));
    assume $IsA#_module.Nat(_module.__default.BinToUnary($LS($LZ), _module.__default.increment($LS($LZ), b13#0)))
       && $IsA#_module.Nat(_module.__default.plus($LS($LZ), 
          _module.__default.BinToUnary($LS($LZ), b13#0), 
          Lit(#_module.Nat.S(Lit(#_module.Nat.O())))))
       && 
      _module.__default.increment#canCall(b13#0)
       && _module.__default.BinToUnary#canCall(_module.__default.increment($LS($LZ), b13#0))
       && 
      _module.__default.BinToUnary#canCall(b13#0)
       && _module.__default.plus#canCall(_module.__default.BinToUnary($LS($LZ), b13#0), 
        Lit(#_module.Nat.S(Lit(#_module.Nat.O()))));
    assert {:subsumption 0} _module.Nat#Equal(_module.__default.BinToUnary($LS($LS($LZ)), _module.__default.increment($LS($LS($LZ)), b13#0)), 
      _module.__default.plus($LS($LS($LZ)), 
        _module.__default.BinToUnary($LS($LS($LZ)), b13#0), 
        Lit(#_module.Nat.S(Lit(#_module.Nat.O())))));
    assume _module.Nat#Equal(_module.__default.BinToUnary($LS($LZ), _module.__default.increment($LS($LZ), b13#0)), 
      _module.__default.plus($LS($LZ), 
        _module.__default.BinToUnary($LS($LZ), b13#0), 
        Lit(#_module.Nat.S(Lit(#_module.Nat.O())))));
}



// function declaration for _module._default.plus'
function _module.__default.plus_k($ly: LayerType, n#0: DatatypeType, m#0: DatatypeType) : DatatypeType;

function _module.__default.plus_k#canCall(n#0: DatatypeType, m#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType :: 
  { _module.__default.plus_k($LS($ly), n#0, m#0) } 
  _module.__default.plus_k($LS($ly), n#0, m#0)
     == _module.__default.plus_k($ly, n#0, m#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType :: 
  { _module.__default.plus_k(AsFuelBottom($ly), n#0, m#0) } 
  _module.__default.plus_k($ly, n#0, m#0)
     == _module.__default.plus_k($LZ, n#0, m#0));

// consequence axiom for _module.__default.plus_k
axiom 42 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType :: 
    { _module.__default.plus_k($ly, n#0, m#0) } 
    _module.__default.plus_k#canCall(n#0, m#0)
         || (42 != $FunctionContextHeight
           && 
          $Is(n#0, Tclass._module.Nat())
           && $Is(m#0, Tclass._module.Nat()))
       ==> $Is(_module.__default.plus_k($ly, n#0, m#0), Tclass._module.Nat()));

function _module.__default.plus_k#requires(LayerType, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.plus_k
axiom (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType :: 
  { _module.__default.plus_k#requires($ly, n#0, m#0) } 
  $Is(n#0, Tclass._module.Nat()) && $Is(m#0, Tclass._module.Nat())
     ==> _module.__default.plus_k#requires($ly, n#0, m#0) == true);

// definition axiom for _module.__default.plus_k (revealed)
axiom 42 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType :: 
    { _module.__default.plus_k($LS($ly), n#0, m#0) } 
    _module.__default.plus_k#canCall(n#0, m#0)
         || (42 != $FunctionContextHeight
           && 
          $Is(n#0, Tclass._module.Nat())
           && $Is(m#0, Tclass._module.Nat()))
       ==> (!_module.Nat.O_q(n#0)
           ==> (var n'#1 := _module.Nat._h0(n#0); _module.__default.plus_k#canCall(n'#1, m#0)))
         && _module.__default.plus_k($LS($ly), n#0, m#0)
           == (if _module.Nat.O_q(n#0)
             then m#0
             else (var n'#0 := _module.Nat._h0(n#0); 
              #_module.Nat.S(_module.__default.plus_k($ly, n'#0, m#0)))));

// definition axiom for _module.__default.plus_k for all literals (revealed)
axiom 42 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType :: 
    {:weight 3} { _module.__default.plus_k($LS($ly), Lit(n#0), Lit(m#0)) } 
    _module.__default.plus_k#canCall(Lit(n#0), Lit(m#0))
         || (42 != $FunctionContextHeight
           && 
          $Is(n#0, Tclass._module.Nat())
           && $Is(m#0, Tclass._module.Nat()))
       ==> (!Lit(_module.Nat.O_q(Lit(n#0)))
           ==> (var n'#3 := Lit(_module.Nat._h0(Lit(n#0))); 
            _module.__default.plus_k#canCall(n'#3, Lit(m#0))))
         && _module.__default.plus_k($LS($ly), Lit(n#0), Lit(m#0))
           == (if _module.Nat.O_q(Lit(n#0))
             then m#0
             else (var n'#2 := Lit(_module.Nat._h0(Lit(n#0))); 
              Lit(#_module.Nat.S(Lit(_module.__default.plus_k($LS($ly), n'#2, Lit(m#0))))))));

procedure CheckWellformed$$_module.__default.plus_k(n#0: DatatypeType where $Is(n#0, Tclass._module.Nat()), 
    m#0: DatatypeType where $Is(m#0, Tclass._module.Nat()));
  free requires 42 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.plus_k(n#0: DatatypeType, m#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: DatatypeType;
  var n'#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var ##n#0: DatatypeType;
  var ##m#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function plus'
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(500,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.plus_k($LS($LZ), n#0, m#0), Tclass._module.Nat());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (n#0 == #_module.Nat.O())
        {
            assume _module.__default.plus_k($LS($LZ), n#0, m#0) == m#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.plus_k($LS($LZ), n#0, m#0), Tclass._module.Nat());
        }
        else if (n#0 == #_module.Nat.S(_mcc#0#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.Nat());
            havoc n'#Z#0;
            assume $Is(n'#Z#0, Tclass._module.Nat());
            assume let#0#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.Nat());
            assume n'#Z#0 == let#0#0#0;
            ##n#0 := n'#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0, Tclass._module.Nat(), $Heap);
            ##m#0 := m#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#0, Tclass._module.Nat(), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(##n#0) < DtRank(n#0)
               || (DtRank(##n#0) == DtRank(n#0) && DtRank(##m#0) < DtRank(m#0));
            assume _module.__default.plus_k#canCall(n'#Z#0, m#0);
            assume _module.__default.plus_k($LS($LZ), n#0, m#0)
               == #_module.Nat.S(_module.__default.plus_k($LS($LZ), n'#Z#0, m#0));
            assume _module.__default.plus_k#canCall(n'#Z#0, m#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.plus_k($LS($LZ), n#0, m#0), Tclass._module.Nat());
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
    }
}



// function declaration for _module._default.decreasingOnTwo
function _module.__default.decreasingOnTwo($ly: LayerType, n#0: DatatypeType, m#0: DatatypeType, p#0: DatatypeType)
   : DatatypeType;

function _module.__default.decreasingOnTwo#canCall(n#0: DatatypeType, m#0: DatatypeType, p#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType, p#0: DatatypeType :: 
  { _module.__default.decreasingOnTwo($LS($ly), n#0, m#0, p#0) } 
  _module.__default.decreasingOnTwo($LS($ly), n#0, m#0, p#0)
     == _module.__default.decreasingOnTwo($ly, n#0, m#0, p#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType, p#0: DatatypeType :: 
  { _module.__default.decreasingOnTwo(AsFuelBottom($ly), n#0, m#0, p#0) } 
  _module.__default.decreasingOnTwo($ly, n#0, m#0, p#0)
     == _module.__default.decreasingOnTwo($LZ, n#0, m#0, p#0));

// consequence axiom for _module.__default.decreasingOnTwo
axiom 43 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType, p#0: DatatypeType :: 
    { _module.__default.decreasingOnTwo($ly, n#0, m#0, p#0) } 
    _module.__default.decreasingOnTwo#canCall(n#0, m#0, p#0)
         || (43 != $FunctionContextHeight
           && 
          $Is(n#0, Tclass._module.Nat())
           && $Is(m#0, Tclass._module.Nat())
           && $Is(p#0, Tclass._module.Nat()))
       ==> $Is(_module.__default.decreasingOnTwo($ly, n#0, m#0, p#0), Tclass._module.Nat()));

function _module.__default.decreasingOnTwo#requires(LayerType, DatatypeType, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.decreasingOnTwo
axiom (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType, p#0: DatatypeType :: 
  { _module.__default.decreasingOnTwo#requires($ly, n#0, m#0, p#0) } 
  $Is(n#0, Tclass._module.Nat())
       && $Is(m#0, Tclass._module.Nat())
       && $Is(p#0, Tclass._module.Nat())
     ==> _module.__default.decreasingOnTwo#requires($ly, n#0, m#0, p#0) == true);

// definition axiom for _module.__default.decreasingOnTwo (revealed)
axiom 43 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType, p#0: DatatypeType :: 
    { _module.__default.decreasingOnTwo($LS($ly), n#0, m#0, p#0) } 
    _module.__default.decreasingOnTwo#canCall(n#0, m#0, p#0)
         || (43 != $FunctionContextHeight
           && 
          $Is(n#0, Tclass._module.Nat())
           && $Is(m#0, Tclass._module.Nat())
           && $Is(p#0, Tclass._module.Nat()))
       ==> (_module.Nat.O_q(p#0)
           ==> 
          !_module.Nat.O_q(n#0)
           ==> (var n'#1 := _module.Nat._h0(n#0); 
            _module.__default.decreasingOnTwo#canCall(n'#1, m#0, Lit(#_module.Nat.S(Lit(#_module.Nat.O()))))))
         && (!_module.Nat.O_q(p#0)
           ==> 
          !_module.Nat.O_q(m#0)
           ==> (var m'#1 := _module.Nat._h0(m#0); 
            _module.__default.decreasingOnTwo#canCall(n#0, m'#1, Lit(#_module.Nat.O()))))
         && _module.__default.decreasingOnTwo($LS($ly), n#0, m#0, p#0)
           == (if _module.Nat.O_q(p#0)
             then (if _module.Nat.O_q(n#0)
               then #_module.Nat.O()
               else (var n'#0 := _module.Nat._h0(n#0); 
                _module.__default.decreasingOnTwo($ly, n'#0, m#0, Lit(#_module.Nat.S(Lit(#_module.Nat.O()))))))
             else (if _module.Nat.O_q(m#0)
               then #_module.Nat.S(Lit(#_module.Nat.O()))
               else (var m'#0 := _module.Nat._h0(m#0); 
                _module.__default.decreasingOnTwo($ly, n#0, m'#0, Lit(#_module.Nat.O()))))));

// definition axiom for _module.__default.decreasingOnTwo for all literals (revealed)
axiom 43 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType, p#0: DatatypeType :: 
    {:weight 3} { _module.__default.decreasingOnTwo($LS($ly), Lit(n#0), Lit(m#0), Lit(p#0)) } 
    _module.__default.decreasingOnTwo#canCall(Lit(n#0), Lit(m#0), Lit(p#0))
         || (43 != $FunctionContextHeight
           && 
          $Is(n#0, Tclass._module.Nat())
           && $Is(m#0, Tclass._module.Nat())
           && $Is(p#0, Tclass._module.Nat()))
       ==> (Lit(_module.Nat.O_q(Lit(p#0)))
           ==> 
          !Lit(_module.Nat.O_q(Lit(n#0)))
           ==> (var n'#3 := Lit(_module.Nat._h0(Lit(n#0))); 
            _module.__default.decreasingOnTwo#canCall(n'#3, Lit(m#0), Lit(#_module.Nat.S(Lit(#_module.Nat.O()))))))
         && (!Lit(_module.Nat.O_q(Lit(p#0)))
           ==> 
          !Lit(_module.Nat.O_q(Lit(m#0)))
           ==> (var m'#3 := Lit(_module.Nat._h0(Lit(m#0))); 
            _module.__default.decreasingOnTwo#canCall(Lit(n#0), m'#3, Lit(#_module.Nat.O()))))
         && _module.__default.decreasingOnTwo($LS($ly), Lit(n#0), Lit(m#0), Lit(p#0))
           == (if _module.Nat.O_q(Lit(p#0))
             then (if _module.Nat.O_q(Lit(n#0))
               then #_module.Nat.O()
               else (var n'#2 := Lit(_module.Nat._h0(Lit(n#0))); 
                Lit(_module.__default.decreasingOnTwo($LS($ly), n'#2, Lit(m#0), Lit(#_module.Nat.S(Lit(#_module.Nat.O())))))))
             else (if _module.Nat.O_q(Lit(m#0))
               then #_module.Nat.S(Lit(#_module.Nat.O()))
               else (var m'#2 := Lit(_module.Nat._h0(Lit(m#0))); 
                Lit(_module.__default.decreasingOnTwo($LS($ly), Lit(n#0), m'#2, Lit(#_module.Nat.O())))))));

procedure CheckWellformed$$_module.__default.decreasingOnTwo(n#0: DatatypeType where $Is(n#0, Tclass._module.Nat()), 
    m#0: DatatypeType where $Is(m#0, Tclass._module.Nat()), 
    p#0: DatatypeType where $Is(p#0, Tclass._module.Nat()));
  free requires 43 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.decreasingOnTwo(n#0: DatatypeType, m#0: DatatypeType, p#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: DatatypeType;
  var _mcc#2#0: DatatypeType;
  var m'#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var ##n#0: DatatypeType;
  var ##m#0: DatatypeType;
  var ##p#0: DatatypeType;
  var _mcc#1#0: DatatypeType;
  var n'#Z#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var ##n#1: DatatypeType;
  var ##m#1: DatatypeType;
  var ##p#1: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function decreasingOnTwo
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/SoftwareFoundations-Basics.dfy(509,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.decreasingOnTwo($LS($LZ), n#0, m#0, p#0), Tclass._module.Nat());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (p#0 == #_module.Nat.O())
        {
            if (n#0 == #_module.Nat.O())
            {
                assume _module.__default.decreasingOnTwo($LS($LZ), n#0, m#0, p#0)
                   == Lit(#_module.Nat.O());
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.decreasingOnTwo($LS($LZ), n#0, m#0, p#0), Tclass._module.Nat());
            }
            else if (n#0 == #_module.Nat.S(_mcc#1#0))
            {
                assume $Is(_mcc#1#0, Tclass._module.Nat());
                havoc n'#Z#0;
                assume $Is(n'#Z#0, Tclass._module.Nat());
                assume let#1#0#0 == _mcc#1#0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(let#1#0#0, Tclass._module.Nat());
                assume n'#Z#0 == let#1#0#0;
                ##n#1 := n'#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#1, Tclass._module.Nat(), $Heap);
                ##m#1 := m#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##m#1, Tclass._module.Nat(), $Heap);
                ##p#1 := Lit(#_module.Nat.S(Lit(#_module.Nat.O())));
                // assume allocatedness for argument to function
                assume $IsAlloc(##p#1, Tclass._module.Nat(), $Heap);
                b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assert DtRank(##n#1) < DtRank(n#0)
                   || (DtRank(##n#1) == DtRank(n#0)
                     && (DtRank(##m#1) < DtRank(m#0)
                       || (DtRank(##m#1) == DtRank(m#0) && DtRank(##p#1) < DtRank(p#0))));
                assume _module.__default.decreasingOnTwo#canCall(n'#Z#0, m#0, Lit(#_module.Nat.S(Lit(#_module.Nat.O()))));
                assume _module.__default.decreasingOnTwo($LS($LZ), n#0, m#0, p#0)
                   == _module.__default.decreasingOnTwo($LS($LZ), n'#Z#0, m#0, Lit(#_module.Nat.S(Lit(#_module.Nat.O()))));
                assume _module.__default.decreasingOnTwo#canCall(n'#Z#0, m#0, Lit(#_module.Nat.S(Lit(#_module.Nat.O()))));
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.decreasingOnTwo($LS($LZ), n#0, m#0, p#0), Tclass._module.Nat());
            }
            else
            {
                assume false;
            }
        }
        else if (p#0 == #_module.Nat.S(_mcc#0#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.Nat());
            if (m#0 == #_module.Nat.O())
            {
                assume _module.__default.decreasingOnTwo($LS($LZ), n#0, m#0, p#0)
                   == Lit(#_module.Nat.S(Lit(#_module.Nat.O())));
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.decreasingOnTwo($LS($LZ), n#0, m#0, p#0), Tclass._module.Nat());
            }
            else if (m#0 == #_module.Nat.S(_mcc#2#0))
            {
                assume $Is(_mcc#2#0, Tclass._module.Nat());
                havoc m'#Z#0;
                assume $Is(m'#Z#0, Tclass._module.Nat());
                assume let#0#0#0 == _mcc#2#0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(let#0#0#0, Tclass._module.Nat());
                assume m'#Z#0 == let#0#0#0;
                ##n#0 := n#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#0, Tclass._module.Nat(), $Heap);
                ##m#0 := m'#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##m#0, Tclass._module.Nat(), $Heap);
                ##p#0 := Lit(#_module.Nat.O());
                // assume allocatedness for argument to function
                assume $IsAlloc(##p#0, Tclass._module.Nat(), $Heap);
                b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assert DtRank(##n#0) < DtRank(n#0)
                   || (DtRank(##n#0) == DtRank(n#0)
                     && (DtRank(##m#0) < DtRank(m#0)
                       || (DtRank(##m#0) == DtRank(m#0) && DtRank(##p#0) < DtRank(p#0))));
                assume _module.__default.decreasingOnTwo#canCall(n#0, m'#Z#0, Lit(#_module.Nat.O()));
                assume _module.__default.decreasingOnTwo($LS($LZ), n#0, m#0, p#0)
                   == _module.__default.decreasingOnTwo($LS($LZ), n#0, m'#Z#0, Lit(#_module.Nat.O()));
                assume _module.__default.decreasingOnTwo#canCall(n#0, m'#Z#0, Lit(#_module.Nat.O()));
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.decreasingOnTwo($LS($LZ), n#0, m#0, p#0), Tclass._module.Nat());
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
        assert b$reqreads#1;
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

const unique tytagFamily$day: TyTagFamily;

const unique tytagFamily$Bool: TyTagFamily;

const unique tytagFamily$Nat: TyTagFamily;

const unique tytagFamily$bin: TyTagFamily;

const unique tytagFamily$_default: TyTagFamily;
