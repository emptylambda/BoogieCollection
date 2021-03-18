// Dafny 3.0.0.30204
// Command Line Options: -compile:0 -noVerify /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy -print:./NipkowKlein-chapter7.bpl

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

function Tclass._System.___hFunc5(Ty, Ty, Ty, Ty, Ty, Ty) : Ty;

const unique Tagclass._System.___hFunc5: TyTag;

// Tclass._System.___hFunc5 Tag
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) } 
  Tag(Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
       == Tagclass._System.___hFunc5
     && TagFamily(Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
       == tytagFamily$_#Func5);

// Tclass._System.___hFunc5 injectivity 0
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) } 
  Tclass._System.___hFunc5_0(Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$T0);

function Tclass._System.___hFunc5_0(Ty) : Ty;

// Tclass._System.___hFunc5 injectivity 1
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) } 
  Tclass._System.___hFunc5_1(Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$T1);

function Tclass._System.___hFunc5_1(Ty) : Ty;

// Tclass._System.___hFunc5 injectivity 2
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) } 
  Tclass._System.___hFunc5_2(Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$T2);

function Tclass._System.___hFunc5_2(Ty) : Ty;

// Tclass._System.___hFunc5 injectivity 3
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) } 
  Tclass._System.___hFunc5_3(Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$T3);

function Tclass._System.___hFunc5_3(Ty) : Ty;

// Tclass._System.___hFunc5 injectivity 4
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) } 
  Tclass._System.___hFunc5_4(Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$T4);

function Tclass._System.___hFunc5_4(Ty) : Ty;

// Tclass._System.___hFunc5 injectivity 5
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) } 
  Tclass._System.___hFunc5_5(Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$R);

function Tclass._System.___hFunc5_5(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hFunc5
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R)) } 
  $IsBox(bx, Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, 
        Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R)));

function Handle5([Heap,Box,Box,Box,Box,Box]Box, 
    [Heap,Box,Box,Box,Box,Box]bool, 
    [Heap,Box,Box,Box,Box,Box]Set Box)
   : HandleType;

function Apply5(Ty, Ty, Ty, Ty, Ty, Ty, Heap, HandleType, Box, Box, Box, Box, Box) : Box;

function Requires5(Ty, Ty, Ty, Ty, Ty, Ty, Heap, HandleType, Box, Box, Box, Box, Box) : bool;

function Reads5(Ty, Ty, Ty, Ty, Ty, Ty, Heap, HandleType, Box, Box, Box, Box, Box) : Set Box;

axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    heap: Heap, 
    h: [Heap,Box,Box,Box,Box,Box]Box, 
    r: [Heap,Box,Box,Box,Box,Box]bool, 
    rd: [Heap,Box,Box,Box,Box,Box]Set Box, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box :: 
  { Apply5(t0, t1, t2, t3, t4, t5, heap, Handle5(h, r, rd), bx0, bx1, bx2, bx3, bx4) } 
  Apply5(t0, t1, t2, t3, t4, t5, heap, Handle5(h, r, rd), bx0, bx1, bx2, bx3, bx4)
     == h[heap, bx0, bx1, bx2, bx3, bx4]);

axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    heap: Heap, 
    h: [Heap,Box,Box,Box,Box,Box]Box, 
    r: [Heap,Box,Box,Box,Box,Box]bool, 
    rd: [Heap,Box,Box,Box,Box,Box]Set Box, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box :: 
  { Requires5(t0, t1, t2, t3, t4, t5, heap, Handle5(h, r, rd), bx0, bx1, bx2, bx3, bx4) } 
  r[heap, bx0, bx1, bx2, bx3, bx4]
     ==> Requires5(t0, t1, t2, t3, t4, t5, heap, Handle5(h, r, rd), bx0, bx1, bx2, bx3, bx4));

axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    heap: Heap, 
    h: [Heap,Box,Box,Box,Box,Box]Box, 
    r: [Heap,Box,Box,Box,Box,Box]bool, 
    rd: [Heap,Box,Box,Box,Box,Box]Set Box, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box, 
    bx: Box :: 
  { Reads5(t0, t1, t2, t3, t4, t5, heap, Handle5(h, r, rd), bx0, bx1, bx2, bx3, bx4)[bx] } 
  Reads5(t0, t1, t2, t3, t4, t5, heap, Handle5(h, r, rd), bx0, bx1, bx2, bx3, bx4)[bx]
     == rd[heap, bx0, bx1, bx2, bx3, bx4][bx]);

function {:inline} Requires5#canCall(t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    heap: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box)
   : bool
{
  true
}

function {:inline} Reads5#canCall(t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    heap: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box)
   : bool
{
  true
}

// frame axiom for Reads5
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box :: 
  { $HeapSucc(h0, h1), Reads5(t0, t1, t2, t3, t4, t5, h1, f, bx0, bx1, bx2, bx3, bx4) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $IsBox(bx4, t4)
       && $Is(f, Tclass._System.___hFunc5(t0, t1, t2, t3, t4, t5))
       && (forall<a> o: ref, fld: Field a :: 
        o != null
             && Reads5(t0, t1, t2, t3, t4, t5, h0, f, bx0, bx1, bx2, bx3, bx4)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads5(t0, t1, t2, t3, t4, t5, h0, f, bx0, bx1, bx2, bx3, bx4)
       == Reads5(t0, t1, t2, t3, t4, t5, h1, f, bx0, bx1, bx2, bx3, bx4));

// frame axiom for Reads5
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box :: 
  { $HeapSucc(h0, h1), Reads5(t0, t1, t2, t3, t4, t5, h1, f, bx0, bx1, bx2, bx3, bx4) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $IsBox(bx4, t4)
       && $Is(f, Tclass._System.___hFunc5(t0, t1, t2, t3, t4, t5))
       && (forall<a> o: ref, fld: Field a :: 
        o != null
             && Reads5(t0, t1, t2, t3, t4, t5, h1, f, bx0, bx1, bx2, bx3, bx4)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads5(t0, t1, t2, t3, t4, t5, h0, f, bx0, bx1, bx2, bx3, bx4)
       == Reads5(t0, t1, t2, t3, t4, t5, h1, f, bx0, bx1, bx2, bx3, bx4));

// frame axiom for Requires5
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box :: 
  { $HeapSucc(h0, h1), Requires5(t0, t1, t2, t3, t4, t5, h1, f, bx0, bx1, bx2, bx3, bx4) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $IsBox(bx4, t4)
       && $Is(f, Tclass._System.___hFunc5(t0, t1, t2, t3, t4, t5))
       && (forall<a> o: ref, fld: Field a :: 
        o != null
             && Reads5(t0, t1, t2, t3, t4, t5, h0, f, bx0, bx1, bx2, bx3, bx4)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires5(t0, t1, t2, t3, t4, t5, h0, f, bx0, bx1, bx2, bx3, bx4)
       == Requires5(t0, t1, t2, t3, t4, t5, h1, f, bx0, bx1, bx2, bx3, bx4));

// frame axiom for Requires5
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box :: 
  { $HeapSucc(h0, h1), Requires5(t0, t1, t2, t3, t4, t5, h1, f, bx0, bx1, bx2, bx3, bx4) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $IsBox(bx4, t4)
       && $Is(f, Tclass._System.___hFunc5(t0, t1, t2, t3, t4, t5))
       && (forall<a> o: ref, fld: Field a :: 
        o != null
             && Reads5(t0, t1, t2, t3, t4, t5, h1, f, bx0, bx1, bx2, bx3, bx4)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires5(t0, t1, t2, t3, t4, t5, h0, f, bx0, bx1, bx2, bx3, bx4)
       == Requires5(t0, t1, t2, t3, t4, t5, h1, f, bx0, bx1, bx2, bx3, bx4));

// frame axiom for Apply5
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box :: 
  { $HeapSucc(h0, h1), Apply5(t0, t1, t2, t3, t4, t5, h1, f, bx0, bx1, bx2, bx3, bx4) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $IsBox(bx4, t4)
       && $Is(f, Tclass._System.___hFunc5(t0, t1, t2, t3, t4, t5))
       && (forall<a> o: ref, fld: Field a :: 
        o != null
             && Reads5(t0, t1, t2, t3, t4, t5, h0, f, bx0, bx1, bx2, bx3, bx4)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply5(t0, t1, t2, t3, t4, t5, h0, f, bx0, bx1, bx2, bx3, bx4)
       == Apply5(t0, t1, t2, t3, t4, t5, h1, f, bx0, bx1, bx2, bx3, bx4));

// frame axiom for Apply5
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box :: 
  { $HeapSucc(h0, h1), Apply5(t0, t1, t2, t3, t4, t5, h1, f, bx0, bx1, bx2, bx3, bx4) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $IsBox(bx4, t4)
       && $Is(f, Tclass._System.___hFunc5(t0, t1, t2, t3, t4, t5))
       && (forall<a> o: ref, fld: Field a :: 
        o != null
             && Reads5(t0, t1, t2, t3, t4, t5, h1, f, bx0, bx1, bx2, bx3, bx4)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply5(t0, t1, t2, t3, t4, t5, h0, f, bx0, bx1, bx2, bx3, bx4)
       == Apply5(t0, t1, t2, t3, t4, t5, h1, f, bx0, bx1, bx2, bx3, bx4));

// empty-reads property for Reads5 
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    heap: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box :: 
  { Reads5(t0, t1, t2, t3, t4, t5, $OneHeap, f, bx0, bx1, bx2, bx3, bx4), $IsGoodHeap(heap) } 
    { Reads5(t0, t1, t2, t3, t4, t5, heap, f, bx0, bx1, bx2, bx3, bx4) } 
  $IsGoodHeap(heap)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $IsBox(bx4, t4)
       && $Is(f, Tclass._System.___hFunc5(t0, t1, t2, t3, t4, t5))
     ==> (Set#Equal(Reads5(t0, t1, t2, t3, t4, t5, $OneHeap, f, bx0, bx1, bx2, bx3, bx4), 
        Set#Empty(): Set Box)
       <==> Set#Equal(Reads5(t0, t1, t2, t3, t4, t5, heap, f, bx0, bx1, bx2, bx3, bx4), 
        Set#Empty(): Set Box)));

// empty-reads property for Requires5
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    heap: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box :: 
  { Requires5(t0, t1, t2, t3, t4, t5, $OneHeap, f, bx0, bx1, bx2, bx3, bx4), $IsGoodHeap(heap) } 
    { Requires5(t0, t1, t2, t3, t4, t5, heap, f, bx0, bx1, bx2, bx3, bx4) } 
  $IsGoodHeap(heap)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $IsBox(bx4, t4)
       && $Is(f, Tclass._System.___hFunc5(t0, t1, t2, t3, t4, t5))
       && Set#Equal(Reads5(t0, t1, t2, t3, t4, t5, $OneHeap, f, bx0, bx1, bx2, bx3, bx4), 
        Set#Empty(): Set Box)
     ==> Requires5(t0, t1, t2, t3, t4, t5, $OneHeap, f, bx0, bx1, bx2, bx3, bx4)
       == Requires5(t0, t1, t2, t3, t4, t5, heap, f, bx0, bx1, bx2, bx3, bx4));

axiom (forall f: HandleType, t0: Ty, t1: Ty, t2: Ty, t3: Ty, t4: Ty, t5: Ty :: 
  { $Is(f, Tclass._System.___hFunc5(t0, t1, t2, t3, t4, t5)) } 
  $Is(f, Tclass._System.___hFunc5(t0, t1, t2, t3, t4, t5))
     <==> (forall h: Heap, bx0: Box, bx1: Box, bx2: Box, bx3: Box, bx4: Box :: 
      { Apply5(t0, t1, t2, t3, t4, t5, h, f, bx0, bx1, bx2, bx3, bx4) } 
      $IsGoodHeap(h)
           && 
          $IsBox(bx0, t0)
           && $IsBox(bx1, t1)
           && $IsBox(bx2, t2)
           && $IsBox(bx3, t3)
           && $IsBox(bx4, t4)
           && Requires5(t0, t1, t2, t3, t4, t5, h, f, bx0, bx1, bx2, bx3, bx4)
         ==> $IsBox(Apply5(t0, t1, t2, t3, t4, t5, h, f, bx0, bx1, bx2, bx3, bx4), t5)));

axiom (forall f: HandleType, 
    t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    u0: Ty, 
    u1: Ty, 
    u2: Ty, 
    u3: Ty, 
    u4: Ty, 
    u5: Ty :: 
  { $Is(f, Tclass._System.___hFunc5(t0, t1, t2, t3, t4, t5)), $Is(f, Tclass._System.___hFunc5(u0, u1, u2, u3, u4, u5)) } 
  $Is(f, Tclass._System.___hFunc5(t0, t1, t2, t3, t4, t5))
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
        { $IsBox(bx, u4) } { $IsBox(bx, t4) } 
        $IsBox(bx, u4) ==> $IsBox(bx, t4))
       && (forall bx: Box :: 
        { $IsBox(bx, t5) } { $IsBox(bx, u5) } 
        $IsBox(bx, t5) ==> $IsBox(bx, u5))
     ==> $Is(f, Tclass._System.___hFunc5(u0, u1, u2, u3, u4, u5)));

axiom (forall f: HandleType, t0: Ty, t1: Ty, t2: Ty, t3: Ty, t4: Ty, t5: Ty, h: Heap :: 
  { $IsAlloc(f, Tclass._System.___hFunc5(t0, t1, t2, t3, t4, t5), h) } 
  $IsGoodHeap(h)
     ==> ($IsAlloc(f, Tclass._System.___hFunc5(t0, t1, t2, t3, t4, t5), h)
       <==> (forall bx0: Box, bx1: Box, bx2: Box, bx3: Box, bx4: Box :: 
        { Apply5(t0, t1, t2, t3, t4, t5, h, f, bx0, bx1, bx2, bx3, bx4) } 
          { Reads5(t0, t1, t2, t3, t4, t5, h, f, bx0, bx1, bx2, bx3, bx4) } 
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
             && 
            $IsBox(bx4, t4)
             && $IsAllocBox(bx4, t4, h)
             && Requires5(t0, t1, t2, t3, t4, t5, h, f, bx0, bx1, bx2, bx3, bx4)
           ==> (forall r: ref :: 
            { Reads5(t0, t1, t2, t3, t4, t5, h, f, bx0, bx1, bx2, bx3, bx4)[$Box(r)] } 
            r != null
                 && Reads5(t0, t1, t2, t3, t4, t5, h, f, bx0, bx1, bx2, bx3, bx4)[$Box(r)]
               ==> read(h, r, alloc)))));

axiom (forall f: HandleType, t0: Ty, t1: Ty, t2: Ty, t3: Ty, t4: Ty, t5: Ty, h: Heap :: 
  { $IsAlloc(f, Tclass._System.___hFunc5(t0, t1, t2, t3, t4, t5), h) } 
  $IsGoodHeap(h)
       && $IsAlloc(f, Tclass._System.___hFunc5(t0, t1, t2, t3, t4, t5), h)
     ==> (forall bx0: Box, bx1: Box, bx2: Box, bx3: Box, bx4: Box :: 
      { Apply5(t0, t1, t2, t3, t4, t5, h, f, bx0, bx1, bx2, bx3, bx4) } 
      $IsAllocBox(bx0, t0, h)
           && $IsAllocBox(bx1, t1, h)
           && $IsAllocBox(bx2, t2, h)
           && $IsAllocBox(bx3, t3, h)
           && $IsAllocBox(bx4, t4, h)
           && Requires5(t0, t1, t2, t3, t4, t5, h, f, bx0, bx1, bx2, bx3, bx4)
         ==> $IsAllocBox(Apply5(t0, t1, t2, t3, t4, t5, h, f, bx0, bx1, bx2, bx3, bx4), t5, h)));

function Tclass._System.___hPartialFunc5(Ty, Ty, Ty, Ty, Ty, Ty) : Ty;

const unique Tagclass._System.___hPartialFunc5: TyTag;

// Tclass._System.___hPartialFunc5 Tag
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) } 
  Tag(Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
       == Tagclass._System.___hPartialFunc5
     && TagFamily(Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
       == tytagFamily$_#PartialFunc5);

// Tclass._System.___hPartialFunc5 injectivity 0
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) } 
  Tclass._System.___hPartialFunc5_0(Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$T0);

function Tclass._System.___hPartialFunc5_0(Ty) : Ty;

// Tclass._System.___hPartialFunc5 injectivity 1
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) } 
  Tclass._System.___hPartialFunc5_1(Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$T1);

function Tclass._System.___hPartialFunc5_1(Ty) : Ty;

// Tclass._System.___hPartialFunc5 injectivity 2
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) } 
  Tclass._System.___hPartialFunc5_2(Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$T2);

function Tclass._System.___hPartialFunc5_2(Ty) : Ty;

// Tclass._System.___hPartialFunc5 injectivity 3
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) } 
  Tclass._System.___hPartialFunc5_3(Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$T3);

function Tclass._System.___hPartialFunc5_3(Ty) : Ty;

// Tclass._System.___hPartialFunc5 injectivity 4
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) } 
  Tclass._System.___hPartialFunc5_4(Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$T4);

function Tclass._System.___hPartialFunc5_4(Ty) : Ty;

// Tclass._System.___hPartialFunc5 injectivity 5
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) } 
  Tclass._System.___hPartialFunc5_5(Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$R);

function Tclass._System.___hPartialFunc5_5(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hPartialFunc5
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R)) } 
  $IsBox(bx, Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, 
        Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R)));

// _System._#PartialFunc5: subset type $Is
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty, f#0: HandleType :: 
  { $Is(f#0, Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R)) } 
  $Is(f#0, Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     <==> $Is(f#0, Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
       && (forall x0#0: Box, x1#0: Box, x2#0: Box, x3#0: Box, x4#0: Box :: 
        $IsBox(x0#0, #$T0)
             && $IsBox(x1#0, #$T1)
             && $IsBox(x2#0, #$T2)
             && $IsBox(x3#0, #$T3)
             && $IsBox(x4#0, #$T4)
           ==> Set#Equal(Reads5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R, $OneHeap, f#0, x0#0, x1#0, x2#0, x3#0, x4#0), 
            Set#Empty(): Set Box)));

// _System._#PartialFunc5: subset type $IsAlloc
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$R: Ty, 
    f#0: HandleType, 
    $h: Heap :: 
  { $IsAlloc(f#0, Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R), $h) } 
  $IsAlloc(f#0, Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R), $h));

function Tclass._System.___hTotalFunc5(Ty, Ty, Ty, Ty, Ty, Ty) : Ty;

const unique Tagclass._System.___hTotalFunc5: TyTag;

// Tclass._System.___hTotalFunc5 Tag
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) } 
  Tag(Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
       == Tagclass._System.___hTotalFunc5
     && TagFamily(Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
       == tytagFamily$_#TotalFunc5);

// Tclass._System.___hTotalFunc5 injectivity 0
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) } 
  Tclass._System.___hTotalFunc5_0(Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$T0);

function Tclass._System.___hTotalFunc5_0(Ty) : Ty;

// Tclass._System.___hTotalFunc5 injectivity 1
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) } 
  Tclass._System.___hTotalFunc5_1(Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$T1);

function Tclass._System.___hTotalFunc5_1(Ty) : Ty;

// Tclass._System.___hTotalFunc5 injectivity 2
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) } 
  Tclass._System.___hTotalFunc5_2(Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$T2);

function Tclass._System.___hTotalFunc5_2(Ty) : Ty;

// Tclass._System.___hTotalFunc5 injectivity 3
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) } 
  Tclass._System.___hTotalFunc5_3(Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$T3);

function Tclass._System.___hTotalFunc5_3(Ty) : Ty;

// Tclass._System.___hTotalFunc5 injectivity 4
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) } 
  Tclass._System.___hTotalFunc5_4(Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$T4);

function Tclass._System.___hTotalFunc5_4(Ty) : Ty;

// Tclass._System.___hTotalFunc5 injectivity 5
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R) } 
  Tclass._System.___hTotalFunc5_5(Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     == #$R);

function Tclass._System.___hTotalFunc5_5(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hTotalFunc5
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R)) } 
  $IsBox(bx, Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, 
        Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R)));

// _System._#TotalFunc5: subset type $Is
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$T4: Ty, #$R: Ty, f#0: HandleType :: 
  { $Is(f#0, Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R)) } 
  $Is(f#0, Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
     <==> $Is(f#0, Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R))
       && (forall x0#0: Box, x1#0: Box, x2#0: Box, x3#0: Box, x4#0: Box :: 
        $IsBox(x0#0, #$T0)
             && $IsBox(x1#0, #$T1)
             && $IsBox(x2#0, #$T2)
             && $IsBox(x3#0, #$T3)
             && $IsBox(x4#0, #$T4)
           ==> Requires5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R, $OneHeap, f#0, x0#0, x1#0, x2#0, x3#0, x4#0)));

// _System._#TotalFunc5: subset type $IsAlloc
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$R: Ty, 
    f#0: HandleType, 
    $h: Heap :: 
  { $IsAlloc(f#0, Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R), $h) } 
  $IsAlloc(f#0, Tclass._System.___hTotalFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hPartialFunc5(#$T0, #$T1, #$T2, #$T3, #$T4, #$R), $h));

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
function #_module.List.Cons(Box, DatatypeType) : DatatypeType;

const unique ##_module.List.Cons: DtCtorId;

// Constructor identifier
axiom (forall a#19#0#0: Box, a#19#1#0: DatatypeType :: 
  { #_module.List.Cons(a#19#0#0, a#19#1#0) } 
  DatatypeCtorId(#_module.List.Cons(a#19#0#0, a#19#1#0)) == ##_module.List.Cons);

function _module.List.Cons_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.List.Cons_q(d) } 
  _module.List.Cons_q(d) <==> DatatypeCtorId(d) == ##_module.List.Cons);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.List.Cons_q(d) } 
  _module.List.Cons_q(d)
     ==> (exists a#20#0#0: Box, a#20#1#0: DatatypeType :: 
      d == #_module.List.Cons(a#20#0#0, a#20#1#0)));

// Constructor $Is
axiom (forall _module.List$T: Ty, a#21#0#0: Box, a#21#1#0: DatatypeType :: 
  { $Is(#_module.List.Cons(a#21#0#0, a#21#1#0), Tclass._module.List(_module.List$T)) } 
  $Is(#_module.List.Cons(a#21#0#0, a#21#1#0), Tclass._module.List(_module.List$T))
     <==> $IsBox(a#21#0#0, _module.List$T)
       && $Is(a#21#1#0, Tclass._module.List(_module.List$T)));

// Constructor $IsAlloc
axiom (forall _module.List$T: Ty, a#22#0#0: Box, a#22#1#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#_module.List.Cons(a#22#0#0, a#22#1#0), Tclass._module.List(_module.List$T), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.List.Cons(a#22#0#0, a#22#1#0), Tclass._module.List(_module.List$T), $h)
       <==> $IsAllocBox(a#22#0#0, _module.List$T, $h)
         && $IsAlloc(a#22#1#0, Tclass._module.List(_module.List$T), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _module.List$T: Ty, $h: Heap :: 
  { $IsAllocBox(_module.List.head(d), _module.List$T, $h) } 
  $IsGoodHeap($h)
       && 
      _module.List.Cons_q(d)
       && $IsAlloc(d, Tclass._module.List(_module.List$T), $h)
     ==> $IsAllocBox(_module.List.head(d), _module.List$T, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _module.List$T: Ty, $h: Heap :: 
  { $IsAlloc(_module.List.tail(d), Tclass._module.List(_module.List$T), $h) } 
  $IsGoodHeap($h)
       && 
      _module.List.Cons_q(d)
       && $IsAlloc(d, Tclass._module.List(_module.List$T), $h)
     ==> $IsAlloc(_module.List.tail(d), Tclass._module.List(_module.List$T), $h));

// Constructor literal
axiom (forall a#23#0#0: Box, a#23#1#0: DatatypeType :: 
  { #_module.List.Cons(Lit(a#23#0#0), Lit(a#23#1#0)) } 
  #_module.List.Cons(Lit(a#23#0#0), Lit(a#23#1#0))
     == Lit(#_module.List.Cons(a#23#0#0, a#23#1#0)));

function _module.List.head(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#24#0#0: Box, a#24#1#0: DatatypeType :: 
  { #_module.List.Cons(a#24#0#0, a#24#1#0) } 
  _module.List.head(#_module.List.Cons(a#24#0#0, a#24#1#0)) == a#24#0#0);

// Inductive rank
axiom (forall a#25#0#0: Box, a#25#1#0: DatatypeType :: 
  { #_module.List.Cons(a#25#0#0, a#25#1#0) } 
  BoxRank(a#25#0#0) < DtRank(#_module.List.Cons(a#25#0#0, a#25#1#0)));

function _module.List.tail(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#26#0#0: Box, a#26#1#0: DatatypeType :: 
  { #_module.List.Cons(a#26#0#0, a#26#1#0) } 
  _module.List.tail(#_module.List.Cons(a#26#0#0, a#26#1#0)) == a#26#1#0);

// Inductive rank
axiom (forall a#27#0#0: Box, a#27#1#0: DatatypeType :: 
  { #_module.List.Cons(a#27#0#0, a#27#1#0) } 
  DtRank(a#27#1#0) < DtRank(#_module.List.Cons(a#27#0#0, a#27#1#0)));

// Depth-one case-split function
function $IsA#_module.List(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.List(d) } 
  $IsA#_module.List(d) ==> _module.List.Nil_q(d) || _module.List.Cons_q(d));

// Questionmark data type disjunctivity
axiom (forall _module.List$T: Ty, d: DatatypeType :: 
  { _module.List.Cons_q(d), $Is(d, Tclass._module.List(_module.List$T)) } 
    { _module.List.Nil_q(d), $Is(d, Tclass._module.List(_module.List$T)) } 
  $Is(d, Tclass._module.List(_module.List$T))
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
       <==> _module.List.head(a) == _module.List.head(b)
         && _module.List#Equal(_module.List.tail(a), _module.List.tail(b))));

// Datatype extensionality axiom: _module.List
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.List#Equal(a, b) } 
  _module.List#Equal(a, b) <==> a == b);

const unique class._module.List: ClassName;

// Constructor function declaration
function #_module.aexp.N(int) : DatatypeType;

const unique ##_module.aexp.N: DtCtorId;

// Constructor identifier
axiom (forall a#28#0#0: int :: 
  { #_module.aexp.N(a#28#0#0) } 
  DatatypeCtorId(#_module.aexp.N(a#28#0#0)) == ##_module.aexp.N);

function _module.aexp.N_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.aexp.N_q(d) } 
  _module.aexp.N_q(d) <==> DatatypeCtorId(d) == ##_module.aexp.N);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.aexp.N_q(d) } 
  _module.aexp.N_q(d) ==> (exists a#29#0#0: int :: d == #_module.aexp.N(a#29#0#0)));

function Tclass._module.aexp() : Ty;

const unique Tagclass._module.aexp: TyTag;

// Tclass._module.aexp Tag
axiom Tag(Tclass._module.aexp()) == Tagclass._module.aexp
   && TagFamily(Tclass._module.aexp()) == tytagFamily$aexp;

// Box/unbox axiom for Tclass._module.aexp
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.aexp()) } 
  $IsBox(bx, Tclass._module.aexp())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.aexp()));

// Constructor $Is
axiom (forall a#30#0#0: int :: 
  { $Is(#_module.aexp.N(a#30#0#0), Tclass._module.aexp()) } 
  $Is(#_module.aexp.N(a#30#0#0), Tclass._module.aexp()) <==> $Is(a#30#0#0, TInt));

// Constructor $IsAlloc
axiom (forall a#31#0#0: int, $h: Heap :: 
  { $IsAlloc(#_module.aexp.N(a#31#0#0), Tclass._module.aexp(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.aexp.N(a#31#0#0), Tclass._module.aexp(), $h)
       <==> $IsAlloc(a#31#0#0, TInt, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.aexp.n(d), TInt, $h) } 
  $IsGoodHeap($h) && _module.aexp.N_q(d) && $IsAlloc(d, Tclass._module.aexp(), $h)
     ==> $IsAlloc(_module.aexp.n(d), TInt, $h));

// Constructor literal
axiom (forall a#32#0#0: int :: 
  { #_module.aexp.N(LitInt(a#32#0#0)) } 
  #_module.aexp.N(LitInt(a#32#0#0)) == Lit(#_module.aexp.N(a#32#0#0)));

function _module.aexp.n(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#33#0#0: int :: 
  { #_module.aexp.N(a#33#0#0) } 
  _module.aexp.n(#_module.aexp.N(a#33#0#0)) == a#33#0#0);

// Constructor function declaration
function #_module.aexp.V(Seq Box) : DatatypeType;

const unique ##_module.aexp.V: DtCtorId;

// Constructor identifier
axiom (forall a#34#0#0: Seq Box :: 
  { #_module.aexp.V(a#34#0#0) } 
  DatatypeCtorId(#_module.aexp.V(a#34#0#0)) == ##_module.aexp.V);

function _module.aexp.V_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.aexp.V_q(d) } 
  _module.aexp.V_q(d) <==> DatatypeCtorId(d) == ##_module.aexp.V);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.aexp.V_q(d) } 
  _module.aexp.V_q(d)
     ==> (exists a#35#0#0: Seq Box :: d == #_module.aexp.V(a#35#0#0)));

// Constructor $Is
axiom (forall a#36#0#0: Seq Box :: 
  { $Is(#_module.aexp.V(a#36#0#0), Tclass._module.aexp()) } 
  $Is(#_module.aexp.V(a#36#0#0), Tclass._module.aexp())
     <==> $Is(a#36#0#0, TSeq(TChar)));

// Constructor $IsAlloc
axiom (forall a#37#0#0: Seq Box, $h: Heap :: 
  { $IsAlloc(#_module.aexp.V(a#37#0#0), Tclass._module.aexp(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.aexp.V(a#37#0#0), Tclass._module.aexp(), $h)
       <==> $IsAlloc(a#37#0#0, TSeq(TChar), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.aexp.x(d), TSeq(TChar), $h) } 
  $IsGoodHeap($h) && _module.aexp.V_q(d) && $IsAlloc(d, Tclass._module.aexp(), $h)
     ==> $IsAlloc(_module.aexp.x(d), TSeq(TChar), $h));

// Constructor literal
axiom (forall a#38#0#0: Seq Box :: 
  { #_module.aexp.V(Lit(a#38#0#0)) } 
  #_module.aexp.V(Lit(a#38#0#0)) == Lit(#_module.aexp.V(a#38#0#0)));

function _module.aexp.x(DatatypeType) : Seq Box;

// Constructor injectivity
axiom (forall a#39#0#0: Seq Box :: 
  { #_module.aexp.V(a#39#0#0) } 
  _module.aexp.x(#_module.aexp.V(a#39#0#0)) == a#39#0#0);

// Inductive seq element rank
axiom (forall a#40#0#0: Seq Box, i: int :: 
  { Seq#Index(a#40#0#0, i), #_module.aexp.V(a#40#0#0) } 
  0 <= i && i < Seq#Length(a#40#0#0)
     ==> DtRank($Unbox(Seq#Index(a#40#0#0, i)): DatatypeType)
       < DtRank(#_module.aexp.V(a#40#0#0)));

// Inductive seq rank
axiom (forall a#41#0#0: Seq Box :: 
  { #_module.aexp.V(a#41#0#0) } 
  Seq#Rank(a#41#0#0) < DtRank(#_module.aexp.V(a#41#0#0)));

// Constructor function declaration
function #_module.aexp.Plus(DatatypeType, DatatypeType) : DatatypeType;

const unique ##_module.aexp.Plus: DtCtorId;

// Constructor identifier
axiom (forall a#42#0#0: DatatypeType, a#42#1#0: DatatypeType :: 
  { #_module.aexp.Plus(a#42#0#0, a#42#1#0) } 
  DatatypeCtorId(#_module.aexp.Plus(a#42#0#0, a#42#1#0)) == ##_module.aexp.Plus);

function _module.aexp.Plus_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.aexp.Plus_q(d) } 
  _module.aexp.Plus_q(d) <==> DatatypeCtorId(d) == ##_module.aexp.Plus);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.aexp.Plus_q(d) } 
  _module.aexp.Plus_q(d)
     ==> (exists a#43#0#0: DatatypeType, a#43#1#0: DatatypeType :: 
      d == #_module.aexp.Plus(a#43#0#0, a#43#1#0)));

// Constructor $Is
axiom (forall a#44#0#0: DatatypeType, a#44#1#0: DatatypeType :: 
  { $Is(#_module.aexp.Plus(a#44#0#0, a#44#1#0), Tclass._module.aexp()) } 
  $Is(#_module.aexp.Plus(a#44#0#0, a#44#1#0), Tclass._module.aexp())
     <==> $Is(a#44#0#0, Tclass._module.aexp()) && $Is(a#44#1#0, Tclass._module.aexp()));

// Constructor $IsAlloc
axiom (forall a#45#0#0: DatatypeType, a#45#1#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#_module.aexp.Plus(a#45#0#0, a#45#1#0), Tclass._module.aexp(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.aexp.Plus(a#45#0#0, a#45#1#0), Tclass._module.aexp(), $h)
       <==> $IsAlloc(a#45#0#0, Tclass._module.aexp(), $h)
         && $IsAlloc(a#45#1#0, Tclass._module.aexp(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.aexp._0(d), Tclass._module.aexp(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.aexp.Plus_q(d)
       && $IsAlloc(d, Tclass._module.aexp(), $h)
     ==> $IsAlloc(_module.aexp._0(d), Tclass._module.aexp(), $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.aexp._1(d), Tclass._module.aexp(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.aexp.Plus_q(d)
       && $IsAlloc(d, Tclass._module.aexp(), $h)
     ==> $IsAlloc(_module.aexp._1(d), Tclass._module.aexp(), $h));

// Constructor literal
axiom (forall a#46#0#0: DatatypeType, a#46#1#0: DatatypeType :: 
  { #_module.aexp.Plus(Lit(a#46#0#0), Lit(a#46#1#0)) } 
  #_module.aexp.Plus(Lit(a#46#0#0), Lit(a#46#1#0))
     == Lit(#_module.aexp.Plus(a#46#0#0, a#46#1#0)));

function _module.aexp._0(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#47#0#0: DatatypeType, a#47#1#0: DatatypeType :: 
  { #_module.aexp.Plus(a#47#0#0, a#47#1#0) } 
  _module.aexp._0(#_module.aexp.Plus(a#47#0#0, a#47#1#0)) == a#47#0#0);

// Inductive rank
axiom (forall a#48#0#0: DatatypeType, a#48#1#0: DatatypeType :: 
  { #_module.aexp.Plus(a#48#0#0, a#48#1#0) } 
  DtRank(a#48#0#0) < DtRank(#_module.aexp.Plus(a#48#0#0, a#48#1#0)));

function _module.aexp._1(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#49#0#0: DatatypeType, a#49#1#0: DatatypeType :: 
  { #_module.aexp.Plus(a#49#0#0, a#49#1#0) } 
  _module.aexp._1(#_module.aexp.Plus(a#49#0#0, a#49#1#0)) == a#49#1#0);

// Inductive rank
axiom (forall a#50#0#0: DatatypeType, a#50#1#0: DatatypeType :: 
  { #_module.aexp.Plus(a#50#0#0, a#50#1#0) } 
  DtRank(a#50#1#0) < DtRank(#_module.aexp.Plus(a#50#0#0, a#50#1#0)));

// Depth-one case-split function
function $IsA#_module.aexp(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.aexp(d) } 
  $IsA#_module.aexp(d)
     ==> _module.aexp.N_q(d) || _module.aexp.V_q(d) || _module.aexp.Plus_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.aexp.Plus_q(d), $Is(d, Tclass._module.aexp()) } 
    { _module.aexp.V_q(d), $Is(d, Tclass._module.aexp()) } 
    { _module.aexp.N_q(d), $Is(d, Tclass._module.aexp()) } 
  $Is(d, Tclass._module.aexp())
     ==> _module.aexp.N_q(d) || _module.aexp.V_q(d) || _module.aexp.Plus_q(d));

// Datatype extensional equality declaration
function _module.aexp#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.aexp.N
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.aexp#Equal(a, b), _module.aexp.N_q(a) } 
    { _module.aexp#Equal(a, b), _module.aexp.N_q(b) } 
  _module.aexp.N_q(a) && _module.aexp.N_q(b)
     ==> (_module.aexp#Equal(a, b) <==> _module.aexp.n(a) == _module.aexp.n(b)));

// Datatype extensional equality definition: #_module.aexp.V
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.aexp#Equal(a, b), _module.aexp.V_q(a) } 
    { _module.aexp#Equal(a, b), _module.aexp.V_q(b) } 
  _module.aexp.V_q(a) && _module.aexp.V_q(b)
     ==> (_module.aexp#Equal(a, b) <==> Seq#Equal(_module.aexp.x(a), _module.aexp.x(b))));

// Datatype extensional equality definition: #_module.aexp.Plus
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.aexp#Equal(a, b), _module.aexp.Plus_q(a) } 
    { _module.aexp#Equal(a, b), _module.aexp.Plus_q(b) } 
  _module.aexp.Plus_q(a) && _module.aexp.Plus_q(b)
     ==> (_module.aexp#Equal(a, b)
       <==> _module.aexp#Equal(_module.aexp._0(a), _module.aexp._0(b))
         && _module.aexp#Equal(_module.aexp._1(a), _module.aexp._1(b))));

// Datatype extensionality axiom: _module.aexp
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.aexp#Equal(a, b) } 
  _module.aexp#Equal(a, b) <==> a == b);

const unique class._module.aexp: ClassName;

// Constructor function declaration
function #_module.bexp.Bc(bool) : DatatypeType;

const unique ##_module.bexp.Bc: DtCtorId;

// Constructor identifier
axiom (forall a#51#0#0: bool :: 
  { #_module.bexp.Bc(a#51#0#0) } 
  DatatypeCtorId(#_module.bexp.Bc(a#51#0#0)) == ##_module.bexp.Bc);

function _module.bexp.Bc_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.bexp.Bc_q(d) } 
  _module.bexp.Bc_q(d) <==> DatatypeCtorId(d) == ##_module.bexp.Bc);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.bexp.Bc_q(d) } 
  _module.bexp.Bc_q(d)
     ==> (exists a#52#0#0: bool :: d == #_module.bexp.Bc(a#52#0#0)));

function Tclass._module.bexp() : Ty;

const unique Tagclass._module.bexp: TyTag;

// Tclass._module.bexp Tag
axiom Tag(Tclass._module.bexp()) == Tagclass._module.bexp
   && TagFamily(Tclass._module.bexp()) == tytagFamily$bexp;

// Box/unbox axiom for Tclass._module.bexp
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.bexp()) } 
  $IsBox(bx, Tclass._module.bexp())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.bexp()));

// Constructor $Is
axiom (forall a#53#0#0: bool :: 
  { $Is(#_module.bexp.Bc(a#53#0#0), Tclass._module.bexp()) } 
  $Is(#_module.bexp.Bc(a#53#0#0), Tclass._module.bexp()) <==> $Is(a#53#0#0, TBool));

// Constructor $IsAlloc
axiom (forall a#54#0#0: bool, $h: Heap :: 
  { $IsAlloc(#_module.bexp.Bc(a#54#0#0), Tclass._module.bexp(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.bexp.Bc(a#54#0#0), Tclass._module.bexp(), $h)
       <==> $IsAlloc(a#54#0#0, TBool, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.bexp.v(d), TBool, $h) } 
  $IsGoodHeap($h)
       && 
      _module.bexp.Bc_q(d)
       && $IsAlloc(d, Tclass._module.bexp(), $h)
     ==> $IsAlloc(_module.bexp.v(d), TBool, $h));

// Constructor literal
axiom (forall a#55#0#0: bool :: 
  { #_module.bexp.Bc(Lit(a#55#0#0)) } 
  #_module.bexp.Bc(Lit(a#55#0#0)) == Lit(#_module.bexp.Bc(a#55#0#0)));

function _module.bexp.v(DatatypeType) : bool;

// Constructor injectivity
axiom (forall a#56#0#0: bool :: 
  { #_module.bexp.Bc(a#56#0#0) } 
  _module.bexp.v(#_module.bexp.Bc(a#56#0#0)) == a#56#0#0);

// Constructor function declaration
function #_module.bexp.Not(DatatypeType) : DatatypeType;

const unique ##_module.bexp.Not: DtCtorId;

// Constructor identifier
axiom (forall a#57#0#0: DatatypeType :: 
  { #_module.bexp.Not(a#57#0#0) } 
  DatatypeCtorId(#_module.bexp.Not(a#57#0#0)) == ##_module.bexp.Not);

function _module.bexp.Not_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.bexp.Not_q(d) } 
  _module.bexp.Not_q(d) <==> DatatypeCtorId(d) == ##_module.bexp.Not);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.bexp.Not_q(d) } 
  _module.bexp.Not_q(d)
     ==> (exists a#58#0#0: DatatypeType :: d == #_module.bexp.Not(a#58#0#0)));

// Constructor $Is
axiom (forall a#59#0#0: DatatypeType :: 
  { $Is(#_module.bexp.Not(a#59#0#0), Tclass._module.bexp()) } 
  $Is(#_module.bexp.Not(a#59#0#0), Tclass._module.bexp())
     <==> $Is(a#59#0#0, Tclass._module.bexp()));

// Constructor $IsAlloc
axiom (forall a#60#0#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#_module.bexp.Not(a#60#0#0), Tclass._module.bexp(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.bexp.Not(a#60#0#0), Tclass._module.bexp(), $h)
       <==> $IsAlloc(a#60#0#0, Tclass._module.bexp(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.bexp.op(d), Tclass._module.bexp(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.bexp.Not_q(d)
       && $IsAlloc(d, Tclass._module.bexp(), $h)
     ==> $IsAlloc(_module.bexp.op(d), Tclass._module.bexp(), $h));

// Constructor literal
axiom (forall a#61#0#0: DatatypeType :: 
  { #_module.bexp.Not(Lit(a#61#0#0)) } 
  #_module.bexp.Not(Lit(a#61#0#0)) == Lit(#_module.bexp.Not(a#61#0#0)));

function _module.bexp.op(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#62#0#0: DatatypeType :: 
  { #_module.bexp.Not(a#62#0#0) } 
  _module.bexp.op(#_module.bexp.Not(a#62#0#0)) == a#62#0#0);

// Inductive rank
axiom (forall a#63#0#0: DatatypeType :: 
  { #_module.bexp.Not(a#63#0#0) } 
  DtRank(a#63#0#0) < DtRank(#_module.bexp.Not(a#63#0#0)));

// Constructor function declaration
function #_module.bexp.And(DatatypeType, DatatypeType) : DatatypeType;

const unique ##_module.bexp.And: DtCtorId;

// Constructor identifier
axiom (forall a#64#0#0: DatatypeType, a#64#1#0: DatatypeType :: 
  { #_module.bexp.And(a#64#0#0, a#64#1#0) } 
  DatatypeCtorId(#_module.bexp.And(a#64#0#0, a#64#1#0)) == ##_module.bexp.And);

function _module.bexp.And_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.bexp.And_q(d) } 
  _module.bexp.And_q(d) <==> DatatypeCtorId(d) == ##_module.bexp.And);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.bexp.And_q(d) } 
  _module.bexp.And_q(d)
     ==> (exists a#65#0#0: DatatypeType, a#65#1#0: DatatypeType :: 
      d == #_module.bexp.And(a#65#0#0, a#65#1#0)));

// Constructor $Is
axiom (forall a#66#0#0: DatatypeType, a#66#1#0: DatatypeType :: 
  { $Is(#_module.bexp.And(a#66#0#0, a#66#1#0), Tclass._module.bexp()) } 
  $Is(#_module.bexp.And(a#66#0#0, a#66#1#0), Tclass._module.bexp())
     <==> $Is(a#66#0#0, Tclass._module.bexp()) && $Is(a#66#1#0, Tclass._module.bexp()));

// Constructor $IsAlloc
axiom (forall a#67#0#0: DatatypeType, a#67#1#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#_module.bexp.And(a#67#0#0, a#67#1#0), Tclass._module.bexp(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.bexp.And(a#67#0#0, a#67#1#0), Tclass._module.bexp(), $h)
       <==> $IsAlloc(a#67#0#0, Tclass._module.bexp(), $h)
         && $IsAlloc(a#67#1#0, Tclass._module.bexp(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.bexp._0(d), Tclass._module.bexp(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.bexp.And_q(d)
       && $IsAlloc(d, Tclass._module.bexp(), $h)
     ==> $IsAlloc(_module.bexp._0(d), Tclass._module.bexp(), $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.bexp._1(d), Tclass._module.bexp(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.bexp.And_q(d)
       && $IsAlloc(d, Tclass._module.bexp(), $h)
     ==> $IsAlloc(_module.bexp._1(d), Tclass._module.bexp(), $h));

// Constructor literal
axiom (forall a#68#0#0: DatatypeType, a#68#1#0: DatatypeType :: 
  { #_module.bexp.And(Lit(a#68#0#0), Lit(a#68#1#0)) } 
  #_module.bexp.And(Lit(a#68#0#0), Lit(a#68#1#0))
     == Lit(#_module.bexp.And(a#68#0#0, a#68#1#0)));

function _module.bexp._0(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#69#0#0: DatatypeType, a#69#1#0: DatatypeType :: 
  { #_module.bexp.And(a#69#0#0, a#69#1#0) } 
  _module.bexp._0(#_module.bexp.And(a#69#0#0, a#69#1#0)) == a#69#0#0);

// Inductive rank
axiom (forall a#70#0#0: DatatypeType, a#70#1#0: DatatypeType :: 
  { #_module.bexp.And(a#70#0#0, a#70#1#0) } 
  DtRank(a#70#0#0) < DtRank(#_module.bexp.And(a#70#0#0, a#70#1#0)));

function _module.bexp._1(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#71#0#0: DatatypeType, a#71#1#0: DatatypeType :: 
  { #_module.bexp.And(a#71#0#0, a#71#1#0) } 
  _module.bexp._1(#_module.bexp.And(a#71#0#0, a#71#1#0)) == a#71#1#0);

// Inductive rank
axiom (forall a#72#0#0: DatatypeType, a#72#1#0: DatatypeType :: 
  { #_module.bexp.And(a#72#0#0, a#72#1#0) } 
  DtRank(a#72#1#0) < DtRank(#_module.bexp.And(a#72#0#0, a#72#1#0)));

// Constructor function declaration
function #_module.bexp.Less(DatatypeType, DatatypeType) : DatatypeType;

const unique ##_module.bexp.Less: DtCtorId;

// Constructor identifier
axiom (forall a#73#0#0: DatatypeType, a#73#1#0: DatatypeType :: 
  { #_module.bexp.Less(a#73#0#0, a#73#1#0) } 
  DatatypeCtorId(#_module.bexp.Less(a#73#0#0, a#73#1#0)) == ##_module.bexp.Less);

function _module.bexp.Less_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.bexp.Less_q(d) } 
  _module.bexp.Less_q(d) <==> DatatypeCtorId(d) == ##_module.bexp.Less);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.bexp.Less_q(d) } 
  _module.bexp.Less_q(d)
     ==> (exists a#74#0#0: DatatypeType, a#74#1#0: DatatypeType :: 
      d == #_module.bexp.Less(a#74#0#0, a#74#1#0)));

// Constructor $Is
axiom (forall a#75#0#0: DatatypeType, a#75#1#0: DatatypeType :: 
  { $Is(#_module.bexp.Less(a#75#0#0, a#75#1#0), Tclass._module.bexp()) } 
  $Is(#_module.bexp.Less(a#75#0#0, a#75#1#0), Tclass._module.bexp())
     <==> $Is(a#75#0#0, Tclass._module.aexp()) && $Is(a#75#1#0, Tclass._module.aexp()));

// Constructor $IsAlloc
axiom (forall a#76#0#0: DatatypeType, a#76#1#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#_module.bexp.Less(a#76#0#0, a#76#1#0), Tclass._module.bexp(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.bexp.Less(a#76#0#0, a#76#1#0), Tclass._module.bexp(), $h)
       <==> $IsAlloc(a#76#0#0, Tclass._module.aexp(), $h)
         && $IsAlloc(a#76#1#0, Tclass._module.aexp(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.bexp.a0(d), Tclass._module.aexp(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.bexp.Less_q(d)
       && $IsAlloc(d, Tclass._module.bexp(), $h)
     ==> $IsAlloc(_module.bexp.a0(d), Tclass._module.aexp(), $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.bexp.a1(d), Tclass._module.aexp(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.bexp.Less_q(d)
       && $IsAlloc(d, Tclass._module.bexp(), $h)
     ==> $IsAlloc(_module.bexp.a1(d), Tclass._module.aexp(), $h));

// Constructor literal
axiom (forall a#77#0#0: DatatypeType, a#77#1#0: DatatypeType :: 
  { #_module.bexp.Less(Lit(a#77#0#0), Lit(a#77#1#0)) } 
  #_module.bexp.Less(Lit(a#77#0#0), Lit(a#77#1#0))
     == Lit(#_module.bexp.Less(a#77#0#0, a#77#1#0)));

function _module.bexp.a0(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#78#0#0: DatatypeType, a#78#1#0: DatatypeType :: 
  { #_module.bexp.Less(a#78#0#0, a#78#1#0) } 
  _module.bexp.a0(#_module.bexp.Less(a#78#0#0, a#78#1#0)) == a#78#0#0);

// Inductive rank
axiom (forall a#79#0#0: DatatypeType, a#79#1#0: DatatypeType :: 
  { #_module.bexp.Less(a#79#0#0, a#79#1#0) } 
  DtRank(a#79#0#0) < DtRank(#_module.bexp.Less(a#79#0#0, a#79#1#0)));

function _module.bexp.a1(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#80#0#0: DatatypeType, a#80#1#0: DatatypeType :: 
  { #_module.bexp.Less(a#80#0#0, a#80#1#0) } 
  _module.bexp.a1(#_module.bexp.Less(a#80#0#0, a#80#1#0)) == a#80#1#0);

// Inductive rank
axiom (forall a#81#0#0: DatatypeType, a#81#1#0: DatatypeType :: 
  { #_module.bexp.Less(a#81#0#0, a#81#1#0) } 
  DtRank(a#81#1#0) < DtRank(#_module.bexp.Less(a#81#0#0, a#81#1#0)));

// Depth-one case-split function
function $IsA#_module.bexp(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.bexp(d) } 
  $IsA#_module.bexp(d)
     ==> _module.bexp.Bc_q(d)
       || _module.bexp.Not_q(d)
       || _module.bexp.And_q(d)
       || _module.bexp.Less_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.bexp.Less_q(d), $Is(d, Tclass._module.bexp()) } 
    { _module.bexp.And_q(d), $Is(d, Tclass._module.bexp()) } 
    { _module.bexp.Not_q(d), $Is(d, Tclass._module.bexp()) } 
    { _module.bexp.Bc_q(d), $Is(d, Tclass._module.bexp()) } 
  $Is(d, Tclass._module.bexp())
     ==> _module.bexp.Bc_q(d)
       || _module.bexp.Not_q(d)
       || _module.bexp.And_q(d)
       || _module.bexp.Less_q(d));

// Datatype extensional equality declaration
function _module.bexp#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.bexp.Bc
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.bexp#Equal(a, b), _module.bexp.Bc_q(a) } 
    { _module.bexp#Equal(a, b), _module.bexp.Bc_q(b) } 
  _module.bexp.Bc_q(a) && _module.bexp.Bc_q(b)
     ==> (_module.bexp#Equal(a, b) <==> _module.bexp.v(a) == _module.bexp.v(b)));

// Datatype extensional equality definition: #_module.bexp.Not
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.bexp#Equal(a, b), _module.bexp.Not_q(a) } 
    { _module.bexp#Equal(a, b), _module.bexp.Not_q(b) } 
  _module.bexp.Not_q(a) && _module.bexp.Not_q(b)
     ==> (_module.bexp#Equal(a, b)
       <==> _module.bexp#Equal(_module.bexp.op(a), _module.bexp.op(b))));

// Datatype extensional equality definition: #_module.bexp.And
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.bexp#Equal(a, b), _module.bexp.And_q(a) } 
    { _module.bexp#Equal(a, b), _module.bexp.And_q(b) } 
  _module.bexp.And_q(a) && _module.bexp.And_q(b)
     ==> (_module.bexp#Equal(a, b)
       <==> _module.bexp#Equal(_module.bexp._0(a), _module.bexp._0(b))
         && _module.bexp#Equal(_module.bexp._1(a), _module.bexp._1(b))));

// Datatype extensional equality definition: #_module.bexp.Less
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.bexp#Equal(a, b), _module.bexp.Less_q(a) } 
    { _module.bexp#Equal(a, b), _module.bexp.Less_q(b) } 
  _module.bexp.Less_q(a) && _module.bexp.Less_q(b)
     ==> (_module.bexp#Equal(a, b)
       <==> _module.aexp#Equal(_module.bexp.a0(a), _module.bexp.a0(b))
         && _module.aexp#Equal(_module.bexp.a1(a), _module.bexp.a1(b))));

// Datatype extensionality axiom: _module.bexp
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.bexp#Equal(a, b) } 
  _module.bexp#Equal(a, b) <==> a == b);

const unique class._module.bexp: ClassName;

// Constructor function declaration
function #_module.com.SKIP() : DatatypeType;

const unique ##_module.com.SKIP: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#_module.com.SKIP()) == ##_module.com.SKIP;

function _module.com.SKIP_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.com.SKIP_q(d) } 
  _module.com.SKIP_q(d) <==> DatatypeCtorId(d) == ##_module.com.SKIP);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.com.SKIP_q(d) } 
  _module.com.SKIP_q(d) ==> d == #_module.com.SKIP());

function Tclass._module.com() : Ty;

const unique Tagclass._module.com: TyTag;

// Tclass._module.com Tag
axiom Tag(Tclass._module.com()) == Tagclass._module.com
   && TagFamily(Tclass._module.com()) == tytagFamily$com;

// Box/unbox axiom for Tclass._module.com
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.com()) } 
  $IsBox(bx, Tclass._module.com())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.com()));

// Constructor $Is
axiom $Is(#_module.com.SKIP(), Tclass._module.com());

// Constructor $IsAlloc
axiom (forall $h: Heap :: 
  { $IsAlloc(#_module.com.SKIP(), Tclass._module.com(), $h) } 
  $IsGoodHeap($h) ==> $IsAlloc(#_module.com.SKIP(), Tclass._module.com(), $h));

// Constructor literal
axiom #_module.com.SKIP() == Lit(#_module.com.SKIP());

// Constructor function declaration
function #_module.com.Assign(Seq Box, DatatypeType) : DatatypeType;

const unique ##_module.com.Assign: DtCtorId;

// Constructor identifier
axiom (forall a#87#0#0: Seq Box, a#87#1#0: DatatypeType :: 
  { #_module.com.Assign(a#87#0#0, a#87#1#0) } 
  DatatypeCtorId(#_module.com.Assign(a#87#0#0, a#87#1#0)) == ##_module.com.Assign);

function _module.com.Assign_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.com.Assign_q(d) } 
  _module.com.Assign_q(d) <==> DatatypeCtorId(d) == ##_module.com.Assign);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.com.Assign_q(d) } 
  _module.com.Assign_q(d)
     ==> (exists a#88#0#0: Seq Box, a#88#1#0: DatatypeType :: 
      d == #_module.com.Assign(a#88#0#0, a#88#1#0)));

// Constructor $Is
axiom (forall a#89#0#0: Seq Box, a#89#1#0: DatatypeType :: 
  { $Is(#_module.com.Assign(a#89#0#0, a#89#1#0), Tclass._module.com()) } 
  $Is(#_module.com.Assign(a#89#0#0, a#89#1#0), Tclass._module.com())
     <==> $Is(a#89#0#0, TSeq(TChar)) && $Is(a#89#1#0, Tclass._module.aexp()));

// Constructor $IsAlloc
axiom (forall a#90#0#0: Seq Box, a#90#1#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#_module.com.Assign(a#90#0#0, a#90#1#0), Tclass._module.com(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.com.Assign(a#90#0#0, a#90#1#0), Tclass._module.com(), $h)
       <==> $IsAlloc(a#90#0#0, TSeq(TChar), $h)
         && $IsAlloc(a#90#1#0, Tclass._module.aexp(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.com._h0(d), TSeq(TChar), $h) } 
  $IsGoodHeap($h)
       && 
      _module.com.Assign_q(d)
       && $IsAlloc(d, Tclass._module.com(), $h)
     ==> $IsAlloc(_module.com._h0(d), TSeq(TChar), $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.com._h1(d), Tclass._module.aexp(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.com.Assign_q(d)
       && $IsAlloc(d, Tclass._module.com(), $h)
     ==> $IsAlloc(_module.com._h1(d), Tclass._module.aexp(), $h));

// Constructor literal
axiom (forall a#91#0#0: Seq Box, a#91#1#0: DatatypeType :: 
  { #_module.com.Assign(Lit(a#91#0#0), Lit(a#91#1#0)) } 
  #_module.com.Assign(Lit(a#91#0#0), Lit(a#91#1#0))
     == Lit(#_module.com.Assign(a#91#0#0, a#91#1#0)));

function _module.com._h0(DatatypeType) : Seq Box;

// Constructor injectivity
axiom (forall a#92#0#0: Seq Box, a#92#1#0: DatatypeType :: 
  { #_module.com.Assign(a#92#0#0, a#92#1#0) } 
  _module.com._h0(#_module.com.Assign(a#92#0#0, a#92#1#0)) == a#92#0#0);

// Inductive seq element rank
axiom (forall a#93#0#0: Seq Box, a#93#1#0: DatatypeType, i: int :: 
  { Seq#Index(a#93#0#0, i), #_module.com.Assign(a#93#0#0, a#93#1#0) } 
  0 <= i && i < Seq#Length(a#93#0#0)
     ==> DtRank($Unbox(Seq#Index(a#93#0#0, i)): DatatypeType)
       < DtRank(#_module.com.Assign(a#93#0#0, a#93#1#0)));

// Inductive seq rank
axiom (forall a#94#0#0: Seq Box, a#94#1#0: DatatypeType :: 
  { #_module.com.Assign(a#94#0#0, a#94#1#0) } 
  Seq#Rank(a#94#0#0) < DtRank(#_module.com.Assign(a#94#0#0, a#94#1#0)));

function _module.com._h1(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#95#0#0: Seq Box, a#95#1#0: DatatypeType :: 
  { #_module.com.Assign(a#95#0#0, a#95#1#0) } 
  _module.com._h1(#_module.com.Assign(a#95#0#0, a#95#1#0)) == a#95#1#0);

// Inductive rank
axiom (forall a#96#0#0: Seq Box, a#96#1#0: DatatypeType :: 
  { #_module.com.Assign(a#96#0#0, a#96#1#0) } 
  DtRank(a#96#1#0) < DtRank(#_module.com.Assign(a#96#0#0, a#96#1#0)));

// Constructor function declaration
function #_module.com.Seq(DatatypeType, DatatypeType) : DatatypeType;

const unique ##_module.com.Seq: DtCtorId;

// Constructor identifier
axiom (forall a#97#0#0: DatatypeType, a#97#1#0: DatatypeType :: 
  { #_module.com.Seq(a#97#0#0, a#97#1#0) } 
  DatatypeCtorId(#_module.com.Seq(a#97#0#0, a#97#1#0)) == ##_module.com.Seq);

function _module.com.Seq_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.com.Seq_q(d) } 
  _module.com.Seq_q(d) <==> DatatypeCtorId(d) == ##_module.com.Seq);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.com.Seq_q(d) } 
  _module.com.Seq_q(d)
     ==> (exists a#98#0#0: DatatypeType, a#98#1#0: DatatypeType :: 
      d == #_module.com.Seq(a#98#0#0, a#98#1#0)));

// Constructor $Is
axiom (forall a#99#0#0: DatatypeType, a#99#1#0: DatatypeType :: 
  { $Is(#_module.com.Seq(a#99#0#0, a#99#1#0), Tclass._module.com()) } 
  $Is(#_module.com.Seq(a#99#0#0, a#99#1#0), Tclass._module.com())
     <==> $Is(a#99#0#0, Tclass._module.com()) && $Is(a#99#1#0, Tclass._module.com()));

// Constructor $IsAlloc
axiom (forall a#100#0#0: DatatypeType, a#100#1#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#_module.com.Seq(a#100#0#0, a#100#1#0), Tclass._module.com(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.com.Seq(a#100#0#0, a#100#1#0), Tclass._module.com(), $h)
       <==> $IsAlloc(a#100#0#0, Tclass._module.com(), $h)
         && $IsAlloc(a#100#1#0, Tclass._module.com(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.com._h2(d), Tclass._module.com(), $h) } 
  $IsGoodHeap($h) && _module.com.Seq_q(d) && $IsAlloc(d, Tclass._module.com(), $h)
     ==> $IsAlloc(_module.com._h2(d), Tclass._module.com(), $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.com._h3(d), Tclass._module.com(), $h) } 
  $IsGoodHeap($h) && _module.com.Seq_q(d) && $IsAlloc(d, Tclass._module.com(), $h)
     ==> $IsAlloc(_module.com._h3(d), Tclass._module.com(), $h));

// Constructor literal
axiom (forall a#101#0#0: DatatypeType, a#101#1#0: DatatypeType :: 
  { #_module.com.Seq(Lit(a#101#0#0), Lit(a#101#1#0)) } 
  #_module.com.Seq(Lit(a#101#0#0), Lit(a#101#1#0))
     == Lit(#_module.com.Seq(a#101#0#0, a#101#1#0)));

function _module.com._h2(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#102#0#0: DatatypeType, a#102#1#0: DatatypeType :: 
  { #_module.com.Seq(a#102#0#0, a#102#1#0) } 
  _module.com._h2(#_module.com.Seq(a#102#0#0, a#102#1#0)) == a#102#0#0);

// Inductive rank
axiom (forall a#103#0#0: DatatypeType, a#103#1#0: DatatypeType :: 
  { #_module.com.Seq(a#103#0#0, a#103#1#0) } 
  DtRank(a#103#0#0) < DtRank(#_module.com.Seq(a#103#0#0, a#103#1#0)));

function _module.com._h3(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#104#0#0: DatatypeType, a#104#1#0: DatatypeType :: 
  { #_module.com.Seq(a#104#0#0, a#104#1#0) } 
  _module.com._h3(#_module.com.Seq(a#104#0#0, a#104#1#0)) == a#104#1#0);

// Inductive rank
axiom (forall a#105#0#0: DatatypeType, a#105#1#0: DatatypeType :: 
  { #_module.com.Seq(a#105#0#0, a#105#1#0) } 
  DtRank(a#105#1#0) < DtRank(#_module.com.Seq(a#105#0#0, a#105#1#0)));

// Constructor function declaration
function #_module.com.If(DatatypeType, DatatypeType, DatatypeType) : DatatypeType;

const unique ##_module.com.If: DtCtorId;

// Constructor identifier
axiom (forall a#106#0#0: DatatypeType, a#106#1#0: DatatypeType, a#106#2#0: DatatypeType :: 
  { #_module.com.If(a#106#0#0, a#106#1#0, a#106#2#0) } 
  DatatypeCtorId(#_module.com.If(a#106#0#0, a#106#1#0, a#106#2#0))
     == ##_module.com.If);

function _module.com.If_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.com.If_q(d) } 
  _module.com.If_q(d) <==> DatatypeCtorId(d) == ##_module.com.If);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.com.If_q(d) } 
  _module.com.If_q(d)
     ==> (exists a#107#0#0: DatatypeType, a#107#1#0: DatatypeType, a#107#2#0: DatatypeType :: 
      d == #_module.com.If(a#107#0#0, a#107#1#0, a#107#2#0)));

// Constructor $Is
axiom (forall a#108#0#0: DatatypeType, a#108#1#0: DatatypeType, a#108#2#0: DatatypeType :: 
  { $Is(#_module.com.If(a#108#0#0, a#108#1#0, a#108#2#0), Tclass._module.com()) } 
  $Is(#_module.com.If(a#108#0#0, a#108#1#0, a#108#2#0), Tclass._module.com())
     <==> $Is(a#108#0#0, Tclass._module.bexp())
       && $Is(a#108#1#0, Tclass._module.com())
       && $Is(a#108#2#0, Tclass._module.com()));

// Constructor $IsAlloc
axiom (forall a#109#0#0: DatatypeType, 
    a#109#1#0: DatatypeType, 
    a#109#2#0: DatatypeType, 
    $h: Heap :: 
  { $IsAlloc(#_module.com.If(a#109#0#0, a#109#1#0, a#109#2#0), Tclass._module.com(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.com.If(a#109#0#0, a#109#1#0, a#109#2#0), Tclass._module.com(), $h)
       <==> $IsAlloc(a#109#0#0, Tclass._module.bexp(), $h)
         && $IsAlloc(a#109#1#0, Tclass._module.com(), $h)
         && $IsAlloc(a#109#2#0, Tclass._module.com(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.com._h4(d), Tclass._module.bexp(), $h) } 
  $IsGoodHeap($h) && _module.com.If_q(d) && $IsAlloc(d, Tclass._module.com(), $h)
     ==> $IsAlloc(_module.com._h4(d), Tclass._module.bexp(), $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.com._h5(d), Tclass._module.com(), $h) } 
  $IsGoodHeap($h) && _module.com.If_q(d) && $IsAlloc(d, Tclass._module.com(), $h)
     ==> $IsAlloc(_module.com._h5(d), Tclass._module.com(), $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.com._h6(d), Tclass._module.com(), $h) } 
  $IsGoodHeap($h) && _module.com.If_q(d) && $IsAlloc(d, Tclass._module.com(), $h)
     ==> $IsAlloc(_module.com._h6(d), Tclass._module.com(), $h));

// Constructor literal
axiom (forall a#110#0#0: DatatypeType, a#110#1#0: DatatypeType, a#110#2#0: DatatypeType :: 
  { #_module.com.If(Lit(a#110#0#0), Lit(a#110#1#0), Lit(a#110#2#0)) } 
  #_module.com.If(Lit(a#110#0#0), Lit(a#110#1#0), Lit(a#110#2#0))
     == Lit(#_module.com.If(a#110#0#0, a#110#1#0, a#110#2#0)));

function _module.com._h4(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#111#0#0: DatatypeType, a#111#1#0: DatatypeType, a#111#2#0: DatatypeType :: 
  { #_module.com.If(a#111#0#0, a#111#1#0, a#111#2#0) } 
  _module.com._h4(#_module.com.If(a#111#0#0, a#111#1#0, a#111#2#0)) == a#111#0#0);

// Inductive rank
axiom (forall a#112#0#0: DatatypeType, a#112#1#0: DatatypeType, a#112#2#0: DatatypeType :: 
  { #_module.com.If(a#112#0#0, a#112#1#0, a#112#2#0) } 
  DtRank(a#112#0#0) < DtRank(#_module.com.If(a#112#0#0, a#112#1#0, a#112#2#0)));

function _module.com._h5(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#113#0#0: DatatypeType, a#113#1#0: DatatypeType, a#113#2#0: DatatypeType :: 
  { #_module.com.If(a#113#0#0, a#113#1#0, a#113#2#0) } 
  _module.com._h5(#_module.com.If(a#113#0#0, a#113#1#0, a#113#2#0)) == a#113#1#0);

// Inductive rank
axiom (forall a#114#0#0: DatatypeType, a#114#1#0: DatatypeType, a#114#2#0: DatatypeType :: 
  { #_module.com.If(a#114#0#0, a#114#1#0, a#114#2#0) } 
  DtRank(a#114#1#0) < DtRank(#_module.com.If(a#114#0#0, a#114#1#0, a#114#2#0)));

function _module.com._h6(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#115#0#0: DatatypeType, a#115#1#0: DatatypeType, a#115#2#0: DatatypeType :: 
  { #_module.com.If(a#115#0#0, a#115#1#0, a#115#2#0) } 
  _module.com._h6(#_module.com.If(a#115#0#0, a#115#1#0, a#115#2#0)) == a#115#2#0);

// Inductive rank
axiom (forall a#116#0#0: DatatypeType, a#116#1#0: DatatypeType, a#116#2#0: DatatypeType :: 
  { #_module.com.If(a#116#0#0, a#116#1#0, a#116#2#0) } 
  DtRank(a#116#2#0) < DtRank(#_module.com.If(a#116#0#0, a#116#1#0, a#116#2#0)));

// Constructor function declaration
function #_module.com.While(DatatypeType, DatatypeType) : DatatypeType;

const unique ##_module.com.While: DtCtorId;

// Constructor identifier
axiom (forall a#117#0#0: DatatypeType, a#117#1#0: DatatypeType :: 
  { #_module.com.While(a#117#0#0, a#117#1#0) } 
  DatatypeCtorId(#_module.com.While(a#117#0#0, a#117#1#0)) == ##_module.com.While);

function _module.com.While_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.com.While_q(d) } 
  _module.com.While_q(d) <==> DatatypeCtorId(d) == ##_module.com.While);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.com.While_q(d) } 
  _module.com.While_q(d)
     ==> (exists a#118#0#0: DatatypeType, a#118#1#0: DatatypeType :: 
      d == #_module.com.While(a#118#0#0, a#118#1#0)));

// Constructor $Is
axiom (forall a#119#0#0: DatatypeType, a#119#1#0: DatatypeType :: 
  { $Is(#_module.com.While(a#119#0#0, a#119#1#0), Tclass._module.com()) } 
  $Is(#_module.com.While(a#119#0#0, a#119#1#0), Tclass._module.com())
     <==> $Is(a#119#0#0, Tclass._module.bexp()) && $Is(a#119#1#0, Tclass._module.com()));

// Constructor $IsAlloc
axiom (forall a#120#0#0: DatatypeType, a#120#1#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#_module.com.While(a#120#0#0, a#120#1#0), Tclass._module.com(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.com.While(a#120#0#0, a#120#1#0), Tclass._module.com(), $h)
       <==> $IsAlloc(a#120#0#0, Tclass._module.bexp(), $h)
         && $IsAlloc(a#120#1#0, Tclass._module.com(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.com._h7(d), Tclass._module.bexp(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.com.While_q(d)
       && $IsAlloc(d, Tclass._module.com(), $h)
     ==> $IsAlloc(_module.com._h7(d), Tclass._module.bexp(), $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.com._h8(d), Tclass._module.com(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.com.While_q(d)
       && $IsAlloc(d, Tclass._module.com(), $h)
     ==> $IsAlloc(_module.com._h8(d), Tclass._module.com(), $h));

// Constructor literal
axiom (forall a#121#0#0: DatatypeType, a#121#1#0: DatatypeType :: 
  { #_module.com.While(Lit(a#121#0#0), Lit(a#121#1#0)) } 
  #_module.com.While(Lit(a#121#0#0), Lit(a#121#1#0))
     == Lit(#_module.com.While(a#121#0#0, a#121#1#0)));

function _module.com._h7(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#122#0#0: DatatypeType, a#122#1#0: DatatypeType :: 
  { #_module.com.While(a#122#0#0, a#122#1#0) } 
  _module.com._h7(#_module.com.While(a#122#0#0, a#122#1#0)) == a#122#0#0);

// Inductive rank
axiom (forall a#123#0#0: DatatypeType, a#123#1#0: DatatypeType :: 
  { #_module.com.While(a#123#0#0, a#123#1#0) } 
  DtRank(a#123#0#0) < DtRank(#_module.com.While(a#123#0#0, a#123#1#0)));

function _module.com._h8(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#124#0#0: DatatypeType, a#124#1#0: DatatypeType :: 
  { #_module.com.While(a#124#0#0, a#124#1#0) } 
  _module.com._h8(#_module.com.While(a#124#0#0, a#124#1#0)) == a#124#1#0);

// Inductive rank
axiom (forall a#125#0#0: DatatypeType, a#125#1#0: DatatypeType :: 
  { #_module.com.While(a#125#0#0, a#125#1#0) } 
  DtRank(a#125#1#0) < DtRank(#_module.com.While(a#125#0#0, a#125#1#0)));

// Depth-one case-split function
function $IsA#_module.com(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.com(d) } 
  $IsA#_module.com(d)
     ==> _module.com.SKIP_q(d)
       || _module.com.Assign_q(d)
       || _module.com.Seq_q(d)
       || _module.com.If_q(d)
       || _module.com.While_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.com.While_q(d), $Is(d, Tclass._module.com()) } 
    { _module.com.If_q(d), $Is(d, Tclass._module.com()) } 
    { _module.com.Seq_q(d), $Is(d, Tclass._module.com()) } 
    { _module.com.Assign_q(d), $Is(d, Tclass._module.com()) } 
    { _module.com.SKIP_q(d), $Is(d, Tclass._module.com()) } 
  $Is(d, Tclass._module.com())
     ==> _module.com.SKIP_q(d)
       || _module.com.Assign_q(d)
       || _module.com.Seq_q(d)
       || _module.com.If_q(d)
       || _module.com.While_q(d));

// Datatype extensional equality declaration
function _module.com#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.com.SKIP
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.com#Equal(a, b), _module.com.SKIP_q(a) } 
    { _module.com#Equal(a, b), _module.com.SKIP_q(b) } 
  _module.com.SKIP_q(a) && _module.com.SKIP_q(b)
     ==> (_module.com#Equal(a, b) <==> true));

// Datatype extensional equality definition: #_module.com.Assign
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.com#Equal(a, b), _module.com.Assign_q(a) } 
    { _module.com#Equal(a, b), _module.com.Assign_q(b) } 
  _module.com.Assign_q(a) && _module.com.Assign_q(b)
     ==> (_module.com#Equal(a, b)
       <==> Seq#Equal(_module.com._h0(a), _module.com._h0(b))
         && _module.aexp#Equal(_module.com._h1(a), _module.com._h1(b))));

// Datatype extensional equality definition: #_module.com.Seq
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.com#Equal(a, b), _module.com.Seq_q(a) } 
    { _module.com#Equal(a, b), _module.com.Seq_q(b) } 
  _module.com.Seq_q(a) && _module.com.Seq_q(b)
     ==> (_module.com#Equal(a, b)
       <==> _module.com#Equal(_module.com._h2(a), _module.com._h2(b))
         && _module.com#Equal(_module.com._h3(a), _module.com._h3(b))));

// Datatype extensional equality definition: #_module.com.If
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.com#Equal(a, b), _module.com.If_q(a) } 
    { _module.com#Equal(a, b), _module.com.If_q(b) } 
  _module.com.If_q(a) && _module.com.If_q(b)
     ==> (_module.com#Equal(a, b)
       <==> _module.bexp#Equal(_module.com._h4(a), _module.com._h4(b))
         && _module.com#Equal(_module.com._h5(a), _module.com._h5(b))
         && _module.com#Equal(_module.com._h6(a), _module.com._h6(b))));

// Datatype extensional equality definition: #_module.com.While
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.com#Equal(a, b), _module.com.While_q(a) } 
    { _module.com#Equal(a, b), _module.com.While_q(b) } 
  _module.com.While_q(a) && _module.com.While_q(b)
     ==> (_module.com#Equal(a, b)
       <==> _module.bexp#Equal(_module.com._h7(a), _module.com._h7(b))
         && _module.com#Equal(_module.com._h8(a), _module.com._h8(b))));

// Datatype extensionality axiom: _module.com
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.com#Equal(a, b) } 
  _module.com#Equal(a, b) <==> a == b);

const unique class._module.com: ClassName;

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

// function declaration for _module._default.aval
function _module.__default.aval($ly: LayerType, a#0: DatatypeType, s#0: Map Box Box) : int;

function _module.__default.aval#canCall(a#0: DatatypeType, s#0: Map Box Box) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, a#0: DatatypeType, s#0: Map Box Box :: 
  { _module.__default.aval($LS($ly), a#0, s#0) } 
  _module.__default.aval($LS($ly), a#0, s#0)
     == _module.__default.aval($ly, a#0, s#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, a#0: DatatypeType, s#0: Map Box Box :: 
  { _module.__default.aval(AsFuelBottom($ly), a#0, s#0) } 
  _module.__default.aval($ly, a#0, s#0) == _module.__default.aval($LZ, a#0, s#0));

// consequence axiom for _module.__default.aval
axiom 6 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, a#0: DatatypeType, s#0: Map Box Box :: 
    { _module.__default.aval($ly, a#0, s#0) } 
    _module.__default.aval#canCall(a#0, s#0)
         || (6 != $FunctionContextHeight
           && 
          $Is(a#0, Tclass._module.aexp())
           && $Is(s#0, TMap(TSeq(TChar), TInt)))
       ==> true);

function _module.__default.aval#requires(LayerType, DatatypeType, Map Box Box) : bool;

// #requires axiom for _module.__default.aval
axiom (forall $ly: LayerType, a#0: DatatypeType, s#0: Map Box Box :: 
  { _module.__default.aval#requires($ly, a#0, s#0) } 
  $Is(a#0, Tclass._module.aexp()) && $Is(s#0, TMap(TSeq(TChar), TInt))
     ==> _module.__default.aval#requires($ly, a#0, s#0) == true);

// definition axiom for _module.__default.aval (revealed)
axiom 6 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, a#0: DatatypeType, s#0: Map Box Box :: 
    { _module.__default.aval($LS($ly), a#0, s#0) } 
    _module.__default.aval#canCall(a#0, s#0)
         || (6 != $FunctionContextHeight
           && 
          $Is(a#0, Tclass._module.aexp())
           && $Is(s#0, TMap(TSeq(TChar), TInt)))
       ==> (!_module.aexp.N_q(a#0)
           ==> 
          !_module.aexp.V_q(a#0)
           ==> (var a1#1 := _module.aexp._1(a#0); 
            (var a0#1 := _module.aexp._0(a#0); 
              _module.__default.aval#canCall(a0#1, s#0)
                 && _module.__default.aval#canCall(a1#1, s#0))))
         && _module.__default.aval($LS($ly), a#0, s#0)
           == (if _module.aexp.N_q(a#0)
             then (var n#0 := _module.aexp.n(a#0); n#0)
             else (if _module.aexp.V_q(a#0)
               then (var x#0 := _module.aexp.x(a#0); 
                (if Map#Domain(s#0)[$Box(x#0)]
                   then $Unbox(Map#Elements(s#0)[$Box(x#0)]): int
                   else 0))
               else (var a1#0 := _module.aexp._1(a#0); 
                (var a0#0 := _module.aexp._0(a#0); 
                  _module.__default.aval($ly, a0#0, s#0) + _module.__default.aval($ly, a1#0, s#0))))));

// definition axiom for _module.__default.aval for all literals (revealed)
axiom 6 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, a#0: DatatypeType, s#0: Map Box Box :: 
    {:weight 3} { _module.__default.aval($LS($ly), Lit(a#0), Lit(s#0)) } 
    _module.__default.aval#canCall(Lit(a#0), Lit(s#0))
         || (6 != $FunctionContextHeight
           && 
          $Is(a#0, Tclass._module.aexp())
           && $Is(s#0, TMap(TSeq(TChar), TInt)))
       ==> (!Lit(_module.aexp.N_q(Lit(a#0)))
           ==> 
          !Lit(_module.aexp.V_q(Lit(a#0)))
           ==> (var a1#3 := Lit(_module.aexp._1(Lit(a#0))); 
            (var a0#3 := Lit(_module.aexp._0(Lit(a#0))); 
              _module.__default.aval#canCall(a0#3, Lit(s#0))
                 && _module.__default.aval#canCall(a1#3, Lit(s#0)))))
         && _module.__default.aval($LS($ly), Lit(a#0), Lit(s#0))
           == (if _module.aexp.N_q(Lit(a#0))
             then (var n#2 := LitInt(_module.aexp.n(Lit(a#0))); n#2)
             else (if _module.aexp.V_q(Lit(a#0))
               then (var x#2 := Lit(_module.aexp.x(Lit(a#0))); 
                (if Map#Domain(s#0)[$Box(x#2)]
                   then $Unbox(Map#Elements(Lit(s#0))[$Box(x#2)]): int
                   else 0))
               else (var a1#2 := Lit(_module.aexp._1(Lit(a#0))); 
                (var a0#2 := Lit(_module.aexp._0(Lit(a#0))); 
                  LitInt(_module.__default.aval($LS($ly), a0#2, Lit(s#0))
                       + _module.__default.aval($LS($ly), a1#2, Lit(s#0))))))));

procedure CheckWellformed$$_module.__default.aval(a#0: DatatypeType where $Is(a#0, Tclass._module.aexp()), 
    s#0: Map Box Box where $Is(s#0, TMap(TSeq(TChar), TInt)));
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.aval(a#0: DatatypeType, s#0: Map Box Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#2#0: DatatypeType;
  var _mcc#3#0: DatatypeType;
  var a1#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var a0#Z#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var ##a#0: DatatypeType;
  var ##s#0: Map Box Box;
  var ##a#1: DatatypeType;
  var ##s#1: Map Box Box;
  var _mcc#1#0: Seq Box;
  var x#Z#0: Seq Box;
  var let#2#0#0: Seq Box;
  var _mcc#0#0: int;
  var n#Z#0: int;
  var let#3#0#0: int;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function aval
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(16,9): initial state"} true;
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
        if (a#0 == #_module.aexp.N(_mcc#0#0))
        {
            havoc n#Z#0;
            assume true;
            assume let#3#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#3#0#0, TInt);
            assume n#Z#0 == let#3#0#0;
            assume _module.__default.aval($LS($LZ), a#0, s#0) == n#Z#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.aval($LS($LZ), a#0, s#0), TInt);
        }
        else if (a#0 == #_module.aexp.V(_mcc#1#0))
        {
            assume $Is(_mcc#1#0, TSeq(TChar));
            havoc x#Z#0;
            assume $Is(x#Z#0, TSeq(TChar));
            assume let#2#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#2#0#0, TSeq(TChar));
            assume x#Z#0 == let#2#0#0;
            if (Map#Domain(s#0)[$Box(x#Z#0)])
            {
                assert Map#Domain(s#0)[$Box(x#Z#0)];
                assume _module.__default.aval($LS($LZ), a#0, s#0)
                   == $Unbox(Map#Elements(s#0)[$Box(x#Z#0)]): int;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.aval($LS($LZ), a#0, s#0), TInt);
            }
            else
            {
                assume _module.__default.aval($LS($LZ), a#0, s#0) == LitInt(0);
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.aval($LS($LZ), a#0, s#0), TInt);
            }
        }
        else if (a#0 == #_module.aexp.Plus(_mcc#2#0, _mcc#3#0))
        {
            assume $Is(_mcc#2#0, Tclass._module.aexp());
            assume $Is(_mcc#3#0, Tclass._module.aexp());
            havoc a1#Z#0;
            assume $Is(a1#Z#0, Tclass._module.aexp());
            assume let#0#0#0 == _mcc#3#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.aexp());
            assume a1#Z#0 == let#0#0#0;
            havoc a0#Z#0;
            assume $Is(a0#Z#0, Tclass._module.aexp());
            assume let#1#0#0 == _mcc#2#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#1#0#0, Tclass._module.aexp());
            assume a0#Z#0 == let#1#0#0;
            ##a#0 := a0#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##a#0, Tclass._module.aexp(), $Heap);
            ##s#0 := s#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#0, TMap(TSeq(TChar), TInt), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(##a#0) < DtRank(a#0)
               || (DtRank(##a#0) == DtRank(a#0)
                 && 
                Set#Subset(Map#Domain(##s#0), Map#Domain(s#0))
                 && !Set#Subset(Map#Domain(s#0), Map#Domain(##s#0)));
            assume _module.__default.aval#canCall(a0#Z#0, s#0);
            ##a#1 := a1#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##a#1, Tclass._module.aexp(), $Heap);
            ##s#1 := s#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#1, TMap(TSeq(TChar), TInt), $Heap);
            b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(##a#1) < DtRank(a#0)
               || (DtRank(##a#1) == DtRank(a#0)
                 && 
                Set#Subset(Map#Domain(##s#1), Map#Domain(s#0))
                 && !Set#Subset(Map#Domain(s#0), Map#Domain(##s#1)));
            assume _module.__default.aval#canCall(a1#Z#0, s#0);
            assume _module.__default.aval($LS($LZ), a#0, s#0)
               == _module.__default.aval($LS($LZ), a0#Z#0, s#0)
                 + _module.__default.aval($LS($LZ), a1#Z#0, s#0);
            assume _module.__default.aval#canCall(a0#Z#0, s#0)
               && _module.__default.aval#canCall(a1#Z#0, s#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.aval($LS($LZ), a#0, s#0), TInt);
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



// function declaration for _module._default.bval
function _module.__default.bval($ly: LayerType, b#0: DatatypeType, s#0: Map Box Box) : bool;

function _module.__default.bval#canCall(b#0: DatatypeType, s#0: Map Box Box) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, b#0: DatatypeType, s#0: Map Box Box :: 
  { _module.__default.bval($LS($ly), b#0, s#0) } 
  _module.__default.bval($LS($ly), b#0, s#0)
     == _module.__default.bval($ly, b#0, s#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, b#0: DatatypeType, s#0: Map Box Box :: 
  { _module.__default.bval(AsFuelBottom($ly), b#0, s#0) } 
  _module.__default.bval($ly, b#0, s#0) == _module.__default.bval($LZ, b#0, s#0));

// consequence axiom for _module.__default.bval
axiom 7 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, b#0: DatatypeType, s#0: Map Box Box :: 
    { _module.__default.bval($ly, b#0, s#0) } 
    _module.__default.bval#canCall(b#0, s#0)
         || (7 != $FunctionContextHeight
           && 
          $Is(b#0, Tclass._module.bexp())
           && $Is(s#0, TMap(TSeq(TChar), TInt)))
       ==> true);

function _module.__default.bval#requires(LayerType, DatatypeType, Map Box Box) : bool;

// #requires axiom for _module.__default.bval
axiom (forall $ly: LayerType, b#0: DatatypeType, s#0: Map Box Box :: 
  { _module.__default.bval#requires($ly, b#0, s#0) } 
  $Is(b#0, Tclass._module.bexp()) && $Is(s#0, TMap(TSeq(TChar), TInt))
     ==> _module.__default.bval#requires($ly, b#0, s#0) == true);

// definition axiom for _module.__default.bval (revealed)
axiom 7 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, b#0: DatatypeType, s#0: Map Box Box :: 
    { _module.__default.bval($LS($ly), b#0, s#0) } 
    _module.__default.bval#canCall(b#0, s#0)
         || (7 != $FunctionContextHeight
           && 
          $Is(b#0, Tclass._module.bexp())
           && $Is(s#0, TMap(TSeq(TChar), TInt)))
       ==> (!_module.bexp.Bc_q(b#0)
           ==> (_module.bexp.Not_q(b#0)
               ==> (var b#2 := _module.bexp.op(b#0); _module.__default.bval#canCall(b#2, s#0)))
             && (!_module.bexp.Not_q(b#0)
               ==> (_module.bexp.And_q(b#0)
                   ==> (var b1#1 := _module.bexp._1(b#0); 
                    (var b0#1 := _module.bexp._0(b#0); 
                      _module.__default.bval#canCall(b0#1, s#0)
                         && (_module.__default.bval($ly, b0#1, s#0)
                           ==> _module.__default.bval#canCall(b1#1, s#0)))))
                 && (!_module.bexp.And_q(b#0)
                   ==> (var a1#1 := _module.bexp.a1(b#0); 
                    (var a0#1 := _module.bexp.a0(b#0); 
                      _module.__default.aval#canCall(a0#1, s#0)
                         && _module.__default.aval#canCall(a1#1, s#0))))))
         && _module.__default.bval($LS($ly), b#0, s#0)
           == (if _module.bexp.Bc_q(b#0)
             then (var v#0 := _module.bexp.v(b#0); v#0)
             else (if _module.bexp.Not_q(b#0)
               then (var b#1 := _module.bexp.op(b#0); !_module.__default.bval($ly, b#1, s#0))
               else (if _module.bexp.And_q(b#0)
                 then (var b1#0 := _module.bexp._1(b#0); 
                  (var b0#0 := _module.bexp._0(b#0); 
                    _module.__default.bval($ly, b0#0, s#0) && _module.__default.bval($ly, b1#0, s#0)))
                 else (var a1#0 := _module.bexp.a1(b#0); 
                  (var a0#0 := _module.bexp.a0(b#0); 
                    _module.__default.aval($LS($LZ), a0#0, s#0)
                       < _module.__default.aval($LS($LZ), a1#0, s#0)))))));

// definition axiom for _module.__default.bval for all literals (revealed)
axiom 7 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, b#0: DatatypeType, s#0: Map Box Box :: 
    {:weight 3} { _module.__default.bval($LS($ly), Lit(b#0), Lit(s#0)) } 
    _module.__default.bval#canCall(Lit(b#0), Lit(s#0))
         || (7 != $FunctionContextHeight
           && 
          $Is(b#0, Tclass._module.bexp())
           && $Is(s#0, TMap(TSeq(TChar), TInt)))
       ==> (!Lit(_module.bexp.Bc_q(Lit(b#0)))
           ==> (Lit(_module.bexp.Not_q(Lit(b#0)))
               ==> (var b#4 := Lit(_module.bexp.op(Lit(b#0))); 
                _module.__default.bval#canCall(b#4, Lit(s#0))))
             && (!Lit(_module.bexp.Not_q(Lit(b#0)))
               ==> (Lit(_module.bexp.And_q(Lit(b#0)))
                   ==> (var b1#3 := Lit(_module.bexp._1(Lit(b#0))); 
                    (var b0#3 := Lit(_module.bexp._0(Lit(b#0))); 
                      _module.__default.bval#canCall(b0#3, Lit(s#0))
                         && (_module.__default.bval($LS($ly), b0#3, Lit(s#0))
                           ==> _module.__default.bval#canCall(b1#3, Lit(s#0))))))
                 && (!Lit(_module.bexp.And_q(Lit(b#0)))
                   ==> (var a1#3 := Lit(_module.bexp.a1(Lit(b#0))); 
                    (var a0#3 := Lit(_module.bexp.a0(Lit(b#0))); 
                      _module.__default.aval#canCall(a0#3, Lit(s#0))
                         && _module.__default.aval#canCall(a1#3, Lit(s#0)))))))
         && _module.__default.bval($LS($ly), Lit(b#0), Lit(s#0))
           == (if _module.bexp.Bc_q(Lit(b#0))
             then (var v#2 := Lit(_module.bexp.v(Lit(b#0))); v#2)
             else (if _module.bexp.Not_q(Lit(b#0))
               then (var b#3 := Lit(_module.bexp.op(Lit(b#0))); 
                !Lit(_module.__default.bval($LS($ly), b#3, Lit(s#0))))
               else (if _module.bexp.And_q(Lit(b#0))
                 then (var b1#2 := Lit(_module.bexp._1(Lit(b#0))); 
                  (var b0#2 := Lit(_module.bexp._0(Lit(b#0))); 
                    Lit(_module.__default.bval($LS($ly), b0#2, Lit(s#0))
                         && _module.__default.bval($LS($ly), b1#2, Lit(s#0)))))
                 else (var a1#2 := Lit(_module.bexp.a1(Lit(b#0))); 
                  (var a0#2 := Lit(_module.bexp.a0(Lit(b#0))); 
                    Lit(_module.__default.aval($LS($LZ), a0#2, Lit(s#0))
                         < _module.__default.aval($LS($LZ), a1#2, Lit(s#0)))))))));

procedure CheckWellformed$$_module.__default.bval(b#0: DatatypeType where $Is(b#0, Tclass._module.bexp()), 
    s#0: Map Box Box where $Is(s#0, TMap(TSeq(TChar), TInt)));
  free requires 7 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.bval(b#0: DatatypeType, s#0: Map Box Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#4#0: DatatypeType;
  var _mcc#5#0: DatatypeType;
  var a1#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var a0#Z#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var ##a#0: DatatypeType;
  var ##s#0: Map Box Box;
  var ##a#1: DatatypeType;
  var ##s#1: Map Box Box;
  var _mcc#2#0: DatatypeType;
  var _mcc#3#0: DatatypeType;
  var b1#Z#0: DatatypeType;
  var let#2#0#0: DatatypeType;
  var b0#Z#0: DatatypeType;
  var let#3#0#0: DatatypeType;
  var ##b#0: DatatypeType;
  var ##s#2: Map Box Box;
  var ##b#1: DatatypeType;
  var ##s#3: Map Box Box;
  var _mcc#1#0: DatatypeType;
  var b#Z#0: DatatypeType;
  var let#4#0#0: DatatypeType;
  var ##b#2: DatatypeType;
  var ##s#4: Map Box Box;
  var _mcc#0#0: bool;
  var v#Z#0: bool;
  var let#5#0#0: bool;
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

    // AddWellformednessCheck for function bval
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(25,9): initial state"} true;
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
        if (b#0 == #_module.bexp.Bc(_mcc#0#0))
        {
            havoc v#Z#0;
            assume true;
            assume let#5#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#5#0#0, TBool);
            assume v#Z#0 == let#5#0#0;
            assume _module.__default.bval($LS($LZ), b#0, s#0) == v#Z#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.bval($LS($LZ), b#0, s#0), TBool);
        }
        else if (b#0 == #_module.bexp.Not(_mcc#1#0))
        {
            assume $Is(_mcc#1#0, Tclass._module.bexp());
            havoc b#Z#0;
            assume $Is(b#Z#0, Tclass._module.bexp());
            assume let#4#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#4#0#0, Tclass._module.bexp());
            assume b#Z#0 == let#4#0#0;
            ##b#2 := b#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#2, Tclass._module.bexp(), $Heap);
            ##s#4 := s#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#4, TMap(TSeq(TChar), TInt), $Heap);
            b$reqreads#4 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(##b#2) < DtRank(b#0)
               || (DtRank(##b#2) == DtRank(b#0)
                 && 
                Set#Subset(Map#Domain(##s#4), Map#Domain(s#0))
                 && !Set#Subset(Map#Domain(s#0), Map#Domain(##s#4)));
            assume _module.__default.bval#canCall(b#Z#0, s#0);
            assume _module.__default.bval($LS($LZ), b#0, s#0)
               == !_module.__default.bval($LS($LZ), b#Z#0, s#0);
            assume _module.__default.bval#canCall(b#Z#0, s#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.bval($LS($LZ), b#0, s#0), TBool);
        }
        else if (b#0 == #_module.bexp.And(_mcc#2#0, _mcc#3#0))
        {
            assume $Is(_mcc#2#0, Tclass._module.bexp());
            assume $Is(_mcc#3#0, Tclass._module.bexp());
            havoc b1#Z#0;
            assume $Is(b1#Z#0, Tclass._module.bexp());
            assume let#2#0#0 == _mcc#3#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#2#0#0, Tclass._module.bexp());
            assume b1#Z#0 == let#2#0#0;
            havoc b0#Z#0;
            assume $Is(b0#Z#0, Tclass._module.bexp());
            assume let#3#0#0 == _mcc#2#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#3#0#0, Tclass._module.bexp());
            assume b0#Z#0 == let#3#0#0;
            ##b#0 := b0#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#0, Tclass._module.bexp(), $Heap);
            ##s#2 := s#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#2, TMap(TSeq(TChar), TInt), $Heap);
            b$reqreads#2 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(##b#0) < DtRank(b#0)
               || (DtRank(##b#0) == DtRank(b#0)
                 && 
                Set#Subset(Map#Domain(##s#2), Map#Domain(s#0))
                 && !Set#Subset(Map#Domain(s#0), Map#Domain(##s#2)));
            assume _module.__default.bval#canCall(b0#Z#0, s#0);
            if (_module.__default.bval($LS($LZ), b0#Z#0, s#0))
            {
                ##b#1 := b1#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##b#1, Tclass._module.bexp(), $Heap);
                ##s#3 := s#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#3, TMap(TSeq(TChar), TInt), $Heap);
                b$reqreads#3 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assert DtRank(##b#1) < DtRank(b#0)
                   || (DtRank(##b#1) == DtRank(b#0)
                     && 
                    Set#Subset(Map#Domain(##s#3), Map#Domain(s#0))
                     && !Set#Subset(Map#Domain(s#0), Map#Domain(##s#3)));
                assume _module.__default.bval#canCall(b1#Z#0, s#0);
            }

            assume _module.__default.bval($LS($LZ), b#0, s#0)
               == (_module.__default.bval($LS($LZ), b0#Z#0, s#0)
                 && _module.__default.bval($LS($LZ), b1#Z#0, s#0));
            assume _module.__default.bval#canCall(b0#Z#0, s#0)
               && (_module.__default.bval($LS($LZ), b0#Z#0, s#0)
                 ==> _module.__default.bval#canCall(b1#Z#0, s#0));
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.bval($LS($LZ), b#0, s#0), TBool);
        }
        else if (b#0 == #_module.bexp.Less(_mcc#4#0, _mcc#5#0))
        {
            assume $Is(_mcc#4#0, Tclass._module.aexp());
            assume $Is(_mcc#5#0, Tclass._module.aexp());
            havoc a1#Z#0;
            assume $Is(a1#Z#0, Tclass._module.aexp());
            assume let#0#0#0 == _mcc#5#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.aexp());
            assume a1#Z#0 == let#0#0#0;
            havoc a0#Z#0;
            assume $Is(a0#Z#0, Tclass._module.aexp());
            assume let#1#0#0 == _mcc#4#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#1#0#0, Tclass._module.aexp());
            assume a0#Z#0 == let#1#0#0;
            ##a#0 := a0#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##a#0, Tclass._module.aexp(), $Heap);
            ##s#0 := s#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#0, TMap(TSeq(TChar), TInt), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.aval#canCall(a0#Z#0, s#0);
            ##a#1 := a1#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##a#1, Tclass._module.aexp(), $Heap);
            ##s#1 := s#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#1, TMap(TSeq(TChar), TInt), $Heap);
            b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.aval#canCall(a1#Z#0, s#0);
            assume _module.__default.bval($LS($LZ), b#0, s#0)
               == (_module.__default.aval($LS($LZ), a0#Z#0, s#0)
                 < _module.__default.aval($LS($LZ), a1#Z#0, s#0));
            assume _module.__default.aval#canCall(a0#Z#0, s#0)
               && _module.__default.aval#canCall(a1#Z#0, s#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.bval($LS($LZ), b#0, s#0), TBool);
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



// function declaration for _module._default.big_step
function _module.__default.big__step($ly: LayerType, c#0: DatatypeType, s#0: Map Box Box, t#0: Map Box Box) : bool;

function _module.__default.big__step#canCall(c#0: DatatypeType, s#0: Map Box Box, t#0: Map Box Box) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, c#0: DatatypeType, s#0: Map Box Box, t#0: Map Box Box :: 
  { _module.__default.big__step($LS($ly), c#0, s#0, t#0) } 
  _module.__default.big__step($LS($ly), c#0, s#0, t#0)
     == _module.__default.big__step($ly, c#0, s#0, t#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, c#0: DatatypeType, s#0: Map Box Box, t#0: Map Box Box :: 
  { _module.__default.big__step(AsFuelBottom($ly), c#0, s#0, t#0) } 
  _module.__default.big__step($ly, c#0, s#0, t#0)
     == _module.__default.big__step($LZ, c#0, s#0, t#0));

// consequence axiom for _module.__default.big__step
axiom 8 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, c#0: DatatypeType, s#0: Map Box Box, t#0: Map Box Box :: 
    { _module.__default.big__step($ly, c#0, s#0, t#0) } 
    _module.__default.big__step#canCall(c#0, s#0, t#0)
         || (8 != $FunctionContextHeight
           && 
          $Is(c#0, Tclass._module.com())
           && $Is(s#0, TMap(TSeq(TChar), TInt))
           && $Is(t#0, TMap(TSeq(TChar), TInt)))
       ==> true);

function _module.__default.big__step#requires(LayerType, DatatypeType, Map Box Box, Map Box Box) : bool;

// #requires axiom for _module.__default.big__step
axiom (forall $ly: LayerType, c#0: DatatypeType, s#0: Map Box Box, t#0: Map Box Box :: 
  { _module.__default.big__step#requires($ly, c#0, s#0, t#0) } 
  $Is(c#0, Tclass._module.com())
       && $Is(s#0, TMap(TSeq(TChar), TInt))
       && $Is(t#0, TMap(TSeq(TChar), TInt))
     ==> _module.__default.big__step#requires($ly, c#0, s#0, t#0) == true);

// definition axiom for _module.__default.big__step (revealed)
axiom 8 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, c#0: DatatypeType, s#0: Map Box Box, t#0: Map Box Box :: 
    { _module.__default.big__step($LS($ly), c#0, s#0, t#0) } 
    _module.__default.big__step#canCall(c#0, s#0, t#0)
         || (8 != $FunctionContextHeight
           && 
          $Is(c#0, Tclass._module.com())
           && $Is(s#0, TMap(TSeq(TChar), TInt))
           && $Is(t#0, TMap(TSeq(TChar), TInt)))
       ==> (!_module.com.SKIP_q(c#0)
           ==> (_module.com.Assign_q(c#0)
               ==> (var a#1 := _module.com._h1(c#0); _module.__default.aval#canCall(a#1, s#0)))
             && (!_module.com.Assign_q(c#0)
               ==> (_module.com.Seq_q(c#0)
                   ==> (var c1#1 := _module.com._h3(c#0); 
                    (var c0#1 := _module.com._h2(c#0); 
                      (forall s'#2: Map Box Box :: 
                        { _module.__default.big__step($ly, c1#1, s'#2, t#0) } 
                          { _module.__default.big__step($ly, c0#1, s#0, s'#2) } 
                        $Is(s'#2, TMap(TSeq(TChar), TInt))
                           ==> _module.__default.big__step#canCall(c0#1, s#0, s'#2)
                             && (_module.__default.big__step($ly, c0#1, s#0, s'#2)
                               ==> _module.__default.big__step#canCall(c1#1, s'#2, t#0))))))
                 && (!_module.com.Seq_q(c#0)
                   ==> (_module.com.If_q(c#0)
                       ==> (var els#1 := _module.com._h6(c#0); 
                        (var thn#1 := _module.com._h5(c#0); 
                          (var b#2 := _module.com._h4(c#0); 
                            _module.__default.bval#canCall(b#2, s#0)
                               && _module.__default.big__step#canCall((if _module.__default.bval($LS($LZ), b#2, s#0) then thn#1 else els#1), s#0, t#0)))))
                     && (!_module.com.If_q(c#0)
                       ==> (var body#1 := _module.com._h8(c#0); 
                        (var b#3 := _module.com._h7(c#0); 
                          _module.__default.bval#canCall(b#3, s#0)
                             && (!(!_module.__default.bval($LS($LZ), b#3, s#0) && Map#Equal(s#0, t#0))
                               ==> _module.__default.bval#canCall(b#3, s#0)
                                 && (_module.__default.bval($LS($LZ), b#3, s#0)
                                   ==> (forall s'#3: Map Box Box :: 
                                    { _module.__default.big__step($ly, #_module.com.While(b#3, body#1), s'#3, t#0) } 
                                      { _module.__default.big__step($ly, body#1, s#0, s'#3) } 
                                    $Is(s'#3, TMap(TSeq(TChar), TInt))
                                       ==> _module.__default.big__step#canCall(body#1, s#0, s'#3)
                                         && (_module.__default.big__step($ly, body#1, s#0, s'#3)
                                           ==> _module.__default.big__step#canCall(#_module.com.While(b#3, body#1), s'#3, t#0)))))))))))
         && _module.__default.big__step($LS($ly), c#0, s#0, t#0)
           == (if _module.com.SKIP_q(c#0)
             then Map#Equal(s#0, t#0)
             else (if _module.com.Assign_q(c#0)
               then (var a#0 := _module.com._h1(c#0); 
                (var x#0 := _module.com._h0(c#0); 
                  Map#Equal(t#0, Map#Build(s#0, $Box(x#0), $Box(_module.__default.aval($LS($LZ), a#0, s#0))))))
               else (if _module.com.Seq_q(c#0)
                 then (var c1#0 := _module.com._h3(c#0); 
                  (var c0#0 := _module.com._h2(c#0); 
                    (exists s'#0: Map Box Box :: 
                      { _module.__default.big__step($ly, c1#0, s'#0, t#0) } 
                        { _module.__default.big__step($ly, c0#0, s#0, s'#0) } 
                      $Is(s'#0, TMap(TSeq(TChar), TInt))
                         && 
                        _module.__default.big__step($ly, c0#0, s#0, s'#0)
                         && _module.__default.big__step($ly, c1#0, s'#0, t#0))))
                 else (if _module.com.If_q(c#0)
                   then (var els#0 := _module.com._h6(c#0); 
                    (var thn#0 := _module.com._h5(c#0); 
                      (var b#0 := _module.com._h4(c#0); 
                        _module.__default.big__step($ly, 
                          (if _module.__default.bval($LS($LZ), b#0, s#0) then thn#0 else els#0), 
                          s#0, 
                          t#0))))
                   else (var body#0 := _module.com._h8(c#0); 
                    (var b#1 := _module.com._h7(c#0); 
                      (!_module.__default.bval($LS($LZ), b#1, s#0) && Map#Equal(s#0, t#0))
                         || (_module.__default.bval($LS($LZ), b#1, s#0)
                           && (exists s'#1: Map Box Box :: 
                            { _module.__default.big__step($ly, #_module.com.While(b#1, body#0), s'#1, t#0) } 
                              { _module.__default.big__step($ly, body#0, s#0, s'#1) } 
                            $Is(s'#1, TMap(TSeq(TChar), TInt))
                               && 
                              _module.__default.big__step($ly, body#0, s#0, s'#1)
                               && _module.__default.big__step($ly, #_module.com.While(b#1, body#0), s'#1, t#0))))))))));

// 1st prefix predicate axiom for _module.__default.big__step_h
axiom 9 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, c#0: DatatypeType, s#0: Map Box Box, t#0: Map Box Box :: 
    { _module.__default.big__step($LS($ly), c#0, s#0, t#0) } 
    $Is(c#0, Tclass._module.com())
         && $Is(s#0, TMap(TSeq(TChar), TInt))
         && $Is(t#0, TMap(TSeq(TChar), TInt))
         && _module.__default.big__step($LS($ly), c#0, s#0, t#0)
       ==> (exists _k#0: Box :: 
        { _module.__default.big__step_h($LS($ly), _k#0, c#0, s#0, t#0) } 
        _module.__default.big__step_h($LS($ly), _k#0, c#0, s#0, t#0)));

// 2nd prefix predicate axiom
axiom 9 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, c#0: DatatypeType, s#0: Map Box Box, t#0: Map Box Box :: 
    { _module.__default.big__step($LS($ly), c#0, s#0, t#0) } 
    $Is(c#0, Tclass._module.com())
         && $Is(s#0, TMap(TSeq(TChar), TInt))
         && $Is(t#0, TMap(TSeq(TChar), TInt))
         && (exists _k#0: Box :: 
          { _module.__default.big__step_h($LS($ly), _k#0, c#0, s#0, t#0) } 
          _module.__default.big__step_h($LS($ly), _k#0, c#0, s#0, t#0))
       ==> _module.__default.big__step($LS($ly), c#0, s#0, t#0));

// 3rd prefix predicate axiom
axiom 9 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, c#0: DatatypeType, s#0: Map Box Box, t#0: Map Box Box, _k#0: Box :: 
    { _module.__default.big__step_h($ly, _k#0, c#0, s#0, t#0) } 
    $Is(c#0, Tclass._module.com())
         && $Is(s#0, TMap(TSeq(TChar), TInt))
         && $Is(t#0, TMap(TSeq(TChar), TInt))
         && _k#0 == ORD#FromNat(0)
       ==> !_module.__default.big__step_h($ly, _k#0, c#0, s#0, t#0));

// targeted prefix predicate monotonicity axiom
axiom 9 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, 
      c#0: DatatypeType, 
      s#0: Map Box Box, 
      t#0: Map Box Box, 
      _k#0: Box, 
      _m: Box, 
      _limit: Box :: 
    { _module.__default.big__step_h($ly, _k#0, c#0, s#0, t#0), ORD#LessThanLimit(_k#0, _limit), ORD#LessThanLimit(_m, _limit) } 
    ORD#Less(_k#0, _m)
       ==> 
      _module.__default.big__step_h($ly, _k#0, c#0, s#0, t#0)
       ==> _module.__default.big__step_h($ly, _m, c#0, s#0, t#0));

procedure CheckWellformed$$_module.__default.big__step(c#0: DatatypeType where $Is(c#0, Tclass._module.com()), 
    s#0: Map Box Box where $Is(s#0, TMap(TSeq(TChar), TInt)), 
    t#0: Map Box Box where $Is(t#0, TMap(TSeq(TChar), TInt)));
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.big__step(c#0: DatatypeType, s#0: Map Box Box, t#0: Map Box Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#7#0: DatatypeType;
  var _mcc#8#0: DatatypeType;
  var body#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var b#Z#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var ##b#0: DatatypeType;
  var ##s#0: Map Box Box;
  var ##b#1: DatatypeType;
  var ##s#1: Map Box Box;
  var s'#4: Map Box Box;
  var ##c#0: DatatypeType;
  var ##s#2: Map Box Box;
  var ##t#0: Map Box Box;
  var ##c#1: DatatypeType;
  var ##s#3: Map Box Box;
  var ##t#1: Map Box Box;
  var _mcc#4#0: DatatypeType;
  var _mcc#5#0: DatatypeType;
  var _mcc#6#0: DatatypeType;
  var els#Z#0: DatatypeType;
  var let#2#0#0: DatatypeType;
  var thn#Z#0: DatatypeType;
  var let#3#0#0: DatatypeType;
  var b#Z#1: DatatypeType;
  var let#4#0#0: DatatypeType;
  var ##b#2: DatatypeType;
  var ##s#4: Map Box Box;
  var ##c#2: DatatypeType;
  var ##s#5: Map Box Box;
  var ##t#2: Map Box Box;
  var _mcc#2#0: DatatypeType;
  var _mcc#3#0: DatatypeType;
  var c1#Z#0: DatatypeType;
  var let#5#0#0: DatatypeType;
  var c0#Z#0: DatatypeType;
  var let#6#0#0: DatatypeType;
  var s'#6: Map Box Box;
  var ##c#3: DatatypeType;
  var ##s#6: Map Box Box;
  var ##t#3: Map Box Box;
  var ##c#4: DatatypeType;
  var ##s#7: Map Box Box;
  var ##t#4: Map Box Box;
  var _mcc#0#0: Seq Box;
  var _mcc#1#0: DatatypeType;
  var a#Z#0: DatatypeType;
  var let#7#0#0: DatatypeType;
  var x#Z#0: Seq Box;
  var let#8#0#0: Seq Box;
  var ##a#0: DatatypeType;
  var ##s#8: Map Box Box;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;
  var b$reqreads#2: bool;
  var b$reqreads#3: bool;
  var b$reqreads#4: bool;
  var b$reqreads#5: bool;
  var b$reqreads#6: bool;
  var b$reqreads#7: bool;
  var b$reqreads#8: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;
    b$reqreads#3 := true;
    b$reqreads#4 := true;
    b$reqreads#5 := true;
    b$reqreads#6 := true;
    b$reqreads#7 := true;
    b$reqreads#8 := true;

    // AddWellformednessCheck for function big_step
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(40,16): initial state"} true;
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
        if (c#0 == #_module.com.SKIP())
        {
            assume _module.__default.big__step($LS($LZ), c#0, s#0, t#0) == Map#Equal(s#0, t#0);
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.big__step($LS($LZ), c#0, s#0, t#0), TBool);
        }
        else if (c#0 == #_module.com.Assign(_mcc#0#0, _mcc#1#0))
        {
            assume $Is(_mcc#0#0, TSeq(TChar));
            assume $Is(_mcc#1#0, Tclass._module.aexp());
            havoc a#Z#0;
            assume $Is(a#Z#0, Tclass._module.aexp());
            assume let#7#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#7#0#0, Tclass._module.aexp());
            assume a#Z#0 == let#7#0#0;
            havoc x#Z#0;
            assume $Is(x#Z#0, TSeq(TChar));
            assume let#8#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#8#0#0, TSeq(TChar));
            assume x#Z#0 == let#8#0#0;
            ##a#0 := a#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##a#0, Tclass._module.aexp(), $Heap);
            ##s#8 := s#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#8, TMap(TSeq(TChar), TInt), $Heap);
            b$reqreads#8 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.aval#canCall(a#Z#0, s#0);
            assume _module.__default.big__step($LS($LZ), c#0, s#0, t#0)
               == Map#Equal(t#0, 
                Map#Build(s#0, $Box(x#Z#0), $Box(_module.__default.aval($LS($LZ), a#Z#0, s#0))));
            assume _module.__default.aval#canCall(a#Z#0, s#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.big__step($LS($LZ), c#0, s#0, t#0), TBool);
        }
        else if (c#0 == #_module.com.Seq(_mcc#2#0, _mcc#3#0))
        {
            assume $Is(_mcc#2#0, Tclass._module.com());
            assume $Is(_mcc#3#0, Tclass._module.com());
            havoc c1#Z#0;
            assume $Is(c1#Z#0, Tclass._module.com());
            assume let#5#0#0 == _mcc#3#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#5#0#0, Tclass._module.com());
            assume c1#Z#0 == let#5#0#0;
            havoc c0#Z#0;
            assume $Is(c0#Z#0, Tclass._module.com());
            assume let#6#0#0 == _mcc#2#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#6#0#0, Tclass._module.com());
            assume c0#Z#0 == let#6#0#0;
            // Begin Comprehension WF check
            havoc s'#6;
            if ($Is(s'#6, TMap(TSeq(TChar), TInt)))
            {
                ##c#3 := c0#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##c#3, Tclass._module.com(), $Heap);
                ##s#6 := s#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#6, TMap(TSeq(TChar), TInt), $Heap);
                ##t#3 := s'#6;
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#3, TMap(TSeq(TChar), TInt), $Heap);
                b$reqreads#6 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assume _module.__default.big__step#canCall(c0#Z#0, s#0, s'#6);
                if (_module.__default.big__step($LS($LZ), c0#Z#0, s#0, s'#6))
                {
                    ##c#4 := c1#Z#0;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c#4, Tclass._module.com(), $Heap);
                    ##s#7 := s'#6;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s#7, TMap(TSeq(TChar), TInt), $Heap);
                    ##t#4 := t#0;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##t#4, TMap(TSeq(TChar), TInt), $Heap);
                    b$reqreads#7 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                    assume _module.__default.big__step#canCall(c1#Z#0, s'#6, t#0);
                }
            }

            // End Comprehension WF check
            assume _module.__default.big__step($LS($LZ), c#0, s#0, t#0)
               == (exists s'#7: Map Box Box :: 
                { _module.__default.big__step($LS($LZ), c1#Z#0, s'#7, t#0) } 
                  { _module.__default.big__step($LS($LZ), c0#Z#0, s#0, s'#7) } 
                $Is(s'#7, TMap(TSeq(TChar), TInt))
                   && 
                  _module.__default.big__step($LS($LZ), c0#Z#0, s#0, s'#7)
                   && _module.__default.big__step($LS($LZ), c1#Z#0, s'#7, t#0));
            assume (forall s'#7: Map Box Box :: 
              { _module.__default.big__step($LS($LZ), c1#Z#0, s'#7, t#0) } 
                { _module.__default.big__step($LS($LZ), c0#Z#0, s#0, s'#7) } 
              $Is(s'#7, TMap(TSeq(TChar), TInt))
                 ==> _module.__default.big__step#canCall(c0#Z#0, s#0, s'#7)
                   && (_module.__default.big__step($LS($LZ), c0#Z#0, s#0, s'#7)
                     ==> _module.__default.big__step#canCall(c1#Z#0, s'#7, t#0)));
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.big__step($LS($LZ), c#0, s#0, t#0), TBool);
        }
        else if (c#0 == #_module.com.If(_mcc#4#0, _mcc#5#0, _mcc#6#0))
        {
            assume $Is(_mcc#4#0, Tclass._module.bexp());
            assume $Is(_mcc#5#0, Tclass._module.com());
            assume $Is(_mcc#6#0, Tclass._module.com());
            havoc els#Z#0;
            assume $Is(els#Z#0, Tclass._module.com());
            assume let#2#0#0 == _mcc#6#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#2#0#0, Tclass._module.com());
            assume els#Z#0 == let#2#0#0;
            havoc thn#Z#0;
            assume $Is(thn#Z#0, Tclass._module.com());
            assume let#3#0#0 == _mcc#5#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#3#0#0, Tclass._module.com());
            assume thn#Z#0 == let#3#0#0;
            havoc b#Z#1;
            assume $Is(b#Z#1, Tclass._module.bexp());
            assume let#4#0#0 == _mcc#4#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#4#0#0, Tclass._module.bexp());
            assume b#Z#1 == let#4#0#0;
            ##b#2 := b#Z#1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#2, Tclass._module.bexp(), $Heap);
            ##s#4 := s#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#4, TMap(TSeq(TChar), TInt), $Heap);
            b$reqreads#4 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.bval#canCall(b#Z#1, s#0);
            if (_module.__default.bval($LS($LZ), b#Z#1, s#0))
            {
            }
            else
            {
            }

            ##c#2 := (if _module.__default.bval($LS($LZ), b#Z#1, s#0) then thn#Z#0 else els#Z#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##c#2, Tclass._module.com(), $Heap);
            ##s#5 := s#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#5, TMap(TSeq(TChar), TInt), $Heap);
            ##t#2 := t#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#2, TMap(TSeq(TChar), TInt), $Heap);
            b$reqreads#5 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.big__step#canCall((if _module.__default.bval($LS($LZ), b#Z#1, s#0) then thn#Z#0 else els#Z#0), 
              s#0, 
              t#0);
            assume _module.__default.big__step($LS($LZ), c#0, s#0, t#0)
               == _module.__default.big__step($LS($LZ), 
                (if _module.__default.bval($LS($LZ), b#Z#1, s#0) then thn#Z#0 else els#Z#0), 
                s#0, 
                t#0);
            assume _module.__default.bval#canCall(b#Z#1, s#0)
               && _module.__default.big__step#canCall((if _module.__default.bval($LS($LZ), b#Z#1, s#0) then thn#Z#0 else els#Z#0), 
                s#0, 
                t#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.big__step($LS($LZ), c#0, s#0, t#0), TBool);
        }
        else if (c#0 == #_module.com.While(_mcc#7#0, _mcc#8#0))
        {
            assume $Is(_mcc#7#0, Tclass._module.bexp());
            assume $Is(_mcc#8#0, Tclass._module.com());
            havoc body#Z#0;
            assume $Is(body#Z#0, Tclass._module.com());
            assume let#0#0#0 == _mcc#8#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.com());
            assume body#Z#0 == let#0#0#0;
            havoc b#Z#0;
            assume $Is(b#Z#0, Tclass._module.bexp());
            assume let#1#0#0 == _mcc#7#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#1#0#0, Tclass._module.bexp());
            assume b#Z#0 == let#1#0#0;
            ##b#0 := b#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#0, Tclass._module.bexp(), $Heap);
            ##s#0 := s#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#0, TMap(TSeq(TChar), TInt), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.bval#canCall(b#Z#0, s#0);
            if (!_module.__default.bval($LS($LZ), b#Z#0, s#0))
            {
            }

            if (!(!_module.__default.bval($LS($LZ), b#Z#0, s#0) && Map#Equal(s#0, t#0)))
            {
                ##b#1 := b#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##b#1, Tclass._module.bexp(), $Heap);
                ##s#1 := s#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#1, TMap(TSeq(TChar), TInt), $Heap);
                b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assume _module.__default.bval#canCall(b#Z#0, s#0);
                if (_module.__default.bval($LS($LZ), b#Z#0, s#0))
                {
                    // Begin Comprehension WF check
                    havoc s'#4;
                    if ($Is(s'#4, TMap(TSeq(TChar), TInt)))
                    {
                        ##c#0 := body#Z#0;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##c#0, Tclass._module.com(), $Heap);
                        ##s#2 := s#0;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##s#2, TMap(TSeq(TChar), TInt), $Heap);
                        ##t#0 := s'#4;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##t#0, TMap(TSeq(TChar), TInt), $Heap);
                        b$reqreads#2 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                        assume _module.__default.big__step#canCall(body#Z#0, s#0, s'#4);
                        if (_module.__default.big__step($LS($LZ), body#Z#0, s#0, s'#4))
                        {
                            ##c#1 := #_module.com.While(b#Z#0, body#Z#0);
                            // assume allocatedness for argument to function
                            assume $IsAlloc(##c#1, Tclass._module.com(), $Heap);
                            ##s#3 := s'#4;
                            // assume allocatedness for argument to function
                            assume $IsAlloc(##s#3, TMap(TSeq(TChar), TInt), $Heap);
                            ##t#1 := t#0;
                            // assume allocatedness for argument to function
                            assume $IsAlloc(##t#1, TMap(TSeq(TChar), TInt), $Heap);
                            b$reqreads#3 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                            assume _module.__default.big__step#canCall(#_module.com.While(b#Z#0, body#Z#0), s'#4, t#0);
                        }
                    }

                    // End Comprehension WF check
                }
            }

            assume _module.__default.big__step($LS($LZ), c#0, s#0, t#0)
               == ((!_module.__default.bval($LS($LZ), b#Z#0, s#0) && Map#Equal(s#0, t#0))
                 || (_module.__default.bval($LS($LZ), b#Z#0, s#0)
                   && (exists s'#5: Map Box Box :: 
                    { _module.__default.big__step($LS($LZ), #_module.com.While(b#Z#0, body#Z#0), s'#5, t#0) } 
                      { _module.__default.big__step($LS($LZ), body#Z#0, s#0, s'#5) } 
                    $Is(s'#5, TMap(TSeq(TChar), TInt))
                       && 
                      _module.__default.big__step($LS($LZ), body#Z#0, s#0, s'#5)
                       && _module.__default.big__step($LS($LZ), #_module.com.While(b#Z#0, body#Z#0), s'#5, t#0))));
            assume _module.__default.bval#canCall(b#Z#0, s#0)
               && (!(!_module.__default.bval($LS($LZ), b#Z#0, s#0) && Map#Equal(s#0, t#0))
                 ==> _module.__default.bval#canCall(b#Z#0, s#0)
                   && (_module.__default.bval($LS($LZ), b#Z#0, s#0)
                     ==> (forall s'#5: Map Box Box :: 
                      { _module.__default.big__step($LS($LZ), #_module.com.While(b#Z#0, body#Z#0), s'#5, t#0) } 
                        { _module.__default.big__step($LS($LZ), body#Z#0, s#0, s'#5) } 
                      $Is(s'#5, TMap(TSeq(TChar), TInt))
                         ==> _module.__default.big__step#canCall(body#Z#0, s#0, s'#5)
                           && (_module.__default.big__step($LS($LZ), body#Z#0, s#0, s'#5)
                             ==> _module.__default.big__step#canCall(#_module.com.While(b#Z#0, body#Z#0), s'#5, t#0)))));
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.big__step($LS($LZ), c#0, s#0, t#0), TBool);
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
        assert b$reqreads#5;
        assert b$reqreads#6;
        assert b$reqreads#7;
        assert b$reqreads#8;
    }
}



// function declaration for _module._default.big_step#
function _module.__default.big__step_h($ly: LayerType, _k#0: Box, c#0: DatatypeType, s#0: Map Box Box, t#0: Map Box Box)
   : bool;

function _module.__default.big__step_h#canCall(_k#0: Box, c#0: DatatypeType, s#0: Map Box Box, t#0: Map Box Box) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, _k#0: Box, c#0: DatatypeType, s#0: Map Box Box, t#0: Map Box Box :: 
  { _module.__default.big__step_h($LS($ly), _k#0, c#0, s#0, t#0) } 
  _module.__default.big__step_h($LS($ly), _k#0, c#0, s#0, t#0)
     == _module.__default.big__step_h($ly, _k#0, c#0, s#0, t#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, _k#0: Box, c#0: DatatypeType, s#0: Map Box Box, t#0: Map Box Box :: 
  { _module.__default.big__step_h(AsFuelBottom($ly), _k#0, c#0, s#0, t#0) } 
  _module.__default.big__step_h($ly, _k#0, c#0, s#0, t#0)
     == _module.__default.big__step_h($LZ, _k#0, c#0, s#0, t#0));

// consequence axiom for _module.__default.big__step_h
axiom 9 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: Box, c#0: DatatypeType, s#0: Map Box Box, t#0: Map Box Box :: 
    { _module.__default.big__step_h($ly, _k#0, c#0, s#0, t#0) } 
    _module.__default.big__step_h#canCall(_k#0, c#0, s#0, t#0)
         || (9 != $FunctionContextHeight
           && 
          $Is(c#0, Tclass._module.com())
           && $Is(s#0, TMap(TSeq(TChar), TInt))
           && $Is(t#0, TMap(TSeq(TChar), TInt)))
       ==> true);

function _module.__default.big__step_h#requires(LayerType, Box, DatatypeType, Map Box Box, Map Box Box) : bool;

// #requires axiom for _module.__default.big__step_h
axiom (forall $ly: LayerType, _k#0: Box, c#0: DatatypeType, s#0: Map Box Box, t#0: Map Box Box :: 
  { _module.__default.big__step_h#requires($ly, _k#0, c#0, s#0, t#0) } 
  $Is(c#0, Tclass._module.com())
       && $Is(s#0, TMap(TSeq(TChar), TInt))
       && $Is(t#0, TMap(TSeq(TChar), TInt))
     ==> _module.__default.big__step_h#requires($ly, _k#0, c#0, s#0, t#0) == true);

// definition axiom for _module.__default.big__step_h (revealed)
axiom 9 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: Box, c#0: DatatypeType, s#0: Map Box Box, t#0: Map Box Box :: 
    { _module.__default.big__step_h($LS($ly), _k#0, c#0, s#0, t#0) } 
    _module.__default.big__step_h#canCall(_k#0, c#0, s#0, t#0)
         || (9 != $FunctionContextHeight
           && 
          $Is(c#0, Tclass._module.com())
           && $Is(s#0, TMap(TSeq(TChar), TInt))
           && $Is(t#0, TMap(TSeq(TChar), TInt)))
       ==> (0 < ORD#Offset(_k#0)
           ==> 
          !_module.com.SKIP_q(c#0)
           ==> (_module.com.Assign_q(c#0)
               ==> (var a#3 := _module.com._h1(c#0); _module.__default.aval#canCall(a#3, s#0)))
             && (!_module.com.Assign_q(c#0)
               ==> (_module.com.Seq_q(c#0)
                   ==> (var c1#3 := _module.com._h3(c#0); 
                    (var c0#3 := _module.com._h2(c#0); 
                      (forall s'#10: Map Box Box :: 
                        { _module.__default.big__step_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), c1#3, s'#10, t#0) } 
                          { _module.__default.big__step_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), c0#3, s#0, s'#10) } 
                        $Is(s'#10, TMap(TSeq(TChar), TInt))
                           ==> _module.__default.big__step_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), c0#3, s#0, s'#10)
                             && (_module.__default.big__step_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), c0#3, s#0, s'#10)
                               ==> _module.__default.big__step_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), c1#3, s'#10, t#0))))))
                 && (!_module.com.Seq_q(c#0)
                   ==> (_module.com.If_q(c#0)
                       ==> (var els#3 := _module.com._h6(c#0); 
                        (var thn#3 := _module.com._h5(c#0); 
                          (var b#6 := _module.com._h4(c#0); 
                            _module.__default.bval#canCall(b#6, s#0)
                               && _module.__default.big__step_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), 
                                (if _module.__default.bval($LS($LZ), b#6, s#0) then thn#3 else els#3), 
                                s#0, 
                                t#0)))))
                     && (!_module.com.If_q(c#0)
                       ==> (var body#3 := _module.com._h8(c#0); 
                        (var b#7 := _module.com._h7(c#0); 
                          _module.__default.bval#canCall(b#7, s#0)
                             && (!(!_module.__default.bval($LS($LZ), b#7, s#0) && Map#Equal(s#0, t#0))
                               ==> _module.__default.bval#canCall(b#7, s#0)
                                 && (_module.__default.bval($LS($LZ), b#7, s#0)
                                   ==> (forall s'#11: Map Box Box :: 
                                    { _module.__default.big__step_h($ly, 
                                        ORD#Minus(_k#0, ORD#FromNat(1)), 
                                        #_module.com.While(b#7, body#3), 
                                        s'#11, 
                                        t#0) } 
                                      { _module.__default.big__step_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), body#3, s#0, s'#11) } 
                                    $Is(s'#11, TMap(TSeq(TChar), TInt))
                                       ==> _module.__default.big__step_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), body#3, s#0, s'#11)
                                         && (_module.__default.big__step_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), body#3, s#0, s'#11)
                                           ==> _module.__default.big__step_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), #_module.com.While(b#7, body#3), s'#11, t#0)))))))))))
         && (
          (0 < ORD#Offset(_k#0)
           ==> (if _module.com.SKIP_q(c#0)
             then Map#Equal(s#0, t#0)
             else (if _module.com.Assign_q(c#0)
               then (var a#4 := _module.com._h1(c#0); 
                (var x#4 := _module.com._h0(c#0); 
                  Map#Equal(t#0, Map#Build(s#0, $Box(x#4), $Box(_module.__default.aval($LS($LZ), a#4, s#0))))))
               else (if _module.com.Seq_q(c#0)
                 then (var c1#4 := _module.com._h3(c#0); 
                  (var c0#4 := _module.com._h2(c#0); 
                    (exists s'#12: Map Box Box :: 
                      { _module.__default.big__step_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), c1#4, s'#12, t#0) } 
                        { _module.__default.big__step_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), c0#4, s#0, s'#12) } 
                      $Is(s'#12, TMap(TSeq(TChar), TInt))
                         && 
                        _module.__default.big__step_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), c0#4, s#0, s'#12)
                         && _module.__default.big__step_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), c1#4, s'#12, t#0))))
                 else (if _module.com.If_q(c#0)
                   then (var els#4 := _module.com._h6(c#0); 
                    (var thn#4 := _module.com._h5(c#0); 
                      (var b#8 := _module.com._h4(c#0); 
                        _module.__default.big__step_h($ly, 
                          ORD#Minus(_k#0, ORD#FromNat(1)), 
                          (if _module.__default.bval($LS($LZ), b#8, s#0) then thn#4 else els#4), 
                          s#0, 
                          t#0))))
                   else (var body#4 := _module.com._h8(c#0); 
                    (var b#9 := _module.com._h7(c#0); 
                      (!_module.__default.bval($LS($LZ), b#9, s#0) && Map#Equal(s#0, t#0))
                         || (_module.__default.bval($LS($LZ), b#9, s#0)
                           && (exists s'#13: Map Box Box :: 
                            { _module.__default.big__step_h($ly, 
                                ORD#Minus(_k#0, ORD#FromNat(1)), 
                                #_module.com.While(b#9, body#4), 
                                s'#13, 
                                t#0) } 
                              { _module.__default.big__step_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), body#4, s#0, s'#13) } 
                            $Is(s'#13, TMap(TSeq(TChar), TInt))
                               && 
                              _module.__default.big__step_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), body#4, s#0, s'#13)
                               && _module.__default.big__step_h($ly, 
                                ORD#Minus(_k#0, ORD#FromNat(1)), 
                                #_module.com.While(b#9, body#4), 
                                s'#13, 
                                t#0))))))))))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#0: Box :: 
            { _module.__default.big__step_h($ly, _k'#0, c#0, s#0, t#0) } 
            ORD#LessThanLimit(_k'#0, _k#0)
               ==> _module.__default.big__step_h#canCall(_k'#0, c#0, s#0, t#0)))
         && _module.__default.big__step_h($LS($ly), _k#0, c#0, s#0, t#0)
           == ((0 < ORD#Offset(_k#0)
               ==> (if _module.com.SKIP_q(c#0)
                 then Map#Equal(s#0, t#0)
                 else (if _module.com.Assign_q(c#0)
                   then (var a#2 := _module.com._h1(c#0); 
                    (var x#2 := _module.com._h0(c#0); 
                      Map#Equal(t#0, Map#Build(s#0, $Box(x#2), $Box(_module.__default.aval($LS($LZ), a#2, s#0))))))
                   else (if _module.com.Seq_q(c#0)
                     then (var c1#2 := _module.com._h3(c#0); 
                      (var c0#2 := _module.com._h2(c#0); 
                        (exists s'#8: Map Box Box :: 
                          { _module.__default.big__step_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), c1#2, s'#8, t#0) } 
                            { _module.__default.big__step_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), c0#2, s#0, s'#8) } 
                          $Is(s'#8, TMap(TSeq(TChar), TInt))
                             && 
                            _module.__default.big__step_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), c0#2, s#0, s'#8)
                             && _module.__default.big__step_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), c1#2, s'#8, t#0))))
                     else (if _module.com.If_q(c#0)
                       then (var els#2 := _module.com._h6(c#0); 
                        (var thn#2 := _module.com._h5(c#0); 
                          (var b#4 := _module.com._h4(c#0); 
                            _module.__default.big__step_h($ly, 
                              ORD#Minus(_k#0, ORD#FromNat(1)), 
                              (if _module.__default.bval($LS($LZ), b#4, s#0) then thn#2 else els#2), 
                              s#0, 
                              t#0))))
                       else (var body#2 := _module.com._h8(c#0); 
                        (var b#5 := _module.com._h7(c#0); 
                          (!_module.__default.bval($LS($LZ), b#5, s#0) && Map#Equal(s#0, t#0))
                             || (_module.__default.bval($LS($LZ), b#5, s#0)
                               && (exists s'#9: Map Box Box :: 
                                { _module.__default.big__step_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), #_module.com.While(b#5, body#2), s'#9, t#0) } 
                                  { _module.__default.big__step_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), body#2, s#0, s'#9) } 
                                $Is(s'#9, TMap(TSeq(TChar), TInt))
                                   && 
                                  _module.__default.big__step_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), body#2, s#0, s'#9)
                                   && _module.__default.big__step_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), #_module.com.While(b#5, body#2), s'#9, t#0))))))))))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (exists _k'#0: Box :: 
                { _module.__default.big__step_h($ly, _k'#0, c#0, s#0, t#0) } 
                ORD#LessThanLimit(_k'#0, _k#0)
                   && _module.__default.big__step_h($ly, _k'#0, c#0, s#0, t#0)))));

// definition axiom for _module.__default.big__step_h for decreasing-related literals (revealed)
axiom 9 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: Box, c#0: DatatypeType, s#0: Map Box Box, t#0: Map Box Box :: 
    {:weight 3} { _module.__default.big__step_h($LS($ly), Lit(_k#0), c#0, s#0, t#0) } 
    _module.__default.big__step_h#canCall(Lit(_k#0), c#0, s#0, t#0)
         || (9 != $FunctionContextHeight
           && 
          $Is(c#0, Tclass._module.com())
           && $Is(s#0, TMap(TSeq(TChar), TInt))
           && $Is(t#0, TMap(TSeq(TChar), TInt)))
       ==> (0 < ORD#Offset(_k#0)
           ==> 
          !_module.com.SKIP_q(c#0)
           ==> (_module.com.Assign_q(c#0)
               ==> (var a#6 := _module.com._h1(c#0); _module.__default.aval#canCall(a#6, s#0)))
             && (!_module.com.Assign_q(c#0)
               ==> (_module.com.Seq_q(c#0)
                   ==> (var c1#6 := _module.com._h3(c#0); 
                    (var c0#6 := _module.com._h2(c#0); 
                      (forall s'#16: Map Box Box :: 
                        { _module.__default.big__step_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), c1#6, s'#16, t#0) } 
                          { _module.__default.big__step_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), c0#6, s#0, s'#16) } 
                        $Is(s'#16, TMap(TSeq(TChar), TInt))
                           ==> _module.__default.big__step_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), c0#6, s#0, s'#16)
                             && (_module.__default.big__step_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), c0#6, s#0, s'#16)
                               ==> _module.__default.big__step_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), c1#6, s'#16, t#0))))))
                 && (!_module.com.Seq_q(c#0)
                   ==> (_module.com.If_q(c#0)
                       ==> (var els#6 := _module.com._h6(c#0); 
                        (var thn#6 := _module.com._h5(c#0); 
                          (var b#12 := _module.com._h4(c#0); 
                            _module.__default.bval#canCall(b#12, s#0)
                               && _module.__default.big__step_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), 
                                (if _module.__default.bval($LS($LZ), b#12, s#0) then thn#6 else els#6), 
                                s#0, 
                                t#0)))))
                     && (!_module.com.If_q(c#0)
                       ==> (var body#6 := _module.com._h8(c#0); 
                        (var b#13 := _module.com._h7(c#0); 
                          _module.__default.bval#canCall(b#13, s#0)
                             && (!(!_module.__default.bval($LS($LZ), b#13, s#0) && Map#Equal(s#0, t#0))
                               ==> _module.__default.bval#canCall(b#13, s#0)
                                 && (_module.__default.bval($LS($LZ), b#13, s#0)
                                   ==> (forall s'#17: Map Box Box :: 
                                    { _module.__default.big__step_h($LS($ly), 
                                        ORD#Minus(_k#0, ORD#FromNat(1)), 
                                        #_module.com.While(b#13, body#6), 
                                        s'#17, 
                                        t#0) } 
                                      { _module.__default.big__step_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), body#6, s#0, s'#17) } 
                                    $Is(s'#17, TMap(TSeq(TChar), TInt))
                                       ==> _module.__default.big__step_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), body#6, s#0, s'#17)
                                         && (_module.__default.big__step_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), body#6, s#0, s'#17)
                                           ==> _module.__default.big__step_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), #_module.com.While(b#13, body#6), s'#17, t#0)))))))))))
         && (
          (0 < ORD#Offset(_k#0)
           ==> (if _module.com.SKIP_q(c#0)
             then Map#Equal(s#0, t#0)
             else (if _module.com.Assign_q(c#0)
               then (var a#7 := _module.com._h1(c#0); 
                (var x#7 := _module.com._h0(c#0); 
                  Map#Equal(t#0, Map#Build(s#0, $Box(x#7), $Box(_module.__default.aval($LS($LZ), a#7, s#0))))))
               else (if _module.com.Seq_q(c#0)
                 then (var c1#7 := _module.com._h3(c#0); 
                  (var c0#7 := _module.com._h2(c#0); 
                    (exists s'#18: Map Box Box :: 
                      { _module.__default.big__step_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), c1#7, s'#18, t#0) } 
                        { _module.__default.big__step_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), c0#7, s#0, s'#18) } 
                      $Is(s'#18, TMap(TSeq(TChar), TInt))
                         && 
                        _module.__default.big__step_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), c0#7, s#0, s'#18)
                         && _module.__default.big__step_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), c1#7, s'#18, t#0))))
                 else (if _module.com.If_q(c#0)
                   then (var els#7 := _module.com._h6(c#0); 
                    (var thn#7 := _module.com._h5(c#0); 
                      (var b#14 := _module.com._h4(c#0); 
                        _module.__default.big__step_h($LS($ly), 
                          ORD#Minus(_k#0, ORD#FromNat(1)), 
                          (if _module.__default.bval($LS($LZ), b#14, s#0) then thn#7 else els#7), 
                          s#0, 
                          t#0))))
                   else (var body#7 := _module.com._h8(c#0); 
                    (var b#15 := _module.com._h7(c#0); 
                      (!_module.__default.bval($LS($LZ), b#15, s#0) && Map#Equal(s#0, t#0))
                         || (_module.__default.bval($LS($LZ), b#15, s#0)
                           && (exists s'#19: Map Box Box :: 
                            { _module.__default.big__step_h($LS($ly), 
                                ORD#Minus(_k#0, ORD#FromNat(1)), 
                                #_module.com.While(b#15, body#7), 
                                s'#19, 
                                t#0) } 
                              { _module.__default.big__step_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), body#7, s#0, s'#19) } 
                            $Is(s'#19, TMap(TSeq(TChar), TInt))
                               && 
                              _module.__default.big__step_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), body#7, s#0, s'#19)
                               && _module.__default.big__step_h($LS($ly), 
                                ORD#Minus(_k#0, ORD#FromNat(1)), 
                                #_module.com.While(b#15, body#7), 
                                s'#19, 
                                t#0))))))))))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#1: Box :: 
            { _module.__default.big__step_h($LS($ly), _k'#1, c#0, s#0, t#0) } 
            ORD#LessThanLimit(_k'#1, _k#0)
               ==> _module.__default.big__step_h#canCall(_k'#1, c#0, s#0, t#0)))
         && _module.__default.big__step_h($LS($ly), Lit(_k#0), c#0, s#0, t#0)
           == ((0 < ORD#Offset(_k#0)
               ==> (if _module.com.SKIP_q(c#0)
                 then Map#Equal(s#0, t#0)
                 else (if _module.com.Assign_q(c#0)
                   then (var a#5 := _module.com._h1(c#0); 
                    (var x#5 := _module.com._h0(c#0); 
                      Map#Equal(t#0, Map#Build(s#0, $Box(x#5), $Box(_module.__default.aval($LS($LZ), a#5, s#0))))))
                   else (if _module.com.Seq_q(c#0)
                     then (var c1#5 := _module.com._h3(c#0); 
                      (var c0#5 := _module.com._h2(c#0); 
                        (exists s'#14: Map Box Box :: 
                          { _module.__default.big__step_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), c1#5, s'#14, t#0) } 
                            { _module.__default.big__step_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), c0#5, s#0, s'#14) } 
                          $Is(s'#14, TMap(TSeq(TChar), TInt))
                             && 
                            _module.__default.big__step_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), c0#5, s#0, s'#14)
                             && _module.__default.big__step_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), c1#5, s'#14, t#0))))
                     else (if _module.com.If_q(c#0)
                       then (var els#5 := _module.com._h6(c#0); 
                        (var thn#5 := _module.com._h5(c#0); 
                          (var b#10 := _module.com._h4(c#0); 
                            _module.__default.big__step_h($LS($ly), 
                              ORD#Minus(_k#0, ORD#FromNat(1)), 
                              (if _module.__default.bval($LS($LZ), b#10, s#0) then thn#5 else els#5), 
                              s#0, 
                              t#0))))
                       else (var body#5 := _module.com._h8(c#0); 
                        (var b#11 := _module.com._h7(c#0); 
                          (!_module.__default.bval($LS($LZ), b#11, s#0) && Map#Equal(s#0, t#0))
                             || (_module.__default.bval($LS($LZ), b#11, s#0)
                               && (exists s'#15: Map Box Box :: 
                                { _module.__default.big__step_h($LS($ly), 
                                    ORD#Minus(_k#0, ORD#FromNat(1)), 
                                    #_module.com.While(b#11, body#5), 
                                    s'#15, 
                                    t#0) } 
                                  { _module.__default.big__step_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), body#5, s#0, s'#15) } 
                                $Is(s'#15, TMap(TSeq(TChar), TInt))
                                   && 
                                  _module.__default.big__step_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), body#5, s#0, s'#15)
                                   && _module.__default.big__step_h($LS($ly), 
                                    ORD#Minus(_k#0, ORD#FromNat(1)), 
                                    #_module.com.While(b#11, body#5), 
                                    s'#15, 
                                    t#0))))))))))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (exists _k'#1: Box :: 
                { _module.__default.big__step_h($LS($ly), _k'#1, c#0, s#0, t#0) } 
                ORD#LessThanLimit(_k'#1, _k#0)
                   && _module.__default.big__step_h($LS($ly), _k'#1, c#0, s#0, t#0)))));

// definition axiom for _module.__default.big__step_h for all literals (revealed)
axiom 9 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: Box, c#0: DatatypeType, s#0: Map Box Box, t#0: Map Box Box :: 
    {:weight 3} { _module.__default.big__step_h($LS($ly), Lit(_k#0), Lit(c#0), Lit(s#0), Lit(t#0)) } 
    _module.__default.big__step_h#canCall(Lit(_k#0), Lit(c#0), Lit(s#0), Lit(t#0))
         || (9 != $FunctionContextHeight
           && 
          $Is(c#0, Tclass._module.com())
           && $Is(s#0, TMap(TSeq(TChar), TInt))
           && $Is(t#0, TMap(TSeq(TChar), TInt)))
       ==> (0 < ORD#Offset(_k#0)
           ==> 
          !_module.com.SKIP_q(c#0)
           ==> (_module.com.Assign_q(c#0)
               ==> (var a#9 := _module.com._h1(c#0); _module.__default.aval#canCall(a#9, s#0)))
             && (!_module.com.Assign_q(c#0)
               ==> (_module.com.Seq_q(c#0)
                   ==> (var c1#9 := _module.com._h3(c#0); 
                    (var c0#9 := _module.com._h2(c#0); 
                      (forall s'#22: Map Box Box :: 
                        { _module.__default.big__step_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), c1#9, s'#22, t#0) } 
                          { _module.__default.big__step_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), c0#9, s#0, s'#22) } 
                        $Is(s'#22, TMap(TSeq(TChar), TInt))
                           ==> _module.__default.big__step_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), c0#9, s#0, s'#22)
                             && (_module.__default.big__step_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), c0#9, s#0, s'#22)
                               ==> _module.__default.big__step_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), c1#9, s'#22, t#0))))))
                 && (!_module.com.Seq_q(c#0)
                   ==> (_module.com.If_q(c#0)
                       ==> (var els#9 := _module.com._h6(c#0); 
                        (var thn#9 := _module.com._h5(c#0); 
                          (var b#18 := _module.com._h4(c#0); 
                            _module.__default.bval#canCall(b#18, s#0)
                               && _module.__default.big__step_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), 
                                (if _module.__default.bval($LS($LZ), b#18, s#0) then thn#9 else els#9), 
                                s#0, 
                                t#0)))))
                     && (!_module.com.If_q(c#0)
                       ==> (var body#9 := _module.com._h8(c#0); 
                        (var b#19 := _module.com._h7(c#0); 
                          _module.__default.bval#canCall(b#19, s#0)
                             && (!(!_module.__default.bval($LS($LZ), b#19, s#0) && Map#Equal(s#0, t#0))
                               ==> _module.__default.bval#canCall(b#19, s#0)
                                 && (_module.__default.bval($LS($LZ), b#19, s#0)
                                   ==> (forall s'#23: Map Box Box :: 
                                    { _module.__default.big__step_h($LS($ly), 
                                        ORD#Minus(_k#0, ORD#FromNat(1)), 
                                        #_module.com.While(b#19, body#9), 
                                        s'#23, 
                                        t#0) } 
                                      { _module.__default.big__step_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), body#9, s#0, s'#23) } 
                                    $Is(s'#23, TMap(TSeq(TChar), TInt))
                                       ==> _module.__default.big__step_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), body#9, s#0, s'#23)
                                         && (_module.__default.big__step_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), body#9, s#0, s'#23)
                                           ==> _module.__default.big__step_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), #_module.com.While(b#19, body#9), s'#23, t#0)))))))))))
         && (
          (0 < ORD#Offset(_k#0)
           ==> (if _module.com.SKIP_q(c#0)
             then Map#Equal(s#0, t#0)
             else (if _module.com.Assign_q(c#0)
               then (var a#10 := _module.com._h1(c#0); 
                (var x#10 := _module.com._h0(c#0); 
                  Map#Equal(t#0, 
                    Map#Build(s#0, $Box(x#10), $Box(_module.__default.aval($LS($LZ), a#10, s#0))))))
               else (if _module.com.Seq_q(c#0)
                 then (var c1#10 := _module.com._h3(c#0); 
                  (var c0#10 := _module.com._h2(c#0); 
                    (exists s'#24: Map Box Box :: 
                      { _module.__default.big__step_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), c1#10, s'#24, t#0) } 
                        { _module.__default.big__step_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), c0#10, s#0, s'#24) } 
                      $Is(s'#24, TMap(TSeq(TChar), TInt))
                         && 
                        _module.__default.big__step_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), c0#10, s#0, s'#24)
                         && _module.__default.big__step_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), c1#10, s'#24, t#0))))
                 else (if _module.com.If_q(c#0)
                   then (var els#10 := _module.com._h6(c#0); 
                    (var thn#10 := _module.com._h5(c#0); 
                      (var b#20 := _module.com._h4(c#0); 
                        _module.__default.big__step_h($LS($ly), 
                          ORD#Minus(_k#0, ORD#FromNat(1)), 
                          (if _module.__default.bval($LS($LZ), b#20, s#0) then thn#10 else els#10), 
                          s#0, 
                          t#0))))
                   else (var body#10 := _module.com._h8(c#0); 
                    (var b#21 := _module.com._h7(c#0); 
                      (!_module.__default.bval($LS($LZ), b#21, s#0) && Map#Equal(s#0, t#0))
                         || (_module.__default.bval($LS($LZ), b#21, s#0)
                           && (exists s'#25: Map Box Box :: 
                            { _module.__default.big__step_h($LS($ly), 
                                ORD#Minus(_k#0, ORD#FromNat(1)), 
                                #_module.com.While(b#21, body#10), 
                                s'#25, 
                                t#0) } 
                              { _module.__default.big__step_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), body#10, s#0, s'#25) } 
                            $Is(s'#25, TMap(TSeq(TChar), TInt))
                               && 
                              _module.__default.big__step_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), body#10, s#0, s'#25)
                               && _module.__default.big__step_h($LS($ly), 
                                ORD#Minus(_k#0, ORD#FromNat(1)), 
                                #_module.com.While(b#21, body#10), 
                                s'#25, 
                                t#0))))))))))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#2: Box :: 
            { _module.__default.big__step_h($LS($ly), _k'#2, c#0, s#0, t#0) } 
            ORD#LessThanLimit(_k'#2, _k#0)
               ==> _module.__default.big__step_h#canCall(_k'#2, c#0, s#0, t#0)))
         && _module.__default.big__step_h($LS($ly), Lit(_k#0), Lit(c#0), Lit(s#0), Lit(t#0))
           == ((0 < ORD#Offset(_k#0)
               ==> (if _module.com.SKIP_q(c#0)
                 then Map#Equal(s#0, t#0)
                 else (if _module.com.Assign_q(c#0)
                   then (var a#8 := _module.com._h1(c#0); 
                    (var x#8 := _module.com._h0(c#0); 
                      Map#Equal(t#0, Map#Build(s#0, $Box(x#8), $Box(_module.__default.aval($LS($LZ), a#8, s#0))))))
                   else (if _module.com.Seq_q(c#0)
                     then (var c1#8 := _module.com._h3(c#0); 
                      (var c0#8 := _module.com._h2(c#0); 
                        (exists s'#20: Map Box Box :: 
                          { _module.__default.big__step_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), c1#8, s'#20, t#0) } 
                            { _module.__default.big__step_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), c0#8, s#0, s'#20) } 
                          $Is(s'#20, TMap(TSeq(TChar), TInt))
                             && 
                            _module.__default.big__step_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), c0#8, s#0, s'#20)
                             && _module.__default.big__step_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), c1#8, s'#20, t#0))))
                     else (if _module.com.If_q(c#0)
                       then (var els#8 := _module.com._h6(c#0); 
                        (var thn#8 := _module.com._h5(c#0); 
                          (var b#16 := _module.com._h4(c#0); 
                            _module.__default.big__step_h($LS($ly), 
                              ORD#Minus(_k#0, ORD#FromNat(1)), 
                              (if _module.__default.bval($LS($LZ), b#16, s#0) then thn#8 else els#8), 
                              s#0, 
                              t#0))))
                       else (var body#8 := _module.com._h8(c#0); 
                        (var b#17 := _module.com._h7(c#0); 
                          (!_module.__default.bval($LS($LZ), b#17, s#0) && Map#Equal(s#0, t#0))
                             || (_module.__default.bval($LS($LZ), b#17, s#0)
                               && (exists s'#21: Map Box Box :: 
                                { _module.__default.big__step_h($LS($ly), 
                                    ORD#Minus(_k#0, ORD#FromNat(1)), 
                                    #_module.com.While(b#17, body#8), 
                                    s'#21, 
                                    t#0) } 
                                  { _module.__default.big__step_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), body#8, s#0, s'#21) } 
                                $Is(s'#21, TMap(TSeq(TChar), TInt))
                                   && 
                                  _module.__default.big__step_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), body#8, s#0, s'#21)
                                   && _module.__default.big__step_h($LS($ly), 
                                    ORD#Minus(_k#0, ORD#FromNat(1)), 
                                    #_module.com.While(b#17, body#8), 
                                    s'#21, 
                                    t#0))))))))))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (exists _k'#2: Box :: 
                { _module.__default.big__step_h($LS($ly), _k'#2, c#0, s#0, t#0) } 
                ORD#LessThanLimit(_k'#2, _k#0)
                   && _module.__default.big__step_h($LS($ly), _k'#2, c#0, s#0, t#0)))));

procedure {:_induction s#0, t#0} CheckWellformed$$_module.__default.Example1(s#0: Map Box Box
       where $Is(s#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s#0, TMap(TSeq(TChar), TInt), $Heap), 
    t#0: Map Box Box
       where $Is(t#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(t#0, TMap(TSeq(TChar), TInt), $Heap));
  free requires 29 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction s#0, t#0} Call$$_module.__default.Example1(s#0: Map Box Box
       where $Is(s#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s#0, TMap(TSeq(TChar), TInt), $Heap), 
    t#0: Map Box Box
       where $Is(t#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(t#0, TMap(TSeq(TChar), TInt), $Heap));
  // user-defined preconditions
  requires Map#Equal(t#0, 
    Map#Build(Map#Build(s#0, 
        $Box(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120))))), 
        $Box(LitInt(5))), 
      $Box(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(121))))), 
      $Box(LitInt(5))));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.big__step#canCall(Lit(#_module.com.Seq(Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))), 
            Lit(#_module.aexp.N(LitInt(5))))), 
        Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(121)))), 
            Lit(#_module.aexp.V(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))))))))), 
    s#0, 
    t#0);
  ensures _module.__default.big__step($LS($LS($LZ)), 
    Lit(#_module.com.Seq(Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))), 
            Lit(#_module.aexp.N(LitInt(5))))), 
        Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(121)))), 
            Lit(#_module.aexp.V(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))))))))), 
    s#0, 
    t#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction s#0, t#0} Impl$$_module.__default.Example1(s#0: Map Box Box
       where $Is(s#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s#0, TMap(TSeq(TChar), TInt), $Heap), 
    t#0: Map Box Box
       where $Is(t#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(t#0, TMap(TSeq(TChar), TInt), $Heap))
   returns ($_reverifyPost: bool);
  free requires 29 == $FunctionContextHeight;
  // user-defined preconditions
  requires Map#Equal(t#0, 
    Map#Build(Map#Build(s#0, 
        $Box(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120))))), 
        $Box(LitInt(5))), 
      $Box(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(121))))), 
      $Box(LitInt(5))));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.big__step#canCall(Lit(#_module.com.Seq(Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))), 
            Lit(#_module.aexp.N(LitInt(5))))), 
        Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(121)))), 
            Lit(#_module.aexp.V(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))))))))), 
    s#0, 
    t#0);
  ensures _module.__default.big__step($LS($LS($LZ)), 
    Lit(#_module.com.Seq(Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))), 
            Lit(#_module.aexp.N(LitInt(5))))), 
        Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(121)))), 
            Lit(#_module.aexp.V(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))))))))), 
    s#0, 
    t#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction s#0, t#0} Impl$$_module.__default.Example1(s#0: Map Box Box, t#0: Map Box Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var s'#0: Map Box Box
     where $Is(s'#0, TMap(TSeq(TChar), TInt))
       && $IsAlloc(s'#0, TMap(TSeq(TChar), TInt), $Heap);
  var ##_k#0_0_0: Box;
  var ##c#0_0_0: DatatypeType;
  var ##s#0_0_0: Map Box Box;
  var ##t#0_0_0: Map Box Box;
  var ##_k#0_0_1: Box;
  var ##c#0_0_1: DatatypeType;
  var ##s#0_0_1: Map Box Box;
  var ##t#0_0_1: Map Box Box;
  var ##_k#0_1_0: Box;
  var ##c#0_1_0: DatatypeType;
  var ##s#0_1_0: Map Box Box;
  var ##t#0_1_0: Map Box Box;
  var ##_k#0_1_1: Box;
  var ##c#0_1_1: DatatypeType;
  var ##s#0_1_1: Map Box Box;
  var ##t#0_1_1: Map Box Box;
  var sm#0_1_0: Map Box Box;
  var ##_k#0_1_2: Box;
  var ##c#0_1_2: DatatypeType;
  var ##s#0_1_2: Map Box Box;
  var ##t#0_1_2: Map Box Box;
  var ##_k#0_1_3: Box;
  var ##c#0_1_3: DatatypeType;
  var ##s#0_1_3: Map Box Box;
  var ##t#0_1_3: Map Box Box;
  var sm#0_2_0: Map Box Box;
  var ##_k#0_2_0: Box;
  var ##c#0_2_0: DatatypeType;
  var ##s#0_2_0: Map Box Box;
  var ##t#0_2_0: Map Box Box;
  var ##_k#0_2_1: Box;
  var ##c#0_2_1: DatatypeType;
  var ##s#0_2_1: Map Box Box;
  var ##t#0_2_1: Map Box Box;
  var ##_k#0_2_2: Box;
  var ##c#0_2_2: DatatypeType;
  var ##s#0_2_2: Map Box Box;
  var ##t#0_2_2: Map Box Box;
  var ##_k#0_3_0: Box;
  var ##c#0_3_0: DatatypeType;
  var ##s#0_3_0: Map Box Box;
  var ##t#0_3_0: Map Box Box;
  var ##c#0_3_1: DatatypeType;
  var ##s#0_3_1: Map Box Box;
  var ##t#0_3_1: Map Box Box;

    // AddMethodImpl: Example1, Impl$$_module.__default.Example1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(63,0): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#s0#0: Map Box Box, $ih#t0#0: Map Box Box :: 
      $Is($ih#s0#0, TMap(TSeq(TChar), TInt))
           && $Is($ih#t0#0, TMap(TSeq(TChar), TInt))
           && Map#Equal($ih#t0#0, 
            Map#Build(Map#Build($ih#s0#0, 
                $Box(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120))))), 
                $Box(LitInt(5))), 
              $Box(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(121))))), 
              $Box(LitInt(5))))
           && ((Set#Subset(Map#Domain($ih#s0#0), Map#Domain(s#0))
               && !Set#Subset(Map#Domain(s#0), Map#Domain($ih#s0#0)))
             || (Set#Equal(Map#Domain($ih#s0#0), Map#Domain(s#0))
               && 
              Set#Subset(Map#Domain($ih#t0#0), Map#Domain(t#0))
               && !Set#Subset(Map#Domain(t#0), Map#Domain($ih#t0#0))))
         ==> _module.__default.big__step($LS($LZ), 
          Lit(#_module.com.Seq(Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))), 
                  Lit(#_module.aexp.N(LitInt(5))))), 
              Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(121)))), 
                  Lit(#_module.aexp.V(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))))))))), 
          $ih#s0#0, 
          $ih#t0#0));
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(64,10)
    assume true;
    assume true;
    s'#0 := Map#Build(s#0, 
      $Box(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120))))), 
      $Box(LitInt(5)));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(64,23)"} true;
    // ----- calc statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(65,3)
    // Assume Fuel Constant
    if (*)
    {
        // ----- assert wf[initial] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(65,3)
        assume true;
        assume false;
    }
    else if (*)
    {
        // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(65,3)
        ##_k#0_3_0 := Lit(ORD#FromNat(5));
        // assume allocatedness for argument to function
        assume $IsAlloc(##_k#0_3_0, TORDINAL, $Heap);
        ##c#0_3_0 := Lit(#_module.com.Seq(Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))), 
                Lit(#_module.aexp.N(LitInt(5))))), 
            Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(121)))), 
                Lit(#_module.aexp.V(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120))))))))));
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#0_3_0, Tclass._module.com(), $Heap);
        ##s#0_3_0 := s#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#0_3_0, TMap(TSeq(TChar), TInt), $Heap);
        ##t#0_3_0 := t#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##t#0_3_0, TMap(TSeq(TChar), TInt), $Heap);
        assume _module.__default.big__step_h#canCall(Lit(ORD#FromNat(5)), 
          Lit(#_module.com.Seq(Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))), 
                  Lit(#_module.aexp.N(LitInt(5))))), 
              Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(121)))), 
                  Lit(#_module.aexp.V(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))))))))), 
          s#0, 
          t#0);
        assume _module.__default.big__step_h#canCall(Lit(ORD#FromNat(5)), 
          Lit(#_module.com.Seq(Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))), 
                  Lit(#_module.aexp.N(LitInt(5))))), 
              Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(121)))), 
                  Lit(#_module.aexp.V(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))))))))), 
          s#0, 
          t#0);
        // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(65,3)
        assume _module.__default.big__step_h($LS($LZ), 
          Lit(ORD#FromNat(5)), 
          Lit(#_module.com.Seq(Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))), 
                  Lit(#_module.aexp.N(LitInt(5))))), 
              Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(121)))), 
                  Lit(#_module.aexp.V(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))))))))), 
          s#0, 
          t#0);
        // ----- Hint0 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(65,3)
        // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(65,3)
        ##c#0_3_1 := Lit(#_module.com.Seq(Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))), 
                Lit(#_module.aexp.N(LitInt(5))))), 
            Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(121)))), 
                Lit(#_module.aexp.V(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120))))))))));
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#0_3_1, Tclass._module.com(), $Heap);
        ##s#0_3_1 := s#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#0_3_1, TMap(TSeq(TChar), TInt), $Heap);
        ##t#0_3_1 := t#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##t#0_3_1, TMap(TSeq(TChar), TInt), $Heap);
        assume _module.__default.big__step#canCall(Lit(#_module.com.Seq(Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))), 
                  Lit(#_module.aexp.N(LitInt(5))))), 
              Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(121)))), 
                  Lit(#_module.aexp.V(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))))))))), 
          s#0, 
          t#0);
        assume _module.__default.big__step#canCall(Lit(#_module.com.Seq(Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))), 
                  Lit(#_module.aexp.N(LitInt(5))))), 
              Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(121)))), 
                  Lit(#_module.aexp.V(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))))))))), 
          s#0, 
          t#0);
        // ----- assert line0 <== line1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(65,3)
        assert {:subsumption 0} _module.__default.big__step_h($LS($LZ), 
            Lit(ORD#FromNat(5)), 
            Lit(#_module.com.Seq(Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))), 
                    Lit(#_module.aexp.N(LitInt(5))))), 
                Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(121)))), 
                    Lit(#_module.aexp.V(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))))))))), 
            s#0, 
            t#0)
           ==> _module.__default.big__step($LS($LS($LZ)), 
            Lit(#_module.com.Seq(Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))), 
                    Lit(#_module.aexp.N(LitInt(5))))), 
                Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(121)))), 
                    Lit(#_module.aexp.V(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))))))))), 
            s#0, 
            t#0);
        assume false;
    }
    else if (*)
    {
        // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(65,3)
        // Begin Comprehension WF check
        havoc sm#0_2_0;
        if ($Is(sm#0_2_0, TMap(TSeq(TChar), TInt)))
        {
            ##_k#0_2_0 := Lit(ORD#FromNat(4));
            // assume allocatedness for argument to function
            assume $IsAlloc(##_k#0_2_0, TORDINAL, $Heap);
            ##c#0_2_0 := Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))), 
                Lit(#_module.aexp.N(LitInt(5)))));
            // assume allocatedness for argument to function
            assume $IsAlloc(##c#0_2_0, Tclass._module.com(), $Heap);
            ##s#0_2_0 := s#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#0_2_0, TMap(TSeq(TChar), TInt), $Heap);
            ##t#0_2_0 := sm#0_2_0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#0_2_0, TMap(TSeq(TChar), TInt), $Heap);
            assume _module.__default.big__step_h#canCall(Lit(ORD#FromNat(4)), 
              Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))), 
                  Lit(#_module.aexp.N(LitInt(5))))), 
              s#0, 
              sm#0_2_0);
            if (_module.__default.big__step_h($LS($LZ), 
              Lit(ORD#FromNat(4)), 
              Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))), 
                  Lit(#_module.aexp.N(LitInt(5))))), 
              s#0, 
              sm#0_2_0))
            {
                ##_k#0_2_1 := Lit(ORD#FromNat(4));
                // assume allocatedness for argument to function
                assume $IsAlloc(##_k#0_2_1, TORDINAL, $Heap);
                ##c#0_2_1 := Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(121)))), 
                    Lit(#_module.aexp.V(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120))))))));
                // assume allocatedness for argument to function
                assume $IsAlloc(##c#0_2_1, Tclass._module.com(), $Heap);
                ##s#0_2_1 := sm#0_2_0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#0_2_1, TMap(TSeq(TChar), TInt), $Heap);
                ##t#0_2_1 := t#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#0_2_1, TMap(TSeq(TChar), TInt), $Heap);
                assume _module.__default.big__step_h#canCall(Lit(ORD#FromNat(4)), 
                  Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(121)))), 
                      Lit(#_module.aexp.V(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))))))), 
                  sm#0_2_0, 
                  t#0);
            }
        }

        // End Comprehension WF check
        assume (forall sm#0_1_1: Map Box Box :: 
          { _module.__default.big__step_h($LS($LZ), 
              ORD#FromNat(4), 
              #_module.com.Assign(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(121))), 
                #_module.aexp.V(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120))))), 
              sm#0_1_1, 
              t#0) } 
            { _module.__default.big__step_h($LS($LZ), 
              ORD#FromNat(4), 
              #_module.com.Assign(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120))), #_module.aexp.N(5)), 
              s#0, 
              sm#0_1_1) } 
          $Is(sm#0_1_1, TMap(TSeq(TChar), TInt))
             ==> _module.__default.big__step_h#canCall(Lit(ORD#FromNat(4)), 
                Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))), 
                    Lit(#_module.aexp.N(LitInt(5))))), 
                s#0, 
                sm#0_1_1)
               && (_module.__default.big__step_h($LS($LZ), 
                  Lit(ORD#FromNat(4)), 
                  Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))), 
                      Lit(#_module.aexp.N(LitInt(5))))), 
                  s#0, 
                  sm#0_1_1)
                 ==> _module.__default.big__step_h#canCall(Lit(ORD#FromNat(4)), 
                  Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(121)))), 
                      Lit(#_module.aexp.V(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))))))), 
                  sm#0_1_1, 
                  t#0)));
        // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(65,3)
        assume (exists sm#0_1_1: Map Box Box :: 
          { _module.__default.big__step_h($LS($LZ), 
              ORD#FromNat(4), 
              #_module.com.Assign(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(121))), 
                #_module.aexp.V(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120))))), 
              sm#0_1_1, 
              t#0) } 
            { _module.__default.big__step_h($LS($LZ), 
              ORD#FromNat(4), 
              #_module.com.Assign(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120))), #_module.aexp.N(5)), 
              s#0, 
              sm#0_1_1) } 
          $Is(sm#0_1_1, TMap(TSeq(TChar), TInt))
             && 
            _module.__default.big__step_h($LS($LZ), 
              Lit(ORD#FromNat(4)), 
              Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))), 
                  Lit(#_module.aexp.N(LitInt(5))))), 
              s#0, 
              sm#0_1_1)
             && _module.__default.big__step_h($LS($LZ), 
              Lit(ORD#FromNat(4)), 
              Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(121)))), 
                  Lit(#_module.aexp.V(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))))))), 
              sm#0_1_1, 
              t#0));
        // ----- Hint1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(65,3)
        // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(65,3)
        ##_k#0_2_2 := Lit(ORD#FromNat(5));
        // assume allocatedness for argument to function
        assume $IsAlloc(##_k#0_2_2, TORDINAL, $Heap);
        ##c#0_2_2 := Lit(#_module.com.Seq(Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))), 
                Lit(#_module.aexp.N(LitInt(5))))), 
            Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(121)))), 
                Lit(#_module.aexp.V(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120))))))))));
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#0_2_2, Tclass._module.com(), $Heap);
        ##s#0_2_2 := s#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#0_2_2, TMap(TSeq(TChar), TInt), $Heap);
        ##t#0_2_2 := t#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##t#0_2_2, TMap(TSeq(TChar), TInt), $Heap);
        assume _module.__default.big__step_h#canCall(Lit(ORD#FromNat(5)), 
          Lit(#_module.com.Seq(Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))), 
                  Lit(#_module.aexp.N(LitInt(5))))), 
              Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(121)))), 
                  Lit(#_module.aexp.V(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))))))))), 
          s#0, 
          t#0);
        assume _module.__default.big__step_h#canCall(Lit(ORD#FromNat(5)), 
          Lit(#_module.com.Seq(Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))), 
                  Lit(#_module.aexp.N(LitInt(5))))), 
              Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(121)))), 
                  Lit(#_module.aexp.V(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))))))))), 
          s#0, 
          t#0);
        // ----- assert line1 <== line2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(65,3)
        assert {:subsumption 0} (exists sm#0_1_1: Map Box Box :: 
            { _module.__default.big__step_h($LS($LZ), 
                ORD#FromNat(4), 
                #_module.com.Assign(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(121))), 
                  #_module.aexp.V(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120))))), 
                sm#0_1_1, 
                t#0) } 
              { _module.__default.big__step_h($LS($LZ), 
                ORD#FromNat(4), 
                #_module.com.Assign(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120))), #_module.aexp.N(5)), 
                s#0, 
                sm#0_1_1) } 
            $Is(sm#0_1_1, TMap(TSeq(TChar), TInt))
               && 
              _module.__default.big__step_h($LS($LZ), 
                Lit(ORD#FromNat(4)), 
                Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))), 
                    Lit(#_module.aexp.N(LitInt(5))))), 
                s#0, 
                sm#0_1_1)
               && _module.__default.big__step_h($LS($LZ), 
                Lit(ORD#FromNat(4)), 
                Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(121)))), 
                    Lit(#_module.aexp.V(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))))))), 
                sm#0_1_1, 
                t#0))
           ==> _module.__default.big__step_h($LS($LS($LZ)), 
            Lit(ORD#FromNat(5)), 
            Lit(#_module.com.Seq(Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))), 
                    Lit(#_module.aexp.N(LitInt(5))))), 
                Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(121)))), 
                    Lit(#_module.aexp.V(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))))))))), 
            s#0, 
            t#0);
        assume false;
    }
    else if (*)
    {
        // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(65,3)
        ##_k#0_1_0 := Lit(ORD#FromNat(4));
        // assume allocatedness for argument to function
        assume $IsAlloc(##_k#0_1_0, TORDINAL, $Heap);
        ##c#0_1_0 := Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))), 
            Lit(#_module.aexp.N(LitInt(5)))));
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#0_1_0, Tclass._module.com(), $Heap);
        ##s#0_1_0 := s#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#0_1_0, TMap(TSeq(TChar), TInt), $Heap);
        ##t#0_1_0 := s'#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##t#0_1_0, TMap(TSeq(TChar), TInt), $Heap);
        assume _module.__default.big__step_h#canCall(Lit(ORD#FromNat(4)), 
          Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))), 
              Lit(#_module.aexp.N(LitInt(5))))), 
          s#0, 
          s'#0);
        if (_module.__default.big__step_h($LS($LZ), 
          Lit(ORD#FromNat(4)), 
          Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))), 
              Lit(#_module.aexp.N(LitInt(5))))), 
          s#0, 
          s'#0))
        {
            ##_k#0_1_1 := Lit(ORD#FromNat(4));
            // assume allocatedness for argument to function
            assume $IsAlloc(##_k#0_1_1, TORDINAL, $Heap);
            ##c#0_1_1 := Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(121)))), 
                Lit(#_module.aexp.V(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120))))))));
            // assume allocatedness for argument to function
            assume $IsAlloc(##c#0_1_1, Tclass._module.com(), $Heap);
            ##s#0_1_1 := s'#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#0_1_1, TMap(TSeq(TChar), TInt), $Heap);
            ##t#0_1_1 := t#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#0_1_1, TMap(TSeq(TChar), TInt), $Heap);
            assume _module.__default.big__step_h#canCall(Lit(ORD#FromNat(4)), 
              Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(121)))), 
                  Lit(#_module.aexp.V(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))))))), 
              s'#0, 
              t#0);
        }

        assume _module.__default.big__step_h#canCall(Lit(ORD#FromNat(4)), 
            Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))), 
                Lit(#_module.aexp.N(LitInt(5))))), 
            s#0, 
            s'#0)
           && (_module.__default.big__step_h($LS($LZ), 
              Lit(ORD#FromNat(4)), 
              Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))), 
                  Lit(#_module.aexp.N(LitInt(5))))), 
              s#0, 
              s'#0)
             ==> _module.__default.big__step_h#canCall(Lit(ORD#FromNat(4)), 
              Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(121)))), 
                  Lit(#_module.aexp.V(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))))))), 
              s'#0, 
              t#0));
        // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(65,3)
        assume _module.__default.big__step_h($LS($LZ), 
            Lit(ORD#FromNat(4)), 
            Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))), 
                Lit(#_module.aexp.N(LitInt(5))))), 
            s#0, 
            s'#0)
           && _module.__default.big__step_h($LS($LZ), 
            Lit(ORD#FromNat(4)), 
            Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(121)))), 
                Lit(#_module.aexp.V(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))))))), 
            s'#0, 
            t#0);
        // ----- Hint2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(65,3)
        // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(65,3)
        // Begin Comprehension WF check
        havoc sm#0_1_0;
        if ($Is(sm#0_1_0, TMap(TSeq(TChar), TInt)))
        {
            ##_k#0_1_2 := Lit(ORD#FromNat(4));
            // assume allocatedness for argument to function
            assume $IsAlloc(##_k#0_1_2, TORDINAL, $Heap);
            ##c#0_1_2 := Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))), 
                Lit(#_module.aexp.N(LitInt(5)))));
            // assume allocatedness for argument to function
            assume $IsAlloc(##c#0_1_2, Tclass._module.com(), $Heap);
            ##s#0_1_2 := s#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#0_1_2, TMap(TSeq(TChar), TInt), $Heap);
            ##t#0_1_2 := sm#0_1_0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#0_1_2, TMap(TSeq(TChar), TInt), $Heap);
            assume _module.__default.big__step_h#canCall(Lit(ORD#FromNat(4)), 
              Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))), 
                  Lit(#_module.aexp.N(LitInt(5))))), 
              s#0, 
              sm#0_1_0);
            if (_module.__default.big__step_h($LS($LZ), 
              Lit(ORD#FromNat(4)), 
              Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))), 
                  Lit(#_module.aexp.N(LitInt(5))))), 
              s#0, 
              sm#0_1_0))
            {
                ##_k#0_1_3 := Lit(ORD#FromNat(4));
                // assume allocatedness for argument to function
                assume $IsAlloc(##_k#0_1_3, TORDINAL, $Heap);
                ##c#0_1_3 := Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(121)))), 
                    Lit(#_module.aexp.V(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120))))))));
                // assume allocatedness for argument to function
                assume $IsAlloc(##c#0_1_3, Tclass._module.com(), $Heap);
                ##s#0_1_3 := sm#0_1_0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#0_1_3, TMap(TSeq(TChar), TInt), $Heap);
                ##t#0_1_3 := t#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#0_1_3, TMap(TSeq(TChar), TInt), $Heap);
                assume _module.__default.big__step_h#canCall(Lit(ORD#FromNat(4)), 
                  Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(121)))), 
                      Lit(#_module.aexp.V(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))))))), 
                  sm#0_1_0, 
                  t#0);
            }
        }

        // End Comprehension WF check
        assume (forall sm#0_1_1: Map Box Box :: 
          { _module.__default.big__step_h($LS($LZ), 
              ORD#FromNat(4), 
              #_module.com.Assign(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(121))), 
                #_module.aexp.V(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120))))), 
              sm#0_1_1, 
              t#0) } 
            { _module.__default.big__step_h($LS($LZ), 
              ORD#FromNat(4), 
              #_module.com.Assign(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120))), #_module.aexp.N(5)), 
              s#0, 
              sm#0_1_1) } 
          $Is(sm#0_1_1, TMap(TSeq(TChar), TInt))
             ==> _module.__default.big__step_h#canCall(Lit(ORD#FromNat(4)), 
                Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))), 
                    Lit(#_module.aexp.N(LitInt(5))))), 
                s#0, 
                sm#0_1_1)
               && (_module.__default.big__step_h($LS($LZ), 
                  Lit(ORD#FromNat(4)), 
                  Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))), 
                      Lit(#_module.aexp.N(LitInt(5))))), 
                  s#0, 
                  sm#0_1_1)
                 ==> _module.__default.big__step_h#canCall(Lit(ORD#FromNat(4)), 
                  Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(121)))), 
                      Lit(#_module.aexp.V(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))))))), 
                  sm#0_1_1, 
                  t#0)));
        // ----- assert line2 <== line3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(65,3)
        assert {:subsumption 0} _module.__default.big__step_h($LS($LZ), 
              Lit(ORD#FromNat(4)), 
              Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))), 
                  Lit(#_module.aexp.N(LitInt(5))))), 
              s#0, 
              s'#0)
             && _module.__default.big__step_h($LS($LZ), 
              Lit(ORD#FromNat(4)), 
              Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(121)))), 
                  Lit(#_module.aexp.V(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))))))), 
              s'#0, 
              t#0)
           ==> (exists sm#0_1_1: Map Box Box :: 
            { _module.__default.big__step_h($LS($LZ), 
                ORD#FromNat(4), 
                #_module.com.Assign(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(121))), 
                  #_module.aexp.V(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120))))), 
                sm#0_1_1, 
                t#0) } 
              { _module.__default.big__step_h($LS($LZ), 
                ORD#FromNat(4), 
                #_module.com.Assign(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120))), #_module.aexp.N(5)), 
                s#0, 
                sm#0_1_1) } 
            $Is(sm#0_1_1, TMap(TSeq(TChar), TInt))
               && 
              _module.__default.big__step_h($LS($LZ), 
                Lit(ORD#FromNat(4)), 
                Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))), 
                    Lit(#_module.aexp.N(LitInt(5))))), 
                s#0, 
                sm#0_1_1)
               && _module.__default.big__step_h($LS($LZ), 
                Lit(ORD#FromNat(4)), 
                Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(121)))), 
                    Lit(#_module.aexp.V(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))))))), 
                sm#0_1_1, 
                t#0));
        assume false;
    }
    else if (*)
    {
        // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(65,3)
        assume true;
        // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(65,3)
        assume true;
        // ----- Hint3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(65,3)
        // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(65,3)
        ##_k#0_0_0 := Lit(ORD#FromNat(4));
        // assume allocatedness for argument to function
        assume $IsAlloc(##_k#0_0_0, TORDINAL, $Heap);
        ##c#0_0_0 := Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))), 
            Lit(#_module.aexp.N(LitInt(5)))));
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#0_0_0, Tclass._module.com(), $Heap);
        ##s#0_0_0 := s#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#0_0_0, TMap(TSeq(TChar), TInt), $Heap);
        ##t#0_0_0 := s'#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##t#0_0_0, TMap(TSeq(TChar), TInt), $Heap);
        assume _module.__default.big__step_h#canCall(Lit(ORD#FromNat(4)), 
          Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))), 
              Lit(#_module.aexp.N(LitInt(5))))), 
          s#0, 
          s'#0);
        if (_module.__default.big__step_h($LS($LZ), 
          Lit(ORD#FromNat(4)), 
          Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))), 
              Lit(#_module.aexp.N(LitInt(5))))), 
          s#0, 
          s'#0))
        {
            ##_k#0_0_1 := Lit(ORD#FromNat(4));
            // assume allocatedness for argument to function
            assume $IsAlloc(##_k#0_0_1, TORDINAL, $Heap);
            ##c#0_0_1 := Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(121)))), 
                Lit(#_module.aexp.V(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120))))))));
            // assume allocatedness for argument to function
            assume $IsAlloc(##c#0_0_1, Tclass._module.com(), $Heap);
            ##s#0_0_1 := s'#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#0_0_1, TMap(TSeq(TChar), TInt), $Heap);
            ##t#0_0_1 := t#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#0_0_1, TMap(TSeq(TChar), TInt), $Heap);
            assume _module.__default.big__step_h#canCall(Lit(ORD#FromNat(4)), 
              Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(121)))), 
                  Lit(#_module.aexp.V(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))))))), 
              s'#0, 
              t#0);
        }

        assume _module.__default.big__step_h#canCall(Lit(ORD#FromNat(4)), 
            Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))), 
                Lit(#_module.aexp.N(LitInt(5))))), 
            s#0, 
            s'#0)
           && (_module.__default.big__step_h($LS($LZ), 
              Lit(ORD#FromNat(4)), 
              Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))), 
                  Lit(#_module.aexp.N(LitInt(5))))), 
              s#0, 
              s'#0)
             ==> _module.__default.big__step_h#canCall(Lit(ORD#FromNat(4)), 
              Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(121)))), 
                  Lit(#_module.aexp.V(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))))))), 
              s'#0, 
              t#0));
        // ----- assert line3 <== line4 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(65,3)
        assert {:subsumption 0} Lit(true)
           ==> _module.__default.big__step_h($LS($LS($LZ)), 
            Lit(ORD#FromNat(4)), 
            Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))), 
                Lit(#_module.aexp.N(LitInt(5))))), 
            s#0, 
            s'#0);
        assert {:subsumption 0} Lit(true)
           ==> _module.__default.big__step_h($LS($LS($LZ)), 
            Lit(ORD#FromNat(4)), 
            Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(121)))), 
                Lit(#_module.aexp.V(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))))))), 
            s'#0, 
            t#0);
        assume false;
    }

    assume true
       ==> _module.__default.big__step($LS($LZ), 
        Lit(#_module.com.Seq(Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))), 
                Lit(#_module.aexp.N(LitInt(5))))), 
            Lit(#_module.com.Assign(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(121)))), 
                Lit(#_module.aexp.V(Lit(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(120)))))))))), 
        s#0, 
        t#0);
}



procedure {:_induction c0#0, c1#0, c2#0, s#0, t#0} CheckWellformed$$_module.__default.SemiAssociativity(c0#0: DatatypeType
       where $Is(c0#0, Tclass._module.com())
         && $IsAlloc(c0#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c0#0), 
    c1#0: DatatypeType
       where $Is(c1#0, Tclass._module.com())
         && $IsAlloc(c1#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c1#0), 
    c2#0: DatatypeType
       where $Is(c2#0, Tclass._module.com())
         && $IsAlloc(c2#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c2#0), 
    s#0: Map Box Box
       where $Is(s#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s#0, TMap(TSeq(TChar), TInt), $Heap), 
    t#0: Map Box Box
       where $Is(t#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(t#0, TMap(TSeq(TChar), TInt), $Heap));
  free requires 30 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction c0#0, c1#0, c2#0, s#0, t#0} Call$$_module.__default.SemiAssociativity(c0#0: DatatypeType
       where $Is(c0#0, Tclass._module.com())
         && $IsAlloc(c0#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c0#0), 
    c1#0: DatatypeType
       where $Is(c1#0, Tclass._module.com())
         && $IsAlloc(c1#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c1#0), 
    c2#0: DatatypeType
       where $Is(c2#0, Tclass._module.com())
         && $IsAlloc(c2#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c2#0), 
    s#0: Map Box Box
       where $Is(s#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s#0, TMap(TSeq(TChar), TInt), $Heap), 
    t#0: Map Box Box
       where $Is(t#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(t#0, TMap(TSeq(TChar), TInt), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.big__step#canCall(#_module.com.Seq(#_module.com.Seq(c0#0, c1#0), c2#0), s#0, t#0)
     && _module.__default.big__step#canCall(#_module.com.Seq(c0#0, #_module.com.Seq(c1#0, c2#0)), s#0, t#0);
  ensures _module.__default.big__step($LS($LS($LZ)), #_module.com.Seq(#_module.com.Seq(c0#0, c1#0), c2#0), s#0, t#0)
     == _module.__default.big__step($LS($LS($LZ)), #_module.com.Seq(c0#0, #_module.com.Seq(c1#0, c2#0)), s#0, t#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction c0#0, c1#0, c2#0, s#0, t#0} Impl$$_module.__default.SemiAssociativity(c0#0: DatatypeType
       where $Is(c0#0, Tclass._module.com())
         && $IsAlloc(c0#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c0#0), 
    c1#0: DatatypeType
       where $Is(c1#0, Tclass._module.com())
         && $IsAlloc(c1#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c1#0), 
    c2#0: DatatypeType
       where $Is(c2#0, Tclass._module.com())
         && $IsAlloc(c2#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c2#0), 
    s#0: Map Box Box
       where $Is(s#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s#0, TMap(TSeq(TChar), TInt), $Heap), 
    t#0: Map Box Box
       where $Is(t#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(t#0, TMap(TSeq(TChar), TInt), $Heap))
   returns ($_reverifyPost: bool);
  free requires 30 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.big__step#canCall(#_module.com.Seq(#_module.com.Seq(c0#0, c1#0), c2#0), s#0, t#0)
     && _module.__default.big__step#canCall(#_module.com.Seq(c0#0, #_module.com.Seq(c1#0, c2#0)), s#0, t#0);
  ensures _module.__default.big__step($LS($LS($LZ)), #_module.com.Seq(#_module.com.Seq(c0#0, c1#0), c2#0), s#0, t#0)
     == _module.__default.big__step($LS($LS($LZ)), #_module.com.Seq(c0#0, #_module.com.Seq(c1#0, c2#0)), s#0, t#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction c0#0, c1#0, c2#0, s#0, t#0} Impl$$_module.__default.SemiAssociativity(c0#0: DatatypeType, 
    c1#0: DatatypeType, 
    c2#0: DatatypeType, 
    s#0: Map Box Box, 
    t#0: Map Box Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;

    // AddMethodImpl: SemiAssociativity, Impl$$_module.__default.SemiAssociativity
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(79,0): initial state"} true;
    assume $IsA#_module.com(c0#0);
    assume $IsA#_module.com(c1#0);
    assume $IsA#_module.com(c2#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#c00#0: DatatypeType, 
        $ih#c10#0: DatatypeType, 
        $ih#c20#0: DatatypeType, 
        $ih#s0#0: Map Box Box, 
        $ih#t0#0: Map Box Box :: 
      $Is($ih#c00#0, Tclass._module.com())
           && $Is($ih#c10#0, Tclass._module.com())
           && $Is($ih#c20#0, Tclass._module.com())
           && $Is($ih#s0#0, TMap(TSeq(TChar), TInt))
           && $Is($ih#t0#0, TMap(TSeq(TChar), TInt))
           && Lit(true)
           && (DtRank($ih#c00#0) < DtRank(c0#0)
             || (DtRank($ih#c00#0) == DtRank(c0#0)
               && (DtRank($ih#c10#0) < DtRank(c1#0)
                 || (DtRank($ih#c10#0) == DtRank(c1#0)
                   && (DtRank($ih#c20#0) < DtRank(c2#0)
                     || (DtRank($ih#c20#0) == DtRank(c2#0)
                       && ((Set#Subset(Map#Domain($ih#s0#0), Map#Domain(s#0))
                           && !Set#Subset(Map#Domain(s#0), Map#Domain($ih#s0#0)))
                         || (Set#Equal(Map#Domain($ih#s0#0), Map#Domain(s#0))
                           && 
                          Set#Subset(Map#Domain($ih#t0#0), Map#Domain(t#0))
                           && !Set#Subset(Map#Domain(t#0), Map#Domain($ih#t0#0))))))))))
         ==> _module.__default.big__step($LS($LZ), 
            #_module.com.Seq(#_module.com.Seq($ih#c00#0, $ih#c10#0), $ih#c20#0), 
            $ih#s0#0, 
            $ih#t0#0)
           == _module.__default.big__step($LS($LZ), 
            #_module.com.Seq($ih#c00#0, #_module.com.Seq($ih#c10#0, $ih#c20#0)), 
            $ih#s0#0, 
            $ih#t0#0));
    $_reverifyPost := false;
}



// function declaration for _module._default.equiv_c
function _module.__default.equiv__c(c#0: DatatypeType, c'#0: DatatypeType) : bool;

function _module.__default.equiv__c#canCall(c#0: DatatypeType, c'#0: DatatypeType) : bool;

// consequence axiom for _module.__default.equiv__c
axiom 10 <= $FunctionContextHeight
   ==> (forall c#0: DatatypeType, c'#0: DatatypeType :: 
    { _module.__default.equiv__c(c#0, c'#0) } 
    _module.__default.equiv__c#canCall(c#0, c'#0)
         || (10 != $FunctionContextHeight
           && 
          $Is(c#0, Tclass._module.com())
           && $Is(c'#0, Tclass._module.com()))
       ==> true);

function _module.__default.equiv__c#requires(DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.equiv__c
axiom (forall c#0: DatatypeType, c'#0: DatatypeType :: 
  { _module.__default.equiv__c#requires(c#0, c'#0) } 
  $Is(c#0, Tclass._module.com()) && $Is(c'#0, Tclass._module.com())
     ==> _module.__default.equiv__c#requires(c#0, c'#0) == true);

// definition axiom for _module.__default.equiv__c (revealed)
axiom 10 <= $FunctionContextHeight
   ==> (forall c#0: DatatypeType, c'#0: DatatypeType :: 
    { _module.__default.equiv__c(c#0, c'#0) } 
    _module.__default.equiv__c#canCall(c#0, c'#0)
         || (10 != $FunctionContextHeight
           && 
          $Is(c#0, Tclass._module.com())
           && $Is(c'#0, Tclass._module.com()))
       ==> (forall s#0: Map Box Box, t#0: Map Box Box :: 
          { _module.__default.big__step($LS($LZ), c'#0, s#0, t#0) } 
            { _module.__default.big__step($LS($LZ), c#0, s#0, t#0) } 
          $Is(s#0, TMap(TSeq(TChar), TInt)) && $Is(t#0, TMap(TSeq(TChar), TInt))
             ==> _module.__default.big__step#canCall(c#0, s#0, t#0)
               && _module.__default.big__step#canCall(c'#0, s#0, t#0))
         && _module.__default.equiv__c(c#0, c'#0)
           == (forall s#0: Map Box Box, t#0: Map Box Box :: 
            { _module.__default.big__step($LS($LZ), c'#0, s#0, t#0) } 
              { _module.__default.big__step($LS($LZ), c#0, s#0, t#0) } 
            $Is(s#0, TMap(TSeq(TChar), TInt)) && $Is(t#0, TMap(TSeq(TChar), TInt))
               ==> _module.__default.big__step($LS($LZ), c#0, s#0, t#0)
                 == _module.__default.big__step($LS($LZ), c'#0, s#0, t#0)));

// definition axiom for _module.__default.equiv__c for all literals (revealed)
axiom 10 <= $FunctionContextHeight
   ==> (forall c#0: DatatypeType, c'#0: DatatypeType :: 
    {:weight 3} { _module.__default.equiv__c(Lit(c#0), Lit(c'#0)) } 
    _module.__default.equiv__c#canCall(Lit(c#0), Lit(c'#0))
         || (10 != $FunctionContextHeight
           && 
          $Is(c#0, Tclass._module.com())
           && $Is(c'#0, Tclass._module.com()))
       ==> (forall s#1: Map Box Box, t#1: Map Box Box :: 
          { _module.__default.big__step($LS($LZ), c'#0, s#1, t#1) } 
            { _module.__default.big__step($LS($LZ), c#0, s#1, t#1) } 
          $Is(s#1, TMap(TSeq(TChar), TInt)) && $Is(t#1, TMap(TSeq(TChar), TInt))
             ==> _module.__default.big__step#canCall(Lit(c#0), s#1, t#1)
               && _module.__default.big__step#canCall(Lit(c'#0), s#1, t#1))
         && _module.__default.equiv__c(Lit(c#0), Lit(c'#0))
           == (forall s#1: Map Box Box, t#1: Map Box Box :: 
            { _module.__default.big__step($LS($LZ), c'#0, s#1, t#1) } 
              { _module.__default.big__step($LS($LZ), c#0, s#1, t#1) } 
            $Is(s#1, TMap(TSeq(TChar), TInt)) && $Is(t#1, TMap(TSeq(TChar), TInt))
               ==> _module.__default.big__step($LS($LZ), Lit(c#0), s#1, t#1)
                 == _module.__default.big__step($LS($LZ), Lit(c'#0), s#1, t#1)));

procedure CheckWellformed$$_module.__default.equiv__c(c#0: DatatypeType where $Is(c#0, Tclass._module.com()), 
    c'#0: DatatypeType where $Is(c'#0, Tclass._module.com()));
  free requires 10 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.equiv__c(c#0: DatatypeType, c'#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var s#2: Map Box Box;
  var t#2: Map Box Box;
  var ##c#0: DatatypeType;
  var ##s#0: Map Box Box;
  var ##t#0: Map Box Box;
  var ##c#1: DatatypeType;
  var ##s#1: Map Box Box;
  var ##t#1: Map Box Box;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function equiv_c
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(82,10): initial state"} true;
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
        havoc s#2;
        havoc t#2;
        if ($Is(s#2, TMap(TSeq(TChar), TInt)) && $Is(t#2, TMap(TSeq(TChar), TInt)))
        {
            ##c#0 := c#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##c#0, Tclass._module.com(), $Heap);
            ##s#0 := s#2;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#0, TMap(TSeq(TChar), TInt), $Heap);
            ##t#0 := t#2;
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#0, TMap(TSeq(TChar), TInt), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.big__step#canCall(c#0, s#2, t#2);
            ##c#1 := c'#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##c#1, Tclass._module.com(), $Heap);
            ##s#1 := s#2;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#1, TMap(TSeq(TChar), TInt), $Heap);
            ##t#1 := t#2;
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#1, TMap(TSeq(TChar), TInt), $Heap);
            b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.big__step#canCall(c'#0, s#2, t#2);
        }

        // End Comprehension WF check
        assume _module.__default.equiv__c(c#0, c'#0)
           == (forall s#3: Map Box Box, t#3: Map Box Box :: 
            { _module.__default.big__step($LS($LZ), c'#0, s#3, t#3) } 
              { _module.__default.big__step($LS($LZ), c#0, s#3, t#3) } 
            $Is(s#3, TMap(TSeq(TChar), TInt)) && $Is(t#3, TMap(TSeq(TChar), TInt))
               ==> _module.__default.big__step($LS($LZ), c#0, s#3, t#3)
                 == _module.__default.big__step($LS($LZ), c'#0, s#3, t#3));
        assume (forall s#3: Map Box Box, t#3: Map Box Box :: 
          { _module.__default.big__step($LS($LZ), c'#0, s#3, t#3) } 
            { _module.__default.big__step($LS($LZ), c#0, s#3, t#3) } 
          $Is(s#3, TMap(TSeq(TChar), TInt)) && $Is(t#3, TMap(TSeq(TChar), TInt))
             ==> _module.__default.big__step#canCall(c#0, s#3, t#3)
               && _module.__default.big__step#canCall(c'#0, s#3, t#3));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.equiv__c(c#0, c'#0), TBool);
        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



procedure CheckWellformed$$_module.__default.lemma__7__3(b#0: DatatypeType
       where $Is(b#0, Tclass._module.bexp())
         && $IsAlloc(b#0, Tclass._module.bexp(), $Heap)
         && $IsA#_module.bexp(b#0), 
    c#0: DatatypeType
       where $Is(c#0, Tclass._module.com())
         && $IsAlloc(c#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#0));
  free requires 31 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.lemma__7__3(b#0: DatatypeType
       where $Is(b#0, Tclass._module.bexp())
         && $IsAlloc(b#0, Tclass._module.bexp(), $Heap)
         && $IsA#_module.bexp(b#0), 
    c#0: DatatypeType
       where $Is(c#0, Tclass._module.com())
         && $IsAlloc(c#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.equiv__c#canCall(#_module.com.While(b#0, c#0), 
    #_module.com.If(b#0, 
      #_module.com.Seq(c#0, #_module.com.While(b#0, c#0)), 
      Lit(#_module.com.SKIP())));
  free ensures _module.__default.equiv__c#canCall(#_module.com.While(b#0, c#0), 
      #_module.com.If(b#0, 
        #_module.com.Seq(c#0, #_module.com.While(b#0, c#0)), 
        Lit(#_module.com.SKIP())))
     && 
    _module.__default.equiv__c(#_module.com.While(b#0, c#0), 
      #_module.com.If(b#0, 
        #_module.com.Seq(c#0, #_module.com.While(b#0, c#0)), 
        Lit(#_module.com.SKIP())))
     && (forall s#0: Map Box Box, t#0: Map Box Box :: 
      { _module.__default.big__step($LS($LZ), 
          #_module.com.If(b#0, #_module.com.Seq(c#0, #_module.com.While(b#0, c#0)), #_module.com.SKIP()), 
          s#0, 
          t#0) } 
        { _module.__default.big__step($LS($LZ), #_module.com.While(b#0, c#0), s#0, t#0) } 
      $Is(s#0, TMap(TSeq(TChar), TInt)) && $Is(t#0, TMap(TSeq(TChar), TInt))
         ==> _module.__default.big__step($LS($LZ), #_module.com.While(b#0, c#0), s#0, t#0)
           == _module.__default.big__step($LS($LZ), 
            #_module.com.If(b#0, 
              #_module.com.Seq(c#0, #_module.com.While(b#0, c#0)), 
              Lit(#_module.com.SKIP())), 
            s#0, 
            t#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.lemma__7__3(b#0: DatatypeType
       where $Is(b#0, Tclass._module.bexp())
         && $IsAlloc(b#0, Tclass._module.bexp(), $Heap)
         && $IsA#_module.bexp(b#0), 
    c#0: DatatypeType
       where $Is(c#0, Tclass._module.com())
         && $IsAlloc(c#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#0))
   returns ($_reverifyPost: bool);
  free requires 31 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.equiv__c#canCall(#_module.com.While(b#0, c#0), 
    #_module.com.If(b#0, 
      #_module.com.Seq(c#0, #_module.com.While(b#0, c#0)), 
      Lit(#_module.com.SKIP())));
  ensures _module.__default.equiv__c#canCall(#_module.com.While(b#0, c#0), 
      #_module.com.If(b#0, 
        #_module.com.Seq(c#0, #_module.com.While(b#0, c#0)), 
        Lit(#_module.com.SKIP())))
     ==> _module.__default.equiv__c(#_module.com.While(b#0, c#0), 
        #_module.com.If(b#0, 
          #_module.com.Seq(c#0, #_module.com.While(b#0, c#0)), 
          Lit(#_module.com.SKIP())))
       || (forall s#1: Map Box Box, t#1: Map Box Box :: 
        { _module.__default.big__step($LS($LS($LZ)), 
            #_module.com.If(b#0, #_module.com.Seq(c#0, #_module.com.While(b#0, c#0)), #_module.com.SKIP()), 
            s#1, 
            t#1) } 
          { _module.__default.big__step($LS($LS($LZ)), #_module.com.While(b#0, c#0), s#1, t#1) } 
        $Is(s#1, TMap(TSeq(TChar), TInt)) && $Is(t#1, TMap(TSeq(TChar), TInt))
           ==> _module.__default.big__step($LS($LS($LZ)), #_module.com.While(b#0, c#0), s#1, t#1)
             == _module.__default.big__step($LS($LS($LZ)), 
              #_module.com.If(b#0, 
                #_module.com.Seq(c#0, #_module.com.While(b#0, c#0)), 
                Lit(#_module.com.SKIP())), 
              s#1, 
              t#1));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.lemma__7__3(b#0: DatatypeType, c#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: lemma_7_3, Impl$$_module.__default.lemma__7__3
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(89,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.lemma__7__4(b#0: DatatypeType
       where $Is(b#0, Tclass._module.bexp())
         && $IsAlloc(b#0, Tclass._module.bexp(), $Heap)
         && $IsA#_module.bexp(b#0), 
    c#0: DatatypeType
       where $Is(c#0, Tclass._module.com())
         && $IsAlloc(c#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#0));
  free requires 32 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.lemma__7__4(b#0: DatatypeType
       where $Is(b#0, Tclass._module.bexp())
         && $IsAlloc(b#0, Tclass._module.bexp(), $Heap)
         && $IsA#_module.bexp(b#0), 
    c#0: DatatypeType
       where $Is(c#0, Tclass._module.com())
         && $IsAlloc(c#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.equiv__c#canCall(#_module.com.If(b#0, c#0, c#0), c#0);
  free ensures _module.__default.equiv__c#canCall(#_module.com.If(b#0, c#0, c#0), c#0)
     && 
    _module.__default.equiv__c(#_module.com.If(b#0, c#0, c#0), c#0)
     && (forall s#0: Map Box Box, t#0: Map Box Box :: 
      { _module.__default.big__step($LS($LZ), c#0, s#0, t#0) } 
        { _module.__default.big__step($LS($LZ), #_module.com.If(b#0, c#0, c#0), s#0, t#0) } 
      $Is(s#0, TMap(TSeq(TChar), TInt)) && $Is(t#0, TMap(TSeq(TChar), TInt))
         ==> _module.__default.big__step($LS($LZ), #_module.com.If(b#0, c#0, c#0), s#0, t#0)
           == _module.__default.big__step($LS($LZ), c#0, s#0, t#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.lemma__7__4(b#0: DatatypeType
       where $Is(b#0, Tclass._module.bexp())
         && $IsAlloc(b#0, Tclass._module.bexp(), $Heap)
         && $IsA#_module.bexp(b#0), 
    c#0: DatatypeType
       where $Is(c#0, Tclass._module.com())
         && $IsAlloc(c#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#0))
   returns ($_reverifyPost: bool);
  free requires 32 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.equiv__c#canCall(#_module.com.If(b#0, c#0, c#0), c#0);
  ensures _module.__default.equiv__c#canCall(#_module.com.If(b#0, c#0, c#0), c#0)
     ==> _module.__default.equiv__c(#_module.com.If(b#0, c#0, c#0), c#0)
       || (forall s#1: Map Box Box, t#1: Map Box Box :: 
        { _module.__default.big__step($LS($LS($LZ)), c#0, s#1, t#1) } 
          { _module.__default.big__step($LS($LS($LZ)), #_module.com.If(b#0, c#0, c#0), s#1, t#1) } 
        $Is(s#1, TMap(TSeq(TChar), TInt)) && $Is(t#1, TMap(TSeq(TChar), TInt))
           ==> _module.__default.big__step($LS($LS($LZ)), #_module.com.If(b#0, c#0, c#0), s#1, t#1)
             == _module.__default.big__step($LS($LS($LZ)), c#0, s#1, t#1));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.lemma__7__4(b#0: DatatypeType, c#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: lemma_7_4, Impl$$_module.__default.lemma__7__4
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(94,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.lemma__7__5(b#0: DatatypeType
       where $Is(b#0, Tclass._module.bexp())
         && $IsAlloc(b#0, Tclass._module.bexp(), $Heap)
         && $IsA#_module.bexp(b#0), 
    c#0: DatatypeType
       where $Is(c#0, Tclass._module.com())
         && $IsAlloc(c#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#0), 
    c'#0: DatatypeType
       where $Is(c'#0, Tclass._module.com())
         && $IsAlloc(c'#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c'#0));
  free requires 33 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.lemma__7__5(b#0: DatatypeType
       where $Is(b#0, Tclass._module.bexp())
         && $IsAlloc(b#0, Tclass._module.bexp(), $Heap)
         && $IsA#_module.bexp(b#0), 
    c#0: DatatypeType
       where $Is(c#0, Tclass._module.com())
         && $IsAlloc(c#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#0), 
    c'#0: DatatypeType
       where $Is(c'#0, Tclass._module.com())
         && $IsAlloc(c'#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c'#0));
  // user-defined preconditions
  requires _module.__default.equiv__c#canCall(c#0, c'#0)
     ==> _module.__default.equiv__c(c#0, c'#0)
       || (forall s#0: Map Box Box, t#0: Map Box Box :: 
        { _module.__default.big__step($LS($LS($LZ)), c'#0, s#0, t#0) } 
          { _module.__default.big__step($LS($LS($LZ)), c#0, s#0, t#0) } 
        $Is(s#0, TMap(TSeq(TChar), TInt)) && $Is(t#0, TMap(TSeq(TChar), TInt))
           ==> _module.__default.big__step($LS($LS($LZ)), c#0, s#0, t#0)
             == _module.__default.big__step($LS($LS($LZ)), c'#0, s#0, t#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.equiv__c#canCall(#_module.com.While(b#0, c#0), #_module.com.While(b#0, c'#0));
  free ensures _module.__default.equiv__c#canCall(#_module.com.While(b#0, c#0), #_module.com.While(b#0, c'#0))
     && 
    _module.__default.equiv__c(#_module.com.While(b#0, c#0), #_module.com.While(b#0, c'#0))
     && (forall s#1: Map Box Box, t#1: Map Box Box :: 
      { _module.__default.big__step($LS($LZ), #_module.com.While(b#0, c'#0), s#1, t#1) } 
        { _module.__default.big__step($LS($LZ), #_module.com.While(b#0, c#0), s#1, t#1) } 
      $Is(s#1, TMap(TSeq(TChar), TInt)) && $Is(t#1, TMap(TSeq(TChar), TInt))
         ==> _module.__default.big__step($LS($LZ), #_module.com.While(b#0, c#0), s#1, t#1)
           == _module.__default.big__step($LS($LZ), #_module.com.While(b#0, c'#0), s#1, t#1));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.lemma__7__5(b#0: DatatypeType
       where $Is(b#0, Tclass._module.bexp())
         && $IsAlloc(b#0, Tclass._module.bexp(), $Heap)
         && $IsA#_module.bexp(b#0), 
    c#0: DatatypeType
       where $Is(c#0, Tclass._module.com())
         && $IsAlloc(c#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#0), 
    c'#0: DatatypeType
       where $Is(c'#0, Tclass._module.com())
         && $IsAlloc(c'#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c'#0))
   returns ($_reverifyPost: bool);
  free requires 33 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.__default.equiv__c#canCall(c#0, c'#0)
     && 
    _module.__default.equiv__c(c#0, c'#0)
     && (forall s#2: Map Box Box, t#2: Map Box Box :: 
      { _module.__default.big__step($LS($LZ), c'#0, s#2, t#2) } 
        { _module.__default.big__step($LS($LZ), c#0, s#2, t#2) } 
      $Is(s#2, TMap(TSeq(TChar), TInt)) && $Is(t#2, TMap(TSeq(TChar), TInt))
         ==> _module.__default.big__step($LS($LZ), c#0, s#2, t#2)
           == _module.__default.big__step($LS($LZ), c'#0, s#2, t#2));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.equiv__c#canCall(#_module.com.While(b#0, c#0), #_module.com.While(b#0, c'#0));
  ensures _module.__default.equiv__c#canCall(#_module.com.While(b#0, c#0), #_module.com.While(b#0, c'#0))
     ==> _module.__default.equiv__c(#_module.com.While(b#0, c#0), #_module.com.While(b#0, c'#0))
       || (forall s#3: Map Box Box, t#3: Map Box Box :: 
        { _module.__default.big__step($LS($LS($LZ)), #_module.com.While(b#0, c'#0), s#3, t#3) } 
          { _module.__default.big__step($LS($LS($LZ)), #_module.com.While(b#0, c#0), s#3, t#3) } 
        $Is(s#3, TMap(TSeq(TChar), TInt)) && $Is(t#3, TMap(TSeq(TChar), TInt))
           ==> _module.__default.big__step($LS($LS($LZ)), #_module.com.While(b#0, c#0), s#3, t#3)
             == _module.__default.big__step($LS($LS($LZ)), #_module.com.While(b#0, c'#0), s#3, t#3));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.lemma__7__5(b#0: DatatypeType, c#0: DatatypeType, c'#0: DatatypeType)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var s#4: Map Box Box;
  var t#4: Map Box Box;
  var ##c#2: DatatypeType;
  var ##s#0: Map Box Box;
  var ##t#0: Map Box Box;
  var b##0_0: DatatypeType;
  var c##0_0: DatatypeType;
  var c'##0_0: DatatypeType;
  var s##0_0: Map Box Box;
  var t##0_0: Map Box Box;
  var ##c#3: DatatypeType;
  var ##s#1: Map Box Box;
  var ##t#1: Map Box Box;
  var b##1_0: DatatypeType;
  var c##1_0: DatatypeType;
  var c'##1_0: DatatypeType;
  var s##1_0: Map Box Box;
  var t##1_0: Map Box Box;

    // AddMethodImpl: lemma_7_5, Impl$$_module.__default.lemma__7__5
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(100,0): initial state"} true;
    $_reverifyPost := false;
    // ----- forall statement (proof) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(101,3)
    if (*)
    {
        // Assume Fuel Constant
        havoc s#4, t#4;
        assume $Is(s#4, TMap(TSeq(TChar), TInt)) && $Is(t#4, TMap(TSeq(TChar), TInt));
        assume true;
        assume true;
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(104,5)
        ##c#2 := #_module.com.While(b#0, c#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#2, Tclass._module.com(), $Heap);
        ##s#0 := s#4;
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#0, TMap(TSeq(TChar), TInt), $Heap);
        ##t#0 := t#4;
        // assume allocatedness for argument to function
        assume $IsAlloc(##t#0, TMap(TSeq(TChar), TInt), $Heap);
        assume _module.__default.big__step#canCall(#_module.com.While(b#0, c#0), s#4, t#4);
        assume _module.__default.big__step#canCall(#_module.com.While(b#0, c#0), s#4, t#4);
        if (_module.__default.big__step($LS($LZ), #_module.com.While(b#0, c#0), s#4, t#4))
        {
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(105,16)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            b##0_0 := b#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            c##0_0 := c#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            c'##0_0 := c'#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            s##0_0 := s#4;
            assume true;
            // ProcessCallStmt: CheckSubrange
            t##0_0 := t#4;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call Call$$_module.__default.lemma__7__6(b##0_0, c##0_0, c'##0_0, s##0_0, t##0_0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(105,31)"} true;
        }
        else
        {
        }

        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(107,5)
        ##c#3 := #_module.com.While(b#0, c'#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#3, Tclass._module.com(), $Heap);
        ##s#1 := s#4;
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#1, TMap(TSeq(TChar), TInt), $Heap);
        ##t#1 := t#4;
        // assume allocatedness for argument to function
        assume $IsAlloc(##t#1, TMap(TSeq(TChar), TInt), $Heap);
        assume _module.__default.big__step#canCall(#_module.com.While(b#0, c'#0), s#4, t#4);
        assume _module.__default.big__step#canCall(#_module.com.While(b#0, c'#0), s#4, t#4);
        if (_module.__default.big__step($LS($LZ), #_module.com.While(b#0, c'#0), s#4, t#4))
        {
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(108,16)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            b##1_0 := b#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            c##1_0 := c'#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            c'##1_0 := c#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            s##1_0 := s#4;
            assume true;
            // ProcessCallStmt: CheckSubrange
            t##1_0 := t#4;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call Call$$_module.__default.lemma__7__6(b##1_0, c##1_0, c'##1_0, s##1_0, t##1_0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(108,31)"} true;
        }
        else
        {
        }

        assert _module.__default.big__step($LS($LS($LZ)), #_module.com.While(b#0, c#0), s#4, t#4)
           == _module.__default.big__step($LS($LS($LZ)), #_module.com.While(b#0, c'#0), s#4, t#4);
        assume false;
    }
    else
    {
        assume (forall s#5: Map Box Box, t#5: Map Box Box :: 
          { _module.__default.big__step($LS($LZ), #_module.com.While(b#0, c'#0), s#5, t#5) } 
            { _module.__default.big__step($LS($LZ), #_module.com.While(b#0, c#0), s#5, t#5) } 
          $Is(s#5, TMap(TSeq(TChar), TInt))
               && $Is(t#5, TMap(TSeq(TChar), TInt))
               && Lit(true)
             ==> _module.__default.big__step($LS($LZ), #_module.com.While(b#0, c#0), s#5, t#5)
               == _module.__default.big__step($LS($LZ), #_module.com.While(b#0, c'#0), s#5, t#5));
    }

    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(110,2)"} true;
}



procedure CheckWellformed$$_module.__default.lemma__7__6(b#0: DatatypeType
       where $Is(b#0, Tclass._module.bexp())
         && $IsAlloc(b#0, Tclass._module.bexp(), $Heap)
         && $IsA#_module.bexp(b#0), 
    c#0: DatatypeType
       where $Is(c#0, Tclass._module.com())
         && $IsAlloc(c#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#0), 
    c'#0: DatatypeType
       where $Is(c'#0, Tclass._module.com())
         && $IsAlloc(c'#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c'#0), 
    s#0: Map Box Box
       where $Is(s#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s#0, TMap(TSeq(TChar), TInt), $Heap), 
    t#0: Map Box Box
       where $Is(t#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(t#0, TMap(TSeq(TChar), TInt), $Heap));
  free requires 11 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.lemma__7__6(b#0: DatatypeType
       where $Is(b#0, Tclass._module.bexp())
         && $IsAlloc(b#0, Tclass._module.bexp(), $Heap)
         && $IsA#_module.bexp(b#0), 
    c#0: DatatypeType
       where $Is(c#0, Tclass._module.com())
         && $IsAlloc(c#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#0), 
    c'#0: DatatypeType
       where $Is(c'#0, Tclass._module.com())
         && $IsAlloc(c'#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c'#0), 
    s#0: Map Box Box
       where $Is(s#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s#0, TMap(TSeq(TChar), TInt), $Heap), 
    t#0: Map Box Box
       where $Is(t#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(t#0, TMap(TSeq(TChar), TInt), $Heap));
  // user-defined preconditions
  requires _module.__default.big__step($LS($LS($LZ)), #_module.com.While(b#0, c#0), s#0, t#0);
  requires _module.__default.equiv__c#canCall(c#0, c'#0)
     ==> _module.__default.equiv__c(c#0, c'#0)
       || (forall s#1: Map Box Box, t#1: Map Box Box :: 
        { _module.__default.big__step($LS($LS($LZ)), c'#0, s#1, t#1) } 
          { _module.__default.big__step($LS($LS($LZ)), c#0, s#1, t#1) } 
        $Is(s#1, TMap(TSeq(TChar), TInt)) && $Is(t#1, TMap(TSeq(TChar), TInt))
           ==> _module.__default.big__step($LS($LS($LZ)), c#0, s#1, t#1)
             == _module.__default.big__step($LS($LS($LZ)), c'#0, s#1, t#1));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.big__step#canCall(#_module.com.While(b#0, c'#0), s#0, t#0);
  ensures _module.__default.big__step($LS($LS($LZ)), #_module.com.While(b#0, c'#0), s#0, t#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, b#1, c#1, c'#1, s#2, t#2} CoCall$$_module.__default.lemma__7__6_h(_k#0: Box, 
    b#1: DatatypeType
       where $Is(b#1, Tclass._module.bexp())
         && $IsAlloc(b#1, Tclass._module.bexp(), $Heap)
         && $IsA#_module.bexp(b#1), 
    c#1: DatatypeType
       where $Is(c#1, Tclass._module.com())
         && $IsAlloc(c#1, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#1), 
    c'#1: DatatypeType
       where $Is(c'#1, Tclass._module.com())
         && $IsAlloc(c'#1, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c'#1), 
    s#2: Map Box Box
       where $Is(s#2, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s#2, TMap(TSeq(TChar), TInt), $Heap), 
    t#2: Map Box Box
       where $Is(t#2, TMap(TSeq(TChar), TInt))
         && $IsAlloc(t#2, TMap(TSeq(TChar), TInt), $Heap));
  // user-defined preconditions
  requires _module.__default.big__step_h($LS($LS($LZ)), _k#0, #_module.com.While(b#1, c#1), s#2, t#2);
  requires _module.__default.equiv__c#canCall(c#1, c'#1)
     ==> _module.__default.equiv__c(c#1, c'#1)
       || (forall s#3: Map Box Box, t#3: Map Box Box :: 
        { _module.__default.big__step($LS($LS($LZ)), c'#1, s#3, t#3) } 
          { _module.__default.big__step($LS($LS($LZ)), c#1, s#3, t#3) } 
        $Is(s#3, TMap(TSeq(TChar), TInt)) && $Is(t#3, TMap(TSeq(TChar), TInt))
           ==> _module.__default.big__step($LS($LS($LZ)), c#1, s#3, t#3)
             == _module.__default.big__step($LS($LS($LZ)), c'#1, s#3, t#3));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.big__step#canCall(#_module.com.While(b#1, c'#1), s#2, t#2);
  ensures _module.__default.big__step($LS($LS($LZ)), #_module.com.While(b#1, c'#1), s#2, t#2);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, b#1, c#1, c'#1, s#2, t#2} Impl$$_module.__default.lemma__7__6_h(_k#0: Box, 
    b#1: DatatypeType
       where $Is(b#1, Tclass._module.bexp())
         && $IsAlloc(b#1, Tclass._module.bexp(), $Heap)
         && $IsA#_module.bexp(b#1), 
    c#1: DatatypeType
       where $Is(c#1, Tclass._module.com())
         && $IsAlloc(c#1, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#1), 
    c'#1: DatatypeType
       where $Is(c'#1, Tclass._module.com())
         && $IsAlloc(c'#1, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c'#1), 
    s#2: Map Box Box
       where $Is(s#2, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s#2, TMap(TSeq(TChar), TInt), $Heap), 
    t#2: Map Box Box
       where $Is(t#2, TMap(TSeq(TChar), TInt))
         && $IsAlloc(t#2, TMap(TSeq(TChar), TInt), $Heap))
   returns ($_reverifyPost: bool);
  free requires 12 == $FunctionContextHeight;
  // user-defined preconditions
  requires _module.__default.big__step_h($LS($LS($LZ)), _k#0, #_module.com.While(b#1, c#1), s#2, t#2);
  free requires _module.__default.equiv__c#canCall(c#1, c'#1)
     && 
    _module.__default.equiv__c(c#1, c'#1)
     && (forall s#4: Map Box Box, t#4: Map Box Box :: 
      { _module.__default.big__step($LS($LZ), c'#1, s#4, t#4) } 
        { _module.__default.big__step($LS($LZ), c#1, s#4, t#4) } 
      $Is(s#4, TMap(TSeq(TChar), TInt)) && $Is(t#4, TMap(TSeq(TChar), TInt))
         ==> _module.__default.big__step($LS($LZ), c#1, s#4, t#4)
           == _module.__default.big__step($LS($LZ), c'#1, s#4, t#4));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.big__step#canCall(#_module.com.While(b#1, c'#1), s#2, t#2);
  ensures _module.__default.big__step($LS($LS($LZ)), #_module.com.While(b#1, c'#1), s#2, t#2);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0, b#1, c#1, c'#1, s#2, t#2} Impl$$_module.__default.lemma__7__6_h(_k#0: Box, 
    b#1: DatatypeType, 
    c#1: DatatypeType, 
    c'#1: DatatypeType, 
    s#2: Map Box Box, 
    t#2: Map Box Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var $initHeapForallStmt#1: Heap;

    // AddMethodImpl: lemma_7_6#, Impl$$_module.__default.lemma__7__6_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(113,12): initial state"} true;
    assume $IsA#_module.bexp(b#1);
    assume $IsA#_module.com(c#1);
    assume $IsA#_module.com(c'#1);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: Box, 
        $ih#b0#0: DatatypeType, 
        $ih#c0#0: DatatypeType, 
        $ih#c'0#0: DatatypeType, 
        $ih#s0#0: Map Box Box, 
        $ih#t0#0: Map Box Box :: 
      $Is($ih#b0#0, Tclass._module.bexp())
           && $Is($ih#c0#0, Tclass._module.com())
           && $Is($ih#c'0#0, Tclass._module.com())
           && $Is($ih#s0#0, TMap(TSeq(TChar), TInt))
           && $Is($ih#t0#0, TMap(TSeq(TChar), TInt))
           && 
          _module.__default.big__step_h($LS($LZ), $ih#_k0#0, #_module.com.While($ih#b0#0, $ih#c0#0), $ih#s0#0, $ih#t0#0)
           && _module.__default.equiv__c($ih#c0#0, $ih#c'0#0)
           && (ORD#Less($ih#_k0#0, _k#0)
             || ($ih#_k0#0 == _k#0
               && (DtRank($ih#b0#0) < DtRank(b#1)
                 || (DtRank($ih#b0#0) == DtRank(b#1)
                   && (DtRank($ih#c0#0) < DtRank(c#1)
                     || (DtRank($ih#c0#0) == DtRank(c#1)
                       && (DtRank($ih#c'0#0) < DtRank(c'#1)
                         || (DtRank($ih#c'0#0) == DtRank(c'#1)
                           && ((Set#Subset(Map#Domain($ih#s0#0), Map#Domain(s#2))
                               && !Set#Subset(Map#Domain(s#2), Map#Domain($ih#s0#0)))
                             || (Set#Equal(Map#Domain($ih#s0#0), Map#Domain(s#2))
                               && 
                              Set#Subset(Map#Domain($ih#t0#0), Map#Domain(t#2))
                               && !Set#Subset(Map#Domain(t#2), Map#Domain($ih#t0#0))))))))))))
         ==> _module.__default.big__step($LS($LZ), #_module.com.While($ih#b0#0, $ih#c'0#0), $ih#s0#0, $ih#t0#0));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(116,1)
    assume true;
    if (0 < ORD#Offset(_k#0))
    {
    }
    else
    {
        // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(113,13)
        $initHeapForallStmt#1 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#1 == $Heap;
        assume (forall _k'#0: Box, 
            b#2: DatatypeType, 
            c#2: DatatypeType, 
            c'#2: DatatypeType, 
            s#5: Map Box Box, 
            t#5: Map Box Box :: 
          $Is(b#2, Tclass._module.bexp())
               && $Is(c#2, Tclass._module.com())
               && $Is(c'#2, Tclass._module.com())
               && $Is(s#5, TMap(TSeq(TChar), TInt))
               && $Is(t#5, TMap(TSeq(TChar), TInt))
               && 
              ORD#Less(_k'#0, _k#0)
               && 
              _module.__default.big__step_h($LS($LZ), _k'#0, #_module.com.While(b#2, c#2), s#5, t#5)
               && _module.__default.equiv__c(c#2, c'#2)
             ==> _module.__default.big__step($LS($LZ), #_module.com.While(b#2, c'#2), s#5, t#5));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(113,12)"} true;
    }
}



procedure CheckWellformed$$_module.__default.equiv__c__reflexive(c#0: DatatypeType
       where $Is(c#0, Tclass._module.com())
         && $IsAlloc(c#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#0), 
    c'#0: DatatypeType
       where $Is(c'#0, Tclass._module.com())
         && $IsAlloc(c'#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c'#0));
  free requires 34 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.equiv__c__reflexive(c#0: DatatypeType
       where $Is(c#0, Tclass._module.com())
         && $IsAlloc(c#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#0), 
    c'#0: DatatypeType
       where $Is(c'#0, Tclass._module.com())
         && $IsAlloc(c'#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c'#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.com(c#0)
     && $IsA#_module.com(c'#0)
     && (_module.com#Equal(c#0, c'#0) ==> _module.__default.equiv__c#canCall(c#0, c'#0));
  free ensures _module.com#Equal(c#0, c'#0)
     ==> _module.__default.equiv__c#canCall(c#0, c'#0)
       && 
      _module.__default.equiv__c(c#0, c'#0)
       && (forall s#0: Map Box Box, t#0: Map Box Box :: 
        { _module.__default.big__step($LS($LZ), c'#0, s#0, t#0) } 
          { _module.__default.big__step($LS($LZ), c#0, s#0, t#0) } 
        $Is(s#0, TMap(TSeq(TChar), TInt)) && $Is(t#0, TMap(TSeq(TChar), TInt))
           ==> _module.__default.big__step($LS($LZ), c#0, s#0, t#0)
             == _module.__default.big__step($LS($LZ), c'#0, s#0, t#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.equiv__c__reflexive(c#0: DatatypeType
       where $Is(c#0, Tclass._module.com())
         && $IsAlloc(c#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#0), 
    c'#0: DatatypeType
       where $Is(c'#0, Tclass._module.com())
         && $IsAlloc(c'#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c'#0))
   returns ($_reverifyPost: bool);
  free requires 34 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.com(c#0)
     && $IsA#_module.com(c'#0)
     && (_module.com#Equal(c#0, c'#0) ==> _module.__default.equiv__c#canCall(c#0, c'#0));
  ensures _module.com#Equal(c#0, c'#0)
     ==> 
    _module.__default.equiv__c#canCall(c#0, c'#0)
     ==> _module.__default.equiv__c(c#0, c'#0)
       || (forall s#1: Map Box Box, t#1: Map Box Box :: 
        { _module.__default.big__step($LS($LS($LZ)), c'#0, s#1, t#1) } 
          { _module.__default.big__step($LS($LS($LZ)), c#0, s#1, t#1) } 
        $Is(s#1, TMap(TSeq(TChar), TInt)) && $Is(t#1, TMap(TSeq(TChar), TInt))
           ==> _module.__default.big__step($LS($LS($LZ)), c#0, s#1, t#1)
             == _module.__default.big__step($LS($LS($LZ)), c'#0, s#1, t#1));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.equiv__c__reflexive(c#0: DatatypeType, c'#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: equiv_c_reflexive, Impl$$_module.__default.equiv__c__reflexive
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(122,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.equiv__c__symmetric(c#0: DatatypeType
       where $Is(c#0, Tclass._module.com())
         && $IsAlloc(c#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#0), 
    c'#0: DatatypeType
       where $Is(c'#0, Tclass._module.com())
         && $IsAlloc(c'#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c'#0));
  free requires 35 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.equiv__c__symmetric(c#0: DatatypeType
       where $Is(c#0, Tclass._module.com())
         && $IsAlloc(c#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#0), 
    c'#0: DatatypeType
       where $Is(c'#0, Tclass._module.com())
         && $IsAlloc(c'#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c'#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.equiv__c#canCall(c#0, c'#0)
     && (_module.__default.equiv__c(c#0, c'#0)
       ==> _module.__default.equiv__c#canCall(c'#0, c#0));
  free ensures _module.__default.equiv__c(c#0, c'#0)
     ==> _module.__default.equiv__c#canCall(c'#0, c#0)
       && 
      _module.__default.equiv__c(c'#0, c#0)
       && (forall s#0: Map Box Box, t#0: Map Box Box :: 
        { _module.__default.big__step($LS($LZ), c#0, s#0, t#0) } 
          { _module.__default.big__step($LS($LZ), c'#0, s#0, t#0) } 
        $Is(s#0, TMap(TSeq(TChar), TInt)) && $Is(t#0, TMap(TSeq(TChar), TInt))
           ==> _module.__default.big__step($LS($LZ), c'#0, s#0, t#0)
             == _module.__default.big__step($LS($LZ), c#0, s#0, t#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.equiv__c__symmetric(c#0: DatatypeType
       where $Is(c#0, Tclass._module.com())
         && $IsAlloc(c#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#0), 
    c'#0: DatatypeType
       where $Is(c'#0, Tclass._module.com())
         && $IsAlloc(c'#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c'#0))
   returns ($_reverifyPost: bool);
  free requires 35 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.equiv__c#canCall(c#0, c'#0)
     && (_module.__default.equiv__c(c#0, c'#0)
       ==> _module.__default.equiv__c#canCall(c'#0, c#0));
  ensures _module.__default.equiv__c(c#0, c'#0)
     ==> 
    _module.__default.equiv__c#canCall(c'#0, c#0)
     ==> _module.__default.equiv__c(c'#0, c#0)
       || (forall s#1: Map Box Box, t#1: Map Box Box :: 
        { _module.__default.big__step($LS($LS($LZ)), c#0, s#1, t#1) } 
          { _module.__default.big__step($LS($LS($LZ)), c'#0, s#1, t#1) } 
        $Is(s#1, TMap(TSeq(TChar), TInt)) && $Is(t#1, TMap(TSeq(TChar), TInt))
           ==> _module.__default.big__step($LS($LS($LZ)), c'#0, s#1, t#1)
             == _module.__default.big__step($LS($LS($LZ)), c#0, s#1, t#1));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.equiv__c__symmetric(c#0: DatatypeType, c'#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: equiv_c_symmetric, Impl$$_module.__default.equiv__c__symmetric
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(126,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.equiv__c__transitive(c#0: DatatypeType
       where $Is(c#0, Tclass._module.com())
         && $IsAlloc(c#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#0), 
    c'#0: DatatypeType
       where $Is(c'#0, Tclass._module.com())
         && $IsAlloc(c'#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c'#0), 
    c''#0: DatatypeType
       where $Is(c''#0, Tclass._module.com())
         && $IsAlloc(c''#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c''#0));
  free requires 36 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.equiv__c__transitive(c#0: DatatypeType
       where $Is(c#0, Tclass._module.com())
         && $IsAlloc(c#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#0), 
    c'#0: DatatypeType
       where $Is(c'#0, Tclass._module.com())
         && $IsAlloc(c'#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c'#0), 
    c''#0: DatatypeType
       where $Is(c''#0, Tclass._module.com())
         && $IsAlloc(c''#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c''#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.equiv__c#canCall(c#0, c'#0)
     && (_module.__default.equiv__c(c#0, c'#0)
       ==> _module.__default.equiv__c#canCall(c'#0, c''#0)
         && (_module.__default.equiv__c(c'#0, c''#0)
           ==> _module.__default.equiv__c#canCall(c#0, c''#0)));
  free ensures _module.__default.equiv__c(c#0, c'#0) && _module.__default.equiv__c(c'#0, c''#0)
     ==> _module.__default.equiv__c#canCall(c#0, c''#0)
       && 
      _module.__default.equiv__c(c#0, c''#0)
       && (forall s#0: Map Box Box, t#0: Map Box Box :: 
        { _module.__default.big__step($LS($LZ), c''#0, s#0, t#0) } 
          { _module.__default.big__step($LS($LZ), c#0, s#0, t#0) } 
        $Is(s#0, TMap(TSeq(TChar), TInt)) && $Is(t#0, TMap(TSeq(TChar), TInt))
           ==> _module.__default.big__step($LS($LZ), c#0, s#0, t#0)
             == _module.__default.big__step($LS($LZ), c''#0, s#0, t#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.equiv__c__transitive(c#0: DatatypeType
       where $Is(c#0, Tclass._module.com())
         && $IsAlloc(c#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#0), 
    c'#0: DatatypeType
       where $Is(c'#0, Tclass._module.com())
         && $IsAlloc(c'#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c'#0), 
    c''#0: DatatypeType
       where $Is(c''#0, Tclass._module.com())
         && $IsAlloc(c''#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c''#0))
   returns ($_reverifyPost: bool);
  free requires 36 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.equiv__c#canCall(c#0, c'#0)
     && (_module.__default.equiv__c(c#0, c'#0)
       ==> _module.__default.equiv__c#canCall(c'#0, c''#0)
         && (_module.__default.equiv__c(c'#0, c''#0)
           ==> _module.__default.equiv__c#canCall(c#0, c''#0)));
  ensures _module.__default.equiv__c(c#0, c'#0) && _module.__default.equiv__c(c'#0, c''#0)
     ==> 
    _module.__default.equiv__c#canCall(c#0, c''#0)
     ==> _module.__default.equiv__c(c#0, c''#0)
       || (forall s#1: Map Box Box, t#1: Map Box Box :: 
        { _module.__default.big__step($LS($LS($LZ)), c''#0, s#1, t#1) } 
          { _module.__default.big__step($LS($LS($LZ)), c#0, s#1, t#1) } 
        $Is(s#1, TMap(TSeq(TChar), TInt)) && $Is(t#1, TMap(TSeq(TChar), TInt))
           ==> _module.__default.big__step($LS($LS($LZ)), c#0, s#1, t#1)
             == _module.__default.big__step($LS($LS($LZ)), c''#0, s#1, t#1));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.equiv__c__transitive(c#0: DatatypeType, c'#0: DatatypeType, c''#0: DatatypeType)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: equiv_c_transitive, Impl$$_module.__default.equiv__c__transitive
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(130,0): initial state"} true;
    $_reverifyPost := false;
}



procedure {:_induction c#0, s#0, t#0, t'#0} CheckWellformed$$_module.__default.IMP__is__deterministic(c#0: DatatypeType
       where $Is(c#0, Tclass._module.com())
         && $IsAlloc(c#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#0), 
    s#0: Map Box Box
       where $Is(s#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s#0, TMap(TSeq(TChar), TInt), $Heap), 
    t#0: Map Box Box
       where $Is(t#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(t#0, TMap(TSeq(TChar), TInt), $Heap), 
    t'#0: Map Box Box
       where $Is(t'#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(t'#0, TMap(TSeq(TChar), TInt), $Heap));
  free requires 38 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction c#0, s#0, t#0, t'#0} Call$$_module.__default.IMP__is__deterministic(c#0: DatatypeType
       where $Is(c#0, Tclass._module.com())
         && $IsAlloc(c#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#0), 
    s#0: Map Box Box
       where $Is(s#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s#0, TMap(TSeq(TChar), TInt), $Heap), 
    t#0: Map Box Box
       where $Is(t#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(t#0, TMap(TSeq(TChar), TInt), $Heap), 
    t'#0: Map Box Box
       where $Is(t'#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(t'#0, TMap(TSeq(TChar), TInt), $Heap));
  // user-defined preconditions
  requires _module.__default.big__step($LS($LS($LZ)), c#0, s#0, t#0);
  requires _module.__default.big__step($LS($LS($LZ)), c#0, s#0, t'#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures Map#Equal(t#0, t'#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction c#0, s#0, t#0, t'#0} Impl$$_module.__default.IMP__is__deterministic(c#0: DatatypeType
       where $Is(c#0, Tclass._module.com())
         && $IsAlloc(c#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#0), 
    s#0: Map Box Box
       where $Is(s#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s#0, TMap(TSeq(TChar), TInt), $Heap), 
    t#0: Map Box Box
       where $Is(t#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(t#0, TMap(TSeq(TChar), TInt), $Heap), 
    t'#0: Map Box Box
       where $Is(t'#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(t'#0, TMap(TSeq(TChar), TInt), $Heap))
   returns ($_reverifyPost: bool);
  free requires 38 == $FunctionContextHeight;
  // user-defined preconditions
  requires _module.__default.big__step($LS($LS($LZ)), c#0, s#0, t#0);
  requires _module.__default.big__step($LS($LS($LZ)), c#0, s#0, t'#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures Map#Equal(t#0, t'#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction c#0, s#0, t#0, t'#0} Impl$$_module.__default.IMP__is__deterministic(c#0: DatatypeType, s#0: Map Box Box, t#0: Map Box Box, t'#0: Map Box Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var k#0: Box;
  var k#1: Box;
  var ##_k#0: Box;
  var ##c#2: DatatypeType;
  var ##s#2: Map Box Box;
  var ##t#2: Map Box Box;
  var k'#0: Box;
  var k'#1: Box;
  var ##_k#1: Box;
  var ##c#3: DatatypeType;
  var ##s#3: Map Box Box;
  var ##t#3: Map Box Box;
  var k##0: Box;
  var k'##0: Box;
  var c##0: DatatypeType;
  var s##0: Map Box Box;
  var t##0: Map Box Box;
  var t'##0: Map Box Box;

    // AddMethodImpl: IMP_is_deterministic, Impl$$_module.__default.IMP__is__deterministic
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(136,0): initial state"} true;
    assume $IsA#_module.com(c#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#c0#0: DatatypeType, 
        $ih#s0#0: Map Box Box, 
        $ih#t0#0: Map Box Box, 
        $ih#t'0#0: Map Box Box :: 
      $Is($ih#c0#0, Tclass._module.com())
           && $Is($ih#s0#0, TMap(TSeq(TChar), TInt))
           && $Is($ih#t0#0, TMap(TSeq(TChar), TInt))
           && $Is($ih#t'0#0, TMap(TSeq(TChar), TInt))
           && 
          _module.__default.big__step($LS($LZ), $ih#c0#0, $ih#s0#0, $ih#t0#0)
           && _module.__default.big__step($LS($LZ), $ih#c0#0, $ih#s0#0, $ih#t'0#0)
           && (DtRank($ih#c0#0) < DtRank(c#0)
             || (DtRank($ih#c0#0) == DtRank(c#0)
               && ((Set#Subset(Map#Domain($ih#s0#0), Map#Domain(s#0))
                   && !Set#Subset(Map#Domain(s#0), Map#Domain($ih#s0#0)))
                 || (Set#Equal(Map#Domain($ih#s0#0), Map#Domain(s#0))
                   && ((Set#Subset(Map#Domain($ih#t0#0), Map#Domain(t#0))
                       && !Set#Subset(Map#Domain(t#0), Map#Domain($ih#t0#0)))
                     || (Set#Equal(Map#Domain($ih#t0#0), Map#Domain(t#0))
                       && 
                      Set#Subset(Map#Domain($ih#t'0#0), Map#Domain(t'#0))
                       && !Set#Subset(Map#Domain(t'#0), Map#Domain($ih#t'0#0))))))))
         ==> Map#Equal($ih#t0#0, $ih#t'0#0));
    $_reverifyPost := false;
    // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(141,9)
    havoc k#1;
    if (true)
    {
        ##_k#0 := k#1;
        // assume allocatedness for argument to function
        assume $IsAlloc(##_k#0, TORDINAL, $Heap);
        ##c#2 := c#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#2, Tclass._module.com(), $Heap);
        ##s#2 := s#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#2, TMap(TSeq(TChar), TInt), $Heap);
        ##t#2 := t#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##t#2, TMap(TSeq(TChar), TInt), $Heap);
        assume _module.__default.big__step_h#canCall(k#1, c#0, s#0, t#0);
        assume _module.__default.big__step_h#canCall(k#1, c#0, s#0, t#0);
    }

    assert (exists $as#k0#0: Box :: 
      _module.__default.big__step_h($LS($LZ), $as#k0#0, c#0, s#0, t#0));
    havoc k#0;
    assume _module.__default.big__step_h($LS($LZ), k#0, c#0, s#0, t#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(141,32)"} true;
    // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(142,10)
    havoc k'#1;
    if (true)
    {
        ##_k#1 := k'#1;
        // assume allocatedness for argument to function
        assume $IsAlloc(##_k#1, TORDINAL, $Heap);
        ##c#3 := c#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#3, Tclass._module.com(), $Heap);
        ##s#3 := s#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#3, TMap(TSeq(TChar), TInt), $Heap);
        ##t#3 := t'#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##t#3, TMap(TSeq(TChar), TInt), $Heap);
        assume _module.__default.big__step_h#canCall(k'#1, c#0, s#0, t'#0);
        assume _module.__default.big__step_h#canCall(k'#1, c#0, s#0, t'#0);
    }

    assert (exists $as#k'0#0: Box :: 
      _module.__default.big__step_h($LS($LZ), $as#k'0#0, c#0, s#0, t'#0));
    havoc k'#0;
    assume _module.__default.big__step_h($LS($LZ), k'#0, c#0, s#0, t'#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(142,35)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(143,27)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    k##0 := k#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    k'##0 := k'#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    c##0 := c#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    s##0 := s#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    t##0 := t#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    t'##0 := t'#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.IMP__is__deterministic__Aux(k##0, k'##0, c##0, s##0, t##0, t'##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(143,46)"} true;
}



procedure {:_induction k#0, k'#0, c#0, s#0, t#0, t'#0} CheckWellformed$$_module.__default.IMP__is__deterministic__Aux(k#0: Box, 
    k'#0: Box, 
    c#0: DatatypeType
       where $Is(c#0, Tclass._module.com())
         && $IsAlloc(c#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#0), 
    s#0: Map Box Box
       where $Is(s#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s#0, TMap(TSeq(TChar), TInt), $Heap), 
    t#0: Map Box Box
       where $Is(t#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(t#0, TMap(TSeq(TChar), TInt), $Heap), 
    t'#0: Map Box Box
       where $Is(t'#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(t'#0, TMap(TSeq(TChar), TInt), $Heap));
  free requires 37 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction k#0, k'#0, c#0, s#0, t#0, t'#0} Call$$_module.__default.IMP__is__deterministic__Aux(k#0: Box, 
    k'#0: Box, 
    c#0: DatatypeType
       where $Is(c#0, Tclass._module.com())
         && $IsAlloc(c#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#0), 
    s#0: Map Box Box
       where $Is(s#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s#0, TMap(TSeq(TChar), TInt), $Heap), 
    t#0: Map Box Box
       where $Is(t#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(t#0, TMap(TSeq(TChar), TInt), $Heap), 
    t'#0: Map Box Box
       where $Is(t'#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(t'#0, TMap(TSeq(TChar), TInt), $Heap));
  // user-defined preconditions
  requires _module.__default.big__step_h($LS($LS($LZ)), k#0, c#0, s#0, t#0);
  requires _module.__default.big__step_h($LS($LS($LZ)), k'#0, c#0, s#0, t'#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures Map#Equal(t#0, t'#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction k#0, k'#0, c#0, s#0, t#0, t'#0} Impl$$_module.__default.IMP__is__deterministic__Aux(k#0: Box, 
    k'#0: Box, 
    c#0: DatatypeType
       where $Is(c#0, Tclass._module.com())
         && $IsAlloc(c#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#0), 
    s#0: Map Box Box
       where $Is(s#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s#0, TMap(TSeq(TChar), TInt), $Heap), 
    t#0: Map Box Box
       where $Is(t#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(t#0, TMap(TSeq(TChar), TInt), $Heap), 
    t'#0: Map Box Box
       where $Is(t'#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(t'#0, TMap(TSeq(TChar), TInt), $Heap))
   returns ($_reverifyPost: bool);
  free requires 37 == $FunctionContextHeight;
  // user-defined preconditions
  requires _module.__default.big__step_h($LS($LS($LZ)), k#0, c#0, s#0, t#0);
  requires _module.__default.big__step_h($LS($LS($LZ)), k'#0, c#0, s#0, t'#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures Map#Equal(t#0, t'#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction k#0, k'#0, c#0, s#0, t#0, t'#0} Impl$$_module.__default.IMP__is__deterministic__Aux(k#0: Box, 
    k'#0: Box, 
    c#0: DatatypeType, 
    s#0: Map Box Box, 
    t#0: Map Box Box, 
    t'#0: Map Box Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;

    // AddMethodImpl: IMP_is_deterministic_Aux, Impl$$_module.__default.IMP__is__deterministic__Aux
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(148,0): initial state"} true;
    assume $IsA#_module.com(c#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#k0#0: Box, 
        $ih#k'0#0: Box, 
        $ih#c0#0: DatatypeType, 
        $ih#s0#0: Map Box Box, 
        $ih#t0#0: Map Box Box, 
        $ih#t'0#0: Map Box Box :: 
      $Is($ih#c0#0, Tclass._module.com())
           && $Is($ih#s0#0, TMap(TSeq(TChar), TInt))
           && $Is($ih#t0#0, TMap(TSeq(TChar), TInt))
           && $Is($ih#t'0#0, TMap(TSeq(TChar), TInt))
           && 
          _module.__default.big__step_h($LS($LZ), $ih#k0#0, $ih#c0#0, $ih#s0#0, $ih#t0#0)
           && _module.__default.big__step_h($LS($LZ), $ih#k'0#0, $ih#c0#0, $ih#s0#0, $ih#t'0#0)
           && (ORD#Less($ih#k0#0, k#0)
             || ($ih#k0#0 == k#0
               && (ORD#Less($ih#k'0#0, k'#0)
                 || ($ih#k'0#0 == k'#0
                   && (DtRank($ih#c0#0) < DtRank(c#0)
                     || (DtRank($ih#c0#0) == DtRank(c#0)
                       && ((Set#Subset(Map#Domain($ih#s0#0), Map#Domain(s#0))
                           && !Set#Subset(Map#Domain(s#0), Map#Domain($ih#s0#0)))
                         || (Set#Equal(Map#Domain($ih#s0#0), Map#Domain(s#0))
                           && ((Set#Subset(Map#Domain($ih#t0#0), Map#Domain(t#0))
                               && !Set#Subset(Map#Domain(t#0), Map#Domain($ih#t0#0)))
                             || (Set#Equal(Map#Domain($ih#t0#0), Map#Domain(t#0))
                               && 
                              Set#Subset(Map#Domain($ih#t'0#0), Map#Domain(t'#0))
                               && !Set#Subset(Map#Domain(t'#0), Map#Domain($ih#t'0#0))))))))))))
         ==> Map#Equal($ih#t0#0, $ih#t'0#0));
    $_reverifyPost := false;
}



// function declaration for _module._default.small_step
function _module.__default.small__step($ly: LayerType, 
    c#0: DatatypeType, 
    s#0: Map Box Box, 
    c'#0: DatatypeType, 
    s'#0: Map Box Box)
   : bool;

function _module.__default.small__step#canCall(c#0: DatatypeType, s#0: Map Box Box, c'#0: DatatypeType, s'#0: Map Box Box)
   : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, 
    c#0: DatatypeType, 
    s#0: Map Box Box, 
    c'#0: DatatypeType, 
    s'#0: Map Box Box :: 
  { _module.__default.small__step($LS($ly), c#0, s#0, c'#0, s'#0) } 
  _module.__default.small__step($LS($ly), c#0, s#0, c'#0, s'#0)
     == _module.__default.small__step($ly, c#0, s#0, c'#0, s'#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, 
    c#0: DatatypeType, 
    s#0: Map Box Box, 
    c'#0: DatatypeType, 
    s'#0: Map Box Box :: 
  { _module.__default.small__step(AsFuelBottom($ly), c#0, s#0, c'#0, s'#0) } 
  _module.__default.small__step($ly, c#0, s#0, c'#0, s'#0)
     == _module.__default.small__step($LZ, c#0, s#0, c'#0, s'#0));

// consequence axiom for _module.__default.small__step
axiom 13 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, 
      c#0: DatatypeType, 
      s#0: Map Box Box, 
      c'#0: DatatypeType, 
      s'#0: Map Box Box :: 
    { _module.__default.small__step($ly, c#0, s#0, c'#0, s'#0) } 
    _module.__default.small__step#canCall(c#0, s#0, c'#0, s'#0)
         || (13 != $FunctionContextHeight
           && 
          $Is(c#0, Tclass._module.com())
           && $Is(s#0, TMap(TSeq(TChar), TInt))
           && $Is(c'#0, Tclass._module.com())
           && $Is(s'#0, TMap(TSeq(TChar), TInt)))
       ==> true);

function _module.__default.small__step#requires(LayerType, DatatypeType, Map Box Box, DatatypeType, Map Box Box) : bool;

// #requires axiom for _module.__default.small__step
axiom (forall $ly: LayerType, 
    c#0: DatatypeType, 
    s#0: Map Box Box, 
    c'#0: DatatypeType, 
    s'#0: Map Box Box :: 
  { _module.__default.small__step#requires($ly, c#0, s#0, c'#0, s'#0) } 
  $Is(c#0, Tclass._module.com())
       && $Is(s#0, TMap(TSeq(TChar), TInt))
       && $Is(c'#0, Tclass._module.com())
       && $Is(s'#0, TMap(TSeq(TChar), TInt))
     ==> _module.__default.small__step#requires($ly, c#0, s#0, c'#0, s'#0) == true);

// definition axiom for _module.__default.small__step (revealed)
axiom 13 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, 
      c#0: DatatypeType, 
      s#0: Map Box Box, 
      c'#0: DatatypeType, 
      s'#0: Map Box Box :: 
    { _module.__default.small__step($LS($ly), c#0, s#0, c'#0, s'#0) } 
    _module.__default.small__step#canCall(c#0, s#0, c'#0, s'#0)
         || (13 != $FunctionContextHeight
           && 
          $Is(c#0, Tclass._module.com())
           && $Is(s#0, TMap(TSeq(TChar), TInt))
           && $Is(c'#0, Tclass._module.com())
           && $Is(s'#0, TMap(TSeq(TChar), TInt)))
       ==> (!_module.com.SKIP_q(c#0)
           ==> (_module.com.Assign_q(c#0)
               ==> (var a#1 := _module.com._h1(c#0); 
                $IsA#_module.com(c'#0)
                   && (_module.com#Equal(c'#0, #_module.com.SKIP())
                     ==> _module.__default.aval#canCall(a#1, s#0))))
             && (!_module.com.Assign_q(c#0)
               ==> (_module.com.Seq_q(c#0)
                   ==> (var c1#1 := _module.com._h3(c#0); 
                    (var c0#1 := _module.com._h2(c#0); 
                      $IsA#_module.com(c0#1)
                         && (_module.com#Equal(c0#1, #_module.com.SKIP())
                           ==> $IsA#_module.com(c'#0) && $IsA#_module.com(c1#1))
                         && (!(
                            _module.com#Equal(c0#1, #_module.com.SKIP())
                             && _module.com#Equal(c'#0, c1#1)
                             && Map#Equal(s'#0, s#0))
                           ==> (forall c0'#1: DatatypeType :: 
                            { _module.__default.small__step($ly, c0#1, s#0, c0'#1, s'#0) } 
                              { #_module.com.Seq(c0'#1, c1#1) } 
                            $Is(c0'#1, Tclass._module.com())
                               ==> $IsA#_module.com(c'#0)
                                 && (_module.com#Equal(c'#0, #_module.com.Seq(c0'#1, c1#1))
                                   ==> _module.__default.small__step#canCall(c0#1, s#0, c0'#1, s'#0)))))))
                 && (!_module.com.Seq_q(c#0)
                   ==> (_module.com.If_q(c#0)
                       ==> (var els#1 := _module.com._h6(c#0); 
                        (var thn#1 := _module.com._h5(c#0); 
                          (var b#2 := _module.com._h4(c#0); 
                            $IsA#_module.com(c'#0)
                               && $IsA#_module.com((if _module.__default.bval($LS($LZ), b#2, s#0) then thn#1 else els#1))
                               && _module.__default.bval#canCall(b#2, s#0)))))
                     && (!_module.com.If_q(c#0) ==> $IsA#_module.com(c'#0)))))
         && _module.__default.small__step($LS($ly), c#0, s#0, c'#0, s'#0)
           == (if _module.com.SKIP_q(c#0)
             then false
             else (if _module.com.Assign_q(c#0)
               then (var a#0 := _module.com._h1(c#0); 
                (var x#0 := _module.com._h0(c#0); 
                  _module.com#Equal(c'#0, #_module.com.SKIP())
                     && Map#Equal(s'#0, 
                      Map#Build(s#0, $Box(x#0), $Box(_module.__default.aval($LS($LZ), a#0, s#0))))))
               else (if _module.com.Seq_q(c#0)
                 then (var c1#0 := _module.com._h3(c#0); 
                  (var c0#0 := _module.com._h2(c#0); 
                    (
                        _module.com#Equal(c0#0, #_module.com.SKIP())
                         && _module.com#Equal(c'#0, c1#0)
                         && Map#Equal(s'#0, s#0))
                       || (exists c0'#0: DatatypeType :: 
                        { _module.__default.small__step($ly, c0#0, s#0, c0'#0, s'#0) } 
                          { #_module.com.Seq(c0'#0, c1#0) } 
                        $Is(c0'#0, Tclass._module.com())
                           && 
                          _module.com#Equal(c'#0, #_module.com.Seq(c0'#0, c1#0))
                           && _module.__default.small__step($ly, c0#0, s#0, c0'#0, s'#0))))
                 else (if _module.com.If_q(c#0)
                   then (var els#0 := _module.com._h6(c#0); 
                    (var thn#0 := _module.com._h5(c#0); 
                      (var b#0 := _module.com._h4(c#0); 
                        _module.com#Equal(c'#0, (if _module.__default.bval($LS($LZ), b#0, s#0) then thn#0 else els#0))
                           && Map#Equal(s'#0, s#0))))
                   else (var body#0 := _module.com._h8(c#0); 
                    (var b#1 := _module.com._h7(c#0); 
                      _module.com#Equal(c'#0, 
                          #_module.com.If(b#1, 
                            #_module.com.Seq(body#0, #_module.com.While(b#1, body#0)), 
                            Lit(#_module.com.SKIP())))
                         && Map#Equal(s'#0, s#0))))))));

// 1st prefix predicate axiom for _module.__default.small__step_h
axiom 14 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, 
      c#0: DatatypeType, 
      s#0: Map Box Box, 
      c'#0: DatatypeType, 
      s'#0: Map Box Box :: 
    { _module.__default.small__step($LS($ly), c#0, s#0, c'#0, s'#0) } 
    $Is(c#0, Tclass._module.com())
         && $Is(s#0, TMap(TSeq(TChar), TInt))
         && $Is(c'#0, Tclass._module.com())
         && $Is(s'#0, TMap(TSeq(TChar), TInt))
         && _module.__default.small__step($LS($ly), c#0, s#0, c'#0, s'#0)
       ==> (exists _k#0: Box :: 
        { _module.__default.small__step_h($LS($ly), _k#0, c#0, s#0, c'#0, s'#0) } 
        _module.__default.small__step_h($LS($ly), _k#0, c#0, s#0, c'#0, s'#0)));

// 2nd prefix predicate axiom
axiom 14 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, 
      c#0: DatatypeType, 
      s#0: Map Box Box, 
      c'#0: DatatypeType, 
      s'#0: Map Box Box :: 
    { _module.__default.small__step($LS($ly), c#0, s#0, c'#0, s'#0) } 
    $Is(c#0, Tclass._module.com())
         && $Is(s#0, TMap(TSeq(TChar), TInt))
         && $Is(c'#0, Tclass._module.com())
         && $Is(s'#0, TMap(TSeq(TChar), TInt))
         && (exists _k#0: Box :: 
          { _module.__default.small__step_h($LS($ly), _k#0, c#0, s#0, c'#0, s'#0) } 
          _module.__default.small__step_h($LS($ly), _k#0, c#0, s#0, c'#0, s'#0))
       ==> _module.__default.small__step($LS($ly), c#0, s#0, c'#0, s'#0));

// 3rd prefix predicate axiom
axiom 14 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, 
      c#0: DatatypeType, 
      s#0: Map Box Box, 
      c'#0: DatatypeType, 
      s'#0: Map Box Box, 
      _k#0: Box :: 
    { _module.__default.small__step_h($ly, _k#0, c#0, s#0, c'#0, s'#0) } 
    $Is(c#0, Tclass._module.com())
         && $Is(s#0, TMap(TSeq(TChar), TInt))
         && $Is(c'#0, Tclass._module.com())
         && $Is(s'#0, TMap(TSeq(TChar), TInt))
         && _k#0 == ORD#FromNat(0)
       ==> !_module.__default.small__step_h($ly, _k#0, c#0, s#0, c'#0, s'#0));

// targeted prefix predicate monotonicity axiom
axiom 14 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, 
      c#0: DatatypeType, 
      s#0: Map Box Box, 
      c'#0: DatatypeType, 
      s'#0: Map Box Box, 
      _k#0: Box, 
      _m: Box, 
      _limit: Box :: 
    { _module.__default.small__step_h($ly, _k#0, c#0, s#0, c'#0, s'#0), ORD#LessThanLimit(_k#0, _limit), ORD#LessThanLimit(_m, _limit) } 
    ORD#Less(_k#0, _m)
       ==> 
      _module.__default.small__step_h($ly, _k#0, c#0, s#0, c'#0, s'#0)
       ==> _module.__default.small__step_h($ly, _m, c#0, s#0, c'#0, s'#0));

procedure CheckWellformed$$_module.__default.small__step(c#0: DatatypeType where $Is(c#0, Tclass._module.com()), 
    s#0: Map Box Box where $Is(s#0, TMap(TSeq(TChar), TInt)), 
    c'#0: DatatypeType where $Is(c'#0, Tclass._module.com()), 
    s'#0: Map Box Box where $Is(s'#0, TMap(TSeq(TChar), TInt)));
  free requires 13 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.small__step(c#0: DatatypeType, s#0: Map Box Box, c'#0: DatatypeType, s'#0: Map Box Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#7#0: DatatypeType;
  var _mcc#8#0: DatatypeType;
  var body#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var b#Z#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var _mcc#4#0: DatatypeType;
  var _mcc#5#0: DatatypeType;
  var _mcc#6#0: DatatypeType;
  var els#Z#0: DatatypeType;
  var let#2#0#0: DatatypeType;
  var thn#Z#0: DatatypeType;
  var let#3#0#0: DatatypeType;
  var b#Z#1: DatatypeType;
  var let#4#0#0: DatatypeType;
  var ##b#0: DatatypeType;
  var ##s#0: Map Box Box;
  var _mcc#2#0: DatatypeType;
  var _mcc#3#0: DatatypeType;
  var c1#Z#0: DatatypeType;
  var let#5#0#0: DatatypeType;
  var c0#Z#0: DatatypeType;
  var let#6#0#0: DatatypeType;
  var c0'#2: DatatypeType;
  var ##c#0: DatatypeType;
  var ##s#1: Map Box Box;
  var ##c'#0: DatatypeType;
  var ##s'#0: Map Box Box;
  var _mcc#0#0: Seq Box;
  var _mcc#1#0: DatatypeType;
  var a#Z#0: DatatypeType;
  var let#7#0#0: DatatypeType;
  var x#Z#0: Seq Box;
  var let#8#0#0: Seq Box;
  var ##a#0: DatatypeType;
  var ##s#2: Map Box Box;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;
  var b$reqreads#2: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;

    // AddWellformednessCheck for function small_step
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(154,16): initial state"} true;
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
        if (c#0 == #_module.com.SKIP())
        {
            assume _module.__default.small__step($LS($LZ), c#0, s#0, c'#0, s'#0) == Lit(false);
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.small__step($LS($LZ), c#0, s#0, c'#0, s'#0), TBool);
        }
        else if (c#0 == #_module.com.Assign(_mcc#0#0, _mcc#1#0))
        {
            assume $Is(_mcc#0#0, TSeq(TChar));
            assume $Is(_mcc#1#0, Tclass._module.aexp());
            havoc a#Z#0;
            assume $Is(a#Z#0, Tclass._module.aexp());
            assume let#7#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#7#0#0, Tclass._module.aexp());
            assume a#Z#0 == let#7#0#0;
            havoc x#Z#0;
            assume $Is(x#Z#0, TSeq(TChar));
            assume let#8#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#8#0#0, TSeq(TChar));
            assume x#Z#0 == let#8#0#0;
            if (_module.com#Equal(c'#0, #_module.com.SKIP()))
            {
                ##a#0 := a#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##a#0, Tclass._module.aexp(), $Heap);
                ##s#2 := s#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#2, TMap(TSeq(TChar), TInt), $Heap);
                b$reqreads#2 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assume _module.__default.aval#canCall(a#Z#0, s#0);
            }

            assume _module.__default.small__step($LS($LZ), c#0, s#0, c'#0, s'#0)
               == (_module.com#Equal(c'#0, #_module.com.SKIP())
                 && Map#Equal(s'#0, 
                  Map#Build(s#0, $Box(x#Z#0), $Box(_module.__default.aval($LS($LZ), a#Z#0, s#0)))));
            assume $IsA#_module.com(c'#0)
               && (_module.com#Equal(c'#0, #_module.com.SKIP())
                 ==> _module.__default.aval#canCall(a#Z#0, s#0));
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.small__step($LS($LZ), c#0, s#0, c'#0, s'#0), TBool);
        }
        else if (c#0 == #_module.com.Seq(_mcc#2#0, _mcc#3#0))
        {
            assume $Is(_mcc#2#0, Tclass._module.com());
            assume $Is(_mcc#3#0, Tclass._module.com());
            havoc c1#Z#0;
            assume $Is(c1#Z#0, Tclass._module.com());
            assume let#5#0#0 == _mcc#3#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#5#0#0, Tclass._module.com());
            assume c1#Z#0 == let#5#0#0;
            havoc c0#Z#0;
            assume $Is(c0#Z#0, Tclass._module.com());
            assume let#6#0#0 == _mcc#2#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#6#0#0, Tclass._module.com());
            assume c0#Z#0 == let#6#0#0;
            if (_module.com#Equal(c0#Z#0, #_module.com.SKIP()))
            {
            }

            if (_module.com#Equal(c0#Z#0, #_module.com.SKIP())
               && _module.com#Equal(c'#0, c1#Z#0))
            {
            }

            if (!(
              _module.com#Equal(c0#Z#0, #_module.com.SKIP())
               && _module.com#Equal(c'#0, c1#Z#0)
               && Map#Equal(s'#0, s#0)))
            {
                // Begin Comprehension WF check
                havoc c0'#2;
                if ($Is(c0'#2, Tclass._module.com()))
                {
                    if (_module.com#Equal(c'#0, #_module.com.Seq(c0'#2, c1#Z#0)))
                    {
                        ##c#0 := c0#Z#0;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##c#0, Tclass._module.com(), $Heap);
                        ##s#1 := s#0;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##s#1, TMap(TSeq(TChar), TInt), $Heap);
                        ##c'#0 := c0'#2;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##c'#0, Tclass._module.com(), $Heap);
                        ##s'#0 := s'#0;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##s'#0, TMap(TSeq(TChar), TInt), $Heap);
                        b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                        assume _module.__default.small__step#canCall(c0#Z#0, s#0, c0'#2, s'#0);
                    }
                }

                // End Comprehension WF check
            }

            assume _module.__default.small__step($LS($LZ), c#0, s#0, c'#0, s'#0)
               == ((
                  _module.com#Equal(c0#Z#0, #_module.com.SKIP())
                   && _module.com#Equal(c'#0, c1#Z#0)
                   && Map#Equal(s'#0, s#0))
                 || (exists c0'#3: DatatypeType :: 
                  { _module.__default.small__step($LS($LZ), c0#Z#0, s#0, c0'#3, s'#0) } 
                    { #_module.com.Seq(c0'#3, c1#Z#0) } 
                  $Is(c0'#3, Tclass._module.com())
                     && 
                    _module.com#Equal(c'#0, #_module.com.Seq(c0'#3, c1#Z#0))
                     && _module.__default.small__step($LS($LZ), c0#Z#0, s#0, c0'#3, s'#0)));
            assume $IsA#_module.com(c0#Z#0)
               && (_module.com#Equal(c0#Z#0, #_module.com.SKIP())
                 ==> $IsA#_module.com(c'#0) && $IsA#_module.com(c1#Z#0))
               && (!(
                  _module.com#Equal(c0#Z#0, #_module.com.SKIP())
                   && _module.com#Equal(c'#0, c1#Z#0)
                   && Map#Equal(s'#0, s#0))
                 ==> (forall c0'#3: DatatypeType :: 
                  { _module.__default.small__step($LS($LZ), c0#Z#0, s#0, c0'#3, s'#0) } 
                    { #_module.com.Seq(c0'#3, c1#Z#0) } 
                  $Is(c0'#3, Tclass._module.com())
                     ==> $IsA#_module.com(c'#0)
                       && (_module.com#Equal(c'#0, #_module.com.Seq(c0'#3, c1#Z#0))
                         ==> _module.__default.small__step#canCall(c0#Z#0, s#0, c0'#3, s'#0))));
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.small__step($LS($LZ), c#0, s#0, c'#0, s'#0), TBool);
        }
        else if (c#0 == #_module.com.If(_mcc#4#0, _mcc#5#0, _mcc#6#0))
        {
            assume $Is(_mcc#4#0, Tclass._module.bexp());
            assume $Is(_mcc#5#0, Tclass._module.com());
            assume $Is(_mcc#6#0, Tclass._module.com());
            havoc els#Z#0;
            assume $Is(els#Z#0, Tclass._module.com());
            assume let#2#0#0 == _mcc#6#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#2#0#0, Tclass._module.com());
            assume els#Z#0 == let#2#0#0;
            havoc thn#Z#0;
            assume $Is(thn#Z#0, Tclass._module.com());
            assume let#3#0#0 == _mcc#5#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#3#0#0, Tclass._module.com());
            assume thn#Z#0 == let#3#0#0;
            havoc b#Z#1;
            assume $Is(b#Z#1, Tclass._module.bexp());
            assume let#4#0#0 == _mcc#4#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#4#0#0, Tclass._module.bexp());
            assume b#Z#1 == let#4#0#0;
            ##b#0 := b#Z#1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#0, Tclass._module.bexp(), $Heap);
            ##s#0 := s#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#0, TMap(TSeq(TChar), TInt), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.bval#canCall(b#Z#1, s#0);
            if (_module.__default.bval($LS($LZ), b#Z#1, s#0))
            {
            }
            else
            {
            }

            if (_module.com#Equal(c'#0, 
              (if _module.__default.bval($LS($LZ), b#Z#1, s#0) then thn#Z#0 else els#Z#0)))
            {
            }

            assume _module.__default.small__step($LS($LZ), c#0, s#0, c'#0, s'#0)
               == (_module.com#Equal(c'#0, 
                  (if _module.__default.bval($LS($LZ), b#Z#1, s#0) then thn#Z#0 else els#Z#0))
                 && Map#Equal(s'#0, s#0));
            assume $IsA#_module.com(c'#0)
               && $IsA#_module.com((if _module.__default.bval($LS($LZ), b#Z#1, s#0) then thn#Z#0 else els#Z#0))
               && _module.__default.bval#canCall(b#Z#1, s#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.small__step($LS($LZ), c#0, s#0, c'#0, s'#0), TBool);
        }
        else if (c#0 == #_module.com.While(_mcc#7#0, _mcc#8#0))
        {
            assume $Is(_mcc#7#0, Tclass._module.bexp());
            assume $Is(_mcc#8#0, Tclass._module.com());
            havoc body#Z#0;
            assume $Is(body#Z#0, Tclass._module.com());
            assume let#0#0#0 == _mcc#8#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.com());
            assume body#Z#0 == let#0#0#0;
            havoc b#Z#0;
            assume $Is(b#Z#0, Tclass._module.bexp());
            assume let#1#0#0 == _mcc#7#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#1#0#0, Tclass._module.bexp());
            assume b#Z#0 == let#1#0#0;
            if (_module.com#Equal(c'#0, 
              #_module.com.If(b#Z#0, 
                #_module.com.Seq(body#Z#0, #_module.com.While(b#Z#0, body#Z#0)), 
                Lit(#_module.com.SKIP()))))
            {
            }

            assume _module.__default.small__step($LS($LZ), c#0, s#0, c'#0, s'#0)
               == (_module.com#Equal(c'#0, 
                  #_module.com.If(b#Z#0, 
                    #_module.com.Seq(body#Z#0, #_module.com.While(b#Z#0, body#Z#0)), 
                    Lit(#_module.com.SKIP())))
                 && Map#Equal(s'#0, s#0));
            assume $IsA#_module.com(c'#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.small__step($LS($LZ), c#0, s#0, c'#0, s'#0), TBool);
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



// function declaration for _module._default.small_step#
function _module.__default.small__step_h($ly: LayerType, 
    _k#0: Box, 
    c#0: DatatypeType, 
    s#0: Map Box Box, 
    c'#0: DatatypeType, 
    s'#0: Map Box Box)
   : bool;

function _module.__default.small__step_h#canCall(_k#0: Box, 
    c#0: DatatypeType, 
    s#0: Map Box Box, 
    c'#0: DatatypeType, 
    s'#0: Map Box Box)
   : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, 
    _k#0: Box, 
    c#0: DatatypeType, 
    s#0: Map Box Box, 
    c'#0: DatatypeType, 
    s'#0: Map Box Box :: 
  { _module.__default.small__step_h($LS($ly), _k#0, c#0, s#0, c'#0, s'#0) } 
  _module.__default.small__step_h($LS($ly), _k#0, c#0, s#0, c'#0, s'#0)
     == _module.__default.small__step_h($ly, _k#0, c#0, s#0, c'#0, s'#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, 
    _k#0: Box, 
    c#0: DatatypeType, 
    s#0: Map Box Box, 
    c'#0: DatatypeType, 
    s'#0: Map Box Box :: 
  { _module.__default.small__step_h(AsFuelBottom($ly), _k#0, c#0, s#0, c'#0, s'#0) } 
  _module.__default.small__step_h($ly, _k#0, c#0, s#0, c'#0, s'#0)
     == _module.__default.small__step_h($LZ, _k#0, c#0, s#0, c'#0, s'#0));

// consequence axiom for _module.__default.small__step_h
axiom 14 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, 
      _k#0: Box, 
      c#0: DatatypeType, 
      s#0: Map Box Box, 
      c'#0: DatatypeType, 
      s'#0: Map Box Box :: 
    { _module.__default.small__step_h($ly, _k#0, c#0, s#0, c'#0, s'#0) } 
    _module.__default.small__step_h#canCall(_k#0, c#0, s#0, c'#0, s'#0)
         || (14 != $FunctionContextHeight
           && 
          $Is(c#0, Tclass._module.com())
           && $Is(s#0, TMap(TSeq(TChar), TInt))
           && $Is(c'#0, Tclass._module.com())
           && $Is(s'#0, TMap(TSeq(TChar), TInt)))
       ==> true);

function _module.__default.small__step_h#requires(LayerType, Box, DatatypeType, Map Box Box, DatatypeType, Map Box Box) : bool;

// #requires axiom for _module.__default.small__step_h
axiom (forall $ly: LayerType, 
    _k#0: Box, 
    c#0: DatatypeType, 
    s#0: Map Box Box, 
    c'#0: DatatypeType, 
    s'#0: Map Box Box :: 
  { _module.__default.small__step_h#requires($ly, _k#0, c#0, s#0, c'#0, s'#0) } 
  $Is(c#0, Tclass._module.com())
       && $Is(s#0, TMap(TSeq(TChar), TInt))
       && $Is(c'#0, Tclass._module.com())
       && $Is(s'#0, TMap(TSeq(TChar), TInt))
     ==> _module.__default.small__step_h#requires($ly, _k#0, c#0, s#0, c'#0, s'#0)
       == true);

// definition axiom for _module.__default.small__step_h (revealed)
axiom 14 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, 
      _k#0: Box, 
      c#0: DatatypeType, 
      s#0: Map Box Box, 
      c'#0: DatatypeType, 
      s'#0: Map Box Box :: 
    { _module.__default.small__step_h($LS($ly), _k#0, c#0, s#0, c'#0, s'#0) } 
    _module.__default.small__step_h#canCall(_k#0, c#0, s#0, c'#0, s'#0)
         || (14 != $FunctionContextHeight
           && 
          $Is(c#0, Tclass._module.com())
           && $Is(s#0, TMap(TSeq(TChar), TInt))
           && $Is(c'#0, Tclass._module.com())
           && $Is(s'#0, TMap(TSeq(TChar), TInt)))
       ==> (0 < ORD#Offset(_k#0)
           ==> 
          !_module.com.SKIP_q(c#0)
           ==> (_module.com.Assign_q(c#0)
               ==> (var a#3 := _module.com._h1(c#0); 
                $IsA#_module.com(c'#0)
                   && (_module.com#Equal(c'#0, #_module.com.SKIP())
                     ==> _module.__default.aval#canCall(a#3, s#0))))
             && (!_module.com.Assign_q(c#0)
               ==> (_module.com.Seq_q(c#0)
                   ==> (var c1#3 := _module.com._h3(c#0); 
                    (var c0#3 := _module.com._h2(c#0); 
                      $IsA#_module.com(c0#3)
                         && (_module.com#Equal(c0#3, #_module.com.SKIP())
                           ==> $IsA#_module.com(c'#0) && $IsA#_module.com(c1#3))
                         && (!(
                            _module.com#Equal(c0#3, #_module.com.SKIP())
                             && _module.com#Equal(c'#0, c1#3)
                             && Map#Equal(s'#0, s#0))
                           ==> (forall c0'#5: DatatypeType :: 
                            { _module.__default.small__step_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), c0#3, s#0, c0'#5, s'#0) } 
                              { #_module.com.Seq(c0'#5, c1#3) } 
                            $Is(c0'#5, Tclass._module.com())
                               ==> $IsA#_module.com(c'#0)
                                 && (_module.com#Equal(c'#0, #_module.com.Seq(c0'#5, c1#3))
                                   ==> _module.__default.small__step_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), c0#3, s#0, c0'#5, s'#0)))))))
                 && (!_module.com.Seq_q(c#0)
                   ==> (_module.com.If_q(c#0)
                       ==> (var els#3 := _module.com._h6(c#0); 
                        (var thn#3 := _module.com._h5(c#0); 
                          (var b#6 := _module.com._h4(c#0); 
                            $IsA#_module.com(c'#0)
                               && $IsA#_module.com((if _module.__default.bval($LS($LZ), b#6, s#0) then thn#3 else els#3))
                               && _module.__default.bval#canCall(b#6, s#0)))))
                     && (!_module.com.If_q(c#0) ==> $IsA#_module.com(c'#0)))))
         && (
          (0 < ORD#Offset(_k#0)
           ==> (if _module.com.SKIP_q(c#0)
             then false
             else (if _module.com.Assign_q(c#0)
               then (var a#4 := _module.com._h1(c#0); 
                (var x#4 := _module.com._h0(c#0); 
                  _module.com#Equal(c'#0, #_module.com.SKIP())
                     && Map#Equal(s'#0, 
                      Map#Build(s#0, $Box(x#4), $Box(_module.__default.aval($LS($LZ), a#4, s#0))))))
               else (if _module.com.Seq_q(c#0)
                 then (var c1#4 := _module.com._h3(c#0); 
                  (var c0#4 := _module.com._h2(c#0); 
                    (
                        _module.com#Equal(c0#4, #_module.com.SKIP())
                         && _module.com#Equal(c'#0, c1#4)
                         && Map#Equal(s'#0, s#0))
                       || (exists c0'#6: DatatypeType :: 
                        { _module.__default.small__step_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), c0#4, s#0, c0'#6, s'#0) } 
                          { #_module.com.Seq(c0'#6, c1#4) } 
                        $Is(c0'#6, Tclass._module.com())
                           && 
                          _module.com#Equal(c'#0, #_module.com.Seq(c0'#6, c1#4))
                           && _module.__default.small__step_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), c0#4, s#0, c0'#6, s'#0))))
                 else (if _module.com.If_q(c#0)
                   then (var els#4 := _module.com._h6(c#0); 
                    (var thn#4 := _module.com._h5(c#0); 
                      (var b#8 := _module.com._h4(c#0); 
                        _module.com#Equal(c'#0, (if _module.__default.bval($LS($LZ), b#8, s#0) then thn#4 else els#4))
                           && Map#Equal(s'#0, s#0))))
                   else (var body#4 := _module.com._h8(c#0); 
                    (var b#9 := _module.com._h7(c#0); 
                      _module.com#Equal(c'#0, 
                          #_module.com.If(b#9, 
                            #_module.com.Seq(body#4, #_module.com.While(b#9, body#4)), 
                            Lit(#_module.com.SKIP())))
                         && Map#Equal(s'#0, s#0))))))))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#0: Box :: 
            { _module.__default.small__step_h($ly, _k'#0, c#0, s#0, c'#0, s'#0) } 
            ORD#LessThanLimit(_k'#0, _k#0)
               ==> _module.__default.small__step_h#canCall(_k'#0, c#0, s#0, c'#0, s'#0)))
         && _module.__default.small__step_h($LS($ly), _k#0, c#0, s#0, c'#0, s'#0)
           == ((0 < ORD#Offset(_k#0)
               ==> (if _module.com.SKIP_q(c#0)
                 then false
                 else (if _module.com.Assign_q(c#0)
                   then (var a#2 := _module.com._h1(c#0); 
                    (var x#2 := _module.com._h0(c#0); 
                      _module.com#Equal(c'#0, #_module.com.SKIP())
                         && Map#Equal(s'#0, 
                          Map#Build(s#0, $Box(x#2), $Box(_module.__default.aval($LS($LZ), a#2, s#0))))))
                   else (if _module.com.Seq_q(c#0)
                     then (var c1#2 := _module.com._h3(c#0); 
                      (var c0#2 := _module.com._h2(c#0); 
                        (
                            _module.com#Equal(c0#2, #_module.com.SKIP())
                             && _module.com#Equal(c'#0, c1#2)
                             && Map#Equal(s'#0, s#0))
                           || (exists c0'#4: DatatypeType :: 
                            { _module.__default.small__step_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), c0#2, s#0, c0'#4, s'#0) } 
                              { #_module.com.Seq(c0'#4, c1#2) } 
                            $Is(c0'#4, Tclass._module.com())
                               && 
                              _module.com#Equal(c'#0, #_module.com.Seq(c0'#4, c1#2))
                               && _module.__default.small__step_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), c0#2, s#0, c0'#4, s'#0))))
                     else (if _module.com.If_q(c#0)
                       then (var els#2 := _module.com._h6(c#0); 
                        (var thn#2 := _module.com._h5(c#0); 
                          (var b#4 := _module.com._h4(c#0); 
                            _module.com#Equal(c'#0, (if _module.__default.bval($LS($LZ), b#4, s#0) then thn#2 else els#2))
                               && Map#Equal(s'#0, s#0))))
                       else (var body#2 := _module.com._h8(c#0); 
                        (var b#5 := _module.com._h7(c#0); 
                          _module.com#Equal(c'#0, 
                              #_module.com.If(b#5, 
                                #_module.com.Seq(body#2, #_module.com.While(b#5, body#2)), 
                                Lit(#_module.com.SKIP())))
                             && Map#Equal(s'#0, s#0))))))))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (exists _k'#0: Box :: 
                { _module.__default.small__step_h($ly, _k'#0, c#0, s#0, c'#0, s'#0) } 
                ORD#LessThanLimit(_k'#0, _k#0)
                   && _module.__default.small__step_h($ly, _k'#0, c#0, s#0, c'#0, s'#0)))));

// definition axiom for _module.__default.small__step_h for decreasing-related literals (revealed)
axiom 14 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, 
      _k#0: Box, 
      c#0: DatatypeType, 
      s#0: Map Box Box, 
      c'#0: DatatypeType, 
      s'#0: Map Box Box :: 
    {:weight 3} { _module.__default.small__step_h($LS($ly), Lit(_k#0), c#0, s#0, c'#0, s'#0) } 
    _module.__default.small__step_h#canCall(Lit(_k#0), c#0, s#0, c'#0, s'#0)
         || (14 != $FunctionContextHeight
           && 
          $Is(c#0, Tclass._module.com())
           && $Is(s#0, TMap(TSeq(TChar), TInt))
           && $Is(c'#0, Tclass._module.com())
           && $Is(s'#0, TMap(TSeq(TChar), TInt)))
       ==> (0 < ORD#Offset(_k#0)
           ==> 
          !_module.com.SKIP_q(c#0)
           ==> (_module.com.Assign_q(c#0)
               ==> (var a#6 := _module.com._h1(c#0); 
                $IsA#_module.com(c'#0)
                   && (_module.com#Equal(c'#0, #_module.com.SKIP())
                     ==> _module.__default.aval#canCall(a#6, s#0))))
             && (!_module.com.Assign_q(c#0)
               ==> (_module.com.Seq_q(c#0)
                   ==> (var c1#6 := _module.com._h3(c#0); 
                    (var c0#6 := _module.com._h2(c#0); 
                      $IsA#_module.com(c0#6)
                         && (_module.com#Equal(c0#6, #_module.com.SKIP())
                           ==> $IsA#_module.com(c'#0) && $IsA#_module.com(c1#6))
                         && (!(
                            _module.com#Equal(c0#6, #_module.com.SKIP())
                             && _module.com#Equal(c'#0, c1#6)
                             && Map#Equal(s'#0, s#0))
                           ==> (forall c0'#8: DatatypeType :: 
                            { _module.__default.small__step_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), c0#6, s#0, c0'#8, s'#0) } 
                              { #_module.com.Seq(c0'#8, c1#6) } 
                            $Is(c0'#8, Tclass._module.com())
                               ==> $IsA#_module.com(c'#0)
                                 && (_module.com#Equal(c'#0, #_module.com.Seq(c0'#8, c1#6))
                                   ==> _module.__default.small__step_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), c0#6, s#0, c0'#8, s'#0)))))))
                 && (!_module.com.Seq_q(c#0)
                   ==> (_module.com.If_q(c#0)
                       ==> (var els#6 := _module.com._h6(c#0); 
                        (var thn#6 := _module.com._h5(c#0); 
                          (var b#12 := _module.com._h4(c#0); 
                            $IsA#_module.com(c'#0)
                               && $IsA#_module.com((if _module.__default.bval($LS($LZ), b#12, s#0) then thn#6 else els#6))
                               && _module.__default.bval#canCall(b#12, s#0)))))
                     && (!_module.com.If_q(c#0) ==> $IsA#_module.com(c'#0)))))
         && (
          (0 < ORD#Offset(_k#0)
           ==> (if _module.com.SKIP_q(c#0)
             then false
             else (if _module.com.Assign_q(c#0)
               then (var a#7 := _module.com._h1(c#0); 
                (var x#7 := _module.com._h0(c#0); 
                  _module.com#Equal(c'#0, #_module.com.SKIP())
                     && Map#Equal(s'#0, 
                      Map#Build(s#0, $Box(x#7), $Box(_module.__default.aval($LS($LZ), a#7, s#0))))))
               else (if _module.com.Seq_q(c#0)
                 then (var c1#7 := _module.com._h3(c#0); 
                  (var c0#7 := _module.com._h2(c#0); 
                    (
                        _module.com#Equal(c0#7, #_module.com.SKIP())
                         && _module.com#Equal(c'#0, c1#7)
                         && Map#Equal(s'#0, s#0))
                       || (exists c0'#9: DatatypeType :: 
                        { _module.__default.small__step_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), c0#7, s#0, c0'#9, s'#0) } 
                          { #_module.com.Seq(c0'#9, c1#7) } 
                        $Is(c0'#9, Tclass._module.com())
                           && 
                          _module.com#Equal(c'#0, #_module.com.Seq(c0'#9, c1#7))
                           && _module.__default.small__step_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), c0#7, s#0, c0'#9, s'#0))))
                 else (if _module.com.If_q(c#0)
                   then (var els#7 := _module.com._h6(c#0); 
                    (var thn#7 := _module.com._h5(c#0); 
                      (var b#14 := _module.com._h4(c#0); 
                        _module.com#Equal(c'#0, (if _module.__default.bval($LS($LZ), b#14, s#0) then thn#7 else els#7))
                           && Map#Equal(s'#0, s#0))))
                   else (var body#7 := _module.com._h8(c#0); 
                    (var b#15 := _module.com._h7(c#0); 
                      _module.com#Equal(c'#0, 
                          #_module.com.If(b#15, 
                            #_module.com.Seq(body#7, #_module.com.While(b#15, body#7)), 
                            Lit(#_module.com.SKIP())))
                         && Map#Equal(s'#0, s#0))))))))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#1: Box :: 
            { _module.__default.small__step_h($LS($ly), _k'#1, c#0, s#0, c'#0, s'#0) } 
            ORD#LessThanLimit(_k'#1, _k#0)
               ==> _module.__default.small__step_h#canCall(_k'#1, c#0, s#0, c'#0, s'#0)))
         && _module.__default.small__step_h($LS($ly), Lit(_k#0), c#0, s#0, c'#0, s'#0)
           == ((0 < ORD#Offset(_k#0)
               ==> (if _module.com.SKIP_q(c#0)
                 then false
                 else (if _module.com.Assign_q(c#0)
                   then (var a#5 := _module.com._h1(c#0); 
                    (var x#5 := _module.com._h0(c#0); 
                      _module.com#Equal(c'#0, #_module.com.SKIP())
                         && Map#Equal(s'#0, 
                          Map#Build(s#0, $Box(x#5), $Box(_module.__default.aval($LS($LZ), a#5, s#0))))))
                   else (if _module.com.Seq_q(c#0)
                     then (var c1#5 := _module.com._h3(c#0); 
                      (var c0#5 := _module.com._h2(c#0); 
                        (
                            _module.com#Equal(c0#5, #_module.com.SKIP())
                             && _module.com#Equal(c'#0, c1#5)
                             && Map#Equal(s'#0, s#0))
                           || (exists c0'#7: DatatypeType :: 
                            { _module.__default.small__step_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), c0#5, s#0, c0'#7, s'#0) } 
                              { #_module.com.Seq(c0'#7, c1#5) } 
                            $Is(c0'#7, Tclass._module.com())
                               && 
                              _module.com#Equal(c'#0, #_module.com.Seq(c0'#7, c1#5))
                               && _module.__default.small__step_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), c0#5, s#0, c0'#7, s'#0))))
                     else (if _module.com.If_q(c#0)
                       then (var els#5 := _module.com._h6(c#0); 
                        (var thn#5 := _module.com._h5(c#0); 
                          (var b#10 := _module.com._h4(c#0); 
                            _module.com#Equal(c'#0, (if _module.__default.bval($LS($LZ), b#10, s#0) then thn#5 else els#5))
                               && Map#Equal(s'#0, s#0))))
                       else (var body#5 := _module.com._h8(c#0); 
                        (var b#11 := _module.com._h7(c#0); 
                          _module.com#Equal(c'#0, 
                              #_module.com.If(b#11, 
                                #_module.com.Seq(body#5, #_module.com.While(b#11, body#5)), 
                                Lit(#_module.com.SKIP())))
                             && Map#Equal(s'#0, s#0))))))))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (exists _k'#1: Box :: 
                { _module.__default.small__step_h($LS($ly), _k'#1, c#0, s#0, c'#0, s'#0) } 
                ORD#LessThanLimit(_k'#1, _k#0)
                   && _module.__default.small__step_h($LS($ly), _k'#1, c#0, s#0, c'#0, s'#0)))));

// definition axiom for _module.__default.small__step_h for all literals (revealed)
axiom 14 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, 
      _k#0: Box, 
      c#0: DatatypeType, 
      s#0: Map Box Box, 
      c'#0: DatatypeType, 
      s'#0: Map Box Box :: 
    {:weight 3} { _module.__default.small__step_h($LS($ly), Lit(_k#0), Lit(c#0), Lit(s#0), Lit(c'#0), Lit(s'#0)) } 
    _module.__default.small__step_h#canCall(Lit(_k#0), Lit(c#0), Lit(s#0), Lit(c'#0), Lit(s'#0))
         || (14 != $FunctionContextHeight
           && 
          $Is(c#0, Tclass._module.com())
           && $Is(s#0, TMap(TSeq(TChar), TInt))
           && $Is(c'#0, Tclass._module.com())
           && $Is(s'#0, TMap(TSeq(TChar), TInt)))
       ==> (0 < ORD#Offset(_k#0)
           ==> 
          !_module.com.SKIP_q(c#0)
           ==> (_module.com.Assign_q(c#0)
               ==> (var a#9 := _module.com._h1(c#0); 
                $IsA#_module.com(c'#0)
                   && (_module.com#Equal(c'#0, #_module.com.SKIP())
                     ==> _module.__default.aval#canCall(a#9, s#0))))
             && (!_module.com.Assign_q(c#0)
               ==> (_module.com.Seq_q(c#0)
                   ==> (var c1#9 := _module.com._h3(c#0); 
                    (var c0#9 := _module.com._h2(c#0); 
                      $IsA#_module.com(c0#9)
                         && (_module.com#Equal(c0#9, #_module.com.SKIP())
                           ==> $IsA#_module.com(c'#0) && $IsA#_module.com(c1#9))
                         && (!(
                            _module.com#Equal(c0#9, #_module.com.SKIP())
                             && _module.com#Equal(c'#0, c1#9)
                             && Map#Equal(s'#0, s#0))
                           ==> (forall c0'#11: DatatypeType :: 
                            { _module.__default.small__step_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), c0#9, s#0, c0'#11, s'#0) } 
                              { #_module.com.Seq(c0'#11, c1#9) } 
                            $Is(c0'#11, Tclass._module.com())
                               ==> $IsA#_module.com(c'#0)
                                 && (_module.com#Equal(c'#0, #_module.com.Seq(c0'#11, c1#9))
                                   ==> _module.__default.small__step_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), c0#9, s#0, c0'#11, s'#0)))))))
                 && (!_module.com.Seq_q(c#0)
                   ==> (_module.com.If_q(c#0)
                       ==> (var els#9 := _module.com._h6(c#0); 
                        (var thn#9 := _module.com._h5(c#0); 
                          (var b#18 := _module.com._h4(c#0); 
                            $IsA#_module.com(c'#0)
                               && $IsA#_module.com((if _module.__default.bval($LS($LZ), b#18, s#0) then thn#9 else els#9))
                               && _module.__default.bval#canCall(b#18, s#0)))))
                     && (!_module.com.If_q(c#0) ==> $IsA#_module.com(c'#0)))))
         && (
          (0 < ORD#Offset(_k#0)
           ==> (if _module.com.SKIP_q(c#0)
             then false
             else (if _module.com.Assign_q(c#0)
               then (var a#10 := _module.com._h1(c#0); 
                (var x#10 := _module.com._h0(c#0); 
                  _module.com#Equal(c'#0, #_module.com.SKIP())
                     && Map#Equal(s'#0, 
                      Map#Build(s#0, $Box(x#10), $Box(_module.__default.aval($LS($LZ), a#10, s#0))))))
               else (if _module.com.Seq_q(c#0)
                 then (var c1#10 := _module.com._h3(c#0); 
                  (var c0#10 := _module.com._h2(c#0); 
                    (
                        _module.com#Equal(c0#10, #_module.com.SKIP())
                         && _module.com#Equal(c'#0, c1#10)
                         && Map#Equal(s'#0, s#0))
                       || (exists c0'#12: DatatypeType :: 
                        { _module.__default.small__step_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), c0#10, s#0, c0'#12, s'#0) } 
                          { #_module.com.Seq(c0'#12, c1#10) } 
                        $Is(c0'#12, Tclass._module.com())
                           && 
                          _module.com#Equal(c'#0, #_module.com.Seq(c0'#12, c1#10))
                           && _module.__default.small__step_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), c0#10, s#0, c0'#12, s'#0))))
                 else (if _module.com.If_q(c#0)
                   then (var els#10 := _module.com._h6(c#0); 
                    (var thn#10 := _module.com._h5(c#0); 
                      (var b#20 := _module.com._h4(c#0); 
                        _module.com#Equal(c'#0, (if _module.__default.bval($LS($LZ), b#20, s#0) then thn#10 else els#10))
                           && Map#Equal(s'#0, s#0))))
                   else (var body#10 := _module.com._h8(c#0); 
                    (var b#21 := _module.com._h7(c#0); 
                      _module.com#Equal(c'#0, 
                          #_module.com.If(b#21, 
                            #_module.com.Seq(body#10, #_module.com.While(b#21, body#10)), 
                            Lit(#_module.com.SKIP())))
                         && Map#Equal(s'#0, s#0))))))))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#2: Box :: 
            { _module.__default.small__step_h($LS($ly), _k'#2, c#0, s#0, c'#0, s'#0) } 
            ORD#LessThanLimit(_k'#2, _k#0)
               ==> _module.__default.small__step_h#canCall(_k'#2, c#0, s#0, c'#0, s'#0)))
         && _module.__default.small__step_h($LS($ly), Lit(_k#0), Lit(c#0), Lit(s#0), Lit(c'#0), Lit(s'#0))
           == ((0 < ORD#Offset(_k#0)
               ==> (if _module.com.SKIP_q(c#0)
                 then false
                 else (if _module.com.Assign_q(c#0)
                   then (var a#8 := _module.com._h1(c#0); 
                    (var x#8 := _module.com._h0(c#0); 
                      _module.com#Equal(c'#0, #_module.com.SKIP())
                         && Map#Equal(s'#0, 
                          Map#Build(s#0, $Box(x#8), $Box(_module.__default.aval($LS($LZ), a#8, s#0))))))
                   else (if _module.com.Seq_q(c#0)
                     then (var c1#8 := _module.com._h3(c#0); 
                      (var c0#8 := _module.com._h2(c#0); 
                        (
                            _module.com#Equal(c0#8, #_module.com.SKIP())
                             && _module.com#Equal(c'#0, c1#8)
                             && Map#Equal(s'#0, s#0))
                           || (exists c0'#10: DatatypeType :: 
                            { _module.__default.small__step_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), c0#8, s#0, c0'#10, s'#0) } 
                              { #_module.com.Seq(c0'#10, c1#8) } 
                            $Is(c0'#10, Tclass._module.com())
                               && 
                              _module.com#Equal(c'#0, #_module.com.Seq(c0'#10, c1#8))
                               && _module.__default.small__step_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), c0#8, s#0, c0'#10, s'#0))))
                     else (if _module.com.If_q(c#0)
                       then (var els#8 := _module.com._h6(c#0); 
                        (var thn#8 := _module.com._h5(c#0); 
                          (var b#16 := _module.com._h4(c#0); 
                            _module.com#Equal(c'#0, (if _module.__default.bval($LS($LZ), b#16, s#0) then thn#8 else els#8))
                               && Map#Equal(s'#0, s#0))))
                       else (var body#8 := _module.com._h8(c#0); 
                        (var b#17 := _module.com._h7(c#0); 
                          _module.com#Equal(c'#0, 
                              #_module.com.If(b#17, 
                                #_module.com.Seq(body#8, #_module.com.While(b#17, body#8)), 
                                Lit(#_module.com.SKIP())))
                             && Map#Equal(s'#0, s#0))))))))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (exists _k'#2: Box :: 
                { _module.__default.small__step_h($LS($ly), _k'#2, c#0, s#0, c'#0, s'#0) } 
                ORD#LessThanLimit(_k'#2, _k#0)
                   && _module.__default.small__step_h($LS($ly), _k'#2, c#0, s#0, c'#0, s'#0)))));

procedure {:_induction k#0, c0#0, c1#0, s#0, c'#0, s'#0} CheckWellformed$$_module.__default.SeqCasesAreExclusive(k#0: Box, 
    c0#0: DatatypeType
       where $Is(c0#0, Tclass._module.com())
         && $IsAlloc(c0#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c0#0), 
    c1#0: DatatypeType
       where $Is(c1#0, Tclass._module.com())
         && $IsAlloc(c1#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c1#0), 
    s#0: Map Box Box
       where $Is(s#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s#0, TMap(TSeq(TChar), TInt), $Heap), 
    c'#0: DatatypeType
       where $Is(c'#0, Tclass._module.com())
         && $IsAlloc(c'#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c'#0), 
    s'#0: Map Box Box
       where $Is(s'#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s'#0, TMap(TSeq(TChar), TInt), $Heap));
  free requires 39 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction k#0, c0#0, c1#0, s#0, c'#0, s'#0} Call$$_module.__default.SeqCasesAreExclusive(k#0: Box, 
    c0#0: DatatypeType
       where $Is(c0#0, Tclass._module.com())
         && $IsAlloc(c0#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c0#0), 
    c1#0: DatatypeType
       where $Is(c1#0, Tclass._module.com())
         && $IsAlloc(c1#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c1#0), 
    s#0: Map Box Box
       where $Is(s#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s#0, TMap(TSeq(TChar), TInt), $Heap), 
    c'#0: DatatypeType
       where $Is(c'#0, Tclass._module.com())
         && $IsAlloc(c'#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c'#0), 
    s'#0: Map Box Box
       where $Is(s'#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s'#0, TMap(TSeq(TChar), TInt), $Heap));
  // user-defined preconditions
  requires ORD#Offset(k#0) > 0;
  requires _module.__default.small__step_h($LS($LS($LZ)), k#0, #_module.com.Seq(c0#0, c1#0), s#0, c'#0, s'#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.com(c0#0)
     && (_module.com#Equal(c0#0, #_module.com.SKIP())
       ==> $IsA#_module.com(c'#0) && $IsA#_module.com(c1#0));
  ensures _module.com#Equal(c0#0, #_module.com.SKIP()) ==> _module.com#Equal(c'#0, c1#0);
  ensures _module.com#Equal(c0#0, #_module.com.SKIP()) ==> Map#Equal(s'#0, s#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction k#0, c0#0, c1#0, s#0, c'#0, s'#0} Impl$$_module.__default.SeqCasesAreExclusive(k#0: Box, 
    c0#0: DatatypeType
       where $Is(c0#0, Tclass._module.com())
         && $IsAlloc(c0#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c0#0), 
    c1#0: DatatypeType
       where $Is(c1#0, Tclass._module.com())
         && $IsAlloc(c1#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c1#0), 
    s#0: Map Box Box
       where $Is(s#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s#0, TMap(TSeq(TChar), TInt), $Heap), 
    c'#0: DatatypeType
       where $Is(c'#0, Tclass._module.com())
         && $IsAlloc(c'#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c'#0), 
    s'#0: Map Box Box
       where $Is(s'#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s'#0, TMap(TSeq(TChar), TInt), $Heap))
   returns ($_reverifyPost: bool);
  free requires 39 == $FunctionContextHeight;
  // user-defined preconditions
  requires ORD#Offset(k#0) > 0;
  requires _module.__default.small__step_h($LS($LS($LZ)), k#0, #_module.com.Seq(c0#0, c1#0), s#0, c'#0, s'#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.com(c0#0)
     && (_module.com#Equal(c0#0, #_module.com.SKIP())
       ==> $IsA#_module.com(c'#0) && $IsA#_module.com(c1#0));
  ensures _module.com#Equal(c0#0, #_module.com.SKIP()) ==> _module.com#Equal(c'#0, c1#0);
  ensures _module.com#Equal(c0#0, #_module.com.SKIP()) ==> Map#Equal(s'#0, s#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction k#0, c0#0, c1#0, s#0, c'#0, s'#0} Impl$$_module.__default.SeqCasesAreExclusive(k#0: Box, 
    c0#0: DatatypeType, 
    c1#0: DatatypeType, 
    s#0: Map Box Box, 
    c'#0: DatatypeType, 
    s'#0: Map Box Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var c0'#0_0: DatatypeType;
  var ##c#0_0: DatatypeType;
  var ##s#0_0: Map Box Box;
  var ##c'#0_0: DatatypeType;
  var ##s'#0_0: Map Box Box;
  var c0'#0_0_0: DatatypeType;
  var ##c#0_0_0: DatatypeType;
  var ##s#0_0_0: Map Box Box;
  var ##c'#0_0_0: DatatypeType;
  var ##s'#0_0_0: Map Box Box;

    // AddMethodImpl: SeqCasesAreExclusive, Impl$$_module.__default.SeqCasesAreExclusive
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(175,0): initial state"} true;
    assume $IsA#_module.com(c0#0);
    assume $IsA#_module.com(c1#0);
    assume $IsA#_module.com(c'#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#k0#0: Box, 
        $ih#c00#0: DatatypeType, 
        $ih#c10#0: DatatypeType, 
        $ih#s0#0: Map Box Box, 
        $ih#c'0#0: DatatypeType, 
        $ih#s'0#0: Map Box Box :: 
      $Is($ih#c00#0, Tclass._module.com())
           && $Is($ih#c10#0, Tclass._module.com())
           && $Is($ih#s0#0, TMap(TSeq(TChar), TInt))
           && $Is($ih#c'0#0, Tclass._module.com())
           && $Is($ih#s'0#0, TMap(TSeq(TChar), TInt))
           && 
          ORD#Offset($ih#k0#0) > 0
           && _module.__default.small__step_h($LS($LZ), 
            $ih#k0#0, 
            #_module.com.Seq($ih#c00#0, $ih#c10#0), 
            $ih#s0#0, 
            $ih#c'0#0, 
            $ih#s'0#0)
           && (ORD#Less($ih#k0#0, k#0)
             || ($ih#k0#0 == k#0
               && (DtRank($ih#c00#0) < DtRank(c0#0)
                 || (DtRank($ih#c00#0) == DtRank(c0#0)
                   && (DtRank($ih#c10#0) < DtRank(c1#0)
                     || (DtRank($ih#c10#0) == DtRank(c1#0)
                       && ((Set#Subset(Map#Domain($ih#s0#0), Map#Domain(s#0))
                           && !Set#Subset(Map#Domain(s#0), Map#Domain($ih#s0#0)))
                         || (Set#Equal(Map#Domain($ih#s0#0), Map#Domain(s#0))
                           && (DtRank($ih#c'0#0) < DtRank(c'#0)
                             || (DtRank($ih#c'0#0) == DtRank(c'#0)
                               && 
                              Set#Subset(Map#Domain($ih#s'0#0), Map#Domain(s'#0))
                               && !Set#Subset(Map#Domain(s'#0), Map#Domain($ih#s'0#0))))))))))))
         ==> 
        _module.com#Equal($ih#c00#0, #_module.com.SKIP())
         ==> _module.com#Equal($ih#c'0#0, $ih#c10#0) && Map#Equal($ih#s'0#0, $ih#s0#0));
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(176,3)
    assume true;
    assert ORD#Offset(k#0) != 0;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(177,3)
    if (_module.com#Equal(c0#0, #_module.com.SKIP()))
    {
    }

    assume $IsA#_module.com(c0#0);
    if (_module.com#Equal(c0#0, #_module.com.SKIP()) && ORD#Offset(k#0) == LitInt(1))
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(178,5)
        if (_module.com#Equal(c0#0, #_module.com.SKIP()))
        {
        }

        if (_module.com#Equal(c0#0, #_module.com.SKIP()) && _module.com#Equal(c'#0, c1#0))
        {
        }

        if (!(
          _module.com#Equal(c0#0, #_module.com.SKIP())
           && _module.com#Equal(c'#0, c1#0)
           && Map#Equal(s'#0, s#0)))
        {
            // Begin Comprehension WF check
            havoc c0'#0_0;
            if ($Is(c0'#0_0, Tclass._module.com()))
            {
                if (_module.com#Equal(c'#0, #_module.com.Seq(c0'#0_0, c1#0)))
                {
                    ##c#0_0 := c0#0;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c#0_0, Tclass._module.com(), $Heap);
                    ##s#0_0 := s#0;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s#0_0, TMap(TSeq(TChar), TInt), $Heap);
                    ##c'#0_0 := c0'#0_0;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c'#0_0, Tclass._module.com(), $Heap);
                    ##s'#0_0 := s'#0;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s'#0_0, TMap(TSeq(TChar), TInt), $Heap);
                    assume _module.__default.small__step#canCall(c0#0, s#0, c0'#0_0, s'#0);
                }
            }

            // End Comprehension WF check
        }

        assume $IsA#_module.com(c0#0)
           && (_module.com#Equal(c0#0, #_module.com.SKIP())
             ==> $IsA#_module.com(c'#0) && $IsA#_module.com(c1#0))
           && (!(
              _module.com#Equal(c0#0, #_module.com.SKIP())
               && _module.com#Equal(c'#0, c1#0)
               && Map#Equal(s'#0, s#0))
             ==> (forall c0'#0_1: DatatypeType :: 
              { _module.__default.small__step($LS($LZ), c0#0, s#0, c0'#0_1, s'#0) } 
                { #_module.com.Seq(c0'#0_1, c1#0) } 
              $Is(c0'#0_1, Tclass._module.com())
                 ==> $IsA#_module.com(c'#0)
                   && (_module.com#Equal(c'#0, #_module.com.Seq(c0'#0_1, c1#0))
                     ==> _module.__default.small__step#canCall(c0#0, s#0, c0'#0_1, s'#0))));
        assert (
            _module.com#Equal(c0#0, #_module.com.SKIP())
             && _module.com#Equal(c'#0, c1#0)
             && Map#Equal(s'#0, s#0))
           || (exists c0'#0_1: DatatypeType :: 
            { _module.__default.small__step($LS($LZ), c0#0, s#0, c0'#0_1, s'#0) } 
              { #_module.com.Seq(c0'#0_1, c1#0) } 
            $Is(c0'#0_1, Tclass._module.com())
               && 
              _module.com#Equal(c'#0, #_module.com.Seq(c0'#0_1, c1#0))
               && _module.__default.small__step($LS($LZ), c0#0, s#0, c0'#0_1, s'#0));
        // ----- alternative statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(179,5)
        if (*)
        {
            if (_module.com#Equal(c0#0, #_module.com.SKIP()))
            {
            }

            if (_module.com#Equal(c0#0, #_module.com.SKIP()) && _module.com#Equal(c'#0, c1#0))
            {
            }

            assume $IsA#_module.com(c0#0)
               && (_module.com#Equal(c0#0, #_module.com.SKIP())
                 ==> $IsA#_module.com(c'#0) && $IsA#_module.com(c1#0));
            assume _module.com#Equal(c0#0, #_module.com.SKIP())
               && _module.com#Equal(c'#0, c1#0)
               && Map#Equal(s'#0, s#0);
        }
        else if (*)
        {
            // Begin Comprehension WF check
            havoc c0'#0_0_0;
            if ($Is(c0'#0_0_0, Tclass._module.com()))
            {
                if (_module.com#Equal(c'#0, #_module.com.Seq(c0'#0_0_0, c1#0)))
                {
                    ##c#0_0_0 := c0#0;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c#0_0_0, Tclass._module.com(), $Heap);
                    ##s#0_0_0 := s#0;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s#0_0_0, TMap(TSeq(TChar), TInt), $Heap);
                    ##c'#0_0_0 := c0'#0_0_0;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c'#0_0_0, Tclass._module.com(), $Heap);
                    ##s'#0_0_0 := s'#0;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s'#0_0_0, TMap(TSeq(TChar), TInt), $Heap);
                    assume _module.__default.small__step#canCall(c0#0, s#0, c0'#0_0_0, s'#0);
                }
            }

            // End Comprehension WF check
            assume (forall c0'#0_2: DatatypeType :: 
              { _module.__default.small__step($LS($LZ), c0#0, s#0, c0'#0_2, s'#0) } 
                { #_module.com.Seq(c0'#0_2, c1#0) } 
              $Is(c0'#0_2, Tclass._module.com())
                 ==> $IsA#_module.com(c'#0)
                   && (_module.com#Equal(c'#0, #_module.com.Seq(c0'#0_2, c1#0))
                     ==> _module.__default.small__step#canCall(c0#0, s#0, c0'#0_2, s'#0)));
            assume (exists c0'#0_2: DatatypeType :: 
              { _module.__default.small__step($LS($LZ), c0#0, s#0, c0'#0_2, s'#0) } 
                { #_module.com.Seq(c0'#0_2, c1#0) } 
              $Is(c0'#0_2, Tclass._module.com())
                 && 
                _module.com#Equal(c'#0, #_module.com.Seq(c0'#0_2, c1#0))
                 && _module.__default.small__step($LS($LZ), c0#0, s#0, c0'#0_2, s'#0));
            // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(183,9)
            assume true;
            assert false;
        }
        else
        {
            assume $IsA#_module.com(c0#0)
               && (_module.com#Equal(c0#0, #_module.com.SKIP())
                 ==> $IsA#_module.com(c'#0) && $IsA#_module.com(c1#0));
            assume (forall c0'#0_2: DatatypeType :: 
              { _module.__default.small__step($LS($LZ), c0#0, s#0, c0'#0_2, s'#0) } 
                { #_module.com.Seq(c0'#0_2, c1#0) } 
              $Is(c0'#0_2, Tclass._module.com())
                 ==> $IsA#_module.com(c'#0)
                   && (_module.com#Equal(c'#0, #_module.com.Seq(c0'#0_2, c1#0))
                     ==> _module.__default.small__step#canCall(c0#0, s#0, c0'#0_2, s'#0)));
            assume !
              (
              _module.com#Equal(c0#0, #_module.com.SKIP())
               && _module.com#Equal(c'#0, c1#0)
               && Map#Equal(s'#0, s#0))
               && !(exists c0'#0_2: DatatypeType :: 
                { _module.__default.small__step($LS($LZ), c0#0, s#0, c0'#0_2, s'#0) } 
                  { #_module.com.Seq(c0'#0_2, c1#0) } 
                $Is(c0'#0_2, Tclass._module.com())
                   && 
                  _module.com#Equal(c'#0, #_module.com.Seq(c0'#0_2, c1#0))
                   && _module.__default.small__step($LS($LZ), c0#0, s#0, c0'#0_2, s'#0));
            assert false;
        }
    }
    else
    {
    }
}



procedure CheckWellformed$$_module.__default.SmallStep__is__deterministic(cs#0: DatatypeType
       where $Is(cs#0, Tclass._System.Tuple2(Tclass._module.com(), TMap(TSeq(TChar), TInt)))
         && $IsAlloc(cs#0, 
          Tclass._System.Tuple2(Tclass._module.com(), TMap(TSeq(TChar), TInt)), 
          $Heap)
         && $IsA#_System.Tuple2(cs#0), 
    cs'#0: DatatypeType
       where $Is(cs'#0, Tclass._System.Tuple2(Tclass._module.com(), TMap(TSeq(TChar), TInt)))
         && $IsAlloc(cs'#0, 
          Tclass._System.Tuple2(Tclass._module.com(), TMap(TSeq(TChar), TInt)), 
          $Heap)
         && $IsA#_System.Tuple2(cs'#0), 
    cs''#0: DatatypeType
       where $Is(cs''#0, Tclass._System.Tuple2(Tclass._module.com(), TMap(TSeq(TChar), TInt)))
         && $IsAlloc(cs''#0, 
          Tclass._System.Tuple2(Tclass._module.com(), TMap(TSeq(TChar), TInt)), 
          $Heap)
         && $IsA#_System.Tuple2(cs''#0));
  free requires 42 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.SmallStep__is__deterministic(cs#0: DatatypeType
       where $Is(cs#0, Tclass._System.Tuple2(Tclass._module.com(), TMap(TSeq(TChar), TInt)))
         && $IsAlloc(cs#0, 
          Tclass._System.Tuple2(Tclass._module.com(), TMap(TSeq(TChar), TInt)), 
          $Heap)
         && $IsA#_System.Tuple2(cs#0), 
    cs'#0: DatatypeType
       where $Is(cs'#0, Tclass._System.Tuple2(Tclass._module.com(), TMap(TSeq(TChar), TInt)))
         && $IsAlloc(cs'#0, 
          Tclass._System.Tuple2(Tclass._module.com(), TMap(TSeq(TChar), TInt)), 
          $Heap)
         && $IsA#_System.Tuple2(cs'#0), 
    cs''#0: DatatypeType
       where $Is(cs''#0, Tclass._System.Tuple2(Tclass._module.com(), TMap(TSeq(TChar), TInt)))
         && $IsAlloc(cs''#0, 
          Tclass._System.Tuple2(Tclass._module.com(), TMap(TSeq(TChar), TInt)), 
          $Heap)
         && $IsA#_System.Tuple2(cs''#0));
  // user-defined preconditions
  requires _module.__default.small__step($LS($LS($LZ)), 
    $Unbox(_System.Tuple2._0(cs#0)): DatatypeType, 
    $Unbox(_System.Tuple2._1(cs#0)): Map Box Box, 
    $Unbox(_System.Tuple2._0(cs'#0)): DatatypeType, 
    $Unbox(_System.Tuple2._1(cs'#0)): Map Box Box);
  requires _module.__default.small__step($LS($LS($LZ)), 
    $Unbox(_System.Tuple2._0(cs#0)): DatatypeType, 
    $Unbox(_System.Tuple2._1(cs#0)): Map Box Box, 
    $Unbox(_System.Tuple2._0(cs''#0)): DatatypeType, 
    $Unbox(_System.Tuple2._1(cs''#0)): Map Box Box);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_System.Tuple2(cs'#0) && $IsA#_System.Tuple2(cs''#0);
  ensures _System.Tuple2#Equal(cs'#0, cs''#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.SmallStep__is__deterministic(cs#0: DatatypeType
       where $Is(cs#0, Tclass._System.Tuple2(Tclass._module.com(), TMap(TSeq(TChar), TInt)))
         && $IsAlloc(cs#0, 
          Tclass._System.Tuple2(Tclass._module.com(), TMap(TSeq(TChar), TInt)), 
          $Heap)
         && $IsA#_System.Tuple2(cs#0), 
    cs'#0: DatatypeType
       where $Is(cs'#0, Tclass._System.Tuple2(Tclass._module.com(), TMap(TSeq(TChar), TInt)))
         && $IsAlloc(cs'#0, 
          Tclass._System.Tuple2(Tclass._module.com(), TMap(TSeq(TChar), TInt)), 
          $Heap)
         && $IsA#_System.Tuple2(cs'#0), 
    cs''#0: DatatypeType
       where $Is(cs''#0, Tclass._System.Tuple2(Tclass._module.com(), TMap(TSeq(TChar), TInt)))
         && $IsAlloc(cs''#0, 
          Tclass._System.Tuple2(Tclass._module.com(), TMap(TSeq(TChar), TInt)), 
          $Heap)
         && $IsA#_System.Tuple2(cs''#0))
   returns ($_reverifyPost: bool);
  free requires 42 == $FunctionContextHeight;
  // user-defined preconditions
  requires _module.__default.small__step($LS($LS($LZ)), 
    $Unbox(_System.Tuple2._0(cs#0)): DatatypeType, 
    $Unbox(_System.Tuple2._1(cs#0)): Map Box Box, 
    $Unbox(_System.Tuple2._0(cs'#0)): DatatypeType, 
    $Unbox(_System.Tuple2._1(cs'#0)): Map Box Box);
  requires _module.__default.small__step($LS($LS($LZ)), 
    $Unbox(_System.Tuple2._0(cs#0)): DatatypeType, 
    $Unbox(_System.Tuple2._1(cs#0)): Map Box Box, 
    $Unbox(_System.Tuple2._0(cs''#0)): DatatypeType, 
    $Unbox(_System.Tuple2._1(cs''#0)): Map Box Box);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_System.Tuple2(cs'#0) && $IsA#_System.Tuple2(cs''#0);
  ensures _System.Tuple2#Equal(cs'#0, cs''#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.SmallStep__is__deterministic(cs#0: DatatypeType, cs'#0: DatatypeType, cs''#0: DatatypeType)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var k#0: Box;
  var k#1: Box;
  var ##_k#0: Box;
  var ##c#2: DatatypeType;
  var ##s#2: Map Box Box;
  var ##c'#2: DatatypeType;
  var ##s'#2: Map Box Box;
  var k'#0: Box;
  var k'#1: Box;
  var ##_k#1: Box;
  var ##c#3: DatatypeType;
  var ##s#3: Map Box Box;
  var ##c'#3: DatatypeType;
  var ##s'#3: Map Box Box;
  var k##0: Box;
  var k'##0: Box;
  var cs##0: DatatypeType;
  var cs'##0: DatatypeType;
  var cs''##0: DatatypeType;

    // AddMethodImpl: SmallStep_is_deterministic, Impl$$_module.__default.SmallStep__is__deterministic
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(192,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(193,9)
    havoc k#1;
    if (true)
    {
        assume _System.Tuple2.___hMake2_q(cs#0);
        assume _System.Tuple2.___hMake2_q(cs#0);
        assume _System.Tuple2.___hMake2_q(cs'#0);
        assume _System.Tuple2.___hMake2_q(cs'#0);
        ##_k#0 := k#1;
        // assume allocatedness for argument to function
        assume $IsAlloc(##_k#0, TORDINAL, $Heap);
        ##c#2 := $Unbox(_System.Tuple2._0(cs#0)): DatatypeType;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#2, Tclass._module.com(), $Heap);
        ##s#2 := $Unbox(_System.Tuple2._1(cs#0)): Map Box Box;
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#2, TMap(TSeq(TChar), TInt), $Heap);
        ##c'#2 := $Unbox(_System.Tuple2._0(cs'#0)): DatatypeType;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c'#2, Tclass._module.com(), $Heap);
        ##s'#2 := $Unbox(_System.Tuple2._1(cs'#0)): Map Box Box;
        // assume allocatedness for argument to function
        assume $IsAlloc(##s'#2, TMap(TSeq(TChar), TInt), $Heap);
        assume _module.__default.small__step_h#canCall(k#1, 
          $Unbox(_System.Tuple2._0(cs#0)): DatatypeType, 
          $Unbox(_System.Tuple2._1(cs#0)): Map Box Box, 
          $Unbox(_System.Tuple2._0(cs'#0)): DatatypeType, 
          $Unbox(_System.Tuple2._1(cs'#0)): Map Box Box);
        assume _System.Tuple2.___hMake2_q(cs#0)
           && _System.Tuple2.___hMake2_q(cs#0)
           && _System.Tuple2.___hMake2_q(cs'#0)
           && _System.Tuple2.___hMake2_q(cs'#0)
           && _module.__default.small__step_h#canCall(k#1, 
            $Unbox(_System.Tuple2._0(cs#0)): DatatypeType, 
            $Unbox(_System.Tuple2._1(cs#0)): Map Box Box, 
            $Unbox(_System.Tuple2._0(cs'#0)): DatatypeType, 
            $Unbox(_System.Tuple2._1(cs'#0)): Map Box Box);
    }

    assert (exists $as#k0#0: Box :: 
      _module.__default.small__step_h($LS($LZ), 
        $as#k0#0, 
        $Unbox(_System.Tuple2._0(cs#0)): DatatypeType, 
        $Unbox(_System.Tuple2._1(cs#0)): Map Box Box, 
        $Unbox(_System.Tuple2._0(cs'#0)): DatatypeType, 
        $Unbox(_System.Tuple2._1(cs'#0)): Map Box Box));
    havoc k#0;
    assume _module.__default.small__step_h($LS($LZ), 
      k#0, 
      $Unbox(_System.Tuple2._0(cs#0)): DatatypeType, 
      $Unbox(_System.Tuple2._1(cs#0)): Map Box Box, 
      $Unbox(_System.Tuple2._0(cs'#0)): DatatypeType, 
      $Unbox(_System.Tuple2._1(cs'#0)): Map Box Box);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(193,51)"} true;
    // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(194,10)
    havoc k'#1;
    if (true)
    {
        assume _System.Tuple2.___hMake2_q(cs#0);
        assume _System.Tuple2.___hMake2_q(cs#0);
        assume _System.Tuple2.___hMake2_q(cs''#0);
        assume _System.Tuple2.___hMake2_q(cs''#0);
        ##_k#1 := k'#1;
        // assume allocatedness for argument to function
        assume $IsAlloc(##_k#1, TORDINAL, $Heap);
        ##c#3 := $Unbox(_System.Tuple2._0(cs#0)): DatatypeType;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#3, Tclass._module.com(), $Heap);
        ##s#3 := $Unbox(_System.Tuple2._1(cs#0)): Map Box Box;
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#3, TMap(TSeq(TChar), TInt), $Heap);
        ##c'#3 := $Unbox(_System.Tuple2._0(cs''#0)): DatatypeType;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c'#3, Tclass._module.com(), $Heap);
        ##s'#3 := $Unbox(_System.Tuple2._1(cs''#0)): Map Box Box;
        // assume allocatedness for argument to function
        assume $IsAlloc(##s'#3, TMap(TSeq(TChar), TInt), $Heap);
        assume _module.__default.small__step_h#canCall(k'#1, 
          $Unbox(_System.Tuple2._0(cs#0)): DatatypeType, 
          $Unbox(_System.Tuple2._1(cs#0)): Map Box Box, 
          $Unbox(_System.Tuple2._0(cs''#0)): DatatypeType, 
          $Unbox(_System.Tuple2._1(cs''#0)): Map Box Box);
        assume _System.Tuple2.___hMake2_q(cs#0)
           && _System.Tuple2.___hMake2_q(cs#0)
           && _System.Tuple2.___hMake2_q(cs''#0)
           && _System.Tuple2.___hMake2_q(cs''#0)
           && _module.__default.small__step_h#canCall(k'#1, 
            $Unbox(_System.Tuple2._0(cs#0)): DatatypeType, 
            $Unbox(_System.Tuple2._1(cs#0)): Map Box Box, 
            $Unbox(_System.Tuple2._0(cs''#0)): DatatypeType, 
            $Unbox(_System.Tuple2._1(cs''#0)): Map Box Box);
    }

    assert (exists $as#k'0#0: Box :: 
      _module.__default.small__step_h($LS($LZ), 
        $as#k'0#0, 
        $Unbox(_System.Tuple2._0(cs#0)): DatatypeType, 
        $Unbox(_System.Tuple2._1(cs#0)): Map Box Box, 
        $Unbox(_System.Tuple2._0(cs''#0)): DatatypeType, 
        $Unbox(_System.Tuple2._1(cs''#0)): Map Box Box));
    havoc k'#0;
    assume _module.__default.small__step_h($LS($LZ), 
      k'#0, 
      $Unbox(_System.Tuple2._0(cs#0)): DatatypeType, 
      $Unbox(_System.Tuple2._1(cs#0)): Map Box Box, 
      $Unbox(_System.Tuple2._0(cs''#0)): DatatypeType, 
      $Unbox(_System.Tuple2._1(cs''#0)): Map Box Box);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(194,55)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(195,33)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    k##0 := k#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    k'##0 := k'#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    cs##0 := cs#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    cs'##0 := cs'#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    cs''##0 := cs''#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.SmallStep__is__deterministic__Aux(k##0, k'##0, cs##0, cs'##0, cs''##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(195,54)"} true;
}



procedure {:_induction k#0, k'#0} CheckWellformed$$_module.__default.SmallStep__is__deterministic__Aux(k#0: Box, 
    k'#0: Box, 
    cs#0: DatatypeType
       where $Is(cs#0, Tclass._System.Tuple2(Tclass._module.com(), TMap(TSeq(TChar), TInt)))
         && $IsAlloc(cs#0, 
          Tclass._System.Tuple2(Tclass._module.com(), TMap(TSeq(TChar), TInt)), 
          $Heap)
         && $IsA#_System.Tuple2(cs#0), 
    cs'#0: DatatypeType
       where $Is(cs'#0, Tclass._System.Tuple2(Tclass._module.com(), TMap(TSeq(TChar), TInt)))
         && $IsAlloc(cs'#0, 
          Tclass._System.Tuple2(Tclass._module.com(), TMap(TSeq(TChar), TInt)), 
          $Heap)
         && $IsA#_System.Tuple2(cs'#0), 
    cs''#0: DatatypeType
       where $Is(cs''#0, Tclass._System.Tuple2(Tclass._module.com(), TMap(TSeq(TChar), TInt)))
         && $IsAlloc(cs''#0, 
          Tclass._System.Tuple2(Tclass._module.com(), TMap(TSeq(TChar), TInt)), 
          $Heap)
         && $IsA#_System.Tuple2(cs''#0));
  free requires 41 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction k#0, k'#0} Call$$_module.__default.SmallStep__is__deterministic__Aux(k#0: Box, 
    k'#0: Box, 
    cs#0: DatatypeType
       where $Is(cs#0, Tclass._System.Tuple2(Tclass._module.com(), TMap(TSeq(TChar), TInt)))
         && $IsAlloc(cs#0, 
          Tclass._System.Tuple2(Tclass._module.com(), TMap(TSeq(TChar), TInt)), 
          $Heap)
         && $IsA#_System.Tuple2(cs#0), 
    cs'#0: DatatypeType
       where $Is(cs'#0, Tclass._System.Tuple2(Tclass._module.com(), TMap(TSeq(TChar), TInt)))
         && $IsAlloc(cs'#0, 
          Tclass._System.Tuple2(Tclass._module.com(), TMap(TSeq(TChar), TInt)), 
          $Heap)
         && $IsA#_System.Tuple2(cs'#0), 
    cs''#0: DatatypeType
       where $Is(cs''#0, Tclass._System.Tuple2(Tclass._module.com(), TMap(TSeq(TChar), TInt)))
         && $IsAlloc(cs''#0, 
          Tclass._System.Tuple2(Tclass._module.com(), TMap(TSeq(TChar), TInt)), 
          $Heap)
         && $IsA#_System.Tuple2(cs''#0));
  // user-defined preconditions
  requires _module.__default.small__step_h($LS($LS($LZ)), 
    k#0, 
    $Unbox(_System.Tuple2._0(cs#0)): DatatypeType, 
    $Unbox(_System.Tuple2._1(cs#0)): Map Box Box, 
    $Unbox(_System.Tuple2._0(cs'#0)): DatatypeType, 
    $Unbox(_System.Tuple2._1(cs'#0)): Map Box Box);
  requires _module.__default.small__step_h($LS($LS($LZ)), 
    k'#0, 
    $Unbox(_System.Tuple2._0(cs#0)): DatatypeType, 
    $Unbox(_System.Tuple2._1(cs#0)): Map Box Box, 
    $Unbox(_System.Tuple2._0(cs''#0)): DatatypeType, 
    $Unbox(_System.Tuple2._1(cs''#0)): Map Box Box);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_System.Tuple2(cs'#0) && $IsA#_System.Tuple2(cs''#0);
  ensures _System.Tuple2#Equal(cs'#0, cs''#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction k#0, k'#0} Impl$$_module.__default.SmallStep__is__deterministic__Aux(k#0: Box, 
    k'#0: Box, 
    cs#0: DatatypeType
       where $Is(cs#0, Tclass._System.Tuple2(Tclass._module.com(), TMap(TSeq(TChar), TInt)))
         && $IsAlloc(cs#0, 
          Tclass._System.Tuple2(Tclass._module.com(), TMap(TSeq(TChar), TInt)), 
          $Heap)
         && $IsA#_System.Tuple2(cs#0), 
    cs'#0: DatatypeType
       where $Is(cs'#0, Tclass._System.Tuple2(Tclass._module.com(), TMap(TSeq(TChar), TInt)))
         && $IsAlloc(cs'#0, 
          Tclass._System.Tuple2(Tclass._module.com(), TMap(TSeq(TChar), TInt)), 
          $Heap)
         && $IsA#_System.Tuple2(cs'#0), 
    cs''#0: DatatypeType
       where $Is(cs''#0, Tclass._System.Tuple2(Tclass._module.com(), TMap(TSeq(TChar), TInt)))
         && $IsAlloc(cs''#0, 
          Tclass._System.Tuple2(Tclass._module.com(), TMap(TSeq(TChar), TInt)), 
          $Heap)
         && $IsA#_System.Tuple2(cs''#0))
   returns ($_reverifyPost: bool);
  free requires 41 == $FunctionContextHeight;
  // user-defined preconditions
  requires _module.__default.small__step_h($LS($LS($LZ)), 
    k#0, 
    $Unbox(_System.Tuple2._0(cs#0)): DatatypeType, 
    $Unbox(_System.Tuple2._1(cs#0)): Map Box Box, 
    $Unbox(_System.Tuple2._0(cs'#0)): DatatypeType, 
    $Unbox(_System.Tuple2._1(cs'#0)): Map Box Box);
  requires _module.__default.small__step_h($LS($LS($LZ)), 
    k'#0, 
    $Unbox(_System.Tuple2._0(cs#0)): DatatypeType, 
    $Unbox(_System.Tuple2._1(cs#0)): Map Box Box, 
    $Unbox(_System.Tuple2._0(cs''#0)): DatatypeType, 
    $Unbox(_System.Tuple2._1(cs''#0)): Map Box Box);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_System.Tuple2(cs'#0) && $IsA#_System.Tuple2(cs''#0);
  ensures _System.Tuple2#Equal(cs'#0, cs''#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction k#0, k'#0} Impl$$_module.__default.SmallStep__is__deterministic__Aux(k#0: Box, 
    k'#0: Box, 
    cs#0: DatatypeType, 
    cs'#0: DatatypeType, 
    cs''#0: DatatypeType)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var m#0_0: Box;
  var m#0_1: Box;
  var ##_k#0_0: Box;
  var ##c#0_0: DatatypeType;
  var ##s#0_0: Map Box Box;
  var ##c'#0_0: DatatypeType;
  var ##s'#0_0: Map Box Box;
  var k##0_0: Box;
  var k'##0_0: Box;
  var cs##0_0: DatatypeType;
  var cs'##0_0: DatatypeType;
  var cs''##0_0: DatatypeType;
  var m#1_0: Box;
  var m#1_1: Box;
  var ##_k#1_0: Box;
  var ##c#1_0: DatatypeType;
  var ##s#1_0: Map Box Box;
  var ##c'#1_0: DatatypeType;
  var ##s'#1_0: Map Box Box;
  var k##1_0: Box;
  var k'##1_0: Box;
  var cs##1_0: DatatypeType;
  var cs'##1_0: DatatypeType;
  var cs''##1_0: DatatypeType;
  var _mcc#7#2_0: DatatypeType;
  var _mcc#8#2_0: DatatypeType;
  var body#2_0: DatatypeType;
  var let#2_0#0#0: DatatypeType;
  var b#2_0: DatatypeType;
  var let#2_1#0#0: DatatypeType;
  var _mcc#4#3_0: DatatypeType;
  var _mcc#5#3_0: DatatypeType;
  var _mcc#6#3_0: DatatypeType;
  var els#3_0: DatatypeType;
  var let#3_0#0#0: DatatypeType;
  var thn#3_0: DatatypeType;
  var let#3_1#0#0: DatatypeType;
  var b#3_0: DatatypeType;
  var let#3_2#0#0: DatatypeType;
  var _mcc#2#4_0: DatatypeType;
  var _mcc#3#4_0: DatatypeType;
  var c1#4_0: DatatypeType;
  var let#4_0#0#0: DatatypeType;
  var c0#4_0: DatatypeType;
  var let#4_1#0#0: DatatypeType;
  var k##4_0: Box;
  var c0##4_0: DatatypeType;
  var c1##4_0: DatatypeType;
  var s##4_0: Map Box Box;
  var c'##4_0: DatatypeType;
  var s'##4_0: Map Box Box;
  var k##4_1: Box;
  var c0##4_1: DatatypeType;
  var c1##4_1: DatatypeType;
  var s##4_1: Map Box Box;
  var c'##4_1: DatatypeType;
  var s'##4_1: Map Box Box;
  var c0'#4_0: DatatypeType
     where $Is(c0'#4_0, Tclass._module.com())
       && $IsAlloc(c0'#4_0, Tclass._module.com(), $Heap);
  var c0'#4_1: DatatypeType;
  var ##_k#4_0: Box;
  var ##c#4_0: DatatypeType;
  var ##s#4_0: Map Box Box;
  var ##c'#4_0: DatatypeType;
  var ##s'#4_0: Map Box Box;
  var c0''#4_0: DatatypeType
     where $Is(c0''#4_0, Tclass._module.com())
       && $IsAlloc(c0''#4_0, Tclass._module.com(), $Heap);
  var c0''#4_1: DatatypeType;
  var ##_k#4_1: Box;
  var ##c#4_1: DatatypeType;
  var ##s#4_1: Map Box Box;
  var ##c'#4_1: DatatypeType;
  var ##s'#4_1: Map Box Box;
  var k##4_2: Box;
  var k'##4_0: Box;
  var cs##4_0: DatatypeType;
  var cs'##4_0: DatatypeType;
  var cs''##4_0: DatatypeType;
  var _mcc#0#5_0: Seq Box;
  var _mcc#1#5_0: DatatypeType;
  var a#5_0: DatatypeType;
  var let#5_0#0#0: DatatypeType;
  var x#5_0: Seq Box;
  var let#5_1#0#0: Seq Box;

    // AddMethodImpl: SmallStep_is_deterministic_Aux, Impl$$_module.__default.SmallStep__is__deterministic__Aux
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(202,0): initial state"} true;
    assume $IsA#_System.Tuple2(cs#0);
    assume $IsA#_System.Tuple2(cs'#0);
    assume $IsA#_System.Tuple2(cs''#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#k0#0: Box, $ih#k'0#0: Box :: 
      _module.__default.small__step_h($LS($LZ), 
            $ih#k0#0, 
            $Unbox(_System.Tuple2._0(cs#0)): DatatypeType, 
            $Unbox(_System.Tuple2._1(cs#0)): Map Box Box, 
            $Unbox(_System.Tuple2._0(cs'#0)): DatatypeType, 
            $Unbox(_System.Tuple2._1(cs'#0)): Map Box Box)
           && _module.__default.small__step_h($LS($LZ), 
            $ih#k'0#0, 
            $Unbox(_System.Tuple2._0(cs#0)): DatatypeType, 
            $Unbox(_System.Tuple2._1(cs#0)): Map Box Box, 
            $Unbox(_System.Tuple2._0(cs''#0)): DatatypeType, 
            $Unbox(_System.Tuple2._1(cs''#0)): Map Box Box)
           && (ORD#Less($ih#k0#0, k#0)
             || ($ih#k0#0 == k#0
               && (ORD#Less($ih#k'0#0, k'#0)
                 || ($ih#k'0#0 == k'#0
                   && (DtRank(cs#0) < DtRank(cs#0)
                     || (DtRank(cs#0) == DtRank(cs#0)
                       && (DtRank(cs'#0) < DtRank(cs'#0)
                         || (DtRank(cs'#0) == DtRank(cs'#0) && DtRank(cs''#0) < DtRank(cs''#0)))))))))
         ==> _System.Tuple2#Equal(cs'#0, cs''#0));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(203,3)
    assume true;
    if (ORD#IsLimit(k#0))
    {
        // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(204,11)
        havoc m#0_1;
        if (true)
        {
            if (ORD#Less(m#0_1, k#0))
            {
                assume _System.Tuple2.___hMake2_q(cs#0);
                assume _System.Tuple2.___hMake2_q(cs#0);
                assume _System.Tuple2.___hMake2_q(cs'#0);
                assume _System.Tuple2.___hMake2_q(cs'#0);
                ##_k#0_0 := m#0_1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##_k#0_0, TORDINAL, $Heap);
                ##c#0_0 := $Unbox(_System.Tuple2._0(cs#0)): DatatypeType;
                // assume allocatedness for argument to function
                assume $IsAlloc(##c#0_0, Tclass._module.com(), $Heap);
                ##s#0_0 := $Unbox(_System.Tuple2._1(cs#0)): Map Box Box;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#0_0, TMap(TSeq(TChar), TInt), $Heap);
                ##c'#0_0 := $Unbox(_System.Tuple2._0(cs'#0)): DatatypeType;
                // assume allocatedness for argument to function
                assume $IsAlloc(##c'#0_0, Tclass._module.com(), $Heap);
                ##s'#0_0 := $Unbox(_System.Tuple2._1(cs'#0)): Map Box Box;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s'#0_0, TMap(TSeq(TChar), TInt), $Heap);
                assume _module.__default.small__step_h#canCall(m#0_1, 
                  $Unbox(_System.Tuple2._0(cs#0)): DatatypeType, 
                  $Unbox(_System.Tuple2._1(cs#0)): Map Box Box, 
                  $Unbox(_System.Tuple2._0(cs'#0)): DatatypeType, 
                  $Unbox(_System.Tuple2._1(cs'#0)): Map Box Box);
            }

            assume ORD#Less(m#0_1, k#0)
               ==> _System.Tuple2.___hMake2_q(cs#0)
                 && _System.Tuple2.___hMake2_q(cs#0)
                 && _System.Tuple2.___hMake2_q(cs'#0)
                 && _System.Tuple2.___hMake2_q(cs'#0)
                 && _module.__default.small__step_h#canCall(m#0_1, 
                  $Unbox(_System.Tuple2._0(cs#0)): DatatypeType, 
                  $Unbox(_System.Tuple2._1(cs#0)): Map Box Box, 
                  $Unbox(_System.Tuple2._0(cs'#0)): DatatypeType, 
                  $Unbox(_System.Tuple2._1(cs'#0)): Map Box Box);
        }

        assert (exists $as#m0_0#0_0: Box :: 
          ORD#Less($as#m0_0#0_0, k#0)
             && _module.__default.small__step_h($LS($LZ), 
              $as#m0_0#0_0, 
              $Unbox(_System.Tuple2._0(cs#0)): DatatypeType, 
              $Unbox(_System.Tuple2._1(cs#0)): Map Box Box, 
              $Unbox(_System.Tuple2._0(cs'#0)): DatatypeType, 
              $Unbox(_System.Tuple2._1(cs'#0)): Map Box Box));
        havoc m#0_0;
        assume ORD#Less(m#0_0, k#0)
           && _module.__default.small__step_h($LS($LZ), 
            m#0_0, 
            $Unbox(_System.Tuple2._0(cs#0)): DatatypeType, 
            $Unbox(_System.Tuple2._1(cs#0)): Map Box Box, 
            $Unbox(_System.Tuple2._0(cs'#0)): DatatypeType, 
            $Unbox(_System.Tuple2._1(cs'#0)): Map Box Box);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(204,62)"} true;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(205,35)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        k##0_0 := m#0_0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        k'##0_0 := k'#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        cs##0_0 := cs#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        cs'##0_0 := cs'#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        cs''##0_0 := cs''#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assert ORD#Less(k##0_0, k#0)
           || (k##0_0 == k#0
             && (ORD#Less(k'##0_0, k'#0)
               || (k'##0_0 == k'#0
                 && (DtRank(cs##0_0) < DtRank(cs#0)
                   || (DtRank(cs##0_0) == DtRank(cs#0)
                     && (DtRank(cs'##0_0) < DtRank(cs'#0)
                       || (DtRank(cs'##0_0) == DtRank(cs'#0) && DtRank(cs''##0_0) < DtRank(cs''#0))))))));
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.SmallStep__is__deterministic__Aux(k##0_0, k'##0_0, cs##0_0, cs'##0_0, cs''##0_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(205,56)"} true;
    }
    else
    {
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(206,10)
        assume true;
        if (ORD#IsLimit(k'#0))
        {
            // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(207,11)
            havoc m#1_1;
            if (true)
            {
                if (ORD#Less(m#1_1, k'#0))
                {
                    assume _System.Tuple2.___hMake2_q(cs#0);
                    assume _System.Tuple2.___hMake2_q(cs#0);
                    assume _System.Tuple2.___hMake2_q(cs''#0);
                    assume _System.Tuple2.___hMake2_q(cs''#0);
                    ##_k#1_0 := m#1_1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##_k#1_0, TORDINAL, $Heap);
                    ##c#1_0 := $Unbox(_System.Tuple2._0(cs#0)): DatatypeType;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c#1_0, Tclass._module.com(), $Heap);
                    ##s#1_0 := $Unbox(_System.Tuple2._1(cs#0)): Map Box Box;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s#1_0, TMap(TSeq(TChar), TInt), $Heap);
                    ##c'#1_0 := $Unbox(_System.Tuple2._0(cs''#0)): DatatypeType;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c'#1_0, Tclass._module.com(), $Heap);
                    ##s'#1_0 := $Unbox(_System.Tuple2._1(cs''#0)): Map Box Box;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s'#1_0, TMap(TSeq(TChar), TInt), $Heap);
                    assume _module.__default.small__step_h#canCall(m#1_1, 
                      $Unbox(_System.Tuple2._0(cs#0)): DatatypeType, 
                      $Unbox(_System.Tuple2._1(cs#0)): Map Box Box, 
                      $Unbox(_System.Tuple2._0(cs''#0)): DatatypeType, 
                      $Unbox(_System.Tuple2._1(cs''#0)): Map Box Box);
                }

                assume ORD#Less(m#1_1, k'#0)
                   ==> _System.Tuple2.___hMake2_q(cs#0)
                     && _System.Tuple2.___hMake2_q(cs#0)
                     && _System.Tuple2.___hMake2_q(cs''#0)
                     && _System.Tuple2.___hMake2_q(cs''#0)
                     && _module.__default.small__step_h#canCall(m#1_1, 
                      $Unbox(_System.Tuple2._0(cs#0)): DatatypeType, 
                      $Unbox(_System.Tuple2._1(cs#0)): Map Box Box, 
                      $Unbox(_System.Tuple2._0(cs''#0)): DatatypeType, 
                      $Unbox(_System.Tuple2._1(cs''#0)): Map Box Box);
            }

            assert (exists $as#m1_0#1_0: Box :: 
              ORD#Less($as#m1_0#1_0, k'#0)
                 && _module.__default.small__step_h($LS($LZ), 
                  $as#m1_0#1_0, 
                  $Unbox(_System.Tuple2._0(cs#0)): DatatypeType, 
                  $Unbox(_System.Tuple2._1(cs#0)): Map Box Box, 
                  $Unbox(_System.Tuple2._0(cs''#0)): DatatypeType, 
                  $Unbox(_System.Tuple2._1(cs''#0)): Map Box Box));
            havoc m#1_0;
            assume ORD#Less(m#1_0, k'#0)
               && _module.__default.small__step_h($LS($LZ), 
                m#1_0, 
                $Unbox(_System.Tuple2._0(cs#0)): DatatypeType, 
                $Unbox(_System.Tuple2._1(cs#0)): Map Box Box, 
                $Unbox(_System.Tuple2._0(cs''#0)): DatatypeType, 
                $Unbox(_System.Tuple2._1(cs''#0)): Map Box Box);
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(207,65)"} true;
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(208,35)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            k##1_0 := k#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            k'##1_0 := m#1_0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            cs##1_0 := cs#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            cs'##1_0 := cs'#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            cs''##1_0 := cs''#0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert ORD#Less(k##1_0, k#0)
               || (k##1_0 == k#0
                 && (ORD#Less(k'##1_0, k'#0)
                   || (k'##1_0 == k'#0
                     && (DtRank(cs##1_0) < DtRank(cs#0)
                       || (DtRank(cs##1_0) == DtRank(cs#0)
                         && (DtRank(cs'##1_0) < DtRank(cs'#0)
                           || (DtRank(cs'##1_0) == DtRank(cs'#0) && DtRank(cs''##1_0) < DtRank(cs''#0))))))));
            // ProcessCallStmt: Make the call
            call Call$$_module.__default.SmallStep__is__deterministic__Aux(k##1_0, k'##1_0, cs##1_0, cs'##1_0, cs''##1_0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(208,55)"} true;
        }
        else
        {
            assume _System.Tuple2.___hMake2_q(cs#0);
            assume _System.Tuple2.___hMake2_q(cs#0);
            havoc _mcc#7#2_0, _mcc#8#2_0;
            havoc _mcc#4#3_0, _mcc#5#3_0, _mcc#6#3_0;
            havoc _mcc#2#4_0, _mcc#3#4_0;
            havoc _mcc#0#5_0, _mcc#1#5_0;
            if ($Unbox(_System.Tuple2._0(cs#0)): DatatypeType
               == #_module.com.Assign(_mcc#0#5_0, _mcc#1#5_0))
            {
                assume $Is(_mcc#0#5_0, TSeq(TChar));
                assume $Is(_mcc#1#5_0, Tclass._module.aexp());
                havoc a#5_0;
                assume $Is(a#5_0, Tclass._module.aexp())
                   && $IsAlloc(a#5_0, Tclass._module.aexp(), $Heap);
                assume let#5_0#0#0 == _mcc#1#5_0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(let#5_0#0#0, Tclass._module.aexp());
                assume a#5_0 == let#5_0#0#0;
                havoc x#5_0;
                assume $Is(x#5_0, TSeq(TChar)) && $IsAlloc(x#5_0, TSeq(TChar), $Heap);
                assume let#5_1#0#0 == _mcc#0#5_0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(let#5_1#0#0, TSeq(TChar));
                assume x#5_0 == let#5_1#0#0;
            }
            else if ($Unbox(_System.Tuple2._0(cs#0)): DatatypeType
               == #_module.com.Seq(_mcc#2#4_0, _mcc#3#4_0))
            {
                assume $Is(_mcc#2#4_0, Tclass._module.com());
                assume $Is(_mcc#3#4_0, Tclass._module.com());
                havoc c1#4_0;
                assume $Is(c1#4_0, Tclass._module.com())
                   && $IsAlloc(c1#4_0, Tclass._module.com(), $Heap);
                assume let#4_0#0#0 == _mcc#3#4_0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(let#4_0#0#0, Tclass._module.com());
                assume c1#4_0 == let#4_0#0#0;
                havoc c0#4_0;
                assume $Is(c0#4_0, Tclass._module.com())
                   && $IsAlloc(c0#4_0, Tclass._module.com(), $Heap);
                assume let#4_1#0#0 == _mcc#2#4_0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(let#4_1#0#0, Tclass._module.com());
                assume c0#4_0 == let#4_1#0#0;
                // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(213,27)
                // TrCallStmt: Before ProcessCallStmt
                assume true;
                // ProcessCallStmt: CheckSubrange
                k##4_0 := k#0;
                assume true;
                // ProcessCallStmt: CheckSubrange
                c0##4_0 := c0#4_0;
                assume true;
                // ProcessCallStmt: CheckSubrange
                c1##4_0 := c1#4_0;
                assume _System.Tuple2.___hMake2_q(cs#0);
                assume _System.Tuple2.___hMake2_q(cs#0);
                // ProcessCallStmt: CheckSubrange
                s##4_0 := $Unbox(_System.Tuple2._1(cs#0)): Map Box Box;
                assume _System.Tuple2.___hMake2_q(cs'#0);
                assume _System.Tuple2.___hMake2_q(cs'#0);
                // ProcessCallStmt: CheckSubrange
                c'##4_0 := $Unbox(_System.Tuple2._0(cs'#0)): DatatypeType;
                assume _System.Tuple2.___hMake2_q(cs'#0);
                assume _System.Tuple2.___hMake2_q(cs'#0);
                // ProcessCallStmt: CheckSubrange
                s'##4_0 := $Unbox(_System.Tuple2._1(cs'#0)): Map Box Box;
                assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                // ProcessCallStmt: Make the call
                call Call$$_module.__default.SeqCasesAreExclusive(k##4_0, c0##4_0, c1##4_0, s##4_0, c'##4_0, s'##4_0);
                // TrCallStmt: After ProcessCallStmt
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(213,57)"} true;
                // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(214,27)
                // TrCallStmt: Before ProcessCallStmt
                assume true;
                // ProcessCallStmt: CheckSubrange
                k##4_1 := k'#0;
                assume true;
                // ProcessCallStmt: CheckSubrange
                c0##4_1 := c0#4_0;
                assume true;
                // ProcessCallStmt: CheckSubrange
                c1##4_1 := c1#4_0;
                assume _System.Tuple2.___hMake2_q(cs#0);
                assume _System.Tuple2.___hMake2_q(cs#0);
                // ProcessCallStmt: CheckSubrange
                s##4_1 := $Unbox(_System.Tuple2._1(cs#0)): Map Box Box;
                assume _System.Tuple2.___hMake2_q(cs''#0);
                assume _System.Tuple2.___hMake2_q(cs''#0);
                // ProcessCallStmt: CheckSubrange
                c'##4_1 := $Unbox(_System.Tuple2._0(cs''#0)): DatatypeType;
                assume _System.Tuple2.___hMake2_q(cs''#0);
                assume _System.Tuple2.___hMake2_q(cs''#0);
                // ProcessCallStmt: CheckSubrange
                s'##4_1 := $Unbox(_System.Tuple2._1(cs''#0)): Map Box Box;
                assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                // ProcessCallStmt: Make the call
                call Call$$_module.__default.SeqCasesAreExclusive(k##4_1, c0##4_1, c1##4_1, s##4_1, c'##4_1, s'##4_1);
                // TrCallStmt: After ProcessCallStmt
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(214,60)"} true;
                // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(215,7)
                assume $IsA#_module.com(c0#4_0);
                if (_module.com#Equal(c0#4_0, #_module.com.SKIP()))
                {
                }
                else
                {
                    // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(217,17)
                    havoc c0'#4_1;
                    if ($Is(c0'#4_1, Tclass._module.com())
                       && $IsAlloc(c0'#4_1, Tclass._module.com(), $Heap))
                    {
                        assume _System.Tuple2.___hMake2_q(cs'#0);
                        if (_module.com#Equal($Unbox(_System.Tuple2._0(cs'#0)): DatatypeType, 
                          #_module.com.Seq(c0'#4_1, c1#4_0)))
                        {
                            assert ORD#IsNat(Lit(ORD#FromNat(1)));
                            assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(k#0);
                            assume _System.Tuple2.___hMake2_q(cs#0);
                            assume _System.Tuple2.___hMake2_q(cs'#0);
                            ##_k#4_0 := ORD#Minus(k#0, ORD#FromNat(1));
                            // assume allocatedness for argument to function
                            assume $IsAlloc(##_k#4_0, TORDINAL, $Heap);
                            ##c#4_0 := c0#4_0;
                            // assume allocatedness for argument to function
                            assume $IsAlloc(##c#4_0, Tclass._module.com(), $Heap);
                            ##s#4_0 := $Unbox(_System.Tuple2._1(cs#0)): Map Box Box;
                            // assume allocatedness for argument to function
                            assume $IsAlloc(##s#4_0, TMap(TSeq(TChar), TInt), $Heap);
                            ##c'#4_0 := c0'#4_1;
                            // assume allocatedness for argument to function
                            assume $IsAlloc(##c'#4_0, Tclass._module.com(), $Heap);
                            ##s'#4_0 := $Unbox(_System.Tuple2._1(cs'#0)): Map Box Box;
                            // assume allocatedness for argument to function
                            assume $IsAlloc(##s'#4_0, TMap(TSeq(TChar), TInt), $Heap);
                            assume _module.__default.small__step_h#canCall(ORD#Minus(k#0, ORD#FromNat(1)), 
                              c0#4_0, 
                              $Unbox(_System.Tuple2._1(cs#0)): Map Box Box, 
                              c0'#4_1, 
                              $Unbox(_System.Tuple2._1(cs'#0)): Map Box Box);
                        }

                        assume $IsA#_module.com($Unbox(_System.Tuple2._0(cs'#0)): DatatypeType)
                           && _System.Tuple2.___hMake2_q(cs'#0)
                           && (_module.com#Equal($Unbox(_System.Tuple2._0(cs'#0)): DatatypeType, 
                              #_module.com.Seq(c0'#4_1, c1#4_0))
                             ==> _System.Tuple2.___hMake2_q(cs#0)
                               && _System.Tuple2.___hMake2_q(cs'#0)
                               && _module.__default.small__step_h#canCall(ORD#Minus(k#0, ORD#FromNat(1)), 
                                c0#4_0, 
                                $Unbox(_System.Tuple2._1(cs#0)): Map Box Box, 
                                c0'#4_1, 
                                $Unbox(_System.Tuple2._1(cs'#0)): Map Box Box));
                    }

                    assert ($Is(Lit(#_module.com.SKIP()), Tclass._module.com())
                         && 
                        _module.com#Equal($Unbox(_System.Tuple2._0(cs'#0)): DatatypeType, 
                          #_module.com.Seq(Lit(#_module.com.SKIP()), c1#4_0))
                         && _module.__default.small__step_h($LS($LZ), 
                          ORD#Minus(k#0, ORD#FromNat(1)), 
                          c0#4_0, 
                          $Unbox(_System.Tuple2._1(cs#0)): Map Box Box, 
                          Lit(#_module.com.SKIP()), 
                          $Unbox(_System.Tuple2._1(cs'#0)): Map Box Box))
                       || (exists $as#c0'4_0#4_0: DatatypeType :: 
                        $Is($as#c0'4_0#4_0, Tclass._module.com())
                           && 
                          _module.com#Equal($Unbox(_System.Tuple2._0(cs'#0)): DatatypeType, 
                            #_module.com.Seq($as#c0'4_0#4_0, c1#4_0))
                           && _module.__default.small__step_h($LS($LZ), 
                            ORD#Minus(k#0, ORD#FromNat(1)), 
                            c0#4_0, 
                            $Unbox(_System.Tuple2._1(cs#0)): Map Box Box, 
                            $as#c0'4_0#4_0, 
                            $Unbox(_System.Tuple2._1(cs'#0)): Map Box Box));
                    havoc c0'#4_0;
                    assume _module.com#Equal($Unbox(_System.Tuple2._0(cs'#0)): DatatypeType, 
                        #_module.com.Seq(c0'#4_0, c1#4_0))
                       && _module.__default.small__step_h($LS($LZ), 
                        ORD#Minus(k#0, ORD#FromNat(1)), 
                        c0#4_0, 
                        $Unbox(_System.Tuple2._1(cs#0)): Map Box Box, 
                        c0'#4_0, 
                        $Unbox(_System.Tuple2._1(cs'#0)): Map Box Box);
                    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(217,82)"} true;
                    // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(218,18)
                    havoc c0''#4_1;
                    if ($Is(c0''#4_1, Tclass._module.com())
                       && $IsAlloc(c0''#4_1, Tclass._module.com(), $Heap))
                    {
                        assume _System.Tuple2.___hMake2_q(cs''#0);
                        if (_module.com#Equal($Unbox(_System.Tuple2._0(cs''#0)): DatatypeType, 
                          #_module.com.Seq(c0''#4_1, c1#4_0)))
                        {
                            assert ORD#IsNat(Lit(ORD#FromNat(1)));
                            assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(k'#0);
                            assume _System.Tuple2.___hMake2_q(cs#0);
                            assume _System.Tuple2.___hMake2_q(cs''#0);
                            ##_k#4_1 := ORD#Minus(k'#0, ORD#FromNat(1));
                            // assume allocatedness for argument to function
                            assume $IsAlloc(##_k#4_1, TORDINAL, $Heap);
                            ##c#4_1 := c0#4_0;
                            // assume allocatedness for argument to function
                            assume $IsAlloc(##c#4_1, Tclass._module.com(), $Heap);
                            ##s#4_1 := $Unbox(_System.Tuple2._1(cs#0)): Map Box Box;
                            // assume allocatedness for argument to function
                            assume $IsAlloc(##s#4_1, TMap(TSeq(TChar), TInt), $Heap);
                            ##c'#4_1 := c0''#4_1;
                            // assume allocatedness for argument to function
                            assume $IsAlloc(##c'#4_1, Tclass._module.com(), $Heap);
                            ##s'#4_1 := $Unbox(_System.Tuple2._1(cs''#0)): Map Box Box;
                            // assume allocatedness for argument to function
                            assume $IsAlloc(##s'#4_1, TMap(TSeq(TChar), TInt), $Heap);
                            assume _module.__default.small__step_h#canCall(ORD#Minus(k'#0, ORD#FromNat(1)), 
                              c0#4_0, 
                              $Unbox(_System.Tuple2._1(cs#0)): Map Box Box, 
                              c0''#4_1, 
                              $Unbox(_System.Tuple2._1(cs''#0)): Map Box Box);
                        }

                        assume $IsA#_module.com($Unbox(_System.Tuple2._0(cs''#0)): DatatypeType)
                           && _System.Tuple2.___hMake2_q(cs''#0)
                           && (_module.com#Equal($Unbox(_System.Tuple2._0(cs''#0)): DatatypeType, 
                              #_module.com.Seq(c0''#4_1, c1#4_0))
                             ==> _System.Tuple2.___hMake2_q(cs#0)
                               && _System.Tuple2.___hMake2_q(cs''#0)
                               && _module.__default.small__step_h#canCall(ORD#Minus(k'#0, ORD#FromNat(1)), 
                                c0#4_0, 
                                $Unbox(_System.Tuple2._1(cs#0)): Map Box Box, 
                                c0''#4_1, 
                                $Unbox(_System.Tuple2._1(cs''#0)): Map Box Box));
                    }

                    assert ($Is(Lit(#_module.com.SKIP()), Tclass._module.com())
                         && 
                        _module.com#Equal($Unbox(_System.Tuple2._0(cs''#0)): DatatypeType, 
                          #_module.com.Seq(Lit(#_module.com.SKIP()), c1#4_0))
                         && _module.__default.small__step_h($LS($LZ), 
                          ORD#Minus(k'#0, ORD#FromNat(1)), 
                          c0#4_0, 
                          $Unbox(_System.Tuple2._1(cs#0)): Map Box Box, 
                          Lit(#_module.com.SKIP()), 
                          $Unbox(_System.Tuple2._1(cs''#0)): Map Box Box))
                       || (exists $as#c0''4_0#4_0: DatatypeType :: 
                        $Is($as#c0''4_0#4_0, Tclass._module.com())
                           && 
                          _module.com#Equal($Unbox(_System.Tuple2._0(cs''#0)): DatatypeType, 
                            #_module.com.Seq($as#c0''4_0#4_0, c1#4_0))
                           && _module.__default.small__step_h($LS($LZ), 
                            ORD#Minus(k'#0, ORD#FromNat(1)), 
                            c0#4_0, 
                            $Unbox(_System.Tuple2._1(cs#0)): Map Box Box, 
                            $as#c0''4_0#4_0, 
                            $Unbox(_System.Tuple2._1(cs''#0)): Map Box Box));
                    havoc c0''#4_0;
                    assume _module.com#Equal($Unbox(_System.Tuple2._0(cs''#0)): DatatypeType, 
                        #_module.com.Seq(c0''#4_0, c1#4_0))
                       && _module.__default.small__step_h($LS($LZ), 
                        ORD#Minus(k'#0, ORD#FromNat(1)), 
                        c0#4_0, 
                        $Unbox(_System.Tuple2._1(cs#0)): Map Box Box, 
                        c0''#4_0, 
                        $Unbox(_System.Tuple2._1(cs''#0)): Map Box Box);
                    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(218,88)"} true;
                    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(219,39)
                    // TrCallStmt: Before ProcessCallStmt
                    assert ORD#IsNat(Lit(ORD#FromNat(1)));
                    assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(k#0);
                    assume true;
                    // ProcessCallStmt: CheckSubrange
                    k##4_2 := ORD#Minus(k#0, ORD#FromNat(1));
                    assert ORD#IsNat(Lit(ORD#FromNat(1)));
                    assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(k'#0);
                    assume true;
                    // ProcessCallStmt: CheckSubrange
                    k'##4_0 := ORD#Minus(k'#0, ORD#FromNat(1));
                    assume _System.Tuple2.___hMake2_q(cs#0);
                    assume _System.Tuple2.___hMake2_q(cs#0);
                    // ProcessCallStmt: CheckSubrange
                    cs##4_0 := #_System._tuple#2._#Make2($Box(c0#4_0), _System.Tuple2._1(cs#0));
                    assume _System.Tuple2.___hMake2_q(cs'#0);
                    assume _System.Tuple2.___hMake2_q(cs'#0);
                    // ProcessCallStmt: CheckSubrange
                    cs'##4_0 := #_System._tuple#2._#Make2($Box(c0'#4_0), _System.Tuple2._1(cs'#0));
                    assume _System.Tuple2.___hMake2_q(cs''#0);
                    assume _System.Tuple2.___hMake2_q(cs''#0);
                    // ProcessCallStmt: CheckSubrange
                    cs''##4_0 := #_System._tuple#2._#Make2($Box(c0''#4_0), _System.Tuple2._1(cs''#0));
                    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                    assert ORD#Less(k##4_2, k#0)
                       || (k##4_2 == k#0
                         && (ORD#Less(k'##4_0, k'#0)
                           || (k'##4_0 == k'#0
                             && (DtRank(cs##4_0) < DtRank(cs#0)
                               || (DtRank(cs##4_0) == DtRank(cs#0)
                                 && (DtRank(cs'##4_0) < DtRank(cs'#0)
                                   || (DtRank(cs'##4_0) == DtRank(cs'#0) && DtRank(cs''##4_0) < DtRank(cs''#0))))))));
                    // ProcessCallStmt: Make the call
                    call Call$$_module.__default.SmallStep__is__deterministic__Aux(k##4_2, k'##4_0, cs##4_0, cs'##4_0, cs''##4_0);
                    // TrCallStmt: After ProcessCallStmt
                    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(219,91)"} true;
                }
            }
            else if ($Unbox(_System.Tuple2._0(cs#0)): DatatypeType
               == #_module.com.If(_mcc#4#3_0, _mcc#5#3_0, _mcc#6#3_0))
            {
                assume $Is(_mcc#4#3_0, Tclass._module.bexp());
                assume $Is(_mcc#5#3_0, Tclass._module.com());
                assume $Is(_mcc#6#3_0, Tclass._module.com());
                havoc els#3_0;
                assume $Is(els#3_0, Tclass._module.com())
                   && $IsAlloc(els#3_0, Tclass._module.com(), $Heap);
                assume let#3_0#0#0 == _mcc#6#3_0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(let#3_0#0#0, Tclass._module.com());
                assume els#3_0 == let#3_0#0#0;
                havoc thn#3_0;
                assume $Is(thn#3_0, Tclass._module.com())
                   && $IsAlloc(thn#3_0, Tclass._module.com(), $Heap);
                assume let#3_1#0#0 == _mcc#5#3_0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(let#3_1#0#0, Tclass._module.com());
                assume thn#3_0 == let#3_1#0#0;
                havoc b#3_0;
                assume $Is(b#3_0, Tclass._module.bexp())
                   && $IsAlloc(b#3_0, Tclass._module.bexp(), $Heap);
                assume let#3_2#0#0 == _mcc#4#3_0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(let#3_2#0#0, Tclass._module.bexp());
                assume b#3_0 == let#3_2#0#0;
            }
            else if ($Unbox(_System.Tuple2._0(cs#0)): DatatypeType
               == #_module.com.While(_mcc#7#2_0, _mcc#8#2_0))
            {
                assume $Is(_mcc#7#2_0, Tclass._module.bexp());
                assume $Is(_mcc#8#2_0, Tclass._module.com());
                havoc body#2_0;
                assume $Is(body#2_0, Tclass._module.com())
                   && $IsAlloc(body#2_0, Tclass._module.com(), $Heap);
                assume let#2_0#0#0 == _mcc#8#2_0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(let#2_0#0#0, Tclass._module.com());
                assume body#2_0 == let#2_0#0#0;
                havoc b#2_0;
                assume $Is(b#2_0, Tclass._module.bexp())
                   && $IsAlloc(b#2_0, Tclass._module.bexp(), $Heap);
                assume let#2_1#0#0 == _mcc#7#2_0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(let#2_1#0#0, Tclass._module.bexp());
                assume b#2_0 == let#2_1#0#0;
            }
            else if ($Unbox(_System.Tuple2._0(cs#0)): DatatypeType == #_module.com.SKIP())
            {
                assert false;
            }
            else
            {
                assume false;
            }
        }
    }
}



// function declaration for _module._default.small_step_star
function _module.__default.small__step__star($ly: LayerType, 
    c#0: DatatypeType, 
    s#0: Map Box Box, 
    c'#0: DatatypeType, 
    s'#0: Map Box Box)
   : bool;

function _module.__default.small__step__star#canCall(c#0: DatatypeType, s#0: Map Box Box, c'#0: DatatypeType, s'#0: Map Box Box)
   : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, 
    c#0: DatatypeType, 
    s#0: Map Box Box, 
    c'#0: DatatypeType, 
    s'#0: Map Box Box :: 
  { _module.__default.small__step__star($LS($ly), c#0, s#0, c'#0, s'#0) } 
  _module.__default.small__step__star($LS($ly), c#0, s#0, c'#0, s'#0)
     == _module.__default.small__step__star($ly, c#0, s#0, c'#0, s'#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, 
    c#0: DatatypeType, 
    s#0: Map Box Box, 
    c'#0: DatatypeType, 
    s'#0: Map Box Box :: 
  { _module.__default.small__step__star(AsFuelBottom($ly), c#0, s#0, c'#0, s'#0) } 
  _module.__default.small__step__star($ly, c#0, s#0, c'#0, s'#0)
     == _module.__default.small__step__star($LZ, c#0, s#0, c'#0, s'#0));

// consequence axiom for _module.__default.small__step__star
axiom 15 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, 
      c#0: DatatypeType, 
      s#0: Map Box Box, 
      c'#0: DatatypeType, 
      s'#0: Map Box Box :: 
    { _module.__default.small__step__star($ly, c#0, s#0, c'#0, s'#0) } 
    _module.__default.small__step__star#canCall(c#0, s#0, c'#0, s'#0)
         || (15 != $FunctionContextHeight
           && 
          $Is(c#0, Tclass._module.com())
           && $Is(s#0, TMap(TSeq(TChar), TInt))
           && $Is(c'#0, Tclass._module.com())
           && $Is(s'#0, TMap(TSeq(TChar), TInt)))
       ==> true);

function _module.__default.small__step__star#requires(LayerType, DatatypeType, Map Box Box, DatatypeType, Map Box Box) : bool;

// #requires axiom for _module.__default.small__step__star
axiom (forall $ly: LayerType, 
    c#0: DatatypeType, 
    s#0: Map Box Box, 
    c'#0: DatatypeType, 
    s'#0: Map Box Box :: 
  { _module.__default.small__step__star#requires($ly, c#0, s#0, c'#0, s'#0) } 
  $Is(c#0, Tclass._module.com())
       && $Is(s#0, TMap(TSeq(TChar), TInt))
       && $Is(c'#0, Tclass._module.com())
       && $Is(s'#0, TMap(TSeq(TChar), TInt))
     ==> _module.__default.small__step__star#requires($ly, c#0, s#0, c'#0, s'#0) == true);

// definition axiom for _module.__default.small__step__star (revealed)
axiom 15 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, 
      c#0: DatatypeType, 
      s#0: Map Box Box, 
      c'#0: DatatypeType, 
      s'#0: Map Box Box :: 
    { _module.__default.small__step__star($LS($ly), c#0, s#0, c'#0, s'#0) } 
    _module.__default.small__step__star#canCall(c#0, s#0, c'#0, s'#0)
         || (15 != $FunctionContextHeight
           && 
          $Is(c#0, Tclass._module.com())
           && $Is(s#0, TMap(TSeq(TChar), TInt))
           && $Is(c'#0, Tclass._module.com())
           && $Is(s'#0, TMap(TSeq(TChar), TInt)))
       ==> $IsA#_module.com(c#0)
         && $IsA#_module.com(c'#0)
         && (!(_module.com#Equal(c#0, c'#0) && Map#Equal(s#0, s'#0))
           ==> (forall c''#0: DatatypeType, s''#0: Map Box Box :: 
            { _module.__default.small__step__star($ly, c''#0, s''#0, c'#0, s'#0) } 
              { _module.__default.small__step($LS($LZ), c#0, s#0, c''#0, s''#0) } 
            $Is(c''#0, Tclass._module.com()) && $Is(s''#0, TMap(TSeq(TChar), TInt))
               ==> _module.__default.small__step#canCall(c#0, s#0, c''#0, s''#0)
                 && (_module.__default.small__step($LS($LZ), c#0, s#0, c''#0, s''#0)
                   ==> _module.__default.small__step__star#canCall(c''#0, s''#0, c'#0, s'#0))))
         && _module.__default.small__step__star($LS($ly), c#0, s#0, c'#0, s'#0)
           == ((_module.com#Equal(c#0, c'#0) && Map#Equal(s#0, s'#0))
             || (exists c''#0: DatatypeType, s''#0: Map Box Box :: 
              { _module.__default.small__step__star($ly, c''#0, s''#0, c'#0, s'#0) } 
                { _module.__default.small__step($LS($LZ), c#0, s#0, c''#0, s''#0) } 
              $Is(c''#0, Tclass._module.com())
                 && $Is(s''#0, TMap(TSeq(TChar), TInt))
                 && 
                _module.__default.small__step($LS($LZ), c#0, s#0, c''#0, s''#0)
                 && _module.__default.small__step__star($ly, c''#0, s''#0, c'#0, s'#0))));

// 1st prefix predicate axiom for _module.__default.small__step__star_h
axiom 16 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, 
      c#0: DatatypeType, 
      s#0: Map Box Box, 
      c'#0: DatatypeType, 
      s'#0: Map Box Box :: 
    { _module.__default.small__step__star($LS($ly), c#0, s#0, c'#0, s'#0) } 
    $Is(c#0, Tclass._module.com())
         && $Is(s#0, TMap(TSeq(TChar), TInt))
         && $Is(c'#0, Tclass._module.com())
         && $Is(s'#0, TMap(TSeq(TChar), TInt))
         && _module.__default.small__step__star($LS($ly), c#0, s#0, c'#0, s'#0)
       ==> (exists _k#0: Box :: 
        { _module.__default.small__step__star_h($LS($ly), _k#0, c#0, s#0, c'#0, s'#0) } 
        _module.__default.small__step__star_h($LS($ly), _k#0, c#0, s#0, c'#0, s'#0)));

// 2nd prefix predicate axiom
axiom 16 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, 
      c#0: DatatypeType, 
      s#0: Map Box Box, 
      c'#0: DatatypeType, 
      s'#0: Map Box Box :: 
    { _module.__default.small__step__star($LS($ly), c#0, s#0, c'#0, s'#0) } 
    $Is(c#0, Tclass._module.com())
         && $Is(s#0, TMap(TSeq(TChar), TInt))
         && $Is(c'#0, Tclass._module.com())
         && $Is(s'#0, TMap(TSeq(TChar), TInt))
         && (exists _k#0: Box :: 
          { _module.__default.small__step__star_h($LS($ly), _k#0, c#0, s#0, c'#0, s'#0) } 
          _module.__default.small__step__star_h($LS($ly), _k#0, c#0, s#0, c'#0, s'#0))
       ==> _module.__default.small__step__star($LS($ly), c#0, s#0, c'#0, s'#0));

// 3rd prefix predicate axiom
axiom 16 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, 
      c#0: DatatypeType, 
      s#0: Map Box Box, 
      c'#0: DatatypeType, 
      s'#0: Map Box Box, 
      _k#0: Box :: 
    { _module.__default.small__step__star_h($ly, _k#0, c#0, s#0, c'#0, s'#0) } 
    $Is(c#0, Tclass._module.com())
         && $Is(s#0, TMap(TSeq(TChar), TInt))
         && $Is(c'#0, Tclass._module.com())
         && $Is(s'#0, TMap(TSeq(TChar), TInt))
         && _k#0 == ORD#FromNat(0)
       ==> !_module.__default.small__step__star_h($ly, _k#0, c#0, s#0, c'#0, s'#0));

// targeted prefix predicate monotonicity axiom
axiom 16 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, 
      c#0: DatatypeType, 
      s#0: Map Box Box, 
      c'#0: DatatypeType, 
      s'#0: Map Box Box, 
      _k#0: Box, 
      _m: Box, 
      _limit: Box :: 
    { _module.__default.small__step__star_h($ly, _k#0, c#0, s#0, c'#0, s'#0), ORD#LessThanLimit(_k#0, _limit), ORD#LessThanLimit(_m, _limit) } 
    ORD#Less(_k#0, _m)
       ==> 
      _module.__default.small__step__star_h($ly, _k#0, c#0, s#0, c'#0, s'#0)
       ==> _module.__default.small__step__star_h($ly, _m, c#0, s#0, c'#0, s'#0));

procedure CheckWellformed$$_module.__default.small__step__star(c#0: DatatypeType where $Is(c#0, Tclass._module.com()), 
    s#0: Map Box Box where $Is(s#0, TMap(TSeq(TChar), TInt)), 
    c'#0: DatatypeType where $Is(c'#0, Tclass._module.com()), 
    s'#0: Map Box Box where $Is(s'#0, TMap(TSeq(TChar), TInt)));
  free requires 15 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.small__step__star(c#0: DatatypeType, s#0: Map Box Box, c'#0: DatatypeType, s'#0: Map Box Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var c''#1: DatatypeType;
  var s''#1: Map Box Box;
  var ##c#0: DatatypeType;
  var ##s#0: Map Box Box;
  var ##c'#0: DatatypeType;
  var ##s'#0: Map Box Box;
  var ##c#1: DatatypeType;
  var ##s#1: Map Box Box;
  var ##c'#1: DatatypeType;
  var ##s'#1: Map Box Box;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function small_step_star
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(226,16): initial state"} true;
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
        if (_module.com#Equal(c#0, c'#0))
        {
        }

        if (!(_module.com#Equal(c#0, c'#0) && Map#Equal(s#0, s'#0)))
        {
            // Begin Comprehension WF check
            havoc c''#1;
            havoc s''#1;
            if ($Is(c''#1, Tclass._module.com()) && $Is(s''#1, TMap(TSeq(TChar), TInt)))
            {
                ##c#0 := c#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##c#0, Tclass._module.com(), $Heap);
                ##s#0 := s#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#0, TMap(TSeq(TChar), TInt), $Heap);
                ##c'#0 := c''#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##c'#0, Tclass._module.com(), $Heap);
                ##s'#0 := s''#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s'#0, TMap(TSeq(TChar), TInt), $Heap);
                b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assume _module.__default.small__step#canCall(c#0, s#0, c''#1, s''#1);
                if (_module.__default.small__step($LS($LZ), c#0, s#0, c''#1, s''#1))
                {
                    ##c#1 := c''#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c#1, Tclass._module.com(), $Heap);
                    ##s#1 := s''#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s#1, TMap(TSeq(TChar), TInt), $Heap);
                    ##c'#1 := c'#0;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c'#1, Tclass._module.com(), $Heap);
                    ##s'#1 := s'#0;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s'#1, TMap(TSeq(TChar), TInt), $Heap);
                    b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                    assume _module.__default.small__step__star#canCall(c''#1, s''#1, c'#0, s'#0);
                }
            }

            // End Comprehension WF check
        }

        assume _module.__default.small__step__star($LS($LZ), c#0, s#0, c'#0, s'#0)
           == ((_module.com#Equal(c#0, c'#0) && Map#Equal(s#0, s'#0))
             || (exists c''#2: DatatypeType, s''#2: Map Box Box :: 
              { _module.__default.small__step__star($LS($LZ), c''#2, s''#2, c'#0, s'#0) } 
                { _module.__default.small__step($LS($LZ), c#0, s#0, c''#2, s''#2) } 
              $Is(c''#2, Tclass._module.com())
                 && $Is(s''#2, TMap(TSeq(TChar), TInt))
                 && 
                _module.__default.small__step($LS($LZ), c#0, s#0, c''#2, s''#2)
                 && _module.__default.small__step__star($LS($LZ), c''#2, s''#2, c'#0, s'#0)));
        assume $IsA#_module.com(c#0)
           && $IsA#_module.com(c'#0)
           && (!(_module.com#Equal(c#0, c'#0) && Map#Equal(s#0, s'#0))
             ==> (forall c''#2: DatatypeType, s''#2: Map Box Box :: 
              { _module.__default.small__step__star($LS($LZ), c''#2, s''#2, c'#0, s'#0) } 
                { _module.__default.small__step($LS($LZ), c#0, s#0, c''#2, s''#2) } 
              $Is(c''#2, Tclass._module.com()) && $Is(s''#2, TMap(TSeq(TChar), TInt))
                 ==> _module.__default.small__step#canCall(c#0, s#0, c''#2, s''#2)
                   && (_module.__default.small__step($LS($LZ), c#0, s#0, c''#2, s''#2)
                     ==> _module.__default.small__step__star#canCall(c''#2, s''#2, c'#0, s'#0))));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.small__step__star($LS($LZ), c#0, s#0, c'#0, s'#0), TBool);
        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



// function declaration for _module._default.small_step_star#
function _module.__default.small__step__star_h($ly: LayerType, 
    _k#0: Box, 
    c#0: DatatypeType, 
    s#0: Map Box Box, 
    c'#0: DatatypeType, 
    s'#0: Map Box Box)
   : bool;

function _module.__default.small__step__star_h#canCall(_k#0: Box, 
    c#0: DatatypeType, 
    s#0: Map Box Box, 
    c'#0: DatatypeType, 
    s'#0: Map Box Box)
   : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, 
    _k#0: Box, 
    c#0: DatatypeType, 
    s#0: Map Box Box, 
    c'#0: DatatypeType, 
    s'#0: Map Box Box :: 
  { _module.__default.small__step__star_h($LS($ly), _k#0, c#0, s#0, c'#0, s'#0) } 
  _module.__default.small__step__star_h($LS($ly), _k#0, c#0, s#0, c'#0, s'#0)
     == _module.__default.small__step__star_h($ly, _k#0, c#0, s#0, c'#0, s'#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, 
    _k#0: Box, 
    c#0: DatatypeType, 
    s#0: Map Box Box, 
    c'#0: DatatypeType, 
    s'#0: Map Box Box :: 
  { _module.__default.small__step__star_h(AsFuelBottom($ly), _k#0, c#0, s#0, c'#0, s'#0) } 
  _module.__default.small__step__star_h($ly, _k#0, c#0, s#0, c'#0, s'#0)
     == _module.__default.small__step__star_h($LZ, _k#0, c#0, s#0, c'#0, s'#0));

// consequence axiom for _module.__default.small__step__star_h
axiom 16 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, 
      _k#0: Box, 
      c#0: DatatypeType, 
      s#0: Map Box Box, 
      c'#0: DatatypeType, 
      s'#0: Map Box Box :: 
    { _module.__default.small__step__star_h($ly, _k#0, c#0, s#0, c'#0, s'#0) } 
    _module.__default.small__step__star_h#canCall(_k#0, c#0, s#0, c'#0, s'#0)
         || (16 != $FunctionContextHeight
           && 
          $Is(c#0, Tclass._module.com())
           && $Is(s#0, TMap(TSeq(TChar), TInt))
           && $Is(c'#0, Tclass._module.com())
           && $Is(s'#0, TMap(TSeq(TChar), TInt)))
       ==> true);

function _module.__default.small__step__star_h#requires(LayerType, Box, DatatypeType, Map Box Box, DatatypeType, Map Box Box) : bool;

// #requires axiom for _module.__default.small__step__star_h
axiom (forall $ly: LayerType, 
    _k#0: Box, 
    c#0: DatatypeType, 
    s#0: Map Box Box, 
    c'#0: DatatypeType, 
    s'#0: Map Box Box :: 
  { _module.__default.small__step__star_h#requires($ly, _k#0, c#0, s#0, c'#0, s'#0) } 
  $Is(c#0, Tclass._module.com())
       && $Is(s#0, TMap(TSeq(TChar), TInt))
       && $Is(c'#0, Tclass._module.com())
       && $Is(s'#0, TMap(TSeq(TChar), TInt))
     ==> _module.__default.small__step__star_h#requires($ly, _k#0, c#0, s#0, c'#0, s'#0)
       == true);

// definition axiom for _module.__default.small__step__star_h (revealed)
axiom 16 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, 
      _k#0: Box, 
      c#0: DatatypeType, 
      s#0: Map Box Box, 
      c'#0: DatatypeType, 
      s'#0: Map Box Box :: 
    { _module.__default.small__step__star_h($LS($ly), _k#0, c#0, s#0, c'#0, s'#0) } 
    _module.__default.small__step__star_h#canCall(_k#0, c#0, s#0, c'#0, s'#0)
         || (16 != $FunctionContextHeight
           && 
          $Is(c#0, Tclass._module.com())
           && $Is(s#0, TMap(TSeq(TChar), TInt))
           && $Is(c'#0, Tclass._module.com())
           && $Is(s'#0, TMap(TSeq(TChar), TInt)))
       ==> (0 < ORD#Offset(_k#0)
           ==> $IsA#_module.com(c#0)
             && $IsA#_module.com(c'#0)
             && (!(_module.com#Equal(c#0, c'#0) && Map#Equal(s#0, s'#0))
               ==> (forall c''#3: DatatypeType, s''#3: Map Box Box :: 
                { _module.__default.small__step__star_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), c''#3, s''#3, c'#0, s'#0) } 
                  { _module.__default.small__step($LS($LZ), c#0, s#0, c''#3, s''#3) } 
                $Is(c''#3, Tclass._module.com()) && $Is(s''#3, TMap(TSeq(TChar), TInt))
                   ==> _module.__default.small__step#canCall(c#0, s#0, c''#3, s''#3)
                     && (_module.__default.small__step($LS($LZ), c#0, s#0, c''#3, s''#3)
                       ==> _module.__default.small__step__star_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), c''#3, s''#3, c'#0, s'#0)))))
         && (
          (0 < ORD#Offset(_k#0)
           ==> (_module.com#Equal(c#0, c'#0) && Map#Equal(s#0, s'#0))
             || (exists c''#3: DatatypeType, s''#3: Map Box Box :: 
              { _module.__default.small__step__star_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), c''#3, s''#3, c'#0, s'#0) } 
                { _module.__default.small__step($LS($LZ), c#0, s#0, c''#3, s''#3) } 
              $Is(c''#3, Tclass._module.com())
                 && $Is(s''#3, TMap(TSeq(TChar), TInt))
                 && 
                _module.__default.small__step($LS($LZ), c#0, s#0, c''#3, s''#3)
                 && _module.__default.small__step__star_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), c''#3, s''#3, c'#0, s'#0)))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#0: Box :: 
            { _module.__default.small__step__star_h($ly, _k'#0, c#0, s#0, c'#0, s'#0) } 
            ORD#LessThanLimit(_k'#0, _k#0)
               ==> _module.__default.small__step__star_h#canCall(_k'#0, c#0, s#0, c'#0, s'#0)))
         && _module.__default.small__step__star_h($LS($ly), _k#0, c#0, s#0, c'#0, s'#0)
           == ((0 < ORD#Offset(_k#0)
               ==> (_module.com#Equal(c#0, c'#0) && Map#Equal(s#0, s'#0))
                 || (exists c''#3: DatatypeType, s''#3: Map Box Box :: 
                  { _module.__default.small__step__star_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), c''#3, s''#3, c'#0, s'#0) } 
                    { _module.__default.small__step($LS($LZ), c#0, s#0, c''#3, s''#3) } 
                  $Is(c''#3, Tclass._module.com())
                     && $Is(s''#3, TMap(TSeq(TChar), TInt))
                     && 
                    _module.__default.small__step($LS($LZ), c#0, s#0, c''#3, s''#3)
                     && _module.__default.small__step__star_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), c''#3, s''#3, c'#0, s'#0)))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (exists _k'#0: Box :: 
                { _module.__default.small__step__star_h($ly, _k'#0, c#0, s#0, c'#0, s'#0) } 
                ORD#LessThanLimit(_k'#0, _k#0)
                   && _module.__default.small__step__star_h($ly, _k'#0, c#0, s#0, c'#0, s'#0)))));

// definition axiom for _module.__default.small__step__star_h for decreasing-related literals (revealed)
axiom 16 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, 
      _k#0: Box, 
      c#0: DatatypeType, 
      s#0: Map Box Box, 
      c'#0: DatatypeType, 
      s'#0: Map Box Box :: 
    {:weight 3} { _module.__default.small__step__star_h($LS($ly), Lit(_k#0), c#0, s#0, c'#0, s'#0) } 
    _module.__default.small__step__star_h#canCall(Lit(_k#0), c#0, s#0, c'#0, s'#0)
         || (16 != $FunctionContextHeight
           && 
          $Is(c#0, Tclass._module.com())
           && $Is(s#0, TMap(TSeq(TChar), TInt))
           && $Is(c'#0, Tclass._module.com())
           && $Is(s'#0, TMap(TSeq(TChar), TInt)))
       ==> (0 < ORD#Offset(_k#0)
           ==> $IsA#_module.com(c#0)
             && $IsA#_module.com(c'#0)
             && (!(_module.com#Equal(c#0, c'#0) && Map#Equal(s#0, s'#0))
               ==> (forall c''#4: DatatypeType, s''#4: Map Box Box :: 
                { _module.__default.small__step__star_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), c''#4, s''#4, c'#0, s'#0) } 
                  { _module.__default.small__step($LS($LZ), c#0, s#0, c''#4, s''#4) } 
                $Is(c''#4, Tclass._module.com()) && $Is(s''#4, TMap(TSeq(TChar), TInt))
                   ==> _module.__default.small__step#canCall(c#0, s#0, c''#4, s''#4)
                     && (_module.__default.small__step($LS($LZ), c#0, s#0, c''#4, s''#4)
                       ==> _module.__default.small__step__star_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), c''#4, s''#4, c'#0, s'#0)))))
         && (
          (0 < ORD#Offset(_k#0)
           ==> (_module.com#Equal(c#0, c'#0) && Map#Equal(s#0, s'#0))
             || (exists c''#4: DatatypeType, s''#4: Map Box Box :: 
              { _module.__default.small__step__star_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), c''#4, s''#4, c'#0, s'#0) } 
                { _module.__default.small__step($LS($LZ), c#0, s#0, c''#4, s''#4) } 
              $Is(c''#4, Tclass._module.com())
                 && $Is(s''#4, TMap(TSeq(TChar), TInt))
                 && 
                _module.__default.small__step($LS($LZ), c#0, s#0, c''#4, s''#4)
                 && _module.__default.small__step__star_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), c''#4, s''#4, c'#0, s'#0)))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#1: Box :: 
            { _module.__default.small__step__star_h($LS($ly), _k'#1, c#0, s#0, c'#0, s'#0) } 
            ORD#LessThanLimit(_k'#1, _k#0)
               ==> _module.__default.small__step__star_h#canCall(_k'#1, c#0, s#0, c'#0, s'#0)))
         && _module.__default.small__step__star_h($LS($ly), Lit(_k#0), c#0, s#0, c'#0, s'#0)
           == ((0 < ORD#Offset(_k#0)
               ==> (_module.com#Equal(c#0, c'#0) && Map#Equal(s#0, s'#0))
                 || (exists c''#4: DatatypeType, s''#4: Map Box Box :: 
                  { _module.__default.small__step__star_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), c''#4, s''#4, c'#0, s'#0) } 
                    { _module.__default.small__step($LS($LZ), c#0, s#0, c''#4, s''#4) } 
                  $Is(c''#4, Tclass._module.com())
                     && $Is(s''#4, TMap(TSeq(TChar), TInt))
                     && 
                    _module.__default.small__step($LS($LZ), c#0, s#0, c''#4, s''#4)
                     && _module.__default.small__step__star_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), c''#4, s''#4, c'#0, s'#0)))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (exists _k'#1: Box :: 
                { _module.__default.small__step__star_h($LS($ly), _k'#1, c#0, s#0, c'#0, s'#0) } 
                ORD#LessThanLimit(_k'#1, _k#0)
                   && _module.__default.small__step__star_h($LS($ly), _k'#1, c#0, s#0, c'#0, s'#0)))));

// definition axiom for _module.__default.small__step__star_h for all literals (revealed)
axiom 16 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, 
      _k#0: Box, 
      c#0: DatatypeType, 
      s#0: Map Box Box, 
      c'#0: DatatypeType, 
      s'#0: Map Box Box :: 
    {:weight 3} { _module.__default.small__step__star_h($LS($ly), Lit(_k#0), Lit(c#0), Lit(s#0), Lit(c'#0), Lit(s'#0)) } 
    _module.__default.small__step__star_h#canCall(Lit(_k#0), Lit(c#0), Lit(s#0), Lit(c'#0), Lit(s'#0))
         || (16 != $FunctionContextHeight
           && 
          $Is(c#0, Tclass._module.com())
           && $Is(s#0, TMap(TSeq(TChar), TInt))
           && $Is(c'#0, Tclass._module.com())
           && $Is(s'#0, TMap(TSeq(TChar), TInt)))
       ==> (0 < ORD#Offset(_k#0)
           ==> $IsA#_module.com(c#0)
             && $IsA#_module.com(c'#0)
             && (!(_module.com#Equal(c#0, c'#0) && Map#Equal(s#0, s'#0))
               ==> (forall c''#5: DatatypeType, s''#5: Map Box Box :: 
                { _module.__default.small__step__star_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), c''#5, s''#5, c'#0, s'#0) } 
                  { _module.__default.small__step($LS($LZ), c#0, s#0, c''#5, s''#5) } 
                $Is(c''#5, Tclass._module.com()) && $Is(s''#5, TMap(TSeq(TChar), TInt))
                   ==> _module.__default.small__step#canCall(c#0, s#0, c''#5, s''#5)
                     && (_module.__default.small__step($LS($LZ), c#0, s#0, c''#5, s''#5)
                       ==> _module.__default.small__step__star_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), c''#5, s''#5, c'#0, s'#0)))))
         && (
          (0 < ORD#Offset(_k#0)
           ==> (_module.com#Equal(c#0, c'#0) && Map#Equal(s#0, s'#0))
             || (exists c''#5: DatatypeType, s''#5: Map Box Box :: 
              { _module.__default.small__step__star_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), c''#5, s''#5, c'#0, s'#0) } 
                { _module.__default.small__step($LS($LZ), c#0, s#0, c''#5, s''#5) } 
              $Is(c''#5, Tclass._module.com())
                 && $Is(s''#5, TMap(TSeq(TChar), TInt))
                 && 
                _module.__default.small__step($LS($LZ), c#0, s#0, c''#5, s''#5)
                 && _module.__default.small__step__star_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), c''#5, s''#5, c'#0, s'#0)))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#2: Box :: 
            { _module.__default.small__step__star_h($LS($ly), _k'#2, c#0, s#0, c'#0, s'#0) } 
            ORD#LessThanLimit(_k'#2, _k#0)
               ==> _module.__default.small__step__star_h#canCall(_k'#2, c#0, s#0, c'#0, s'#0)))
         && _module.__default.small__step__star_h($LS($ly), Lit(_k#0), Lit(c#0), Lit(s#0), Lit(c'#0), Lit(s'#0))
           == ((0 < ORD#Offset(_k#0)
               ==> (_module.com#Equal(c#0, c'#0) && Map#Equal(s#0, s'#0))
                 || (exists c''#5: DatatypeType, s''#5: Map Box Box :: 
                  { _module.__default.small__step__star_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), c''#5, s''#5, c'#0, s'#0) } 
                    { _module.__default.small__step($LS($LZ), c#0, s#0, c''#5, s''#5) } 
                  $Is(c''#5, Tclass._module.com())
                     && $Is(s''#5, TMap(TSeq(TChar), TInt))
                     && 
                    _module.__default.small__step($LS($LZ), c#0, s#0, c''#5, s''#5)
                     && _module.__default.small__step__star_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), c''#5, s''#5, c'#0, s'#0)))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (exists _k'#2: Box :: 
                { _module.__default.small__step__star_h($LS($ly), _k'#2, c#0, s#0, c'#0, s'#0) } 
                ORD#LessThanLimit(_k'#2, _k#0)
                   && _module.__default.small__step__star_h($LS($ly), _k'#2, c#0, s#0, c'#0, s'#0)))));

procedure {:_induction c0#0, s0#0, c1#0, s1#0, c2#0, s2#0} CheckWellformed$$_module.__default.star__transitive(c0#0: DatatypeType
       where $Is(c0#0, Tclass._module.com())
         && $IsAlloc(c0#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c0#0), 
    s0#0: Map Box Box
       where $Is(s0#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s0#0, TMap(TSeq(TChar), TInt), $Heap), 
    c1#0: DatatypeType
       where $Is(c1#0, Tclass._module.com())
         && $IsAlloc(c1#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c1#0), 
    s1#0: Map Box Box
       where $Is(s1#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s1#0, TMap(TSeq(TChar), TInt), $Heap), 
    c2#0: DatatypeType
       where $Is(c2#0, Tclass._module.com())
         && $IsAlloc(c2#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c2#0), 
    s2#0: Map Box Box
       where $Is(s2#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s2#0, TMap(TSeq(TChar), TInt), $Heap));
  free requires 19 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction c0#0, s0#0, c1#0, s1#0, c2#0, s2#0} Call$$_module.__default.star__transitive(c0#0: DatatypeType
       where $Is(c0#0, Tclass._module.com())
         && $IsAlloc(c0#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c0#0), 
    s0#0: Map Box Box
       where $Is(s0#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s0#0, TMap(TSeq(TChar), TInt), $Heap), 
    c1#0: DatatypeType
       where $Is(c1#0, Tclass._module.com())
         && $IsAlloc(c1#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c1#0), 
    s1#0: Map Box Box
       where $Is(s1#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s1#0, TMap(TSeq(TChar), TInt), $Heap), 
    c2#0: DatatypeType
       where $Is(c2#0, Tclass._module.com())
         && $IsAlloc(c2#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c2#0), 
    s2#0: Map Box Box
       where $Is(s2#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s2#0, TMap(TSeq(TChar), TInt), $Heap));
  // user-defined preconditions
  requires _module.__default.small__step__star#canCall(c0#0, s0#0, c1#0, s1#0)
     ==> _module.__default.small__step__star($LS($LZ), c0#0, s0#0, c1#0, s1#0)
       || 
      (_module.com#Equal(c0#0, c1#0) && Map#Equal(s0#0, s1#0))
       || (exists c''#0: DatatypeType, s''#0: Map Box Box :: 
        { _module.__default.small__step__star($LS($LS($LZ)), c''#0, s''#0, c1#0, s1#0) } 
          { _module.__default.small__step($LS($LS($LZ)), c0#0, s0#0, c''#0, s''#0) } 
        $Is(c''#0, Tclass._module.com())
           && $Is(s''#0, TMap(TSeq(TChar), TInt))
           && 
          _module.__default.small__step($LS($LS($LZ)), c0#0, s0#0, c''#0, s''#0)
           && _module.__default.small__step__star($LS($LS($LZ)), c''#0, s''#0, c1#0, s1#0));
  requires _module.__default.small__step__star#canCall(c1#0, s1#0, c2#0, s2#0)
     ==> _module.__default.small__step__star($LS($LZ), c1#0, s1#0, c2#0, s2#0)
       || 
      (_module.com#Equal(c1#0, c2#0) && Map#Equal(s1#0, s2#0))
       || (exists c''#1: DatatypeType, s''#1: Map Box Box :: 
        { _module.__default.small__step__star($LS($LS($LZ)), c''#1, s''#1, c2#0, s2#0) } 
          { _module.__default.small__step($LS($LS($LZ)), c1#0, s1#0, c''#1, s''#1) } 
        $Is(c''#1, Tclass._module.com())
           && $Is(s''#1, TMap(TSeq(TChar), TInt))
           && 
          _module.__default.small__step($LS($LS($LZ)), c1#0, s1#0, c''#1, s''#1)
           && _module.__default.small__step__star($LS($LS($LZ)), c''#1, s''#1, c2#0, s2#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.small__step__star#canCall(c0#0, s0#0, c2#0, s2#0);
  free ensures _module.__default.small__step__star#canCall(c0#0, s0#0, c2#0, s2#0)
     && 
    _module.__default.small__step__star($LS($LZ), c0#0, s0#0, c2#0, s2#0)
     && ((_module.com#Equal(c0#0, c2#0) && Map#Equal(s0#0, s2#0))
       || (exists c''#2: DatatypeType, s''#2: Map Box Box :: 
        { _module.__default.small__step__star($LS($LZ), c''#2, s''#2, c2#0, s2#0) } 
          { _module.__default.small__step($LS($LZ), c0#0, s0#0, c''#2, s''#2) } 
        $Is(c''#2, Tclass._module.com())
           && $Is(s''#2, TMap(TSeq(TChar), TInt))
           && 
          _module.__default.small__step($LS($LZ), c0#0, s0#0, c''#2, s''#2)
           && _module.__default.small__step__star($LS($LZ), c''#2, s''#2, c2#0, s2#0)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction c0#0, s0#0, c1#0, s1#0, c2#0, s2#0} Impl$$_module.__default.star__transitive(c0#0: DatatypeType
       where $Is(c0#0, Tclass._module.com())
         && $IsAlloc(c0#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c0#0), 
    s0#0: Map Box Box
       where $Is(s0#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s0#0, TMap(TSeq(TChar), TInt), $Heap), 
    c1#0: DatatypeType
       where $Is(c1#0, Tclass._module.com())
         && $IsAlloc(c1#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c1#0), 
    s1#0: Map Box Box
       where $Is(s1#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s1#0, TMap(TSeq(TChar), TInt), $Heap), 
    c2#0: DatatypeType
       where $Is(c2#0, Tclass._module.com())
         && $IsAlloc(c2#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c2#0), 
    s2#0: Map Box Box
       where $Is(s2#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s2#0, TMap(TSeq(TChar), TInt), $Heap))
   returns ($_reverifyPost: bool);
  free requires 19 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.__default.small__step__star#canCall(c0#0, s0#0, c1#0, s1#0)
     && 
    _module.__default.small__step__star($LS($LZ), c0#0, s0#0, c1#0, s1#0)
     && ((_module.com#Equal(c0#0, c1#0) && Map#Equal(s0#0, s1#0))
       || (exists c''#3: DatatypeType, s''#3: Map Box Box :: 
        { _module.__default.small__step__star($LS($LZ), c''#3, s''#3, c1#0, s1#0) } 
          { _module.__default.small__step($LS($LZ), c0#0, s0#0, c''#3, s''#3) } 
        $Is(c''#3, Tclass._module.com())
           && $Is(s''#3, TMap(TSeq(TChar), TInt))
           && 
          _module.__default.small__step($LS($LZ), c0#0, s0#0, c''#3, s''#3)
           && _module.__default.small__step__star($LS($LZ), c''#3, s''#3, c1#0, s1#0)));
  free requires _module.__default.small__step__star#canCall(c1#0, s1#0, c2#0, s2#0)
     && 
    _module.__default.small__step__star($LS($LZ), c1#0, s1#0, c2#0, s2#0)
     && ((_module.com#Equal(c1#0, c2#0) && Map#Equal(s1#0, s2#0))
       || (exists c''#4: DatatypeType, s''#4: Map Box Box :: 
        { _module.__default.small__step__star($LS($LZ), c''#4, s''#4, c2#0, s2#0) } 
          { _module.__default.small__step($LS($LZ), c1#0, s1#0, c''#4, s''#4) } 
        $Is(c''#4, Tclass._module.com())
           && $Is(s''#4, TMap(TSeq(TChar), TInt))
           && 
          _module.__default.small__step($LS($LZ), c1#0, s1#0, c''#4, s''#4)
           && _module.__default.small__step__star($LS($LZ), c''#4, s''#4, c2#0, s2#0)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.small__step__star#canCall(c0#0, s0#0, c2#0, s2#0);
  ensures _module.__default.small__step__star#canCall(c0#0, s0#0, c2#0, s2#0)
     ==> _module.__default.small__step__star($LS($LZ), c0#0, s0#0, c2#0, s2#0)
       || 
      (_module.com#Equal(c0#0, c2#0) && Map#Equal(s0#0, s2#0))
       || (exists c''#5: DatatypeType, s''#5: Map Box Box :: 
        { _module.__default.small__step__star($LS($LS($LZ)), c''#5, s''#5, c2#0, s2#0) } 
          { _module.__default.small__step($LS($LS($LZ)), c0#0, s0#0, c''#5, s''#5) } 
        $Is(c''#5, Tclass._module.com())
           && $Is(s''#5, TMap(TSeq(TChar), TInt))
           && 
          _module.__default.small__step($LS($LS($LZ)), c0#0, s0#0, c''#5, s''#5)
           && _module.__default.small__step__star($LS($LS($LZ)), c''#5, s''#5, c2#0, s2#0));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction c0#0, s0#0, c1#0, s1#0, c2#0, s2#0} Impl$$_module.__default.star__transitive(c0#0: DatatypeType, 
    s0#0: Map Box Box, 
    c1#0: DatatypeType, 
    s1#0: Map Box Box, 
    c2#0: DatatypeType, 
    s2#0: Map Box Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var c0##0: DatatypeType;
  var s0##0: Map Box Box;
  var c1##0: DatatypeType;
  var s1##0: Map Box Box;
  var c2##0: DatatypeType;
  var s2##0: Map Box Box;

    // AddMethodImpl: star_transitive, Impl$$_module.__default.star__transitive
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(236,0): initial state"} true;
    assume $IsA#_module.com(c0#0);
    assume $IsA#_module.com(c1#0);
    assume $IsA#_module.com(c2#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#c00#0: DatatypeType, 
        $ih#s00#0: Map Box Box, 
        $ih#c10#0: DatatypeType, 
        $ih#s10#0: Map Box Box, 
        $ih#c20#0: DatatypeType, 
        $ih#s20#0: Map Box Box :: 
      $Is($ih#c00#0, Tclass._module.com())
           && $Is($ih#s00#0, TMap(TSeq(TChar), TInt))
           && $Is($ih#c10#0, Tclass._module.com())
           && $Is($ih#s10#0, TMap(TSeq(TChar), TInt))
           && $Is($ih#c20#0, Tclass._module.com())
           && $Is($ih#s20#0, TMap(TSeq(TChar), TInt))
           && 
          _module.__default.small__step__star($LS($LZ), $ih#c00#0, $ih#s00#0, $ih#c10#0, $ih#s10#0)
           && _module.__default.small__step__star($LS($LZ), $ih#c10#0, $ih#s10#0, $ih#c20#0, $ih#s20#0)
           && (DtRank($ih#c00#0) < DtRank(c0#0)
             || (DtRank($ih#c00#0) == DtRank(c0#0)
               && ((Set#Subset(Map#Domain($ih#s00#0), Map#Domain(s0#0))
                   && !Set#Subset(Map#Domain(s0#0), Map#Domain($ih#s00#0)))
                 || (Set#Equal(Map#Domain($ih#s00#0), Map#Domain(s0#0))
                   && (DtRank($ih#c10#0) < DtRank(c1#0)
                     || (DtRank($ih#c10#0) == DtRank(c1#0)
                       && ((Set#Subset(Map#Domain($ih#s10#0), Map#Domain(s1#0))
                           && !Set#Subset(Map#Domain(s1#0), Map#Domain($ih#s10#0)))
                         || (Set#Equal(Map#Domain($ih#s10#0), Map#Domain(s1#0))
                           && (DtRank($ih#c20#0) < DtRank(c2#0)
                             || (DtRank($ih#c20#0) == DtRank(c2#0)
                               && 
                              Set#Subset(Map#Domain($ih#s20#0), Map#Domain(s2#0))
                               && !Set#Subset(Map#Domain(s2#0), Map#Domain($ih#s20#0))))))))))))
         ==> _module.__default.small__step__star($LS($LZ), $ih#c00#0, $ih#s00#0, $ih#c20#0, $ih#s20#0));
    $_reverifyPost := false;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(237,22)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    c0##0 := c0#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    s0##0 := s0#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    c1##0 := c1#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    s1##0 := s1#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    c2##0 := c2#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    s2##0 := s2#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.star__transitive__aux(c0##0, s0##0, c1##0, s1##0, c2##0, s2##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(237,45)"} true;
}



procedure CheckWellformed$$_module.__default.star__transitive__aux(c0#0: DatatypeType
       where $Is(c0#0, Tclass._module.com())
         && $IsAlloc(c0#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c0#0), 
    s0#0: Map Box Box
       where $Is(s0#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s0#0, TMap(TSeq(TChar), TInt), $Heap), 
    c1#0: DatatypeType
       where $Is(c1#0, Tclass._module.com())
         && $IsAlloc(c1#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c1#0), 
    s1#0: Map Box Box
       where $Is(s1#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s1#0, TMap(TSeq(TChar), TInt), $Heap), 
    c2#0: DatatypeType
       where $Is(c2#0, Tclass._module.com())
         && $IsAlloc(c2#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c2#0), 
    s2#0: Map Box Box
       where $Is(s2#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s2#0, TMap(TSeq(TChar), TInt), $Heap));
  free requires 17 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.star__transitive__aux(c0#0: DatatypeType
       where $Is(c0#0, Tclass._module.com())
         && $IsAlloc(c0#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c0#0), 
    s0#0: Map Box Box
       where $Is(s0#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s0#0, TMap(TSeq(TChar), TInt), $Heap), 
    c1#0: DatatypeType
       where $Is(c1#0, Tclass._module.com())
         && $IsAlloc(c1#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c1#0), 
    s1#0: Map Box Box
       where $Is(s1#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s1#0, TMap(TSeq(TChar), TInt), $Heap), 
    c2#0: DatatypeType
       where $Is(c2#0, Tclass._module.com())
         && $IsAlloc(c2#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c2#0), 
    s2#0: Map Box Box
       where $Is(s2#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s2#0, TMap(TSeq(TChar), TInt), $Heap));
  // user-defined preconditions
  requires _module.__default.small__step__star#canCall(c0#0, s0#0, c1#0, s1#0)
     ==> _module.__default.small__step__star($LS($LZ), c0#0, s0#0, c1#0, s1#0)
       || 
      (_module.com#Equal(c0#0, c1#0) && Map#Equal(s0#0, s1#0))
       || (exists c''#0: DatatypeType, s''#0: Map Box Box :: 
        { _module.__default.small__step__star($LS($LS($LZ)), c''#0, s''#0, c1#0, s1#0) } 
          { _module.__default.small__step($LS($LS($LZ)), c0#0, s0#0, c''#0, s''#0) } 
        $Is(c''#0, Tclass._module.com())
           && $Is(s''#0, TMap(TSeq(TChar), TInt))
           && 
          _module.__default.small__step($LS($LS($LZ)), c0#0, s0#0, c''#0, s''#0)
           && _module.__default.small__step__star($LS($LS($LZ)), c''#0, s''#0, c1#0, s1#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.small__step__star#canCall(c1#0, s1#0, c2#0, s2#0)
     && (_module.__default.small__step__star($LS($LZ), c1#0, s1#0, c2#0, s2#0)
       ==> _module.__default.small__step__star#canCall(c0#0, s0#0, c2#0, s2#0));
  free ensures _module.__default.small__step__star($LS($LZ), c1#0, s1#0, c2#0, s2#0)
     ==> _module.__default.small__step__star#canCall(c0#0, s0#0, c2#0, s2#0)
       && 
      _module.__default.small__step__star($LS($LZ), c0#0, s0#0, c2#0, s2#0)
       && ((_module.com#Equal(c0#0, c2#0) && Map#Equal(s0#0, s2#0))
         || (exists c''#1: DatatypeType, s''#1: Map Box Box :: 
          { _module.__default.small__step__star($LS($LZ), c''#1, s''#1, c2#0, s2#0) } 
            { _module.__default.small__step($LS($LZ), c0#0, s0#0, c''#1, s''#1) } 
          $Is(c''#1, Tclass._module.com())
             && $Is(s''#1, TMap(TSeq(TChar), TInt))
             && 
            _module.__default.small__step($LS($LZ), c0#0, s0#0, c''#1, s''#1)
             && _module.__default.small__step__star($LS($LZ), c''#1, s''#1, c2#0, s2#0)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, c0#1, s0#1, c1#1, s1#1, c2#1, s2#1} CoCall$$_module.__default.star__transitive__aux_h(_k#0: Box, 
    c0#1: DatatypeType
       where $Is(c0#1, Tclass._module.com())
         && $IsAlloc(c0#1, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c0#1), 
    s0#1: Map Box Box
       where $Is(s0#1, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s0#1, TMap(TSeq(TChar), TInt), $Heap), 
    c1#1: DatatypeType
       where $Is(c1#1, Tclass._module.com())
         && $IsAlloc(c1#1, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c1#1), 
    s1#1: Map Box Box
       where $Is(s1#1, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s1#1, TMap(TSeq(TChar), TInt), $Heap), 
    c2#1: DatatypeType
       where $Is(c2#1, Tclass._module.com())
         && $IsAlloc(c2#1, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c2#1), 
    s2#1: Map Box Box
       where $Is(s2#1, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s2#1, TMap(TSeq(TChar), TInt), $Heap));
  // user-defined preconditions
  requires _module.__default.small__step__star_h#canCall(_k#0, c0#1, s0#1, c1#1, s1#1)
     ==> _module.__default.small__step__star_h($LS($LZ), _k#0, c0#1, s0#1, c1#1, s1#1)
       || (0 < ORD#Offset(_k#0)
         ==> (_module.com#Equal(c0#1, c1#1) && Map#Equal(s0#1, s1#1))
           || (exists c''#2: DatatypeType, s''#2: Map Box Box :: 
            { _module.__default.small__step__star_h($LS($LS($LZ)), ORD#Minus(_k#0, ORD#FromNat(1)), c''#2, s''#2, c1#1, s1#1) } 
              { _module.__default.small__step($LS($LS($LZ)), c0#1, s0#1, c''#2, s''#2) } 
            $Is(c''#2, Tclass._module.com())
               && $Is(s''#2, TMap(TSeq(TChar), TInt))
               && 
              _module.__default.small__step($LS($LS($LZ)), c0#1, s0#1, c''#2, s''#2)
               && _module.__default.small__step__star_h($LS($LS($LZ)), ORD#Minus(_k#0, ORD#FromNat(1)), c''#2, s''#2, c1#1, s1#1)));
  requires _module.__default.small__step__star_h#canCall(_k#0, c0#1, s0#1, c1#1, s1#1)
     ==> _module.__default.small__step__star_h($LS($LZ), _k#0, c0#1, s0#1, c1#1, s1#1)
       || (LitInt(0) == ORD#Offset(_k#0)
         ==> (exists _k'#0: Box :: 
          { _module.__default.small__step__star_h($LS($LZ), _k'#0, c0#1, s0#1, c1#1, s1#1) } 
          ORD#LessThanLimit(_k'#0, _k#0)
             && _module.__default.small__step__star_h($LS($LZ), _k'#0, c0#1, s0#1, c1#1, s1#1)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.small__step__star#canCall(c1#1, s1#1, c2#1, s2#1)
     && (_module.__default.small__step__star($LS($LZ), c1#1, s1#1, c2#1, s2#1)
       ==> _module.__default.small__step__star#canCall(c0#1, s0#1, c2#1, s2#1));
  free ensures _module.__default.small__step__star($LS($LZ), c1#1, s1#1, c2#1, s2#1)
     ==> _module.__default.small__step__star#canCall(c0#1, s0#1, c2#1, s2#1)
       && 
      _module.__default.small__step__star($LS($LZ), c0#1, s0#1, c2#1, s2#1)
       && ((_module.com#Equal(c0#1, c2#1) && Map#Equal(s0#1, s2#1))
         || (exists c''#3: DatatypeType, s''#3: Map Box Box :: 
          { _module.__default.small__step__star($LS($LZ), c''#3, s''#3, c2#1, s2#1) } 
            { _module.__default.small__step($LS($LZ), c0#1, s0#1, c''#3, s''#3) } 
          $Is(c''#3, Tclass._module.com())
             && $Is(s''#3, TMap(TSeq(TChar), TInt))
             && 
            _module.__default.small__step($LS($LZ), c0#1, s0#1, c''#3, s''#3)
             && _module.__default.small__step__star($LS($LZ), c''#3, s''#3, c2#1, s2#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, c0#1, s0#1, c1#1, s1#1, c2#1, s2#1} Impl$$_module.__default.star__transitive__aux_h(_k#0: Box, 
    c0#1: DatatypeType
       where $Is(c0#1, Tclass._module.com())
         && $IsAlloc(c0#1, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c0#1), 
    s0#1: Map Box Box
       where $Is(s0#1, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s0#1, TMap(TSeq(TChar), TInt), $Heap), 
    c1#1: DatatypeType
       where $Is(c1#1, Tclass._module.com())
         && $IsAlloc(c1#1, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c1#1), 
    s1#1: Map Box Box
       where $Is(s1#1, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s1#1, TMap(TSeq(TChar), TInt), $Heap), 
    c2#1: DatatypeType
       where $Is(c2#1, Tclass._module.com())
         && $IsAlloc(c2#1, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c2#1), 
    s2#1: Map Box Box
       where $Is(s2#1, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s2#1, TMap(TSeq(TChar), TInt), $Heap))
   returns ($_reverifyPost: bool);
  free requires 18 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.__default.small__step__star_h#canCall(_k#0, c0#1, s0#1, c1#1, s1#1)
     && 
    _module.__default.small__step__star_h($LS($LZ), _k#0, c0#1, s0#1, c1#1, s1#1)
     && 
    (0 < ORD#Offset(_k#0)
       ==> (_module.com#Equal(c0#1, c1#1) && Map#Equal(s0#1, s1#1))
         || (exists c''#4: DatatypeType, s''#4: Map Box Box :: 
          { _module.__default.small__step__star_h($LS($LZ), ORD#Minus(_k#0, ORD#FromNat(1)), c''#4, s''#4, c1#1, s1#1) } 
            { _module.__default.small__step($LS($LZ), c0#1, s0#1, c''#4, s''#4) } 
          $Is(c''#4, Tclass._module.com())
             && $Is(s''#4, TMap(TSeq(TChar), TInt))
             && 
            _module.__default.small__step($LS($LZ), c0#1, s0#1, c''#4, s''#4)
             && _module.__default.small__step__star_h($LS($LZ), ORD#Minus(_k#0, ORD#FromNat(1)), c''#4, s''#4, c1#1, s1#1)))
     && (LitInt(0) == ORD#Offset(_k#0)
       ==> (exists _k'#1: Box :: 
        { _module.__default.small__step__star_h($LS($LZ), _k'#1, c0#1, s0#1, c1#1, s1#1) } 
        ORD#LessThanLimit(_k'#1, _k#0)
           && _module.__default.small__step__star_h($LS($LZ), _k'#1, c0#1, s0#1, c1#1, s1#1)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.small__step__star#canCall(c1#1, s1#1, c2#1, s2#1)
     && (_module.__default.small__step__star($LS($LZ), c1#1, s1#1, c2#1, s2#1)
       ==> _module.__default.small__step__star#canCall(c0#1, s0#1, c2#1, s2#1));
  ensures _module.__default.small__step__star($LS($LZ), c1#1, s1#1, c2#1, s2#1)
     ==> 
    _module.__default.small__step__star#canCall(c0#1, s0#1, c2#1, s2#1)
     ==> _module.__default.small__step__star($LS($LZ), c0#1, s0#1, c2#1, s2#1)
       || 
      (_module.com#Equal(c0#1, c2#1) && Map#Equal(s0#1, s2#1))
       || (exists c''#5: DatatypeType, s''#5: Map Box Box :: 
        { _module.__default.small__step__star($LS($LS($LZ)), c''#5, s''#5, c2#1, s2#1) } 
          { _module.__default.small__step($LS($LS($LZ)), c0#1, s0#1, c''#5, s''#5) } 
        $Is(c''#5, Tclass._module.com())
           && $Is(s''#5, TMap(TSeq(TChar), TInt))
           && 
          _module.__default.small__step($LS($LS($LZ)), c0#1, s0#1, c''#5, s''#5)
           && _module.__default.small__step__star($LS($LS($LZ)), c''#5, s''#5, c2#1, s2#1));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0, c0#1, s0#1, c1#1, s1#1, c2#1, s2#1} Impl$$_module.__default.star__transitive__aux_h(_k#0: Box, 
    c0#1: DatatypeType, 
    s0#1: Map Box Box, 
    c1#1: DatatypeType, 
    s1#1: Map Box Box, 
    c2#1: DatatypeType, 
    s2#1: Map Box Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var $initHeapForallStmt#1: Heap;

    // AddMethodImpl: star_transitive_aux#, Impl$$_module.__default.star__transitive__aux_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(239,12): initial state"} true;
    assume $IsA#_module.com(c0#1);
    assume $IsA#_module.com(c1#1);
    assume $IsA#_module.com(c2#1);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: Box, 
        $ih#c00#0: DatatypeType, 
        $ih#s00#0: Map Box Box, 
        $ih#c10#0: DatatypeType, 
        $ih#s10#0: Map Box Box, 
        $ih#c20#0: DatatypeType, 
        $ih#s20#0: Map Box Box :: 
      $Is($ih#c00#0, Tclass._module.com())
           && $Is($ih#s00#0, TMap(TSeq(TChar), TInt))
           && $Is($ih#c10#0, Tclass._module.com())
           && $Is($ih#s10#0, TMap(TSeq(TChar), TInt))
           && $Is($ih#c20#0, Tclass._module.com())
           && $Is($ih#s20#0, TMap(TSeq(TChar), TInt))
           && _module.__default.small__step__star_h($LS($LZ), $ih#_k0#0, $ih#c00#0, $ih#s00#0, $ih#c10#0, $ih#s10#0)
           && (ORD#Less($ih#_k0#0, _k#0)
             || ($ih#_k0#0 == _k#0
               && (DtRank($ih#c00#0) < DtRank(c0#1)
                 || (DtRank($ih#c00#0) == DtRank(c0#1)
                   && ((Set#Subset(Map#Domain($ih#s00#0), Map#Domain(s0#1))
                       && !Set#Subset(Map#Domain(s0#1), Map#Domain($ih#s00#0)))
                     || (Set#Equal(Map#Domain($ih#s00#0), Map#Domain(s0#1))
                       && (DtRank($ih#c10#0) < DtRank(c1#1)
                         || (DtRank($ih#c10#0) == DtRank(c1#1)
                           && ((Set#Subset(Map#Domain($ih#s10#0), Map#Domain(s1#1))
                               && !Set#Subset(Map#Domain(s1#1), Map#Domain($ih#s10#0)))
                             || (Set#Equal(Map#Domain($ih#s10#0), Map#Domain(s1#1))
                               && (DtRank($ih#c20#0) < DtRank(c2#1)
                                 || (DtRank($ih#c20#0) == DtRank(c2#1)
                                   && 
                                  Set#Subset(Map#Domain($ih#s20#0), Map#Domain(s2#1))
                                   && !Set#Subset(Map#Domain(s2#1), Map#Domain($ih#s20#0))))))))))))))
         ==> 
        _module.__default.small__step__star($LS($LZ), $ih#c10#0, $ih#s10#0, $ih#c20#0, $ih#s20#0)
         ==> _module.__default.small__step__star($LS($LZ), $ih#c00#0, $ih#s00#0, $ih#c20#0, $ih#s20#0));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(242,1)
    assume true;
    if (0 < ORD#Offset(_k#0))
    {
    }
    else
    {
        // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(239,13)
        $initHeapForallStmt#1 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#1 == $Heap;
        assume (forall _k'#2: Box, 
            c0#2: DatatypeType, 
            s0#2: Map Box Box, 
            c1#2: DatatypeType, 
            s1#2: Map Box Box, 
            c2#2: DatatypeType, 
            s2#2: Map Box Box :: 
          $Is(c0#2, Tclass._module.com())
               && $Is(s0#2, TMap(TSeq(TChar), TInt))
               && $Is(c1#2, Tclass._module.com())
               && $Is(s1#2, TMap(TSeq(TChar), TInt))
               && $Is(c2#2, Tclass._module.com())
               && $Is(s2#2, TMap(TSeq(TChar), TInt))
               && 
              ORD#Less(_k'#2, _k#0)
               && _module.__default.small__step__star_h($LS($LZ), _k'#2, c0#2, s0#2, c1#2, s1#2)
             ==> 
            _module.__default.small__step__star($LS($LZ), c1#2, s1#2, c2#2, s2#2)
             ==> _module.__default.small__step__star($LS($LZ), c0#2, s0#2, c2#2, s2#2));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(239,12)"} true;
    }
}



procedure CheckWellformed$$_module.__default.BigStep__implies__SmallStepStar(c#0: DatatypeType
       where $Is(c#0, Tclass._module.com())
         && $IsAlloc(c#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#0), 
    s#0: Map Box Box
       where $Is(s#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s#0, TMap(TSeq(TChar), TInt), $Heap), 
    t#0: Map Box Box
       where $Is(t#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(t#0, TMap(TSeq(TChar), TInt), $Heap));
  free requires 21 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.BigStep__implies__SmallStepStar(c#0: DatatypeType
       where $Is(c#0, Tclass._module.com())
         && $IsAlloc(c#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#0), 
    s#0: Map Box Box
       where $Is(s#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s#0, TMap(TSeq(TChar), TInt), $Heap), 
    t#0: Map Box Box
       where $Is(t#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(t#0, TMap(TSeq(TChar), TInt), $Heap));
  // user-defined preconditions
  requires _module.__default.big__step($LS($LS($LZ)), c#0, s#0, t#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.small__step__star#canCall(c#0, s#0, Lit(#_module.com.SKIP()), t#0);
  free ensures _module.__default.small__step__star#canCall(c#0, s#0, Lit(#_module.com.SKIP()), t#0)
     && 
    _module.__default.small__step__star($LS($LZ), c#0, s#0, Lit(#_module.com.SKIP()), t#0)
     && ((_module.com#Equal(c#0, #_module.com.SKIP()) && Map#Equal(s#0, t#0))
       || (exists c''#0: DatatypeType, s''#0: Map Box Box :: 
        { _module.__default.small__step__star($LS($LZ), c''#0, s''#0, #_module.com.SKIP(), t#0) } 
          { _module.__default.small__step($LS($LZ), c#0, s#0, c''#0, s''#0) } 
        $Is(c''#0, Tclass._module.com())
           && $Is(s''#0, TMap(TSeq(TChar), TInt))
           && 
          _module.__default.small__step($LS($LZ), c#0, s#0, c''#0, s''#0)
           && _module.__default.small__step__star($LS($LZ), c''#0, s''#0, Lit(#_module.com.SKIP()), t#0)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, c#1, s#1, t#1} CoCall$$_module.__default.BigStep__implies__SmallStepStar_h(_k#0: Box, 
    c#1: DatatypeType
       where $Is(c#1, Tclass._module.com())
         && $IsAlloc(c#1, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#1), 
    s#1: Map Box Box
       where $Is(s#1, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s#1, TMap(TSeq(TChar), TInt), $Heap), 
    t#1: Map Box Box
       where $Is(t#1, TMap(TSeq(TChar), TInt))
         && $IsAlloc(t#1, TMap(TSeq(TChar), TInt), $Heap));
  // user-defined preconditions
  requires _module.__default.big__step_h($LS($LS($LZ)), _k#0, c#1, s#1, t#1);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.small__step__star#canCall(c#1, s#1, Lit(#_module.com.SKIP()), t#1);
  free ensures _module.__default.small__step__star#canCall(c#1, s#1, Lit(#_module.com.SKIP()), t#1)
     && 
    _module.__default.small__step__star($LS($LZ), c#1, s#1, Lit(#_module.com.SKIP()), t#1)
     && ((_module.com#Equal(c#1, #_module.com.SKIP()) && Map#Equal(s#1, t#1))
       || (exists c''#1: DatatypeType, s''#1: Map Box Box :: 
        { _module.__default.small__step__star($LS($LZ), c''#1, s''#1, #_module.com.SKIP(), t#1) } 
          { _module.__default.small__step($LS($LZ), c#1, s#1, c''#1, s''#1) } 
        $Is(c''#1, Tclass._module.com())
           && $Is(s''#1, TMap(TSeq(TChar), TInt))
           && 
          _module.__default.small__step($LS($LZ), c#1, s#1, c''#1, s''#1)
           && _module.__default.small__step__star($LS($LZ), c''#1, s''#1, Lit(#_module.com.SKIP()), t#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, c#1, s#1, t#1} Impl$$_module.__default.BigStep__implies__SmallStepStar_h(_k#0: Box, 
    c#1: DatatypeType
       where $Is(c#1, Tclass._module.com())
         && $IsAlloc(c#1, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#1), 
    s#1: Map Box Box
       where $Is(s#1, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s#1, TMap(TSeq(TChar), TInt), $Heap), 
    t#1: Map Box Box
       where $Is(t#1, TMap(TSeq(TChar), TInt))
         && $IsAlloc(t#1, TMap(TSeq(TChar), TInt), $Heap))
   returns ($_reverifyPost: bool);
  free requires 22 == $FunctionContextHeight;
  // user-defined preconditions
  requires _module.__default.big__step_h($LS($LS($LZ)), _k#0, c#1, s#1, t#1);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.small__step__star#canCall(c#1, s#1, Lit(#_module.com.SKIP()), t#1);
  ensures _module.__default.small__step__star#canCall(c#1, s#1, Lit(#_module.com.SKIP()), t#1)
     ==> _module.__default.small__step__star($LS($LZ), c#1, s#1, Lit(#_module.com.SKIP()), t#1)
       || 
      (_module.com#Equal(c#1, #_module.com.SKIP()) && Map#Equal(s#1, t#1))
       || (exists c''#2: DatatypeType, s''#2: Map Box Box :: 
        { _module.__default.small__step__star($LS($LS($LZ)), c''#2, s''#2, #_module.com.SKIP(), t#1) } 
          { _module.__default.small__step($LS($LS($LZ)), c#1, s#1, c''#2, s''#2) } 
        $Is(c''#2, Tclass._module.com())
           && $Is(s''#2, TMap(TSeq(TChar), TInt))
           && 
          _module.__default.small__step($LS($LS($LZ)), c#1, s#1, c''#2, s''#2)
           && _module.__default.small__step__star($LS($LS($LZ)), c''#2, s''#2, Lit(#_module.com.SKIP()), t#1));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0, c#1, s#1, t#1} Impl$$_module.__default.BigStep__implies__SmallStepStar_h(_k#0: Box, c#1: DatatypeType, s#1: Map Box Box, t#1: Map Box Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var _mcc#7#0: DatatypeType;
  var _mcc#8#0: DatatypeType;
  var body#0: DatatypeType;
  var let#0_0_0#0#0: DatatypeType;
  var b#0: DatatypeType;
  var let#0_0_1#0#0: DatatypeType;
  var ##b#0: DatatypeType;
  var ##s#2: Map Box Box;
  var ##c#2: DatatypeType;
  var ##s#3: Map Box Box;
  var ##c'#1: DatatypeType;
  var ##s'#1: Map Box Box;
  var ##c#3: DatatypeType;
  var ##s#4: Map Box Box;
  var ##c'#2: DatatypeType;
  var ##s'#2: Map Box Box;
  var ##c#4: DatatypeType;
  var ##s#5: Map Box Box;
  var ##c'#3: DatatypeType;
  var ##s'#3: Map Box Box;
  var ##c#5: DatatypeType;
  var ##s#6: Map Box Box;
  var ##c'#4: DatatypeType;
  var ##s'#4: Map Box Box;
  var ##c#6: DatatypeType;
  var ##s#7: Map Box Box;
  var ##c'#5: DatatypeType;
  var ##s'#5: Map Box Box;
  var ##c#7: DatatypeType;
  var ##s#8: Map Box Box;
  var ##c'#6: DatatypeType;
  var ##s'#6: Map Box Box;
  var ##c#8: DatatypeType;
  var ##s#9: Map Box Box;
  var ##c'#7: DatatypeType;
  var ##s'#7: Map Box Box;
  var s'#0: Map Box Box
     where $Is(s'#0, TMap(TSeq(TChar), TInt))
       && $IsAlloc(s'#0, TMap(TSeq(TChar), TInt), $Heap);
  var s'#1: Map Box Box;
  var ##_k#0: Box;
  var ##c#9: DatatypeType;
  var ##s#10: Map Box Box;
  var ##t#1: Map Box Box;
  var ##_k#1: Box;
  var ##c#10: DatatypeType;
  var ##s#11: Map Box Box;
  var ##t#2: Map Box Box;
  var ##c#11: DatatypeType;
  var ##s#12: Map Box Box;
  var ##c'#8: DatatypeType;
  var ##s'#8: Map Box Box;
  var ##c#12: DatatypeType;
  var ##s#13: Map Box Box;
  var ##c'#9: DatatypeType;
  var ##s'#9: Map Box Box;
  var ##c#13: DatatypeType;
  var ##s#14: Map Box Box;
  var ##c'#10: DatatypeType;
  var ##s'#10: Map Box Box;
  var ##c#14: DatatypeType;
  var ##s#15: Map Box Box;
  var ##c'#11: DatatypeType;
  var ##s'#11: Map Box Box;
  var ##c#15: DatatypeType;
  var ##s#16: Map Box Box;
  var ##c'#12: DatatypeType;
  var ##s'#12: Map Box Box;
  var ##c#16: DatatypeType;
  var ##s#17: Map Box Box;
  var ##c'#13: DatatypeType;
  var ##s'#13: Map Box Box;
  var ##c#17: DatatypeType;
  var ##s#18: Map Box Box;
  var ##c'#14: DatatypeType;
  var ##s'#14: Map Box Box;
  var ##c#18: DatatypeType;
  var ##s#19: Map Box Box;
  var ##c'#15: DatatypeType;
  var ##s'#15: Map Box Box;
  var ##c#19: DatatypeType;
  var ##s#20: Map Box Box;
  var ##c'#16: DatatypeType;
  var ##s'#16: Map Box Box;
  var c0##0: DatatypeType;
  var s0##0: Map Box Box;
  var c##0: DatatypeType;
  var t##0: Map Box Box;
  var c1##0: DatatypeType;
  var ##c#20: DatatypeType;
  var ##s#21: Map Box Box;
  var ##c'#17: DatatypeType;
  var ##s'#17: Map Box Box;
  var ##c#21: DatatypeType;
  var ##s#22: Map Box Box;
  var ##c'#18: DatatypeType;
  var ##s'#18: Map Box Box;
  var ##c#22: DatatypeType;
  var ##s#23: Map Box Box;
  var ##c'#19: DatatypeType;
  var ##s'#19: Map Box Box;
  var ##c#23: DatatypeType;
  var ##s#24: Map Box Box;
  var ##c'#20: DatatypeType;
  var ##s'#20: Map Box Box;
  var c0##1: DatatypeType;
  var s0##1: Map Box Box;
  var c1##1: DatatypeType;
  var s1##0: Map Box Box;
  var c2##0: DatatypeType;
  var s2##0: Map Box Box;
  var ##c#24: DatatypeType;
  var ##s#25: Map Box Box;
  var ##c'#21: DatatypeType;
  var ##s'#21: Map Box Box;
  var ##c#25: DatatypeType;
  var ##s#26: Map Box Box;
  var ##c'#22: DatatypeType;
  var ##s'#22: Map Box Box;
  var ##c#26: DatatypeType;
  var ##s#27: Map Box Box;
  var ##c'#23: DatatypeType;
  var ##s'#23: Map Box Box;
  var ##c#27: DatatypeType;
  var ##s#28: Map Box Box;
  var ##c'#24: DatatypeType;
  var ##s'#24: Map Box Box;
  var ##c#28: DatatypeType;
  var ##s#29: Map Box Box;
  var ##c'#25: DatatypeType;
  var ##s'#25: Map Box Box;
  var ##c#29: DatatypeType;
  var ##s#30: Map Box Box;
  var ##c'#26: DatatypeType;
  var ##s'#26: Map Box Box;
  var ##c#30: DatatypeType;
  var ##s#31: Map Box Box;
  var ##c'#27: DatatypeType;
  var ##s'#27: Map Box Box;
  var _mcc#4#0: DatatypeType;
  var _mcc#5#0: DatatypeType;
  var _mcc#6#0: DatatypeType;
  var els#0: DatatypeType;
  var let#0_1_0#0#0: DatatypeType;
  var thn#0: DatatypeType;
  var let#0_1_1#0#0: DatatypeType;
  var b#1: DatatypeType;
  var let#0_1_2#0#0: DatatypeType;
  var _mcc#2#0: DatatypeType;
  var _mcc#3#0: DatatypeType;
  var c1#0: DatatypeType;
  var let#0_2_0#0#0: DatatypeType;
  var c0#0: DatatypeType;
  var let#0_2_1#0#0: DatatypeType;
  var s'#2: Map Box Box
     where $Is(s'#2, TMap(TSeq(TChar), TInt))
       && $IsAlloc(s'#2, TMap(TSeq(TChar), TInt), $Heap);
  var s'#3: Map Box Box;
  var ##_k#2: Box;
  var ##c#31: DatatypeType;
  var ##s#32: Map Box Box;
  var ##t#3: Map Box Box;
  var ##_k#3: Box;
  var ##c#32: DatatypeType;
  var ##s#33: Map Box Box;
  var ##t#4: Map Box Box;
  var ##c#33: DatatypeType;
  var ##s#34: Map Box Box;
  var ##c'#28: DatatypeType;
  var ##s'#28: Map Box Box;
  var ##c#34: DatatypeType;
  var ##s#35: Map Box Box;
  var ##c'#29: DatatypeType;
  var ##s'#29: Map Box Box;
  var ##c#35: DatatypeType;
  var ##s#36: Map Box Box;
  var ##c'#30: DatatypeType;
  var ##s'#30: Map Box Box;
  var ##c#36: DatatypeType;
  var ##s#37: Map Box Box;
  var ##c'#31: DatatypeType;
  var ##s'#31: Map Box Box;
  var ##c#37: DatatypeType;
  var ##s#38: Map Box Box;
  var ##c'#32: DatatypeType;
  var ##s'#32: Map Box Box;
  var ##c#38: DatatypeType;
  var ##s#39: Map Box Box;
  var ##c'#33: DatatypeType;
  var ##s'#33: Map Box Box;
  var ##c#39: DatatypeType;
  var ##s#40: Map Box Box;
  var ##c'#34: DatatypeType;
  var ##s'#34: Map Box Box;
  var ##c#40: DatatypeType;
  var ##s#41: Map Box Box;
  var ##c'#35: DatatypeType;
  var ##s'#35: Map Box Box;
  var ##c#41: DatatypeType;
  var ##s#42: Map Box Box;
  var ##c'#36: DatatypeType;
  var ##s'#36: Map Box Box;
  var c0##2: DatatypeType;
  var s0##2: Map Box Box;
  var c##1: DatatypeType;
  var t##1: Map Box Box;
  var c1##2: DatatypeType;
  var ##c#42: DatatypeType;
  var ##s#43: Map Box Box;
  var ##c'#37: DatatypeType;
  var ##s'#37: Map Box Box;
  var ##c#43: DatatypeType;
  var ##s#44: Map Box Box;
  var ##c'#38: DatatypeType;
  var ##s'#38: Map Box Box;
  var ##c#44: DatatypeType;
  var ##s#45: Map Box Box;
  var ##c'#39: DatatypeType;
  var ##s'#39: Map Box Box;
  var ##c#45: DatatypeType;
  var ##s#46: Map Box Box;
  var ##c'#40: DatatypeType;
  var ##s'#40: Map Box Box;
  var c0##3: DatatypeType;
  var s0##3: Map Box Box;
  var c1##3: DatatypeType;
  var s1##1: Map Box Box;
  var c2##1: DatatypeType;
  var s2##1: Map Box Box;
  var ##c#46: DatatypeType;
  var ##s#47: Map Box Box;
  var ##c'#41: DatatypeType;
  var ##s'#41: Map Box Box;
  var _mcc#0#0: Seq Box;
  var _mcc#1#0: DatatypeType;
  var a#0: DatatypeType;
  var let#0_3_0#0#0: DatatypeType;
  var x#0: Seq Box;
  var let#0_3_1#0#0: Seq Box;
  var ##c#47: DatatypeType;
  var ##s#48: Map Box Box;
  var ##c'#42: DatatypeType;
  var ##s'#42: Map Box Box;
  var $initHeapForallStmt#1: Heap;

    // AddMethodImpl: BigStep_implies_SmallStepStar#, Impl$$_module.__default.BigStep__implies__SmallStepStar_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(246,12): initial state"} true;
    assume $IsA#_module.com(c#1);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: Box, 
        $ih#c0#0: DatatypeType, 
        $ih#s0#0: Map Box Box, 
        $ih#t0#0: Map Box Box :: 
      $Is($ih#c0#0, Tclass._module.com())
           && $Is($ih#s0#0, TMap(TSeq(TChar), TInt))
           && $Is($ih#t0#0, TMap(TSeq(TChar), TInt))
           && _module.__default.big__step_h($LS($LZ), $ih#_k0#0, $ih#c0#0, $ih#s0#0, $ih#t0#0)
           && (ORD#Less($ih#_k0#0, _k#0)
             || ($ih#_k0#0 == _k#0
               && (DtRank($ih#c0#0) < DtRank(c#1)
                 || (DtRank($ih#c0#0) == DtRank(c#1)
                   && ((Set#Subset(Map#Domain($ih#s0#0), Map#Domain(s#1))
                       && !Set#Subset(Map#Domain(s#1), Map#Domain($ih#s0#0)))
                     || (Set#Equal(Map#Domain($ih#s0#0), Map#Domain(s#1))
                       && 
                      Set#Subset(Map#Domain($ih#t0#0), Map#Domain(t#1))
                       && !Set#Subset(Map#Domain(t#1), Map#Domain($ih#t0#0))))))))
         ==> _module.__default.small__step__star($LS($LZ), $ih#c0#0, $ih#s0#0, Lit(#_module.com.SKIP()), $ih#t0#0));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(249,1)
    assume true;
    if (0 < ORD#Offset(_k#0))
    {
        assume true;
        havoc _mcc#7#0, _mcc#8#0;
        havoc _mcc#4#0, _mcc#5#0, _mcc#6#0;
        havoc _mcc#2#0, _mcc#3#0;
        havoc _mcc#0#0, _mcc#1#0;
        if (c#1 == #_module.com.SKIP())
        {
        }
        else if (c#1 == #_module.com.Assign(_mcc#0#0, _mcc#1#0))
        {
            assume $Is(_mcc#0#0, TSeq(TChar)) && $IsAlloc(_mcc#0#0, TSeq(TChar), $Heap);
            assume $Is(_mcc#1#0, Tclass._module.aexp())
               && $IsAlloc(_mcc#1#0, Tclass._module.aexp(), $Heap);
            havoc a#0;
            assume $Is(a#0, Tclass._module.aexp()) && $IsAlloc(a#0, Tclass._module.aexp(), $Heap);
            assume let#0_3_0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0_3_0#0#0, Tclass._module.aexp());
            assume a#0 == let#0_3_0#0#0;
            havoc x#0;
            assume $Is(x#0, TSeq(TChar)) && $IsAlloc(x#0, TSeq(TChar), $Heap);
            assume let#0_3_1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0_3_1#0#0, TSeq(TChar));
            assume x#0 == let#0_3_1#0#0;
            // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(254,5)
            ##c#47 := Lit(#_module.com.SKIP());
            // assume allocatedness for argument to function
            assume $IsAlloc(##c#47, Tclass._module.com(), $Heap);
            ##s#48 := t#1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#48, TMap(TSeq(TChar), TInt), $Heap);
            ##c'#42 := Lit(#_module.com.SKIP());
            // assume allocatedness for argument to function
            assume $IsAlloc(##c'#42, Tclass._module.com(), $Heap);
            ##s'#42 := t#1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s'#42, TMap(TSeq(TChar), TInt), $Heap);
            assume _module.__default.small__step__star#canCall(Lit(#_module.com.SKIP()), t#1, Lit(#_module.com.SKIP()), t#1);
            assume _module.__default.small__step__star#canCall(Lit(#_module.com.SKIP()), t#1, Lit(#_module.com.SKIP()), t#1);
            assert {:subsumption 0} _module.__default.small__step__star#canCall(Lit(#_module.com.SKIP()), t#1, Lit(#_module.com.SKIP()), t#1)
               ==> _module.__default.small__step__star($LS($LZ), Lit(#_module.com.SKIP()), t#1, Lit(#_module.com.SKIP()), t#1)
                 || 
                (_module.com#Equal(#_module.com.SKIP(), #_module.com.SKIP())
                   && Map#Equal(t#1, t#1))
                 || (exists c''#22: DatatypeType, s''#22: Map Box Box :: 
                  { _module.__default.small__step__star($LS($LZ), c''#22, s''#22, #_module.com.SKIP(), t#1) } 
                    { _module.__default.small__step($LS($LZ), #_module.com.SKIP(), t#1, c''#22, s''#22) } 
                  $Is(c''#22, Tclass._module.com())
                     && $Is(s''#22, TMap(TSeq(TChar), TInt))
                     && 
                    _module.__default.small__step($LS($LZ), Lit(#_module.com.SKIP()), t#1, c''#22, s''#22)
                     && _module.__default.small__step__star($LS($LZ), c''#22, s''#22, Lit(#_module.com.SKIP()), t#1));
            assume _module.__default.small__step__star($LS($LS($LZ)), Lit(#_module.com.SKIP()), t#1, Lit(#_module.com.SKIP()), t#1);
        }
        else if (c#1 == #_module.com.Seq(_mcc#2#0, _mcc#3#0))
        {
            assume $Is(_mcc#2#0, Tclass._module.com())
               && $IsAlloc(_mcc#2#0, Tclass._module.com(), $Heap);
            assume $Is(_mcc#3#0, Tclass._module.com())
               && $IsAlloc(_mcc#3#0, Tclass._module.com(), $Heap);
            havoc c1#0;
            assume $Is(c1#0, Tclass._module.com()) && $IsAlloc(c1#0, Tclass._module.com(), $Heap);
            assume let#0_2_0#0#0 == _mcc#3#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0_2_0#0#0, Tclass._module.com());
            assume c1#0 == let#0_2_0#0#0;
            havoc c0#0;
            assume $Is(c0#0, Tclass._module.com()) && $IsAlloc(c0#0, Tclass._module.com(), $Heap);
            assume let#0_2_1#0#0 == _mcc#2#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0_2_1#0#0, Tclass._module.com());
            assume c0#0 == let#0_2_1#0#0;
            // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(256,12)
            havoc s'#3;
            if ($Is(s'#3, TMap(TSeq(TChar), TInt))
               && $IsAlloc(s'#3, TMap(TSeq(TChar), TInt), $Heap))
            {
                assert ORD#IsNat(Lit(ORD#FromNat(1)));
                assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
                ##_k#2 := ORD#Minus(_k#0, ORD#FromNat(1));
                // assume allocatedness for argument to function
                assume $IsAlloc(##_k#2, TORDINAL, $Heap);
                ##c#31 := c0#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##c#31, Tclass._module.com(), $Heap);
                ##s#32 := s#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#32, TMap(TSeq(TChar), TInt), $Heap);
                ##t#3 := s'#3;
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#3, TMap(TSeq(TChar), TInt), $Heap);
                assume _module.__default.big__step_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), c0#0, s#1, s'#3);
                if (_module.__default.big__step_h($LS($LZ), ORD#Minus(_k#0, ORD#FromNat(1)), c0#0, s#1, s'#3))
                {
                    assert ORD#IsNat(Lit(ORD#FromNat(1)));
                    assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
                    ##_k#3 := ORD#Minus(_k#0, ORD#FromNat(1));
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##_k#3, TORDINAL, $Heap);
                    ##c#32 := c1#0;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c#32, Tclass._module.com(), $Heap);
                    ##s#33 := s'#3;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s#33, TMap(TSeq(TChar), TInt), $Heap);
                    ##t#4 := t#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##t#4, TMap(TSeq(TChar), TInt), $Heap);
                    assume _module.__default.big__step_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), c1#0, s'#3, t#1);
                }

                assume _module.__default.big__step_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), c0#0, s#1, s'#3)
                   && (_module.__default.big__step_h($LS($LZ), ORD#Minus(_k#0, ORD#FromNat(1)), c0#0, s#1, s'#3)
                     ==> _module.__default.big__step_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), c1#0, s'#3, t#1));
            }

            assert (exists $as#s'0_2_0#0: Map Box Box :: 
              $Is($as#s'0_2_0#0, TMap(TSeq(TChar), TInt))
                 && 
                _module.__default.big__step_h($LS($LZ), ORD#Minus(_k#0, ORD#FromNat(1)), c0#0, s#1, $as#s'0_2_0#0)
                 && _module.__default.big__step_h($LS($LZ), ORD#Minus(_k#0, ORD#FromNat(1)), c1#0, $as#s'0_2_0#0, t#1));
            havoc s'#2;
            assume _module.__default.big__step_h($LS($LZ), ORD#Minus(_k#0, ORD#FromNat(1)), c0#0, s#1, s'#2)
               && _module.__default.big__step_h($LS($LZ), ORD#Minus(_k#0, ORD#FromNat(1)), c1#0, s'#2, t#1);
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(256,56)"} true;
            // ----- calc statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(257,5)
            // Assume Fuel Constant
            if (*)
            {
                // ----- assert wf[initial] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(257,5)
                assume true;
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(257,5)
                ##c#44 := #_module.com.Seq(c0#0, c1#0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##c#44, Tclass._module.com(), $Heap);
                ##s#45 := s#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#45, TMap(TSeq(TChar), TInt), $Heap);
                ##c'#39 := #_module.com.Seq(Lit(#_module.com.SKIP()), c1#0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##c'#39, Tclass._module.com(), $Heap);
                ##s'#39 := s'#2;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s'#39, TMap(TSeq(TChar), TInt), $Heap);
                assume _module.__default.small__step__star#canCall(#_module.com.Seq(c0#0, c1#0), 
                  s#1, 
                  #_module.com.Seq(Lit(#_module.com.SKIP()), c1#0), 
                  s'#2);
                if (_module.__default.small__step__star($LS($LZ), 
                  #_module.com.Seq(c0#0, c1#0), 
                  s#1, 
                  #_module.com.Seq(Lit(#_module.com.SKIP()), c1#0), 
                  s'#2))
                {
                    ##c#45 := #_module.com.Seq(Lit(#_module.com.SKIP()), c1#0);
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c#45, Tclass._module.com(), $Heap);
                    ##s#46 := s'#2;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s#46, TMap(TSeq(TChar), TInt), $Heap);
                    ##c'#40 := Lit(#_module.com.SKIP());
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c'#40, Tclass._module.com(), $Heap);
                    ##s'#40 := t#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s'#40, TMap(TSeq(TChar), TInt), $Heap);
                    assume _module.__default.small__step__star#canCall(#_module.com.Seq(Lit(#_module.com.SKIP()), c1#0), 
                      s'#2, 
                      Lit(#_module.com.SKIP()), 
                      t#1);
                }

                assume _module.__default.small__step__star#canCall(#_module.com.Seq(c0#0, c1#0), 
                    s#1, 
                    #_module.com.Seq(Lit(#_module.com.SKIP()), c1#0), 
                    s'#2)
                   && (_module.__default.small__step__star($LS($LZ), 
                      #_module.com.Seq(c0#0, c1#0), 
                      s#1, 
                      #_module.com.Seq(Lit(#_module.com.SKIP()), c1#0), 
                      s'#2)
                     ==> _module.__default.small__step__star#canCall(#_module.com.Seq(Lit(#_module.com.SKIP()), c1#0), 
                      s'#2, 
                      Lit(#_module.com.SKIP()), 
                      t#1));
                // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(257,5)
                assume _module.__default.small__step__star($LS($LZ), 
                    #_module.com.Seq(c0#0, c1#0), 
                    s#1, 
                    #_module.com.Seq(Lit(#_module.com.SKIP()), c1#0), 
                    s'#2)
                   && _module.__default.small__step__star($LS($LZ), 
                    #_module.com.Seq(Lit(#_module.com.SKIP()), c1#0), 
                    s'#2, 
                    Lit(#_module.com.SKIP()), 
                    t#1);
                // ----- Hint0 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(257,5)
                // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(259,24)
                // TrCallStmt: Before ProcessCallStmt
                assume true;
                // ProcessCallStmt: CheckSubrange
                c0##3 := #_module.com.Seq(c0#0, c1#0);
                assume true;
                // ProcessCallStmt: CheckSubrange
                s0##3 := s#1;
                assume true;
                // ProcessCallStmt: CheckSubrange
                c1##3 := #_module.com.Seq(Lit(#_module.com.SKIP()), c1#0);
                assume true;
                // ProcessCallStmt: CheckSubrange
                s1##1 := s'#2;
                assume true;
                // ProcessCallStmt: CheckSubrange
                c2##1 := Lit(#_module.com.SKIP());
                assume true;
                // ProcessCallStmt: CheckSubrange
                s2##1 := t#1;
                assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                // ProcessCallStmt: Make the call
                call Call$$_module.__default.star__transitive(c0##3, s0##3, c1##3, s1##1, c2##1, s2##1);
                // TrCallStmt: After ProcessCallStmt
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(259,67)"} true;
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(257,5)
                ##c#46 := c#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##c#46, Tclass._module.com(), $Heap);
                ##s#47 := s#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#47, TMap(TSeq(TChar), TInt), $Heap);
                ##c'#41 := Lit(#_module.com.SKIP());
                // assume allocatedness for argument to function
                assume $IsAlloc(##c'#41, Tclass._module.com(), $Heap);
                ##s'#41 := t#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s'#41, TMap(TSeq(TChar), TInt), $Heap);
                assume _module.__default.small__step__star#canCall(c#1, s#1, Lit(#_module.com.SKIP()), t#1);
                assume _module.__default.small__step__star#canCall(c#1, s#1, Lit(#_module.com.SKIP()), t#1);
                // ----- assert line0 <== line1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(257,5)
                assert {:subsumption 0} _module.__default.small__step__star($LS($LZ), 
                      #_module.com.Seq(c0#0, c1#0), 
                      s#1, 
                      #_module.com.Seq(Lit(#_module.com.SKIP()), c1#0), 
                      s'#2)
                     && _module.__default.small__step__star($LS($LZ), 
                      #_module.com.Seq(Lit(#_module.com.SKIP()), c1#0), 
                      s'#2, 
                      Lit(#_module.com.SKIP()), 
                      t#1)
                   ==> 
                  _module.__default.small__step__star#canCall(c#1, s#1, Lit(#_module.com.SKIP()), t#1)
                   ==> _module.__default.small__step__star($LS($LZ), c#1, s#1, Lit(#_module.com.SKIP()), t#1)
                     || 
                    (_module.com#Equal(c#1, #_module.com.SKIP()) && Map#Equal(s#1, t#1))
                     || (exists c''#21: DatatypeType, s''#21: Map Box Box :: 
                      { _module.__default.small__step__star($LS($LS($LZ)), c''#21, s''#21, #_module.com.SKIP(), t#1) } 
                        { _module.__default.small__step($LS($LS($LZ)), c#1, s#1, c''#21, s''#21) } 
                      $Is(c''#21, Tclass._module.com())
                         && $Is(s''#21, TMap(TSeq(TChar), TInt))
                         && 
                        _module.__default.small__step($LS($LS($LZ)), c#1, s#1, c''#21, s''#21)
                         && _module.__default.small__step__star($LS($LS($LZ)), c''#21, s''#21, Lit(#_module.com.SKIP()), t#1));
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(257,5)
                ##c#40 := c0#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##c#40, Tclass._module.com(), $Heap);
                ##s#41 := s#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#41, TMap(TSeq(TChar), TInt), $Heap);
                ##c'#35 := Lit(#_module.com.SKIP());
                // assume allocatedness for argument to function
                assume $IsAlloc(##c'#35, Tclass._module.com(), $Heap);
                ##s'#35 := s'#2;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s'#35, TMap(TSeq(TChar), TInt), $Heap);
                assume _module.__default.small__step__star#canCall(c0#0, s#1, Lit(#_module.com.SKIP()), s'#2);
                if (_module.__default.small__step__star($LS($LZ), c0#0, s#1, Lit(#_module.com.SKIP()), s'#2))
                {
                    ##c#41 := #_module.com.Seq(Lit(#_module.com.SKIP()), c1#0);
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c#41, Tclass._module.com(), $Heap);
                    ##s#42 := s'#2;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s#42, TMap(TSeq(TChar), TInt), $Heap);
                    ##c'#36 := Lit(#_module.com.SKIP());
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c'#36, Tclass._module.com(), $Heap);
                    ##s'#36 := t#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s'#36, TMap(TSeq(TChar), TInt), $Heap);
                    assume _module.__default.small__step__star#canCall(#_module.com.Seq(Lit(#_module.com.SKIP()), c1#0), 
                      s'#2, 
                      Lit(#_module.com.SKIP()), 
                      t#1);
                }

                assume _module.__default.small__step__star#canCall(c0#0, s#1, Lit(#_module.com.SKIP()), s'#2)
                   && (_module.__default.small__step__star($LS($LZ), c0#0, s#1, Lit(#_module.com.SKIP()), s'#2)
                     ==> _module.__default.small__step__star#canCall(#_module.com.Seq(Lit(#_module.com.SKIP()), c1#0), 
                      s'#2, 
                      Lit(#_module.com.SKIP()), 
                      t#1));
                // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(257,5)
                assume _module.__default.small__step__star($LS($LZ), c0#0, s#1, Lit(#_module.com.SKIP()), s'#2)
                   && _module.__default.small__step__star($LS($LZ), 
                    #_module.com.Seq(Lit(#_module.com.SKIP()), c1#0), 
                    s'#2, 
                    Lit(#_module.com.SKIP()), 
                    t#1);
                // ----- Hint1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(257,5)
                // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(261,19)
                // TrCallStmt: Before ProcessCallStmt
                assume true;
                // ProcessCallStmt: CheckSubrange
                c0##2 := c0#0;
                assume true;
                // ProcessCallStmt: CheckSubrange
                s0##2 := s#1;
                assume true;
                // ProcessCallStmt: CheckSubrange
                c##1 := Lit(#_module.com.SKIP());
                assume true;
                // ProcessCallStmt: CheckSubrange
                t##1 := s'#2;
                assume true;
                // ProcessCallStmt: CheckSubrange
                c1##2 := c1#0;
                assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                // ProcessCallStmt: Make the call
                call Call$$_module.__default.lemma__7__13(c0##2, s0##2, c##1, t##1, c1##2);
                // TrCallStmt: After ProcessCallStmt
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(261,39)"} true;
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(257,5)
                ##c#42 := #_module.com.Seq(c0#0, c1#0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##c#42, Tclass._module.com(), $Heap);
                ##s#43 := s#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#43, TMap(TSeq(TChar), TInt), $Heap);
                ##c'#37 := #_module.com.Seq(Lit(#_module.com.SKIP()), c1#0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##c'#37, Tclass._module.com(), $Heap);
                ##s'#37 := s'#2;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s'#37, TMap(TSeq(TChar), TInt), $Heap);
                assume _module.__default.small__step__star#canCall(#_module.com.Seq(c0#0, c1#0), 
                  s#1, 
                  #_module.com.Seq(Lit(#_module.com.SKIP()), c1#0), 
                  s'#2);
                if (_module.__default.small__step__star($LS($LZ), 
                  #_module.com.Seq(c0#0, c1#0), 
                  s#1, 
                  #_module.com.Seq(Lit(#_module.com.SKIP()), c1#0), 
                  s'#2))
                {
                    ##c#43 := #_module.com.Seq(Lit(#_module.com.SKIP()), c1#0);
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c#43, Tclass._module.com(), $Heap);
                    ##s#44 := s'#2;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s#44, TMap(TSeq(TChar), TInt), $Heap);
                    ##c'#38 := Lit(#_module.com.SKIP());
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c'#38, Tclass._module.com(), $Heap);
                    ##s'#38 := t#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s'#38, TMap(TSeq(TChar), TInt), $Heap);
                    assume _module.__default.small__step__star#canCall(#_module.com.Seq(Lit(#_module.com.SKIP()), c1#0), 
                      s'#2, 
                      Lit(#_module.com.SKIP()), 
                      t#1);
                }

                assume _module.__default.small__step__star#canCall(#_module.com.Seq(c0#0, c1#0), 
                    s#1, 
                    #_module.com.Seq(Lit(#_module.com.SKIP()), c1#0), 
                    s'#2)
                   && (_module.__default.small__step__star($LS($LZ), 
                      #_module.com.Seq(c0#0, c1#0), 
                      s#1, 
                      #_module.com.Seq(Lit(#_module.com.SKIP()), c1#0), 
                      s'#2)
                     ==> _module.__default.small__step__star#canCall(#_module.com.Seq(Lit(#_module.com.SKIP()), c1#0), 
                      s'#2, 
                      Lit(#_module.com.SKIP()), 
                      t#1));
                // ----- assert line1 <== line2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(257,5)
                assert {:subsumption 0} _module.__default.small__step__star($LS($LZ), c0#0, s#1, Lit(#_module.com.SKIP()), s'#2)
                     && _module.__default.small__step__star($LS($LZ), 
                      #_module.com.Seq(Lit(#_module.com.SKIP()), c1#0), 
                      s'#2, 
                      Lit(#_module.com.SKIP()), 
                      t#1)
                   ==> 
                  _module.__default.small__step__star#canCall(#_module.com.Seq(c0#0, c1#0), 
                    s#1, 
                    #_module.com.Seq(Lit(#_module.com.SKIP()), c1#0), 
                    s'#2)
                   ==> _module.__default.small__step__star($LS($LZ), 
                      #_module.com.Seq(c0#0, c1#0), 
                      s#1, 
                      #_module.com.Seq(Lit(#_module.com.SKIP()), c1#0), 
                      s'#2)
                     || 
                    (_module.com#Equal(#_module.com.Seq(c0#0, c1#0), #_module.com.Seq(Lit(#_module.com.SKIP()), c1#0))
                       && Map#Equal(s#1, s'#2))
                     || (exists c''#19: DatatypeType, s''#19: Map Box Box :: 
                      { _module.__default.small__step__star($LS($LS($LZ)), c''#19, s''#19, #_module.com.Seq(#_module.com.SKIP(), c1#0), s'#2) } 
                        { _module.__default.small__step($LS($LS($LZ)), #_module.com.Seq(c0#0, c1#0), s#1, c''#19, s''#19) } 
                      $Is(c''#19, Tclass._module.com())
                         && $Is(s''#19, TMap(TSeq(TChar), TInt))
                         && 
                        _module.__default.small__step($LS($LS($LZ)), #_module.com.Seq(c0#0, c1#0), s#1, c''#19, s''#19)
                         && _module.__default.small__step__star($LS($LS($LZ)), 
                          c''#19, 
                          s''#19, 
                          #_module.com.Seq(Lit(#_module.com.SKIP()), c1#0), 
                          s'#2));
                assert {:subsumption 0} _module.__default.small__step__star($LS($LZ), c0#0, s#1, Lit(#_module.com.SKIP()), s'#2)
                     && _module.__default.small__step__star($LS($LZ), 
                      #_module.com.Seq(Lit(#_module.com.SKIP()), c1#0), 
                      s'#2, 
                      Lit(#_module.com.SKIP()), 
                      t#1)
                   ==> 
                  _module.__default.small__step__star#canCall(#_module.com.Seq(Lit(#_module.com.SKIP()), c1#0), 
                    s'#2, 
                    Lit(#_module.com.SKIP()), 
                    t#1)
                   ==> _module.__default.small__step__star($LS($LZ), 
                      #_module.com.Seq(Lit(#_module.com.SKIP()), c1#0), 
                      s'#2, 
                      Lit(#_module.com.SKIP()), 
                      t#1)
                     || 
                    (_module.com#Equal(#_module.com.Seq(Lit(#_module.com.SKIP()), c1#0), #_module.com.SKIP())
                       && Map#Equal(s'#2, t#1))
                     || (exists c''#20: DatatypeType, s''#20: Map Box Box :: 
                      { _module.__default.small__step__star($LS($LS($LZ)), c''#20, s''#20, #_module.com.SKIP(), t#1) } 
                        { _module.__default.small__step($LS($LS($LZ)), #_module.com.Seq(#_module.com.SKIP(), c1#0), s'#2, c''#20, s''#20) } 
                      $Is(c''#20, Tclass._module.com())
                         && $Is(s''#20, TMap(TSeq(TChar), TInt))
                         && 
                        _module.__default.small__step($LS($LS($LZ)), 
                          #_module.com.Seq(Lit(#_module.com.SKIP()), c1#0), 
                          s'#2, 
                          c''#20, 
                          s''#20)
                         && _module.__default.small__step__star($LS($LS($LZ)), c''#20, s''#20, Lit(#_module.com.SKIP()), t#1));
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(257,5)
                ##c#37 := #_module.com.Seq(Lit(#_module.com.SKIP()), c1#0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##c#37, Tclass._module.com(), $Heap);
                ##s#38 := s'#2;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#38, TMap(TSeq(TChar), TInt), $Heap);
                ##c'#32 := Lit(#_module.com.SKIP());
                // assume allocatedness for argument to function
                assume $IsAlloc(##c'#32, Tclass._module.com(), $Heap);
                ##s'#32 := t#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s'#32, TMap(TSeq(TChar), TInt), $Heap);
                assume _module.__default.small__step__star#canCall(#_module.com.Seq(Lit(#_module.com.SKIP()), c1#0), 
                  s'#2, 
                  Lit(#_module.com.SKIP()), 
                  t#1);
                assume _module.__default.small__step__star#canCall(#_module.com.Seq(Lit(#_module.com.SKIP()), c1#0), 
                  s'#2, 
                  Lit(#_module.com.SKIP()), 
                  t#1);
                // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(257,5)
                assume _module.__default.small__step__star($LS($LZ), 
                  #_module.com.Seq(Lit(#_module.com.SKIP()), c1#0), 
                  s'#2, 
                  Lit(#_module.com.SKIP()), 
                  t#1);
                // ----- Hint2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(257,5)
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(257,5)
                ##c#38 := c0#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##c#38, Tclass._module.com(), $Heap);
                ##s#39 := s#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#39, TMap(TSeq(TChar), TInt), $Heap);
                ##c'#33 := Lit(#_module.com.SKIP());
                // assume allocatedness for argument to function
                assume $IsAlloc(##c'#33, Tclass._module.com(), $Heap);
                ##s'#33 := s'#2;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s'#33, TMap(TSeq(TChar), TInt), $Heap);
                assume _module.__default.small__step__star#canCall(c0#0, s#1, Lit(#_module.com.SKIP()), s'#2);
                if (_module.__default.small__step__star($LS($LZ), c0#0, s#1, Lit(#_module.com.SKIP()), s'#2))
                {
                    ##c#39 := #_module.com.Seq(Lit(#_module.com.SKIP()), c1#0);
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c#39, Tclass._module.com(), $Heap);
                    ##s#40 := s'#2;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s#40, TMap(TSeq(TChar), TInt), $Heap);
                    ##c'#34 := Lit(#_module.com.SKIP());
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c'#34, Tclass._module.com(), $Heap);
                    ##s'#34 := t#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s'#34, TMap(TSeq(TChar), TInt), $Heap);
                    assume _module.__default.small__step__star#canCall(#_module.com.Seq(Lit(#_module.com.SKIP()), c1#0), 
                      s'#2, 
                      Lit(#_module.com.SKIP()), 
                      t#1);
                }

                assume _module.__default.small__step__star#canCall(c0#0, s#1, Lit(#_module.com.SKIP()), s'#2)
                   && (_module.__default.small__step__star($LS($LZ), c0#0, s#1, Lit(#_module.com.SKIP()), s'#2)
                     ==> _module.__default.small__step__star#canCall(#_module.com.Seq(Lit(#_module.com.SKIP()), c1#0), 
                      s'#2, 
                      Lit(#_module.com.SKIP()), 
                      t#1));
                // ----- assert line2 <== line3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(257,5)
                assert {:subsumption 0} _module.__default.small__step__star($LS($LZ), 
                    #_module.com.Seq(Lit(#_module.com.SKIP()), c1#0), 
                    s'#2, 
                    Lit(#_module.com.SKIP()), 
                    t#1)
                   ==> 
                  _module.__default.small__step__star#canCall(c0#0, s#1, Lit(#_module.com.SKIP()), s'#2)
                   ==> _module.__default.small__step__star($LS($LZ), c0#0, s#1, Lit(#_module.com.SKIP()), s'#2)
                     || 
                    (_module.com#Equal(c0#0, #_module.com.SKIP()) && Map#Equal(s#1, s'#2))
                     || (exists c''#17: DatatypeType, s''#17: Map Box Box :: 
                      { _module.__default.small__step__star($LS($LS($LZ)), c''#17, s''#17, #_module.com.SKIP(), s'#2) } 
                        { _module.__default.small__step($LS($LS($LZ)), c0#0, s#1, c''#17, s''#17) } 
                      $Is(c''#17, Tclass._module.com())
                         && $Is(s''#17, TMap(TSeq(TChar), TInt))
                         && 
                        _module.__default.small__step($LS($LS($LZ)), c0#0, s#1, c''#17, s''#17)
                         && _module.__default.small__step__star($LS($LS($LZ)), c''#17, s''#17, Lit(#_module.com.SKIP()), s'#2));
                assert {:subsumption 0} _module.__default.small__step__star($LS($LZ), 
                    #_module.com.Seq(Lit(#_module.com.SKIP()), c1#0), 
                    s'#2, 
                    Lit(#_module.com.SKIP()), 
                    t#1)
                   ==> 
                  _module.__default.small__step__star#canCall(#_module.com.Seq(Lit(#_module.com.SKIP()), c1#0), 
                    s'#2, 
                    Lit(#_module.com.SKIP()), 
                    t#1)
                   ==> _module.__default.small__step__star($LS($LZ), 
                      #_module.com.Seq(Lit(#_module.com.SKIP()), c1#0), 
                      s'#2, 
                      Lit(#_module.com.SKIP()), 
                      t#1)
                     || 
                    (_module.com#Equal(#_module.com.Seq(Lit(#_module.com.SKIP()), c1#0), #_module.com.SKIP())
                       && Map#Equal(s'#2, t#1))
                     || (exists c''#18: DatatypeType, s''#18: Map Box Box :: 
                      { _module.__default.small__step__star($LS($LS($LZ)), c''#18, s''#18, #_module.com.SKIP(), t#1) } 
                        { _module.__default.small__step($LS($LS($LZ)), #_module.com.Seq(#_module.com.SKIP(), c1#0), s'#2, c''#18, s''#18) } 
                      $Is(c''#18, Tclass._module.com())
                         && $Is(s''#18, TMap(TSeq(TChar), TInt))
                         && 
                        _module.__default.small__step($LS($LS($LZ)), 
                          #_module.com.Seq(Lit(#_module.com.SKIP()), c1#0), 
                          s'#2, 
                          c''#18, 
                          s''#18)
                         && _module.__default.small__step__star($LS($LS($LZ)), c''#18, s''#18, Lit(#_module.com.SKIP()), t#1));
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(257,5)
                ##c#34 := c1#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##c#34, Tclass._module.com(), $Heap);
                ##s#35 := s'#2;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#35, TMap(TSeq(TChar), TInt), $Heap);
                ##c'#29 := Lit(#_module.com.SKIP());
                // assume allocatedness for argument to function
                assume $IsAlloc(##c'#29, Tclass._module.com(), $Heap);
                ##s'#29 := t#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s'#29, TMap(TSeq(TChar), TInt), $Heap);
                assume _module.__default.small__step__star#canCall(c1#0, s'#2, Lit(#_module.com.SKIP()), t#1);
                assume _module.__default.small__step__star#canCall(c1#0, s'#2, Lit(#_module.com.SKIP()), t#1);
                // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(257,5)
                assume _module.__default.small__step__star($LS($LZ), c1#0, s'#2, Lit(#_module.com.SKIP()), t#1);
                // ----- Hint3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(257,5)
                // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(265,9)
                ##c#35 := #_module.com.Seq(Lit(#_module.com.SKIP()), c1#0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##c#35, Tclass._module.com(), $Heap);
                ##s#36 := s'#2;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#36, TMap(TSeq(TChar), TInt), $Heap);
                ##c'#30 := c1#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##c'#30, Tclass._module.com(), $Heap);
                ##s'#30 := s'#2;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s'#30, TMap(TSeq(TChar), TInt), $Heap);
                assume _module.__default.small__step#canCall(#_module.com.Seq(Lit(#_module.com.SKIP()), c1#0), s'#2, c1#0, s'#2);
                assume _module.__default.small__step#canCall(#_module.com.Seq(Lit(#_module.com.SKIP()), c1#0), s'#2, c1#0, s'#2);
                assert {:subsumption 0} _module.__default.small__step($LS($LS($LZ)), 
                  #_module.com.Seq(Lit(#_module.com.SKIP()), c1#0), 
                  s'#2, 
                  c1#0, 
                  s'#2);
                assume _module.__default.small__step($LS($LS($LZ)), 
                  #_module.com.Seq(Lit(#_module.com.SKIP()), c1#0), 
                  s'#2, 
                  c1#0, 
                  s'#2);
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(257,5)
                ##c#36 := #_module.com.Seq(Lit(#_module.com.SKIP()), c1#0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##c#36, Tclass._module.com(), $Heap);
                ##s#37 := s'#2;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#37, TMap(TSeq(TChar), TInt), $Heap);
                ##c'#31 := Lit(#_module.com.SKIP());
                // assume allocatedness for argument to function
                assume $IsAlloc(##c'#31, Tclass._module.com(), $Heap);
                ##s'#31 := t#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s'#31, TMap(TSeq(TChar), TInt), $Heap);
                assume _module.__default.small__step__star#canCall(#_module.com.Seq(Lit(#_module.com.SKIP()), c1#0), 
                  s'#2, 
                  Lit(#_module.com.SKIP()), 
                  t#1);
                assume _module.__default.small__step__star#canCall(#_module.com.Seq(Lit(#_module.com.SKIP()), c1#0), 
                  s'#2, 
                  Lit(#_module.com.SKIP()), 
                  t#1);
                // ----- assert line3 <== line4 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(257,5)
                assert {:subsumption 0} _module.__default.small__step__star($LS($LZ), c1#0, s'#2, Lit(#_module.com.SKIP()), t#1)
                   ==> 
                  _module.__default.small__step__star#canCall(#_module.com.Seq(Lit(#_module.com.SKIP()), c1#0), 
                    s'#2, 
                    Lit(#_module.com.SKIP()), 
                    t#1)
                   ==> _module.__default.small__step__star($LS($LZ), 
                      #_module.com.Seq(Lit(#_module.com.SKIP()), c1#0), 
                      s'#2, 
                      Lit(#_module.com.SKIP()), 
                      t#1)
                     || 
                    (_module.com#Equal(#_module.com.Seq(Lit(#_module.com.SKIP()), c1#0), #_module.com.SKIP())
                       && Map#Equal(s'#2, t#1))
                     || (exists c''#16: DatatypeType, s''#16: Map Box Box :: 
                      { _module.__default.small__step__star($LS($LS($LZ)), c''#16, s''#16, #_module.com.SKIP(), t#1) } 
                        { _module.__default.small__step($LS($LS($LZ)), #_module.com.Seq(#_module.com.SKIP(), c1#0), s'#2, c''#16, s''#16) } 
                      $Is(c''#16, Tclass._module.com())
                         && $Is(s''#16, TMap(TSeq(TChar), TInt))
                         && 
                        _module.__default.small__step($LS($LS($LZ)), 
                          #_module.com.Seq(Lit(#_module.com.SKIP()), c1#0), 
                          s'#2, 
                          c''#16, 
                          s''#16)
                         && _module.__default.small__step__star($LS($LS($LZ)), c''#16, s''#16, Lit(#_module.com.SKIP()), t#1));
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(257,5)
                assume true;
                // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(257,5)
                assume true;
                // ----- Hint4 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(257,5)
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(257,5)
                ##c#33 := c1#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##c#33, Tclass._module.com(), $Heap);
                ##s#34 := s'#2;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#34, TMap(TSeq(TChar), TInt), $Heap);
                ##c'#28 := Lit(#_module.com.SKIP());
                // assume allocatedness for argument to function
                assume $IsAlloc(##c'#28, Tclass._module.com(), $Heap);
                ##s'#28 := t#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s'#28, TMap(TSeq(TChar), TInt), $Heap);
                assume _module.__default.small__step__star#canCall(c1#0, s'#2, Lit(#_module.com.SKIP()), t#1);
                assume _module.__default.small__step__star#canCall(c1#0, s'#2, Lit(#_module.com.SKIP()), t#1);
                // ----- assert line4 <== line5 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(257,5)
                assert {:subsumption 0} Lit(true)
                   ==> 
                  _module.__default.small__step__star#canCall(c1#0, s'#2, Lit(#_module.com.SKIP()), t#1)
                   ==> _module.__default.small__step__star($LS($LZ), c1#0, s'#2, Lit(#_module.com.SKIP()), t#1)
                     || 
                    (_module.com#Equal(c1#0, #_module.com.SKIP()) && Map#Equal(s'#2, t#1))
                     || (exists c''#15: DatatypeType, s''#15: Map Box Box :: 
                      { _module.__default.small__step__star($LS($LS($LZ)), c''#15, s''#15, #_module.com.SKIP(), t#1) } 
                        { _module.__default.small__step($LS($LS($LZ)), c1#0, s'#2, c''#15, s''#15) } 
                      $Is(c''#15, Tclass._module.com())
                         && $Is(s''#15, TMap(TSeq(TChar), TInt))
                         && 
                        _module.__default.small__step($LS($LS($LZ)), c1#0, s'#2, c''#15, s''#15)
                         && _module.__default.small__step__star($LS($LS($LZ)), c''#15, s''#15, Lit(#_module.com.SKIP()), t#1));
                assume false;
            }

            assume true
               ==> _module.__default.small__step__star($LS($LZ), c#1, s#1, Lit(#_module.com.SKIP()), t#1);
        }
        else if (c#1 == #_module.com.If(_mcc#4#0, _mcc#5#0, _mcc#6#0))
        {
            assume $Is(_mcc#4#0, Tclass._module.bexp())
               && $IsAlloc(_mcc#4#0, Tclass._module.bexp(), $Heap);
            assume $Is(_mcc#5#0, Tclass._module.com())
               && $IsAlloc(_mcc#5#0, Tclass._module.com(), $Heap);
            assume $Is(_mcc#6#0, Tclass._module.com())
               && $IsAlloc(_mcc#6#0, Tclass._module.com(), $Heap);
            havoc els#0;
            assume $Is(els#0, Tclass._module.com()) && $IsAlloc(els#0, Tclass._module.com(), $Heap);
            assume let#0_1_0#0#0 == _mcc#6#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0_1_0#0#0, Tclass._module.com());
            assume els#0 == let#0_1_0#0#0;
            havoc thn#0;
            assume $Is(thn#0, Tclass._module.com()) && $IsAlloc(thn#0, Tclass._module.com(), $Heap);
            assume let#0_1_1#0#0 == _mcc#5#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0_1_1#0#0, Tclass._module.com());
            assume thn#0 == let#0_1_1#0#0;
            havoc b#1;
            assume $Is(b#1, Tclass._module.bexp()) && $IsAlloc(b#1, Tclass._module.bexp(), $Heap);
            assume let#0_1_2#0#0 == _mcc#4#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0_1_2#0#0, Tclass._module.bexp());
            assume b#1 == let#0_1_2#0#0;
        }
        else if (c#1 == #_module.com.While(_mcc#7#0, _mcc#8#0))
        {
            assume $Is(_mcc#7#0, Tclass._module.bexp())
               && $IsAlloc(_mcc#7#0, Tclass._module.bexp(), $Heap);
            assume $Is(_mcc#8#0, Tclass._module.com())
               && $IsAlloc(_mcc#8#0, Tclass._module.com(), $Heap);
            havoc body#0;
            assume $Is(body#0, Tclass._module.com())
               && $IsAlloc(body#0, Tclass._module.com(), $Heap);
            assume let#0_0_0#0#0 == _mcc#8#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0_0_0#0#0, Tclass._module.com());
            assume body#0 == let#0_0_0#0#0;
            havoc b#0;
            assume $Is(b#0, Tclass._module.bexp()) && $IsAlloc(b#0, Tclass._module.bexp(), $Heap);
            assume let#0_0_1#0#0 == _mcc#7#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0_0_1#0#0, Tclass._module.bexp());
            assume b#0 == let#0_0_1#0#0;
            // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(272,5)
            ##b#0 := b#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#0, Tclass._module.bexp(), $Heap);
            ##s#2 := s#1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#2, TMap(TSeq(TChar), TInt), $Heap);
            assume _module.__default.bval#canCall(b#0, s#1);
            if (!_module.__default.bval($LS($LZ), b#0, s#1))
            {
            }

            assume _module.__default.bval#canCall(b#0, s#1);
            if (!_module.__default.bval($LS($LZ), b#0, s#1) && Map#Equal(s#1, t#1))
            {
                // ----- calc statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(273,7)
                // Assume Fuel Constant
                if (*)
                {
                    // ----- assert wf[initial] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(273,7)
                    assume true;
                    assume false;
                }
                else if (*)
                {
                    // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(273,7)
                    ##c#6 := #_module.com.If(b#0, 
                      #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                      Lit(#_module.com.SKIP()));
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c#6, Tclass._module.com(), $Heap);
                    ##s#7 := s#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s#7, TMap(TSeq(TChar), TInt), $Heap);
                    ##c'#5 := Lit(#_module.com.SKIP());
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c'#5, Tclass._module.com(), $Heap);
                    ##s'#5 := t#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s'#5, TMap(TSeq(TChar), TInt), $Heap);
                    assume _module.__default.small__step__star#canCall(#_module.com.If(b#0, 
                        #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                        Lit(#_module.com.SKIP())), 
                      s#1, 
                      Lit(#_module.com.SKIP()), 
                      t#1);
                    assume _module.__default.small__step__star#canCall(#_module.com.If(b#0, 
                        #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                        Lit(#_module.com.SKIP())), 
                      s#1, 
                      Lit(#_module.com.SKIP()), 
                      t#1);
                    // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(273,7)
                    assume _module.__default.small__step__star($LS($LZ), 
                      #_module.com.If(b#0, 
                        #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                        Lit(#_module.com.SKIP())), 
                      s#1, 
                      Lit(#_module.com.SKIP()), 
                      t#1);
                    // ----- Hint0 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(273,7)
                    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(275,11)
                    ##c#7 := c#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c#7, Tclass._module.com(), $Heap);
                    ##s#8 := s#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s#8, TMap(TSeq(TChar), TInt), $Heap);
                    ##c'#6 := #_module.com.If(b#0, 
                      #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                      Lit(#_module.com.SKIP()));
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c'#6, Tclass._module.com(), $Heap);
                    ##s'#6 := s#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s'#6, TMap(TSeq(TChar), TInt), $Heap);
                    assume _module.__default.small__step#canCall(c#1, 
                      s#1, 
                      #_module.com.If(b#0, 
                        #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                        Lit(#_module.com.SKIP())), 
                      s#1);
                    assume _module.__default.small__step#canCall(c#1, 
                      s#1, 
                      #_module.com.If(b#0, 
                        #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                        Lit(#_module.com.SKIP())), 
                      s#1);
                    assert {:subsumption 0} _module.__default.small__step($LS($LS($LZ)), 
                      c#1, 
                      s#1, 
                      #_module.com.If(b#0, 
                        #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                        Lit(#_module.com.SKIP())), 
                      s#1);
                    assume _module.__default.small__step($LS($LS($LZ)), 
                      c#1, 
                      s#1, 
                      #_module.com.If(b#0, 
                        #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                        Lit(#_module.com.SKIP())), 
                      s#1);
                    // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(273,7)
                    ##c#8 := c#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c#8, Tclass._module.com(), $Heap);
                    ##s#9 := s#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s#9, TMap(TSeq(TChar), TInt), $Heap);
                    ##c'#7 := Lit(#_module.com.SKIP());
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c'#7, Tclass._module.com(), $Heap);
                    ##s'#7 := t#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s'#7, TMap(TSeq(TChar), TInt), $Heap);
                    assume _module.__default.small__step__star#canCall(c#1, s#1, Lit(#_module.com.SKIP()), t#1);
                    assume _module.__default.small__step__star#canCall(c#1, s#1, Lit(#_module.com.SKIP()), t#1);
                    // ----- assert line0 <== line1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(273,7)
                    assert {:subsumption 0} _module.__default.small__step__star($LS($LZ), 
                        #_module.com.If(b#0, 
                          #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                          Lit(#_module.com.SKIP())), 
                        s#1, 
                        Lit(#_module.com.SKIP()), 
                        t#1)
                       ==> 
                      _module.__default.small__step__star#canCall(c#1, s#1, Lit(#_module.com.SKIP()), t#1)
                       ==> _module.__default.small__step__star($LS($LZ), c#1, s#1, Lit(#_module.com.SKIP()), t#1)
                         || 
                        (_module.com#Equal(c#1, #_module.com.SKIP()) && Map#Equal(s#1, t#1))
                         || (exists c''#5: DatatypeType, s''#5: Map Box Box :: 
                          { _module.__default.small__step__star($LS($LS($LZ)), c''#5, s''#5, #_module.com.SKIP(), t#1) } 
                            { _module.__default.small__step($LS($LS($LZ)), c#1, s#1, c''#5, s''#5) } 
                          $Is(c''#5, Tclass._module.com())
                             && $Is(s''#5, TMap(TSeq(TChar), TInt))
                             && 
                            _module.__default.small__step($LS($LS($LZ)), c#1, s#1, c''#5, s''#5)
                             && _module.__default.small__step__star($LS($LS($LZ)), c''#5, s''#5, Lit(#_module.com.SKIP()), t#1));
                    assume false;
                }
                else if (*)
                {
                    // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(273,7)
                    ##c#3 := Lit(#_module.com.SKIP());
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c#3, Tclass._module.com(), $Heap);
                    ##s#4 := s#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s#4, TMap(TSeq(TChar), TInt), $Heap);
                    ##c'#2 := Lit(#_module.com.SKIP());
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c'#2, Tclass._module.com(), $Heap);
                    ##s'#2 := t#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s'#2, TMap(TSeq(TChar), TInt), $Heap);
                    assume _module.__default.small__step__star#canCall(Lit(#_module.com.SKIP()), s#1, Lit(#_module.com.SKIP()), t#1);
                    assume _module.__default.small__step__star#canCall(Lit(#_module.com.SKIP()), s#1, Lit(#_module.com.SKIP()), t#1);
                    // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(273,7)
                    assume _module.__default.small__step__star($LS($LZ), Lit(#_module.com.SKIP()), s#1, Lit(#_module.com.SKIP()), t#1);
                    // ----- Hint1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(273,7)
                    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(277,11)
                    ##c#4 := #_module.com.If(b#0, 
                      #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                      Lit(#_module.com.SKIP()));
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c#4, Tclass._module.com(), $Heap);
                    ##s#5 := s#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s#5, TMap(TSeq(TChar), TInt), $Heap);
                    ##c'#3 := Lit(#_module.com.SKIP());
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c'#3, Tclass._module.com(), $Heap);
                    ##s'#3 := s#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s'#3, TMap(TSeq(TChar), TInt), $Heap);
                    assume _module.__default.small__step#canCall(#_module.com.If(b#0, 
                        #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                        Lit(#_module.com.SKIP())), 
                      s#1, 
                      Lit(#_module.com.SKIP()), 
                      s#1);
                    assume _module.__default.small__step#canCall(#_module.com.If(b#0, 
                        #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                        Lit(#_module.com.SKIP())), 
                      s#1, 
                      Lit(#_module.com.SKIP()), 
                      s#1);
                    assert {:subsumption 0} _module.__default.small__step($LS($LS($LZ)), 
                      #_module.com.If(b#0, 
                        #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                        Lit(#_module.com.SKIP())), 
                      s#1, 
                      Lit(#_module.com.SKIP()), 
                      s#1);
                    assume _module.__default.small__step($LS($LS($LZ)), 
                      #_module.com.If(b#0, 
                        #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                        Lit(#_module.com.SKIP())), 
                      s#1, 
                      Lit(#_module.com.SKIP()), 
                      s#1);
                    // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(273,7)
                    ##c#5 := #_module.com.If(b#0, 
                      #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                      Lit(#_module.com.SKIP()));
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c#5, Tclass._module.com(), $Heap);
                    ##s#6 := s#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s#6, TMap(TSeq(TChar), TInt), $Heap);
                    ##c'#4 := Lit(#_module.com.SKIP());
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c'#4, Tclass._module.com(), $Heap);
                    ##s'#4 := t#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s'#4, TMap(TSeq(TChar), TInt), $Heap);
                    assume _module.__default.small__step__star#canCall(#_module.com.If(b#0, 
                        #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                        Lit(#_module.com.SKIP())), 
                      s#1, 
                      Lit(#_module.com.SKIP()), 
                      t#1);
                    assume _module.__default.small__step__star#canCall(#_module.com.If(b#0, 
                        #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                        Lit(#_module.com.SKIP())), 
                      s#1, 
                      Lit(#_module.com.SKIP()), 
                      t#1);
                    // ----- assert line1 <== line2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(273,7)
                    assert {:subsumption 0} _module.__default.small__step__star($LS($LZ), Lit(#_module.com.SKIP()), s#1, Lit(#_module.com.SKIP()), t#1)
                       ==> 
                      _module.__default.small__step__star#canCall(#_module.com.If(b#0, 
                          #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                          Lit(#_module.com.SKIP())), 
                        s#1, 
                        Lit(#_module.com.SKIP()), 
                        t#1)
                       ==> _module.__default.small__step__star($LS($LZ), 
                          #_module.com.If(b#0, 
                            #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                            Lit(#_module.com.SKIP())), 
                          s#1, 
                          Lit(#_module.com.SKIP()), 
                          t#1)
                         || 
                        (_module.com#Equal(#_module.com.If(b#0, 
                              #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                              Lit(#_module.com.SKIP())), 
                            #_module.com.SKIP())
                           && Map#Equal(s#1, t#1))
                         || (exists c''#4: DatatypeType, s''#4: Map Box Box :: 
                          { _module.__default.small__step__star($LS($LS($LZ)), c''#4, s''#4, #_module.com.SKIP(), t#1) } 
                            { _module.__default.small__step($LS($LS($LZ)), 
                              #_module.com.If(b#0, 
                                #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                                #_module.com.SKIP()), 
                              s#1, 
                              c''#4, 
                              s''#4) } 
                          $Is(c''#4, Tclass._module.com())
                             && $Is(s''#4, TMap(TSeq(TChar), TInt))
                             && 
                            _module.__default.small__step($LS($LS($LZ)), 
                              #_module.com.If(b#0, 
                                #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                                Lit(#_module.com.SKIP())), 
                              s#1, 
                              c''#4, 
                              s''#4)
                             && _module.__default.small__step__star($LS($LS($LZ)), c''#4, s''#4, Lit(#_module.com.SKIP()), t#1));
                    assume false;
                }
                else if (*)
                {
                    // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(273,7)
                    assume true;
                    // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(273,7)
                    assume true;
                    // ----- Hint2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(273,7)
                    // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(273,7)
                    ##c#2 := Lit(#_module.com.SKIP());
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c#2, Tclass._module.com(), $Heap);
                    ##s#3 := s#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s#3, TMap(TSeq(TChar), TInt), $Heap);
                    ##c'#1 := Lit(#_module.com.SKIP());
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c'#1, Tclass._module.com(), $Heap);
                    ##s'#1 := t#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s'#1, TMap(TSeq(TChar), TInt), $Heap);
                    assume _module.__default.small__step__star#canCall(Lit(#_module.com.SKIP()), s#1, Lit(#_module.com.SKIP()), t#1);
                    assume _module.__default.small__step__star#canCall(Lit(#_module.com.SKIP()), s#1, Lit(#_module.com.SKIP()), t#1);
                    // ----- assert line2 <== line3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(273,7)
                    assert {:subsumption 0} Lit(true)
                       ==> 
                      _module.__default.small__step__star#canCall(Lit(#_module.com.SKIP()), s#1, Lit(#_module.com.SKIP()), t#1)
                       ==> _module.__default.small__step__star($LS($LZ), Lit(#_module.com.SKIP()), s#1, Lit(#_module.com.SKIP()), t#1)
                         || 
                        (_module.com#Equal(#_module.com.SKIP(), #_module.com.SKIP())
                           && Map#Equal(s#1, t#1))
                         || (exists c''#3: DatatypeType, s''#3: Map Box Box :: 
                          { _module.__default.small__step__star($LS($LS($LZ)), c''#3, s''#3, #_module.com.SKIP(), t#1) } 
                            { _module.__default.small__step($LS($LS($LZ)), #_module.com.SKIP(), s#1, c''#3, s''#3) } 
                          $Is(c''#3, Tclass._module.com())
                             && $Is(s''#3, TMap(TSeq(TChar), TInt))
                             && 
                            _module.__default.small__step($LS($LS($LZ)), Lit(#_module.com.SKIP()), s#1, c''#3, s''#3)
                             && _module.__default.small__step__star($LS($LS($LZ)), c''#3, s''#3, Lit(#_module.com.SKIP()), t#1));
                    assume false;
                }

                assume true
                   ==> _module.__default.small__step__star($LS($LZ), c#1, s#1, Lit(#_module.com.SKIP()), t#1);
            }
            else
            {
                // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(282,14)
                havoc s'#1;
                if ($Is(s'#1, TMap(TSeq(TChar), TInt))
                   && $IsAlloc(s'#1, TMap(TSeq(TChar), TInt), $Heap))
                {
                    assert ORD#IsNat(Lit(ORD#FromNat(1)));
                    assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
                    ##_k#0 := ORD#Minus(_k#0, ORD#FromNat(1));
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##_k#0, TORDINAL, $Heap);
                    ##c#9 := body#0;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c#9, Tclass._module.com(), $Heap);
                    ##s#10 := s#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s#10, TMap(TSeq(TChar), TInt), $Heap);
                    ##t#1 := s'#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##t#1, TMap(TSeq(TChar), TInt), $Heap);
                    assume _module.__default.big__step_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), body#0, s#1, s'#1);
                    if (_module.__default.big__step_h($LS($LZ), ORD#Minus(_k#0, ORD#FromNat(1)), body#0, s#1, s'#1))
                    {
                        assert ORD#IsNat(Lit(ORD#FromNat(1)));
                        assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
                        ##_k#1 := ORD#Minus(_k#0, ORD#FromNat(1));
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##_k#1, TORDINAL, $Heap);
                        ##c#10 := #_module.com.While(b#0, body#0);
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##c#10, Tclass._module.com(), $Heap);
                        ##s#11 := s'#1;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##s#11, TMap(TSeq(TChar), TInt), $Heap);
                        ##t#2 := t#1;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##t#2, TMap(TSeq(TChar), TInt), $Heap);
                        assume _module.__default.big__step_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), #_module.com.While(b#0, body#0), s'#1, t#1);
                    }

                    assume _module.__default.big__step_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), body#0, s#1, s'#1)
                       && (_module.__default.big__step_h($LS($LZ), ORD#Minus(_k#0, ORD#FromNat(1)), body#0, s#1, s'#1)
                         ==> _module.__default.big__step_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), #_module.com.While(b#0, body#0), s'#1, t#1));
                }

                assert (exists $as#s'0_0_0#0: Map Box Box :: 
                  $Is($as#s'0_0_0#0, TMap(TSeq(TChar), TInt))
                     && 
                    _module.__default.big__step_h($LS($LZ), ORD#Minus(_k#0, ORD#FromNat(1)), body#0, s#1, $as#s'0_0_0#0)
                     && _module.__default.big__step_h($LS($LZ), 
                      ORD#Minus(_k#0, ORD#FromNat(1)), 
                      #_module.com.While(b#0, body#0), 
                      $as#s'0_0_0#0, 
                      t#1));
                havoc s'#0;
                assume _module.__default.big__step_h($LS($LZ), ORD#Minus(_k#0, ORD#FromNat(1)), body#0, s#1, s'#0)
                   && _module.__default.big__step_h($LS($LZ), 
                    ORD#Minus(_k#0, ORD#FromNat(1)), 
                    #_module.com.While(b#0, body#0), 
                    s'#0, 
                    t#1);
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(282,72)"} true;
                // ----- calc statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(283,7)
                // Assume Fuel Constant
                if (*)
                {
                    // ----- assert wf[initial] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(283,7)
                    assume true;
                    assume false;
                }
                else if (*)
                {
                    // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(283,7)
                    ##c#28 := #_module.com.If(b#0, 
                      #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                      Lit(#_module.com.SKIP()));
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c#28, Tclass._module.com(), $Heap);
                    ##s#29 := s#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s#29, TMap(TSeq(TChar), TInt), $Heap);
                    ##c'#25 := Lit(#_module.com.SKIP());
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c'#25, Tclass._module.com(), $Heap);
                    ##s'#25 := t#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s'#25, TMap(TSeq(TChar), TInt), $Heap);
                    assume _module.__default.small__step__star#canCall(#_module.com.If(b#0, 
                        #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                        Lit(#_module.com.SKIP())), 
                      s#1, 
                      Lit(#_module.com.SKIP()), 
                      t#1);
                    assume _module.__default.small__step__star#canCall(#_module.com.If(b#0, 
                        #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                        Lit(#_module.com.SKIP())), 
                      s#1, 
                      Lit(#_module.com.SKIP()), 
                      t#1);
                    // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(283,7)
                    assume _module.__default.small__step__star($LS($LZ), 
                      #_module.com.If(b#0, 
                        #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                        Lit(#_module.com.SKIP())), 
                      s#1, 
                      Lit(#_module.com.SKIP()), 
                      t#1);
                    // ----- Hint0 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(283,7)
                    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(285,11)
                    ##c#29 := c#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c#29, Tclass._module.com(), $Heap);
                    ##s#30 := s#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s#30, TMap(TSeq(TChar), TInt), $Heap);
                    ##c'#26 := #_module.com.If(b#0, 
                      #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                      Lit(#_module.com.SKIP()));
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c'#26, Tclass._module.com(), $Heap);
                    ##s'#26 := s#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s'#26, TMap(TSeq(TChar), TInt), $Heap);
                    assume _module.__default.small__step#canCall(c#1, 
                      s#1, 
                      #_module.com.If(b#0, 
                        #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                        Lit(#_module.com.SKIP())), 
                      s#1);
                    assume _module.__default.small__step#canCall(c#1, 
                      s#1, 
                      #_module.com.If(b#0, 
                        #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                        Lit(#_module.com.SKIP())), 
                      s#1);
                    assert {:subsumption 0} _module.__default.small__step($LS($LS($LZ)), 
                      c#1, 
                      s#1, 
                      #_module.com.If(b#0, 
                        #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                        Lit(#_module.com.SKIP())), 
                      s#1);
                    assume _module.__default.small__step($LS($LS($LZ)), 
                      c#1, 
                      s#1, 
                      #_module.com.If(b#0, 
                        #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                        Lit(#_module.com.SKIP())), 
                      s#1);
                    // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(283,7)
                    ##c#30 := c#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c#30, Tclass._module.com(), $Heap);
                    ##s#31 := s#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s#31, TMap(TSeq(TChar), TInt), $Heap);
                    ##c'#27 := Lit(#_module.com.SKIP());
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c'#27, Tclass._module.com(), $Heap);
                    ##s'#27 := t#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s'#27, TMap(TSeq(TChar), TInt), $Heap);
                    assume _module.__default.small__step__star#canCall(c#1, s#1, Lit(#_module.com.SKIP()), t#1);
                    assume _module.__default.small__step__star#canCall(c#1, s#1, Lit(#_module.com.SKIP()), t#1);
                    // ----- assert line0 <== line1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(283,7)
                    assert {:subsumption 0} _module.__default.small__step__star($LS($LZ), 
                        #_module.com.If(b#0, 
                          #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                          Lit(#_module.com.SKIP())), 
                        s#1, 
                        Lit(#_module.com.SKIP()), 
                        t#1)
                       ==> 
                      _module.__default.small__step__star#canCall(c#1, s#1, Lit(#_module.com.SKIP()), t#1)
                       ==> _module.__default.small__step__star($LS($LZ), c#1, s#1, Lit(#_module.com.SKIP()), t#1)
                         || 
                        (_module.com#Equal(c#1, #_module.com.SKIP()) && Map#Equal(s#1, t#1))
                         || (exists c''#14: DatatypeType, s''#14: Map Box Box :: 
                          { _module.__default.small__step__star($LS($LS($LZ)), c''#14, s''#14, #_module.com.SKIP(), t#1) } 
                            { _module.__default.small__step($LS($LS($LZ)), c#1, s#1, c''#14, s''#14) } 
                          $Is(c''#14, Tclass._module.com())
                             && $Is(s''#14, TMap(TSeq(TChar), TInt))
                             && 
                            _module.__default.small__step($LS($LS($LZ)), c#1, s#1, c''#14, s''#14)
                             && _module.__default.small__step__star($LS($LS($LZ)), c''#14, s''#14, Lit(#_module.com.SKIP()), t#1));
                    assume false;
                }
                else if (*)
                {
                    // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(283,7)
                    ##c#25 := #_module.com.Seq(body#0, #_module.com.While(b#0, body#0));
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c#25, Tclass._module.com(), $Heap);
                    ##s#26 := s#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s#26, TMap(TSeq(TChar), TInt), $Heap);
                    ##c'#22 := Lit(#_module.com.SKIP());
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c'#22, Tclass._module.com(), $Heap);
                    ##s'#22 := t#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s'#22, TMap(TSeq(TChar), TInt), $Heap);
                    assume _module.__default.small__step__star#canCall(#_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                      s#1, 
                      Lit(#_module.com.SKIP()), 
                      t#1);
                    assume _module.__default.small__step__star#canCall(#_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                      s#1, 
                      Lit(#_module.com.SKIP()), 
                      t#1);
                    // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(283,7)
                    assume _module.__default.small__step__star($LS($LZ), 
                      #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                      s#1, 
                      Lit(#_module.com.SKIP()), 
                      t#1);
                    // ----- Hint1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(283,7)
                    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(287,11)
                    ##c#26 := #_module.com.If(b#0, 
                      #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                      Lit(#_module.com.SKIP()));
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c#26, Tclass._module.com(), $Heap);
                    ##s#27 := s#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s#27, TMap(TSeq(TChar), TInt), $Heap);
                    ##c'#23 := #_module.com.Seq(body#0, #_module.com.While(b#0, body#0));
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c'#23, Tclass._module.com(), $Heap);
                    ##s'#23 := s#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s'#23, TMap(TSeq(TChar), TInt), $Heap);
                    assume _module.__default.small__step#canCall(#_module.com.If(b#0, 
                        #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                        Lit(#_module.com.SKIP())), 
                      s#1, 
                      #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                      s#1);
                    assume _module.__default.small__step#canCall(#_module.com.If(b#0, 
                        #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                        Lit(#_module.com.SKIP())), 
                      s#1, 
                      #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                      s#1);
                    assert {:subsumption 0} _module.__default.small__step($LS($LS($LZ)), 
                      #_module.com.If(b#0, 
                        #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                        Lit(#_module.com.SKIP())), 
                      s#1, 
                      #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                      s#1);
                    assume _module.__default.small__step($LS($LS($LZ)), 
                      #_module.com.If(b#0, 
                        #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                        Lit(#_module.com.SKIP())), 
                      s#1, 
                      #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                      s#1);
                    // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(283,7)
                    ##c#27 := #_module.com.If(b#0, 
                      #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                      Lit(#_module.com.SKIP()));
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c#27, Tclass._module.com(), $Heap);
                    ##s#28 := s#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s#28, TMap(TSeq(TChar), TInt), $Heap);
                    ##c'#24 := Lit(#_module.com.SKIP());
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c'#24, Tclass._module.com(), $Heap);
                    ##s'#24 := t#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s'#24, TMap(TSeq(TChar), TInt), $Heap);
                    assume _module.__default.small__step__star#canCall(#_module.com.If(b#0, 
                        #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                        Lit(#_module.com.SKIP())), 
                      s#1, 
                      Lit(#_module.com.SKIP()), 
                      t#1);
                    assume _module.__default.small__step__star#canCall(#_module.com.If(b#0, 
                        #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                        Lit(#_module.com.SKIP())), 
                      s#1, 
                      Lit(#_module.com.SKIP()), 
                      t#1);
                    // ----- assert line1 <== line2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(283,7)
                    assert {:subsumption 0} _module.__default.small__step__star($LS($LZ), 
                        #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                        s#1, 
                        Lit(#_module.com.SKIP()), 
                        t#1)
                       ==> 
                      _module.__default.small__step__star#canCall(#_module.com.If(b#0, 
                          #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                          Lit(#_module.com.SKIP())), 
                        s#1, 
                        Lit(#_module.com.SKIP()), 
                        t#1)
                       ==> _module.__default.small__step__star($LS($LZ), 
                          #_module.com.If(b#0, 
                            #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                            Lit(#_module.com.SKIP())), 
                          s#1, 
                          Lit(#_module.com.SKIP()), 
                          t#1)
                         || 
                        (_module.com#Equal(#_module.com.If(b#0, 
                              #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                              Lit(#_module.com.SKIP())), 
                            #_module.com.SKIP())
                           && Map#Equal(s#1, t#1))
                         || (exists c''#13: DatatypeType, s''#13: Map Box Box :: 
                          { _module.__default.small__step__star($LS($LS($LZ)), c''#13, s''#13, #_module.com.SKIP(), t#1) } 
                            { _module.__default.small__step($LS($LS($LZ)), 
                              #_module.com.If(b#0, 
                                #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                                #_module.com.SKIP()), 
                              s#1, 
                              c''#13, 
                              s''#13) } 
                          $Is(c''#13, Tclass._module.com())
                             && $Is(s''#13, TMap(TSeq(TChar), TInt))
                             && 
                            _module.__default.small__step($LS($LS($LZ)), 
                              #_module.com.If(b#0, 
                                #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                                Lit(#_module.com.SKIP())), 
                              s#1, 
                              c''#13, 
                              s''#13)
                             && _module.__default.small__step__star($LS($LS($LZ)), c''#13, s''#13, Lit(#_module.com.SKIP()), t#1));
                    assume false;
                }
                else if (*)
                {
                    // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(283,7)
                    ##c#22 := #_module.com.Seq(body#0, #_module.com.While(b#0, body#0));
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c#22, Tclass._module.com(), $Heap);
                    ##s#23 := s#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s#23, TMap(TSeq(TChar), TInt), $Heap);
                    ##c'#19 := #_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0));
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c'#19, Tclass._module.com(), $Heap);
                    ##s'#19 := s'#0;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s'#19, TMap(TSeq(TChar), TInt), $Heap);
                    assume _module.__default.small__step__star#canCall(#_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                      s#1, 
                      #_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0)), 
                      s'#0);
                    if (_module.__default.small__step__star($LS($LZ), 
                      #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                      s#1, 
                      #_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0)), 
                      s'#0))
                    {
                        ##c#23 := #_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0));
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##c#23, Tclass._module.com(), $Heap);
                        ##s#24 := s'#0;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##s#24, TMap(TSeq(TChar), TInt), $Heap);
                        ##c'#20 := Lit(#_module.com.SKIP());
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##c'#20, Tclass._module.com(), $Heap);
                        ##s'#20 := t#1;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##s'#20, TMap(TSeq(TChar), TInt), $Heap);
                        assume _module.__default.small__step__star#canCall(#_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0)), 
                          s'#0, 
                          Lit(#_module.com.SKIP()), 
                          t#1);
                    }

                    assume _module.__default.small__step__star#canCall(#_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                        s#1, 
                        #_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0)), 
                        s'#0)
                       && (_module.__default.small__step__star($LS($LZ), 
                          #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                          s#1, 
                          #_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0)), 
                          s'#0)
                         ==> _module.__default.small__step__star#canCall(#_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0)), 
                          s'#0, 
                          Lit(#_module.com.SKIP()), 
                          t#1));
                    // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(283,7)
                    assume _module.__default.small__step__star($LS($LZ), 
                        #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                        s#1, 
                        #_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0)), 
                        s'#0)
                       && _module.__default.small__step__star($LS($LZ), 
                        #_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0)), 
                        s'#0, 
                        Lit(#_module.com.SKIP()), 
                        t#1);
                    // ----- Hint2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(283,7)
                    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(289,26)
                    // TrCallStmt: Before ProcessCallStmt
                    assume true;
                    // ProcessCallStmt: CheckSubrange
                    c0##1 := #_module.com.Seq(body#0, #_module.com.While(b#0, body#0));
                    assume true;
                    // ProcessCallStmt: CheckSubrange
                    s0##1 := s#1;
                    assume true;
                    // ProcessCallStmt: CheckSubrange
                    c1##1 := #_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0));
                    assume true;
                    // ProcessCallStmt: CheckSubrange
                    s1##0 := s'#0;
                    assume true;
                    // ProcessCallStmt: CheckSubrange
                    c2##0 := Lit(#_module.com.SKIP());
                    assume true;
                    // ProcessCallStmt: CheckSubrange
                    s2##0 := t#1;
                    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                    // ProcessCallStmt: Make the call
                    call Call$$_module.__default.star__transitive(c0##1, s0##1, c1##1, s1##0, c2##0, s2##0);
                    // TrCallStmt: After ProcessCallStmt
                    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(289,95)"} true;
                    // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(283,7)
                    ##c#24 := #_module.com.Seq(body#0, #_module.com.While(b#0, body#0));
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c#24, Tclass._module.com(), $Heap);
                    ##s#25 := s#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s#25, TMap(TSeq(TChar), TInt), $Heap);
                    ##c'#21 := Lit(#_module.com.SKIP());
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c'#21, Tclass._module.com(), $Heap);
                    ##s'#21 := t#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s'#21, TMap(TSeq(TChar), TInt), $Heap);
                    assume _module.__default.small__step__star#canCall(#_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                      s#1, 
                      Lit(#_module.com.SKIP()), 
                      t#1);
                    assume _module.__default.small__step__star#canCall(#_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                      s#1, 
                      Lit(#_module.com.SKIP()), 
                      t#1);
                    // ----- assert line2 <== line3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(283,7)
                    assert {:subsumption 0} _module.__default.small__step__star($LS($LZ), 
                          #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                          s#1, 
                          #_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0)), 
                          s'#0)
                         && _module.__default.small__step__star($LS($LZ), 
                          #_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0)), 
                          s'#0, 
                          Lit(#_module.com.SKIP()), 
                          t#1)
                       ==> 
                      _module.__default.small__step__star#canCall(#_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                        s#1, 
                        Lit(#_module.com.SKIP()), 
                        t#1)
                       ==> _module.__default.small__step__star($LS($LZ), 
                          #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                          s#1, 
                          Lit(#_module.com.SKIP()), 
                          t#1)
                         || 
                        (_module.com#Equal(#_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), #_module.com.SKIP())
                           && Map#Equal(s#1, t#1))
                         || (exists c''#12: DatatypeType, s''#12: Map Box Box :: 
                          { _module.__default.small__step__star($LS($LS($LZ)), c''#12, s''#12, #_module.com.SKIP(), t#1) } 
                            { _module.__default.small__step($LS($LS($LZ)), 
                              #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                              s#1, 
                              c''#12, 
                              s''#12) } 
                          $Is(c''#12, Tclass._module.com())
                             && $Is(s''#12, TMap(TSeq(TChar), TInt))
                             && 
                            _module.__default.small__step($LS($LS($LZ)), 
                              #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                              s#1, 
                              c''#12, 
                              s''#12)
                             && _module.__default.small__step__star($LS($LS($LZ)), c''#12, s''#12, Lit(#_module.com.SKIP()), t#1));
                    assume false;
                }
                else if (*)
                {
                    // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(283,7)
                    ##c#18 := body#0;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c#18, Tclass._module.com(), $Heap);
                    ##s#19 := s#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s#19, TMap(TSeq(TChar), TInt), $Heap);
                    ##c'#15 := Lit(#_module.com.SKIP());
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c'#15, Tclass._module.com(), $Heap);
                    ##s'#15 := s'#0;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s'#15, TMap(TSeq(TChar), TInt), $Heap);
                    assume _module.__default.small__step__star#canCall(body#0, s#1, Lit(#_module.com.SKIP()), s'#0);
                    if (_module.__default.small__step__star($LS($LZ), body#0, s#1, Lit(#_module.com.SKIP()), s'#0))
                    {
                        ##c#19 := #_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0));
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##c#19, Tclass._module.com(), $Heap);
                        ##s#20 := s'#0;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##s#20, TMap(TSeq(TChar), TInt), $Heap);
                        ##c'#16 := Lit(#_module.com.SKIP());
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##c'#16, Tclass._module.com(), $Heap);
                        ##s'#16 := t#1;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##s'#16, TMap(TSeq(TChar), TInt), $Heap);
                        assume _module.__default.small__step__star#canCall(#_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0)), 
                          s'#0, 
                          Lit(#_module.com.SKIP()), 
                          t#1);
                    }

                    assume _module.__default.small__step__star#canCall(body#0, s#1, Lit(#_module.com.SKIP()), s'#0)
                       && (_module.__default.small__step__star($LS($LZ), body#0, s#1, Lit(#_module.com.SKIP()), s'#0)
                         ==> _module.__default.small__step__star#canCall(#_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0)), 
                          s'#0, 
                          Lit(#_module.com.SKIP()), 
                          t#1));
                    // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(283,7)
                    assume _module.__default.small__step__star($LS($LZ), body#0, s#1, Lit(#_module.com.SKIP()), s'#0)
                       && _module.__default.small__step__star($LS($LZ), 
                        #_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0)), 
                        s'#0, 
                        Lit(#_module.com.SKIP()), 
                        t#1);
                    // ----- Hint3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(283,7)
                    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(291,21)
                    // TrCallStmt: Before ProcessCallStmt
                    assume true;
                    // ProcessCallStmt: CheckSubrange
                    c0##0 := body#0;
                    assume true;
                    // ProcessCallStmt: CheckSubrange
                    s0##0 := s#1;
                    assume true;
                    // ProcessCallStmt: CheckSubrange
                    c##0 := Lit(#_module.com.SKIP());
                    assume true;
                    // ProcessCallStmt: CheckSubrange
                    t##0 := s'#0;
                    assume true;
                    // ProcessCallStmt: CheckSubrange
                    c1##0 := #_module.com.While(b#0, body#0);
                    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                    // ProcessCallStmt: Make the call
                    call Call$$_module.__default.lemma__7__13(c0##0, s0##0, c##0, t##0, c1##0);
                    // TrCallStmt: After ProcessCallStmt
                    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(291,55)"} true;
                    // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(283,7)
                    ##c#20 := #_module.com.Seq(body#0, #_module.com.While(b#0, body#0));
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c#20, Tclass._module.com(), $Heap);
                    ##s#21 := s#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s#21, TMap(TSeq(TChar), TInt), $Heap);
                    ##c'#17 := #_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0));
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c'#17, Tclass._module.com(), $Heap);
                    ##s'#17 := s'#0;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s'#17, TMap(TSeq(TChar), TInt), $Heap);
                    assume _module.__default.small__step__star#canCall(#_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                      s#1, 
                      #_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0)), 
                      s'#0);
                    if (_module.__default.small__step__star($LS($LZ), 
                      #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                      s#1, 
                      #_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0)), 
                      s'#0))
                    {
                        ##c#21 := #_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0));
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##c#21, Tclass._module.com(), $Heap);
                        ##s#22 := s'#0;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##s#22, TMap(TSeq(TChar), TInt), $Heap);
                        ##c'#18 := Lit(#_module.com.SKIP());
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##c'#18, Tclass._module.com(), $Heap);
                        ##s'#18 := t#1;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##s'#18, TMap(TSeq(TChar), TInt), $Heap);
                        assume _module.__default.small__step__star#canCall(#_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0)), 
                          s'#0, 
                          Lit(#_module.com.SKIP()), 
                          t#1);
                    }

                    assume _module.__default.small__step__star#canCall(#_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                        s#1, 
                        #_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0)), 
                        s'#0)
                       && (_module.__default.small__step__star($LS($LZ), 
                          #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                          s#1, 
                          #_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0)), 
                          s'#0)
                         ==> _module.__default.small__step__star#canCall(#_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0)), 
                          s'#0, 
                          Lit(#_module.com.SKIP()), 
                          t#1));
                    // ----- assert line3 <== line4 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(283,7)
                    assert {:subsumption 0} _module.__default.small__step__star($LS($LZ), body#0, s#1, Lit(#_module.com.SKIP()), s'#0)
                         && _module.__default.small__step__star($LS($LZ), 
                          #_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0)), 
                          s'#0, 
                          Lit(#_module.com.SKIP()), 
                          t#1)
                       ==> 
                      _module.__default.small__step__star#canCall(#_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                        s#1, 
                        #_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0)), 
                        s'#0)
                       ==> _module.__default.small__step__star($LS($LZ), 
                          #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                          s#1, 
                          #_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0)), 
                          s'#0)
                         || 
                        (_module.com#Equal(#_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                            #_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0)))
                           && Map#Equal(s#1, s'#0))
                         || (exists c''#10: DatatypeType, s''#10: Map Box Box :: 
                          { _module.__default.small__step__star($LS($LS($LZ)), 
                              c''#10, 
                              s''#10, 
                              #_module.com.Seq(#_module.com.SKIP(), #_module.com.While(b#0, body#0)), 
                              s'#0) } 
                            { _module.__default.small__step($LS($LS($LZ)), 
                              #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                              s#1, 
                              c''#10, 
                              s''#10) } 
                          $Is(c''#10, Tclass._module.com())
                             && $Is(s''#10, TMap(TSeq(TChar), TInt))
                             && 
                            _module.__default.small__step($LS($LS($LZ)), 
                              #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                              s#1, 
                              c''#10, 
                              s''#10)
                             && _module.__default.small__step__star($LS($LS($LZ)), 
                              c''#10, 
                              s''#10, 
                              #_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0)), 
                              s'#0));
                    assert {:subsumption 0} _module.__default.small__step__star($LS($LZ), body#0, s#1, Lit(#_module.com.SKIP()), s'#0)
                         && _module.__default.small__step__star($LS($LZ), 
                          #_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0)), 
                          s'#0, 
                          Lit(#_module.com.SKIP()), 
                          t#1)
                       ==> 
                      _module.__default.small__step__star#canCall(#_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0)), 
                        s'#0, 
                        Lit(#_module.com.SKIP()), 
                        t#1)
                       ==> _module.__default.small__step__star($LS($LZ), 
                          #_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0)), 
                          s'#0, 
                          Lit(#_module.com.SKIP()), 
                          t#1)
                         || 
                        (_module.com#Equal(#_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0)), 
                            #_module.com.SKIP())
                           && Map#Equal(s'#0, t#1))
                         || (exists c''#11: DatatypeType, s''#11: Map Box Box :: 
                          { _module.__default.small__step__star($LS($LS($LZ)), c''#11, s''#11, #_module.com.SKIP(), t#1) } 
                            { _module.__default.small__step($LS($LS($LZ)), 
                              #_module.com.Seq(#_module.com.SKIP(), #_module.com.While(b#0, body#0)), 
                              s'#0, 
                              c''#11, 
                              s''#11) } 
                          $Is(c''#11, Tclass._module.com())
                             && $Is(s''#11, TMap(TSeq(TChar), TInt))
                             && 
                            _module.__default.small__step($LS($LS($LZ)), 
                              #_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0)), 
                              s'#0, 
                              c''#11, 
                              s''#11)
                             && _module.__default.small__step__star($LS($LS($LZ)), c''#11, s''#11, Lit(#_module.com.SKIP()), t#1));
                    assume false;
                }
                else if (*)
                {
                    // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(283,7)
                    ##c#15 := #_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0));
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c#15, Tclass._module.com(), $Heap);
                    ##s#16 := s'#0;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s#16, TMap(TSeq(TChar), TInt), $Heap);
                    ##c'#12 := Lit(#_module.com.SKIP());
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c'#12, Tclass._module.com(), $Heap);
                    ##s'#12 := t#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s'#12, TMap(TSeq(TChar), TInt), $Heap);
                    assume _module.__default.small__step__star#canCall(#_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0)), 
                      s'#0, 
                      Lit(#_module.com.SKIP()), 
                      t#1);
                    assume _module.__default.small__step__star#canCall(#_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0)), 
                      s'#0, 
                      Lit(#_module.com.SKIP()), 
                      t#1);
                    // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(283,7)
                    assume _module.__default.small__step__star($LS($LZ), 
                      #_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0)), 
                      s'#0, 
                      Lit(#_module.com.SKIP()), 
                      t#1);
                    // ----- Hint4 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(283,7)
                    // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(283,7)
                    ##c#16 := body#0;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c#16, Tclass._module.com(), $Heap);
                    ##s#17 := s#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s#17, TMap(TSeq(TChar), TInt), $Heap);
                    ##c'#13 := Lit(#_module.com.SKIP());
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c'#13, Tclass._module.com(), $Heap);
                    ##s'#13 := s'#0;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s'#13, TMap(TSeq(TChar), TInt), $Heap);
                    assume _module.__default.small__step__star#canCall(body#0, s#1, Lit(#_module.com.SKIP()), s'#0);
                    if (_module.__default.small__step__star($LS($LZ), body#0, s#1, Lit(#_module.com.SKIP()), s'#0))
                    {
                        ##c#17 := #_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0));
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##c#17, Tclass._module.com(), $Heap);
                        ##s#18 := s'#0;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##s#18, TMap(TSeq(TChar), TInt), $Heap);
                        ##c'#14 := Lit(#_module.com.SKIP());
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##c'#14, Tclass._module.com(), $Heap);
                        ##s'#14 := t#1;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##s'#14, TMap(TSeq(TChar), TInt), $Heap);
                        assume _module.__default.small__step__star#canCall(#_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0)), 
                          s'#0, 
                          Lit(#_module.com.SKIP()), 
                          t#1);
                    }

                    assume _module.__default.small__step__star#canCall(body#0, s#1, Lit(#_module.com.SKIP()), s'#0)
                       && (_module.__default.small__step__star($LS($LZ), body#0, s#1, Lit(#_module.com.SKIP()), s'#0)
                         ==> _module.__default.small__step__star#canCall(#_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0)), 
                          s'#0, 
                          Lit(#_module.com.SKIP()), 
                          t#1));
                    // ----- assert line4 <== line5 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(283,7)
                    assert {:subsumption 0} _module.__default.small__step__star($LS($LZ), 
                        #_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0)), 
                        s'#0, 
                        Lit(#_module.com.SKIP()), 
                        t#1)
                       ==> 
                      _module.__default.small__step__star#canCall(body#0, s#1, Lit(#_module.com.SKIP()), s'#0)
                       ==> _module.__default.small__step__star($LS($LZ), body#0, s#1, Lit(#_module.com.SKIP()), s'#0)
                         || 
                        (_module.com#Equal(body#0, #_module.com.SKIP()) && Map#Equal(s#1, s'#0))
                         || (exists c''#8: DatatypeType, s''#8: Map Box Box :: 
                          { _module.__default.small__step__star($LS($LS($LZ)), c''#8, s''#8, #_module.com.SKIP(), s'#0) } 
                            { _module.__default.small__step($LS($LS($LZ)), body#0, s#1, c''#8, s''#8) } 
                          $Is(c''#8, Tclass._module.com())
                             && $Is(s''#8, TMap(TSeq(TChar), TInt))
                             && 
                            _module.__default.small__step($LS($LS($LZ)), body#0, s#1, c''#8, s''#8)
                             && _module.__default.small__step__star($LS($LS($LZ)), c''#8, s''#8, Lit(#_module.com.SKIP()), s'#0));
                    assert {:subsumption 0} _module.__default.small__step__star($LS($LZ), 
                        #_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0)), 
                        s'#0, 
                        Lit(#_module.com.SKIP()), 
                        t#1)
                       ==> 
                      _module.__default.small__step__star#canCall(#_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0)), 
                        s'#0, 
                        Lit(#_module.com.SKIP()), 
                        t#1)
                       ==> _module.__default.small__step__star($LS($LZ), 
                          #_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0)), 
                          s'#0, 
                          Lit(#_module.com.SKIP()), 
                          t#1)
                         || 
                        (_module.com#Equal(#_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0)), 
                            #_module.com.SKIP())
                           && Map#Equal(s'#0, t#1))
                         || (exists c''#9: DatatypeType, s''#9: Map Box Box :: 
                          { _module.__default.small__step__star($LS($LS($LZ)), c''#9, s''#9, #_module.com.SKIP(), t#1) } 
                            { _module.__default.small__step($LS($LS($LZ)), 
                              #_module.com.Seq(#_module.com.SKIP(), #_module.com.While(b#0, body#0)), 
                              s'#0, 
                              c''#9, 
                              s''#9) } 
                          $Is(c''#9, Tclass._module.com())
                             && $Is(s''#9, TMap(TSeq(TChar), TInt))
                             && 
                            _module.__default.small__step($LS($LS($LZ)), 
                              #_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0)), 
                              s'#0, 
                              c''#9, 
                              s''#9)
                             && _module.__default.small__step__star($LS($LS($LZ)), c''#9, s''#9, Lit(#_module.com.SKIP()), t#1));
                    assume false;
                }
                else if (*)
                {
                    // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(283,7)
                    ##c#12 := #_module.com.While(b#0, body#0);
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c#12, Tclass._module.com(), $Heap);
                    ##s#13 := s'#0;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s#13, TMap(TSeq(TChar), TInt), $Heap);
                    ##c'#9 := Lit(#_module.com.SKIP());
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c'#9, Tclass._module.com(), $Heap);
                    ##s'#9 := t#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s'#9, TMap(TSeq(TChar), TInt), $Heap);
                    assume _module.__default.small__step__star#canCall(#_module.com.While(b#0, body#0), s'#0, Lit(#_module.com.SKIP()), t#1);
                    assume _module.__default.small__step__star#canCall(#_module.com.While(b#0, body#0), s'#0, Lit(#_module.com.SKIP()), t#1);
                    // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(283,7)
                    assume _module.__default.small__step__star($LS($LZ), #_module.com.While(b#0, body#0), s'#0, Lit(#_module.com.SKIP()), t#1);
                    // ----- Hint5 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(283,7)
                    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(295,11)
                    ##c#13 := #_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0));
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c#13, Tclass._module.com(), $Heap);
                    ##s#14 := s'#0;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s#14, TMap(TSeq(TChar), TInt), $Heap);
                    ##c'#10 := #_module.com.While(b#0, body#0);
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c'#10, Tclass._module.com(), $Heap);
                    ##s'#10 := s'#0;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s'#10, TMap(TSeq(TChar), TInt), $Heap);
                    assume _module.__default.small__step#canCall(#_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0)), 
                      s'#0, 
                      #_module.com.While(b#0, body#0), 
                      s'#0);
                    assume _module.__default.small__step#canCall(#_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0)), 
                      s'#0, 
                      #_module.com.While(b#0, body#0), 
                      s'#0);
                    assert {:subsumption 0} _module.__default.small__step($LS($LS($LZ)), 
                      #_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0)), 
                      s'#0, 
                      #_module.com.While(b#0, body#0), 
                      s'#0);
                    assume _module.__default.small__step($LS($LS($LZ)), 
                      #_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0)), 
                      s'#0, 
                      #_module.com.While(b#0, body#0), 
                      s'#0);
                    // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(283,7)
                    ##c#14 := #_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0));
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c#14, Tclass._module.com(), $Heap);
                    ##s#15 := s'#0;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s#15, TMap(TSeq(TChar), TInt), $Heap);
                    ##c'#11 := Lit(#_module.com.SKIP());
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c'#11, Tclass._module.com(), $Heap);
                    ##s'#11 := t#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s'#11, TMap(TSeq(TChar), TInt), $Heap);
                    assume _module.__default.small__step__star#canCall(#_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0)), 
                      s'#0, 
                      Lit(#_module.com.SKIP()), 
                      t#1);
                    assume _module.__default.small__step__star#canCall(#_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0)), 
                      s'#0, 
                      Lit(#_module.com.SKIP()), 
                      t#1);
                    // ----- assert line5 <== line6 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(283,7)
                    assert {:subsumption 0} _module.__default.small__step__star($LS($LZ), #_module.com.While(b#0, body#0), s'#0, Lit(#_module.com.SKIP()), t#1)
                       ==> 
                      _module.__default.small__step__star#canCall(#_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0)), 
                        s'#0, 
                        Lit(#_module.com.SKIP()), 
                        t#1)
                       ==> _module.__default.small__step__star($LS($LZ), 
                          #_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0)), 
                          s'#0, 
                          Lit(#_module.com.SKIP()), 
                          t#1)
                         || 
                        (_module.com#Equal(#_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0)), 
                            #_module.com.SKIP())
                           && Map#Equal(s'#0, t#1))
                         || (exists c''#7: DatatypeType, s''#7: Map Box Box :: 
                          { _module.__default.small__step__star($LS($LS($LZ)), c''#7, s''#7, #_module.com.SKIP(), t#1) } 
                            { _module.__default.small__step($LS($LS($LZ)), 
                              #_module.com.Seq(#_module.com.SKIP(), #_module.com.While(b#0, body#0)), 
                              s'#0, 
                              c''#7, 
                              s''#7) } 
                          $Is(c''#7, Tclass._module.com())
                             && $Is(s''#7, TMap(TSeq(TChar), TInt))
                             && 
                            _module.__default.small__step($LS($LS($LZ)), 
                              #_module.com.Seq(Lit(#_module.com.SKIP()), #_module.com.While(b#0, body#0)), 
                              s'#0, 
                              c''#7, 
                              s''#7)
                             && _module.__default.small__step__star($LS($LS($LZ)), c''#7, s''#7, Lit(#_module.com.SKIP()), t#1));
                    assume false;
                }
                else if (*)
                {
                    // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(283,7)
                    assume true;
                    // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(283,7)
                    assume true;
                    // ----- Hint6 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(283,7)
                    // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(283,7)
                    ##c#11 := #_module.com.While(b#0, body#0);
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c#11, Tclass._module.com(), $Heap);
                    ##s#12 := s'#0;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s#12, TMap(TSeq(TChar), TInt), $Heap);
                    ##c'#8 := Lit(#_module.com.SKIP());
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c'#8, Tclass._module.com(), $Heap);
                    ##s'#8 := t#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s'#8, TMap(TSeq(TChar), TInt), $Heap);
                    assume _module.__default.small__step__star#canCall(#_module.com.While(b#0, body#0), s'#0, Lit(#_module.com.SKIP()), t#1);
                    assume _module.__default.small__step__star#canCall(#_module.com.While(b#0, body#0), s'#0, Lit(#_module.com.SKIP()), t#1);
                    // ----- assert line6 <== line7 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(283,7)
                    assert {:subsumption 0} Lit(true)
                       ==> 
                      _module.__default.small__step__star#canCall(#_module.com.While(b#0, body#0), s'#0, Lit(#_module.com.SKIP()), t#1)
                       ==> _module.__default.small__step__star($LS($LZ), #_module.com.While(b#0, body#0), s'#0, Lit(#_module.com.SKIP()), t#1)
                         || 
                        (_module.com#Equal(#_module.com.While(b#0, body#0), #_module.com.SKIP())
                           && Map#Equal(s'#0, t#1))
                         || (exists c''#6: DatatypeType, s''#6: Map Box Box :: 
                          { _module.__default.small__step__star($LS($LS($LZ)), c''#6, s''#6, #_module.com.SKIP(), t#1) } 
                            { _module.__default.small__step($LS($LS($LZ)), #_module.com.While(b#0, body#0), s'#0, c''#6, s''#6) } 
                          $Is(c''#6, Tclass._module.com())
                             && $Is(s''#6, TMap(TSeq(TChar), TInt))
                             && 
                            _module.__default.small__step($LS($LS($LZ)), #_module.com.While(b#0, body#0), s'#0, c''#6, s''#6)
                             && _module.__default.small__step__star($LS($LS($LZ)), c''#6, s''#6, Lit(#_module.com.SKIP()), t#1));
                    assume false;
                }

                assume true
                   ==> _module.__default.small__step__star($LS($LZ), c#1, s#1, Lit(#_module.com.SKIP()), t#1);
            }
        }
        else
        {
            assume false;
        }
    }
    else
    {
        // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(246,13)
        $initHeapForallStmt#1 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#1 == $Heap;
        assume (forall _k'#0: Box, c#2: DatatypeType, s#2: Map Box Box, t#2: Map Box Box :: 
          $Is(c#2, Tclass._module.com())
               && $Is(s#2, TMap(TSeq(TChar), TInt))
               && $Is(t#2, TMap(TSeq(TChar), TInt))
               && 
              ORD#Less(_k'#0, _k#0)
               && _module.__default.big__step_h($LS($LZ), _k'#0, c#2, s#2, t#2)
             ==> _module.__default.small__step__star($LS($LZ), c#2, s#2, Lit(#_module.com.SKIP()), t#2));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(246,12)"} true;
    }
}



procedure CheckWellformed$$_module.__default.lemma__7__13(c0#0: DatatypeType
       where $Is(c0#0, Tclass._module.com())
         && $IsAlloc(c0#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c0#0), 
    s0#0: Map Box Box
       where $Is(s0#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s0#0, TMap(TSeq(TChar), TInt), $Heap), 
    c#0: DatatypeType
       where $Is(c#0, Tclass._module.com())
         && $IsAlloc(c#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#0), 
    t#0: Map Box Box
       where $Is(t#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(t#0, TMap(TSeq(TChar), TInt), $Heap), 
    c1#0: DatatypeType
       where $Is(c1#0, Tclass._module.com())
         && $IsAlloc(c1#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c1#0));
  free requires 20 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.lemma__7__13(c0#0: DatatypeType
       where $Is(c0#0, Tclass._module.com())
         && $IsAlloc(c0#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c0#0), 
    s0#0: Map Box Box
       where $Is(s0#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s0#0, TMap(TSeq(TChar), TInt), $Heap), 
    c#0: DatatypeType
       where $Is(c#0, Tclass._module.com())
         && $IsAlloc(c#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#0), 
    t#0: Map Box Box
       where $Is(t#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(t#0, TMap(TSeq(TChar), TInt), $Heap), 
    c1#0: DatatypeType
       where $Is(c1#0, Tclass._module.com())
         && $IsAlloc(c1#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c1#0));
  // user-defined preconditions
  requires _module.__default.small__step__star#canCall(c0#0, s0#0, c#0, t#0)
     ==> _module.__default.small__step__star($LS($LZ), c0#0, s0#0, c#0, t#0)
       || 
      (_module.com#Equal(c0#0, c#0) && Map#Equal(s0#0, t#0))
       || (exists c''#0: DatatypeType, s''#0: Map Box Box :: 
        { _module.__default.small__step__star($LS($LS($LZ)), c''#0, s''#0, c#0, t#0) } 
          { _module.__default.small__step($LS($LS($LZ)), c0#0, s0#0, c''#0, s''#0) } 
        $Is(c''#0, Tclass._module.com())
           && $Is(s''#0, TMap(TSeq(TChar), TInt))
           && 
          _module.__default.small__step($LS($LS($LZ)), c0#0, s0#0, c''#0, s''#0)
           && _module.__default.small__step__star($LS($LS($LZ)), c''#0, s''#0, c#0, t#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.small__step__star#canCall(#_module.com.Seq(c0#0, c1#0), s0#0, #_module.com.Seq(c#0, c1#0), t#0);
  free ensures _module.__default.small__step__star#canCall(#_module.com.Seq(c0#0, c1#0), s0#0, #_module.com.Seq(c#0, c1#0), t#0)
     && 
    _module.__default.small__step__star($LS($LZ), #_module.com.Seq(c0#0, c1#0), s0#0, #_module.com.Seq(c#0, c1#0), t#0)
     && ((_module.com#Equal(#_module.com.Seq(c0#0, c1#0), #_module.com.Seq(c#0, c1#0))
         && Map#Equal(s0#0, t#0))
       || (exists c''#1: DatatypeType, s''#1: Map Box Box :: 
        { _module.__default.small__step__star($LS($LZ), c''#1, s''#1, #_module.com.Seq(c#0, c1#0), t#0) } 
          { _module.__default.small__step($LS($LZ), #_module.com.Seq(c0#0, c1#0), s0#0, c''#1, s''#1) } 
        $Is(c''#1, Tclass._module.com())
           && $Is(s''#1, TMap(TSeq(TChar), TInt))
           && 
          _module.__default.small__step($LS($LZ), #_module.com.Seq(c0#0, c1#0), s0#0, c''#1, s''#1)
           && _module.__default.small__step__star($LS($LZ), c''#1, s''#1, #_module.com.Seq(c#0, c1#0), t#0)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, c0#1, s0#1, c#1, t#1, c1#1} CoCall$$_module.__default.lemma__7__13_h(_k#0: Box, 
    c0#1: DatatypeType
       where $Is(c0#1, Tclass._module.com())
         && $IsAlloc(c0#1, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c0#1), 
    s0#1: Map Box Box
       where $Is(s0#1, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s0#1, TMap(TSeq(TChar), TInt), $Heap), 
    c#1: DatatypeType
       where $Is(c#1, Tclass._module.com())
         && $IsAlloc(c#1, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#1), 
    t#1: Map Box Box
       where $Is(t#1, TMap(TSeq(TChar), TInt))
         && $IsAlloc(t#1, TMap(TSeq(TChar), TInt), $Heap), 
    c1#1: DatatypeType
       where $Is(c1#1, Tclass._module.com())
         && $IsAlloc(c1#1, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c1#1));
  // user-defined preconditions
  requires _module.__default.small__step__star_h#canCall(_k#0, c0#1, s0#1, c#1, t#1)
     ==> _module.__default.small__step__star_h($LS($LZ), _k#0, c0#1, s0#1, c#1, t#1)
       || (0 < ORD#Offset(_k#0)
         ==> (_module.com#Equal(c0#1, c#1) && Map#Equal(s0#1, t#1))
           || (exists c''#2: DatatypeType, s''#2: Map Box Box :: 
            { _module.__default.small__step__star_h($LS($LS($LZ)), ORD#Minus(_k#0, ORD#FromNat(1)), c''#2, s''#2, c#1, t#1) } 
              { _module.__default.small__step($LS($LS($LZ)), c0#1, s0#1, c''#2, s''#2) } 
            $Is(c''#2, Tclass._module.com())
               && $Is(s''#2, TMap(TSeq(TChar), TInt))
               && 
              _module.__default.small__step($LS($LS($LZ)), c0#1, s0#1, c''#2, s''#2)
               && _module.__default.small__step__star_h($LS($LS($LZ)), ORD#Minus(_k#0, ORD#FromNat(1)), c''#2, s''#2, c#1, t#1)));
  requires _module.__default.small__step__star_h#canCall(_k#0, c0#1, s0#1, c#1, t#1)
     ==> _module.__default.small__step__star_h($LS($LZ), _k#0, c0#1, s0#1, c#1, t#1)
       || (LitInt(0) == ORD#Offset(_k#0)
         ==> (exists _k'#0: Box :: 
          { _module.__default.small__step__star_h($LS($LZ), _k'#0, c0#1, s0#1, c#1, t#1) } 
          ORD#LessThanLimit(_k'#0, _k#0)
             && _module.__default.small__step__star_h($LS($LZ), _k'#0, c0#1, s0#1, c#1, t#1)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.small__step__star#canCall(#_module.com.Seq(c0#1, c1#1), s0#1, #_module.com.Seq(c#1, c1#1), t#1);
  free ensures _module.__default.small__step__star#canCall(#_module.com.Seq(c0#1, c1#1), s0#1, #_module.com.Seq(c#1, c1#1), t#1)
     && 
    _module.__default.small__step__star($LS($LZ), #_module.com.Seq(c0#1, c1#1), s0#1, #_module.com.Seq(c#1, c1#1), t#1)
     && ((_module.com#Equal(#_module.com.Seq(c0#1, c1#1), #_module.com.Seq(c#1, c1#1))
         && Map#Equal(s0#1, t#1))
       || (exists c''#3: DatatypeType, s''#3: Map Box Box :: 
        { _module.__default.small__step__star($LS($LZ), c''#3, s''#3, #_module.com.Seq(c#1, c1#1), t#1) } 
          { _module.__default.small__step($LS($LZ), #_module.com.Seq(c0#1, c1#1), s0#1, c''#3, s''#3) } 
        $Is(c''#3, Tclass._module.com())
           && $Is(s''#3, TMap(TSeq(TChar), TInt))
           && 
          _module.__default.small__step($LS($LZ), #_module.com.Seq(c0#1, c1#1), s0#1, c''#3, s''#3)
           && _module.__default.small__step__star($LS($LZ), c''#3, s''#3, #_module.com.Seq(c#1, c1#1), t#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, c0#1, s0#1, c#1, t#1, c1#1} Impl$$_module.__default.lemma__7__13_h(_k#0: Box, 
    c0#1: DatatypeType
       where $Is(c0#1, Tclass._module.com())
         && $IsAlloc(c0#1, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c0#1), 
    s0#1: Map Box Box
       where $Is(s0#1, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s0#1, TMap(TSeq(TChar), TInt), $Heap), 
    c#1: DatatypeType
       where $Is(c#1, Tclass._module.com())
         && $IsAlloc(c#1, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#1), 
    t#1: Map Box Box
       where $Is(t#1, TMap(TSeq(TChar), TInt))
         && $IsAlloc(t#1, TMap(TSeq(TChar), TInt), $Heap), 
    c1#1: DatatypeType
       where $Is(c1#1, Tclass._module.com())
         && $IsAlloc(c1#1, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c1#1))
   returns ($_reverifyPost: bool);
  free requires 23 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.__default.small__step__star_h#canCall(_k#0, c0#1, s0#1, c#1, t#1)
     && 
    _module.__default.small__step__star_h($LS($LZ), _k#0, c0#1, s0#1, c#1, t#1)
     && 
    (0 < ORD#Offset(_k#0)
       ==> (_module.com#Equal(c0#1, c#1) && Map#Equal(s0#1, t#1))
         || (exists c''#4: DatatypeType, s''#4: Map Box Box :: 
          { _module.__default.small__step__star_h($LS($LZ), ORD#Minus(_k#0, ORD#FromNat(1)), c''#4, s''#4, c#1, t#1) } 
            { _module.__default.small__step($LS($LZ), c0#1, s0#1, c''#4, s''#4) } 
          $Is(c''#4, Tclass._module.com())
             && $Is(s''#4, TMap(TSeq(TChar), TInt))
             && 
            _module.__default.small__step($LS($LZ), c0#1, s0#1, c''#4, s''#4)
             && _module.__default.small__step__star_h($LS($LZ), ORD#Minus(_k#0, ORD#FromNat(1)), c''#4, s''#4, c#1, t#1)))
     && (LitInt(0) == ORD#Offset(_k#0)
       ==> (exists _k'#1: Box :: 
        { _module.__default.small__step__star_h($LS($LZ), _k'#1, c0#1, s0#1, c#1, t#1) } 
        ORD#LessThanLimit(_k'#1, _k#0)
           && _module.__default.small__step__star_h($LS($LZ), _k'#1, c0#1, s0#1, c#1, t#1)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.small__step__star#canCall(#_module.com.Seq(c0#1, c1#1), s0#1, #_module.com.Seq(c#1, c1#1), t#1);
  ensures _module.__default.small__step__star#canCall(#_module.com.Seq(c0#1, c1#1), s0#1, #_module.com.Seq(c#1, c1#1), t#1)
     ==> _module.__default.small__step__star($LS($LZ), #_module.com.Seq(c0#1, c1#1), s0#1, #_module.com.Seq(c#1, c1#1), t#1)
       || 
      (_module.com#Equal(#_module.com.Seq(c0#1, c1#1), #_module.com.Seq(c#1, c1#1))
         && Map#Equal(s0#1, t#1))
       || (exists c''#5: DatatypeType, s''#5: Map Box Box :: 
        { _module.__default.small__step__star($LS($LS($LZ)), c''#5, s''#5, #_module.com.Seq(c#1, c1#1), t#1) } 
          { _module.__default.small__step($LS($LS($LZ)), #_module.com.Seq(c0#1, c1#1), s0#1, c''#5, s''#5) } 
        $Is(c''#5, Tclass._module.com())
           && $Is(s''#5, TMap(TSeq(TChar), TInt))
           && 
          _module.__default.small__step($LS($LS($LZ)), #_module.com.Seq(c0#1, c1#1), s0#1, c''#5, s''#5)
           && _module.__default.small__step__star($LS($LS($LZ)), c''#5, s''#5, #_module.com.Seq(c#1, c1#1), t#1));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0, c0#1, s0#1, c#1, t#1, c1#1} Impl$$_module.__default.lemma__7__13_h(_k#0: Box, 
    c0#1: DatatypeType, 
    s0#1: Map Box Box, 
    c#1: DatatypeType, 
    t#1: Map Box Box, 
    c1#1: DatatypeType)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var c'#0: DatatypeType
     where $Is(c'#0, Tclass._module.com()) && $IsAlloc(c'#0, Tclass._module.com(), $Heap);
  var s'#0: Map Box Box
     where $Is(s'#0, TMap(TSeq(TChar), TInt))
       && $IsAlloc(s'#0, TMap(TSeq(TChar), TInt), $Heap);
  var c'#1: DatatypeType;
  var s'#1: Map Box Box;
  var ##c#2: DatatypeType;
  var ##s#2: Map Box Box;
  var ##c'#2: DatatypeType;
  var ##s'#2: Map Box Box;
  var ##_k#0: Box;
  var ##c#3: DatatypeType;
  var ##s#3: Map Box Box;
  var ##c'#3: DatatypeType;
  var ##s'#3: Map Box Box;
  var _k##0: Box;
  var c0##0: DatatypeType;
  var s0##0: Map Box Box;
  var c##0: DatatypeType;
  var t##0: Map Box Box;
  var c1##0: DatatypeType;
  var $initHeapForallStmt#1: Heap;

    // AddMethodImpl: lemma_7_13#, Impl$$_module.__default.lemma__7__13_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(303,12): initial state"} true;
    assume $IsA#_module.com(c0#1);
    assume $IsA#_module.com(c#1);
    assume $IsA#_module.com(c1#1);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: Box, 
        $ih#c00#0: DatatypeType, 
        $ih#s00#0: Map Box Box, 
        $ih#c0#0: DatatypeType, 
        $ih#t0#0: Map Box Box, 
        $ih#c10#0: DatatypeType :: 
      $Is($ih#c00#0, Tclass._module.com())
           && $Is($ih#s00#0, TMap(TSeq(TChar), TInt))
           && $Is($ih#c0#0, Tclass._module.com())
           && $Is($ih#t0#0, TMap(TSeq(TChar), TInt))
           && $Is($ih#c10#0, Tclass._module.com())
           && _module.__default.small__step__star_h($LS($LZ), $ih#_k0#0, $ih#c00#0, $ih#s00#0, $ih#c0#0, $ih#t0#0)
           && (ORD#Less($ih#_k0#0, _k#0)
             || ($ih#_k0#0 == _k#0
               && (DtRank($ih#c00#0) < DtRank(c0#1)
                 || (DtRank($ih#c00#0) == DtRank(c0#1)
                   && ((Set#Subset(Map#Domain($ih#s00#0), Map#Domain(s0#1))
                       && !Set#Subset(Map#Domain(s0#1), Map#Domain($ih#s00#0)))
                     || (Set#Equal(Map#Domain($ih#s00#0), Map#Domain(s0#1))
                       && (DtRank($ih#c0#0) < DtRank(c#1)
                         || (DtRank($ih#c0#0) == DtRank(c#1)
                           && ((Set#Subset(Map#Domain($ih#t0#0), Map#Domain(t#1))
                               && !Set#Subset(Map#Domain(t#1), Map#Domain($ih#t0#0)))
                             || (Set#Equal(Map#Domain($ih#t0#0), Map#Domain(t#1))
                               && DtRank($ih#c10#0) < DtRank(c1#1)))))))))))
         ==> _module.__default.small__step__star($LS($LZ), 
          #_module.com.Seq($ih#c00#0, $ih#c10#0), 
          $ih#s00#0, 
          #_module.com.Seq($ih#c0#0, $ih#c10#0), 
          $ih#t0#0));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(306,1)
    assume true;
    if (0 < ORD#Offset(_k#0))
    {
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(307,3)
        if (_module.com#Equal(c0#1, c#1))
        {
        }

        assume $IsA#_module.com(c0#1) && $IsA#_module.com(c#1);
        if (_module.com#Equal(c0#1, c#1) && Map#Equal(s0#1, t#1))
        {
        }
        else
        {
            // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(309,16)
            havoc c'#1;
            havoc s'#1;
            if ($Is(c'#1, Tclass._module.com())
               && $IsAlloc(c'#1, Tclass._module.com(), $Heap)
               && 
              $Is(s'#1, TMap(TSeq(TChar), TInt))
               && $IsAlloc(s'#1, TMap(TSeq(TChar), TInt), $Heap))
            {
                ##c#2 := c0#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##c#2, Tclass._module.com(), $Heap);
                ##s#2 := s0#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#2, TMap(TSeq(TChar), TInt), $Heap);
                ##c'#2 := c'#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##c'#2, Tclass._module.com(), $Heap);
                ##s'#2 := s'#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s'#2, TMap(TSeq(TChar), TInt), $Heap);
                assume _module.__default.small__step#canCall(c0#1, s0#1, c'#1, s'#1);
                if (_module.__default.small__step($LS($LZ), c0#1, s0#1, c'#1, s'#1))
                {
                    assert ORD#IsNat(Lit(ORD#FromNat(1)));
                    assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
                    ##_k#0 := ORD#Minus(_k#0, ORD#FromNat(1));
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##_k#0, TORDINAL, $Heap);
                    ##c#3 := c'#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c#3, Tclass._module.com(), $Heap);
                    ##s#3 := s'#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s#3, TMap(TSeq(TChar), TInt), $Heap);
                    ##c'#3 := c#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c'#3, Tclass._module.com(), $Heap);
                    ##s'#3 := t#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s'#3, TMap(TSeq(TChar), TInt), $Heap);
                    assume _module.__default.small__step__star_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), c'#1, s'#1, c#1, t#1);
                }

                assume _module.__default.small__step#canCall(c0#1, s0#1, c'#1, s'#1)
                   && (_module.__default.small__step($LS($LZ), c0#1, s0#1, c'#1, s'#1)
                     ==> _module.__default.small__step__star_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), c'#1, s'#1, c#1, t#1));
            }

            assert (exists $as#s'0_0#0: Map Box Box :: 
                $Is($as#s'0_0#0, TMap(TSeq(TChar), TInt))
                   && 
                  $Is(Lit(#_module.com.SKIP()), Tclass._module.com())
                   && 
                  _module.__default.small__step($LS($LZ), c0#1, s0#1, Lit(#_module.com.SKIP()), $as#s'0_0#0)
                   && _module.__default.small__step__star_h($LS($LZ), 
                    ORD#Minus(_k#0, ORD#FromNat(1)), 
                    Lit(#_module.com.SKIP()), 
                    $as#s'0_0#0, 
                    c#1, 
                    t#1))
               || (exists $as#c'0_0#0: DatatypeType, $as#s'0_0#0: Map Box Box :: 
                $Is($as#c'0_0#0, Tclass._module.com())
                   && $Is($as#s'0_0#0, TMap(TSeq(TChar), TInt))
                   && 
                  _module.__default.small__step($LS($LZ), c0#1, s0#1, $as#c'0_0#0, $as#s'0_0#0)
                   && _module.__default.small__step__star_h($LS($LZ), ORD#Minus(_k#0, ORD#FromNat(1)), $as#c'0_0#0, $as#s'0_0#0, c#1, t#1));
            havoc c'#0, s'#0;
            assume _module.__default.small__step($LS($LZ), c0#1, s0#1, c'#0, s'#0)
               && _module.__default.small__step__star_h($LS($LZ), ORD#Minus(_k#0, ORD#FromNat(1)), c'#0, s'#0, c#1, t#1);
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(309,77)"} true;
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(310,15)
            // TrCallStmt: Before ProcessCallStmt
            assert ORD#IsNat(Lit(ORD#FromNat(1)));
            assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
            assume true;
            // ProcessCallStmt: CheckSubrange
            _k##0 := ORD#Minus(_k#0, ORD#FromNat(1));
            assume true;
            // ProcessCallStmt: CheckSubrange
            c0##0 := c'#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            s0##0 := s'#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            c##0 := c#1;
            assume true;
            // ProcessCallStmt: CheckSubrange
            t##0 := t#1;
            assume true;
            // ProcessCallStmt: CheckSubrange
            c1##0 := c1#1;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call CoCall$$_module.__default.lemma__7__13_h(_k##0, c0##0, s0##0, c##0, t##0, c1##0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(310,32)"} true;
        }
    }
    else
    {
        // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(303,13)
        $initHeapForallStmt#1 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#1 == $Heap;
        assume (forall _k'#2: Box, 
            c0#2: DatatypeType, 
            s0#2: Map Box Box, 
            c#2: DatatypeType, 
            t#2: Map Box Box, 
            c1#2: DatatypeType :: 
          $Is(c0#2, Tclass._module.com())
               && $Is(s0#2, TMap(TSeq(TChar), TInt))
               && $Is(c#2, Tclass._module.com())
               && $Is(t#2, TMap(TSeq(TChar), TInt))
               && $Is(c1#2, Tclass._module.com())
               && 
              ORD#Less(_k'#2, _k#0)
               && _module.__default.small__step__star_h($LS($LZ), _k'#2, c0#2, s0#2, c#2, t#2)
             ==> _module.__default.small__step__star($LS($LZ), #_module.com.Seq(c0#2, c1#2), s0#2, #_module.com.Seq(c#2, c1#2), t#2));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(303,12)"} true;
    }
}



procedure CheckWellformed$$_module.__default.SmallStepStar__implies__BigStep(c#0: DatatypeType
       where $Is(c#0, Tclass._module.com())
         && $IsAlloc(c#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#0), 
    s#0: Map Box Box
       where $Is(s#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s#0, TMap(TSeq(TChar), TInt), $Heap), 
    t#0: Map Box Box
       where $Is(t#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(t#0, TMap(TSeq(TChar), TInt), $Heap));
  free requires 25 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.SmallStepStar__implies__BigStep(c#0: DatatypeType
       where $Is(c#0, Tclass._module.com())
         && $IsAlloc(c#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#0), 
    s#0: Map Box Box
       where $Is(s#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s#0, TMap(TSeq(TChar), TInt), $Heap), 
    t#0: Map Box Box
       where $Is(t#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(t#0, TMap(TSeq(TChar), TInt), $Heap));
  // user-defined preconditions
  requires _module.__default.small__step__star#canCall(c#0, s#0, Lit(#_module.com.SKIP()), t#0)
     ==> _module.__default.small__step__star($LS($LZ), c#0, s#0, Lit(#_module.com.SKIP()), t#0)
       || 
      (_module.com#Equal(c#0, #_module.com.SKIP()) && Map#Equal(s#0, t#0))
       || (exists c''#0: DatatypeType, s''#0: Map Box Box :: 
        { _module.__default.small__step__star($LS($LS($LZ)), c''#0, s''#0, #_module.com.SKIP(), t#0) } 
          { _module.__default.small__step($LS($LS($LZ)), c#0, s#0, c''#0, s''#0) } 
        $Is(c''#0, Tclass._module.com())
           && $Is(s''#0, TMap(TSeq(TChar), TInt))
           && 
          _module.__default.small__step($LS($LS($LZ)), c#0, s#0, c''#0, s''#0)
           && _module.__default.small__step__star($LS($LS($LZ)), c''#0, s''#0, Lit(#_module.com.SKIP()), t#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.big__step#canCall(c#0, s#0, t#0);
  ensures _module.__default.big__step($LS($LS($LZ)), c#0, s#0, t#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, c#1, s#1, t#1} CoCall$$_module.__default.SmallStepStar__implies__BigStep_h(_k#0: Box, 
    c#1: DatatypeType
       where $Is(c#1, Tclass._module.com())
         && $IsAlloc(c#1, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#1), 
    s#1: Map Box Box
       where $Is(s#1, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s#1, TMap(TSeq(TChar), TInt), $Heap), 
    t#1: Map Box Box
       where $Is(t#1, TMap(TSeq(TChar), TInt))
         && $IsAlloc(t#1, TMap(TSeq(TChar), TInt), $Heap));
  // user-defined preconditions
  requires _module.__default.small__step__star_h#canCall(_k#0, c#1, s#1, Lit(#_module.com.SKIP()), t#1)
     ==> _module.__default.small__step__star_h($LS($LZ), _k#0, c#1, s#1, Lit(#_module.com.SKIP()), t#1)
       || (0 < ORD#Offset(_k#0)
         ==> (_module.com#Equal(c#1, #_module.com.SKIP()) && Map#Equal(s#1, t#1))
           || (exists c''#1: DatatypeType, s''#1: Map Box Box :: 
            { _module.__default.small__step__star_h($LS($LS($LZ)), 
                ORD#Minus(_k#0, ORD#FromNat(1)), 
                c''#1, 
                s''#1, 
                #_module.com.SKIP(), 
                t#1) } 
              { _module.__default.small__step($LS($LS($LZ)), c#1, s#1, c''#1, s''#1) } 
            $Is(c''#1, Tclass._module.com())
               && $Is(s''#1, TMap(TSeq(TChar), TInt))
               && 
              _module.__default.small__step($LS($LS($LZ)), c#1, s#1, c''#1, s''#1)
               && _module.__default.small__step__star_h($LS($LS($LZ)), 
                ORD#Minus(_k#0, ORD#FromNat(1)), 
                c''#1, 
                s''#1, 
                Lit(#_module.com.SKIP()), 
                t#1)));
  requires _module.__default.small__step__star_h#canCall(_k#0, c#1, s#1, Lit(#_module.com.SKIP()), t#1)
     ==> _module.__default.small__step__star_h($LS($LZ), _k#0, c#1, s#1, Lit(#_module.com.SKIP()), t#1)
       || (LitInt(0) == ORD#Offset(_k#0)
         ==> (exists _k'#0: Box :: 
          { _module.__default.small__step__star_h($LS($LZ), _k'#0, c#1, s#1, #_module.com.SKIP(), t#1) } 
          ORD#LessThanLimit(_k'#0, _k#0)
             && _module.__default.small__step__star_h($LS($LZ), _k'#0, c#1, s#1, Lit(#_module.com.SKIP()), t#1)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.big__step#canCall(c#1, s#1, t#1);
  ensures _module.__default.big__step($LS($LS($LZ)), c#1, s#1, t#1);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, c#1, s#1, t#1} Impl$$_module.__default.SmallStepStar__implies__BigStep_h(_k#0: Box, 
    c#1: DatatypeType
       where $Is(c#1, Tclass._module.com())
         && $IsAlloc(c#1, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#1), 
    s#1: Map Box Box
       where $Is(s#1, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s#1, TMap(TSeq(TChar), TInt), $Heap), 
    t#1: Map Box Box
       where $Is(t#1, TMap(TSeq(TChar), TInt))
         && $IsAlloc(t#1, TMap(TSeq(TChar), TInt), $Heap))
   returns ($_reverifyPost: bool);
  free requires 26 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.__default.small__step__star_h#canCall(_k#0, c#1, s#1, Lit(#_module.com.SKIP()), t#1)
     && 
    _module.__default.small__step__star_h($LS($LZ), _k#0, c#1, s#1, Lit(#_module.com.SKIP()), t#1)
     && 
    (0 < ORD#Offset(_k#0)
       ==> (_module.com#Equal(c#1, #_module.com.SKIP()) && Map#Equal(s#1, t#1))
         || (exists c''#2: DatatypeType, s''#2: Map Box Box :: 
          { _module.__default.small__step__star_h($LS($LZ), 
              ORD#Minus(_k#0, ORD#FromNat(1)), 
              c''#2, 
              s''#2, 
              #_module.com.SKIP(), 
              t#1) } 
            { _module.__default.small__step($LS($LZ), c#1, s#1, c''#2, s''#2) } 
          $Is(c''#2, Tclass._module.com())
             && $Is(s''#2, TMap(TSeq(TChar), TInt))
             && 
            _module.__default.small__step($LS($LZ), c#1, s#1, c''#2, s''#2)
             && _module.__default.small__step__star_h($LS($LZ), 
              ORD#Minus(_k#0, ORD#FromNat(1)), 
              c''#2, 
              s''#2, 
              Lit(#_module.com.SKIP()), 
              t#1)))
     && (LitInt(0) == ORD#Offset(_k#0)
       ==> (exists _k'#1: Box :: 
        { _module.__default.small__step__star_h($LS($LZ), _k'#1, c#1, s#1, #_module.com.SKIP(), t#1) } 
        ORD#LessThanLimit(_k'#1, _k#0)
           && _module.__default.small__step__star_h($LS($LZ), _k'#1, c#1, s#1, Lit(#_module.com.SKIP()), t#1)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.big__step#canCall(c#1, s#1, t#1);
  ensures _module.__default.big__step($LS($LS($LZ)), c#1, s#1, t#1);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0, c#1, s#1, t#1} Impl$$_module.__default.SmallStepStar__implies__BigStep_h(_k#0: Box, c#1: DatatypeType, s#1: Map Box Box, t#1: Map Box Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var c'#0: DatatypeType
     where $Is(c'#0, Tclass._module.com()) && $IsAlloc(c'#0, Tclass._module.com(), $Heap);
  var s'#0: Map Box Box
     where $Is(s'#0, TMap(TSeq(TChar), TInt))
       && $IsAlloc(s'#0, TMap(TSeq(TChar), TInt), $Heap);
  var c'#1: DatatypeType;
  var s'#1: Map Box Box;
  var ##c#2: DatatypeType;
  var ##s#2: Map Box Box;
  var ##c'#1: DatatypeType;
  var ##s'#1: Map Box Box;
  var ##_k#0: Box;
  var ##c#3: DatatypeType;
  var ##s#3: Map Box Box;
  var ##c'#2: DatatypeType;
  var ##s'#2: Map Box Box;
  var c##0: DatatypeType;
  var s##0: Map Box Box;
  var c'##0: DatatypeType;
  var s'##0: Map Box Box;
  var t##0: Map Box Box;
  var $initHeapForallStmt#1: Heap;

    // AddMethodImpl: SmallStepStar_implies_BigStep#, Impl$$_module.__default.SmallStepStar__implies__BigStep_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(314,12): initial state"} true;
    assume $IsA#_module.com(c#1);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: Box, 
        $ih#c0#0: DatatypeType, 
        $ih#s0#0: Map Box Box, 
        $ih#t0#0: Map Box Box :: 
      $Is($ih#c0#0, Tclass._module.com())
           && $Is($ih#s0#0, TMap(TSeq(TChar), TInt))
           && $Is($ih#t0#0, TMap(TSeq(TChar), TInt))
           && _module.__default.small__step__star_h($LS($LZ), $ih#_k0#0, $ih#c0#0, $ih#s0#0, Lit(#_module.com.SKIP()), $ih#t0#0)
           && (ORD#Less($ih#_k0#0, _k#0)
             || ($ih#_k0#0 == _k#0
               && (DtRank($ih#c0#0) < DtRank(c#1)
                 || (DtRank($ih#c0#0) == DtRank(c#1)
                   && ((Set#Subset(Map#Domain($ih#s0#0), Map#Domain(s#1))
                       && !Set#Subset(Map#Domain(s#1), Map#Domain($ih#s0#0)))
                     || (Set#Equal(Map#Domain($ih#s0#0), Map#Domain(s#1))
                       && 
                      Set#Subset(Map#Domain($ih#t0#0), Map#Domain(t#1))
                       && !Set#Subset(Map#Domain(t#1), Map#Domain($ih#t0#0))))))))
         ==> _module.__default.big__step($LS($LZ), $ih#c0#0, $ih#s0#0, $ih#t0#0));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(317,1)
    assume true;
    if (0 < ORD#Offset(_k#0))
    {
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(318,3)
        if (_module.com#Equal(c#1, #_module.com.SKIP()))
        {
        }

        assume $IsA#_module.com(c#1);
        if (_module.com#Equal(c#1, #_module.com.SKIP()) && Map#Equal(s#1, t#1))
        {
        }
        else
        {
            // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(320,16)
            havoc c'#1;
            havoc s'#1;
            if ($Is(c'#1, Tclass._module.com())
               && $IsAlloc(c'#1, Tclass._module.com(), $Heap)
               && 
              $Is(s'#1, TMap(TSeq(TChar), TInt))
               && $IsAlloc(s'#1, TMap(TSeq(TChar), TInt), $Heap))
            {
                ##c#2 := c#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##c#2, Tclass._module.com(), $Heap);
                ##s#2 := s#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#2, TMap(TSeq(TChar), TInt), $Heap);
                ##c'#1 := c'#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##c'#1, Tclass._module.com(), $Heap);
                ##s'#1 := s'#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s'#1, TMap(TSeq(TChar), TInt), $Heap);
                assume _module.__default.small__step#canCall(c#1, s#1, c'#1, s'#1);
                if (_module.__default.small__step($LS($LZ), c#1, s#1, c'#1, s'#1))
                {
                    assert ORD#IsNat(Lit(ORD#FromNat(1)));
                    assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
                    ##_k#0 := ORD#Minus(_k#0, ORD#FromNat(1));
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##_k#0, TORDINAL, $Heap);
                    ##c#3 := c'#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c#3, Tclass._module.com(), $Heap);
                    ##s#3 := s'#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s#3, TMap(TSeq(TChar), TInt), $Heap);
                    ##c'#2 := Lit(#_module.com.SKIP());
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##c'#2, Tclass._module.com(), $Heap);
                    ##s'#2 := t#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s'#2, TMap(TSeq(TChar), TInt), $Heap);
                    assume _module.__default.small__step__star_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), c'#1, s'#1, Lit(#_module.com.SKIP()), t#1);
                }

                assume _module.__default.small__step#canCall(c#1, s#1, c'#1, s'#1)
                   && (_module.__default.small__step($LS($LZ), c#1, s#1, c'#1, s'#1)
                     ==> _module.__default.small__step__star_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), c'#1, s'#1, Lit(#_module.com.SKIP()), t#1));
            }

            assert (exists $as#s'0_0#0: Map Box Box :: 
                $Is($as#s'0_0#0, TMap(TSeq(TChar), TInt))
                   && 
                  $Is(Lit(#_module.com.SKIP()), Tclass._module.com())
                   && 
                  _module.__default.small__step($LS($LZ), c#1, s#1, Lit(#_module.com.SKIP()), $as#s'0_0#0)
                   && _module.__default.small__step__star_h($LS($LZ), 
                    ORD#Minus(_k#0, ORD#FromNat(1)), 
                    Lit(#_module.com.SKIP()), 
                    $as#s'0_0#0, 
                    Lit(#_module.com.SKIP()), 
                    t#1))
               || (exists $as#c'0_0#0: DatatypeType, $as#s'0_0#0: Map Box Box :: 
                $Is($as#c'0_0#0, Tclass._module.com())
                   && $Is($as#s'0_0#0, TMap(TSeq(TChar), TInt))
                   && 
                  _module.__default.small__step($LS($LZ), c#1, s#1, $as#c'0_0#0, $as#s'0_0#0)
                   && _module.__default.small__step__star_h($LS($LZ), 
                    ORD#Minus(_k#0, ORD#FromNat(1)), 
                    $as#c'0_0#0, 
                    $as#s'0_0#0, 
                    Lit(#_module.com.SKIP()), 
                    t#1));
            havoc c'#0, s'#0;
            assume _module.__default.small__step($LS($LZ), c#1, s#1, c'#0, s'#0)
               && _module.__default.small__step__star_h($LS($LZ), 
                ORD#Minus(_k#0, ORD#FromNat(1)), 
                c'#0, 
                s'#0, 
                Lit(#_module.com.SKIP()), 
                t#1);
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(320,78)"} true;
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(321,27)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            c##0 := c#1;
            assume true;
            // ProcessCallStmt: CheckSubrange
            s##0 := s#1;
            assume true;
            // ProcessCallStmt: CheckSubrange
            c'##0 := c'#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            s'##0 := s'#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            t##0 := t#1;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call Call$$_module.__default.SmallStep__plus__BigStep(c##0, s##0, c'##0, s'##0, t##0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(321,43)"} true;
        }
    }
    else
    {
        // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(314,13)
        $initHeapForallStmt#1 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#1 == $Heap;
        assume (forall _k'#2: Box, c#2: DatatypeType, s#2: Map Box Box, t#2: Map Box Box :: 
          $Is(c#2, Tclass._module.com())
               && $Is(s#2, TMap(TSeq(TChar), TInt))
               && $Is(t#2, TMap(TSeq(TChar), TInt))
               && 
              ORD#Less(_k'#2, _k#0)
               && _module.__default.small__step__star_h($LS($LZ), _k'#2, c#2, s#2, Lit(#_module.com.SKIP()), t#2)
             ==> _module.__default.big__step($LS($LZ), c#2, s#2, t#2));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(314,12)"} true;
    }
}



procedure CheckWellformed$$_module.__default.SmallStep__plus__BigStep(c#0: DatatypeType
       where $Is(c#0, Tclass._module.com())
         && $IsAlloc(c#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#0), 
    s#0: Map Box Box
       where $Is(s#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s#0, TMap(TSeq(TChar), TInt), $Heap), 
    c'#0: DatatypeType
       where $Is(c'#0, Tclass._module.com())
         && $IsAlloc(c'#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c'#0), 
    s'#0: Map Box Box
       where $Is(s'#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s'#0, TMap(TSeq(TChar), TInt), $Heap), 
    t#0: Map Box Box
       where $Is(t#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(t#0, TMap(TSeq(TChar), TInt), $Heap));
  free requires 24 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.SmallStep__plus__BigStep(c#0: DatatypeType
       where $Is(c#0, Tclass._module.com())
         && $IsAlloc(c#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#0), 
    s#0: Map Box Box
       where $Is(s#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s#0, TMap(TSeq(TChar), TInt), $Heap), 
    c'#0: DatatypeType
       where $Is(c'#0, Tclass._module.com())
         && $IsAlloc(c'#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c'#0), 
    s'#0: Map Box Box
       where $Is(s'#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s'#0, TMap(TSeq(TChar), TInt), $Heap), 
    t#0: Map Box Box
       where $Is(t#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(t#0, TMap(TSeq(TChar), TInt), $Heap));
  // user-defined preconditions
  requires _module.__default.small__step($LS($LS($LZ)), c#0, s#0, c'#0, s'#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.big__step#canCall(c'#0, s'#0, t#0)
     && (_module.__default.big__step($LS($LZ), c'#0, s'#0, t#0)
       ==> _module.__default.big__step#canCall(c#0, s#0, t#0));
  ensures _module.__default.big__step($LS($LZ), c'#0, s'#0, t#0)
     ==> _module.__default.big__step($LS($LS($LZ)), c#0, s#0, t#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, c#1, s#1, c'#1, s'#1, t#1} CoCall$$_module.__default.SmallStep__plus__BigStep_h(_k#0: Box, 
    c#1: DatatypeType
       where $Is(c#1, Tclass._module.com())
         && $IsAlloc(c#1, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#1), 
    s#1: Map Box Box
       where $Is(s#1, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s#1, TMap(TSeq(TChar), TInt), $Heap), 
    c'#1: DatatypeType
       where $Is(c'#1, Tclass._module.com())
         && $IsAlloc(c'#1, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c'#1), 
    s'#1: Map Box Box
       where $Is(s'#1, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s'#1, TMap(TSeq(TChar), TInt), $Heap), 
    t#1: Map Box Box
       where $Is(t#1, TMap(TSeq(TChar), TInt))
         && $IsAlloc(t#1, TMap(TSeq(TChar), TInt), $Heap));
  // user-defined preconditions
  requires _module.__default.small__step_h($LS($LS($LZ)), _k#0, c#1, s#1, c'#1, s'#1);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.big__step#canCall(c'#1, s'#1, t#1)
     && (_module.__default.big__step($LS($LZ), c'#1, s'#1, t#1)
       ==> _module.__default.big__step#canCall(c#1, s#1, t#1));
  ensures _module.__default.big__step($LS($LZ), c'#1, s'#1, t#1)
     ==> _module.__default.big__step($LS($LS($LZ)), c#1, s#1, t#1);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, c#1, s#1, c'#1, s'#1, t#1} Impl$$_module.__default.SmallStep__plus__BigStep_h(_k#0: Box, 
    c#1: DatatypeType
       where $Is(c#1, Tclass._module.com())
         && $IsAlloc(c#1, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#1), 
    s#1: Map Box Box
       where $Is(s#1, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s#1, TMap(TSeq(TChar), TInt), $Heap), 
    c'#1: DatatypeType
       where $Is(c'#1, Tclass._module.com())
         && $IsAlloc(c'#1, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c'#1), 
    s'#1: Map Box Box
       where $Is(s'#1, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s'#1, TMap(TSeq(TChar), TInt), $Heap), 
    t#1: Map Box Box
       where $Is(t#1, TMap(TSeq(TChar), TInt))
         && $IsAlloc(t#1, TMap(TSeq(TChar), TInt), $Heap))
   returns ($_reverifyPost: bool);
  free requires 27 == $FunctionContextHeight;
  // user-defined preconditions
  requires _module.__default.small__step_h($LS($LS($LZ)), _k#0, c#1, s#1, c'#1, s'#1);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.big__step#canCall(c'#1, s'#1, t#1)
     && (_module.__default.big__step($LS($LZ), c'#1, s'#1, t#1)
       ==> _module.__default.big__step#canCall(c#1, s#1, t#1));
  ensures _module.__default.big__step($LS($LZ), c'#1, s'#1, t#1)
     ==> _module.__default.big__step($LS($LS($LZ)), c#1, s#1, t#1);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0, c#1, s#1, c'#1, s'#1, t#1} Impl$$_module.__default.SmallStep__plus__BigStep_h(_k#0: Box, 
    c#1: DatatypeType, 
    s#1: Map Box Box, 
    c'#1: DatatypeType, 
    s'#1: Map Box Box, 
    t#1: Map Box Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var _mcc#7#0: DatatypeType;
  var _mcc#8#0: DatatypeType;
  var body#0: DatatypeType;
  var let#0_0_0#0#0: DatatypeType;
  var b#0: DatatypeType;
  var let#0_0_1#0#0: DatatypeType;
  var ##c#3: DatatypeType;
  var ##s#3: Map Box Box;
  var ##t#2: Map Box Box;
  var ##b#0: DatatypeType;
  var ##s#4: Map Box Box;
  var ##c#4: DatatypeType;
  var ##s#5: Map Box Box;
  var ##t#3: Map Box Box;
  var _mcc#4#0: DatatypeType;
  var _mcc#5#0: DatatypeType;
  var _mcc#6#0: DatatypeType;
  var els#0: DatatypeType;
  var let#0_1_0#0#0: DatatypeType;
  var thn#0: DatatypeType;
  var let#0_1_1#0#0: DatatypeType;
  var b#1: DatatypeType;
  var let#0_1_2#0#0: DatatypeType;
  var _mcc#2#0: DatatypeType;
  var _mcc#3#0: DatatypeType;
  var c1#0: DatatypeType;
  var let#0_2_0#0#0: DatatypeType;
  var c0#0: DatatypeType;
  var let#0_2_1#0#0: DatatypeType;
  var c0'#0: DatatypeType
     where $Is(c0'#0, Tclass._module.com()) && $IsAlloc(c0'#0, Tclass._module.com(), $Heap);
  var c0'#1: DatatypeType;
  var ##_k#0: Box;
  var ##c#5: DatatypeType;
  var ##s#6: Map Box Box;
  var ##c'#1: DatatypeType;
  var ##s'#1: Map Box Box;
  var ##c#6: DatatypeType;
  var ##s#7: Map Box Box;
  var ##t#4: Map Box Box;
  var s''#0: Map Box Box
     where $Is(s''#0, TMap(TSeq(TChar), TInt))
       && $IsAlloc(s''#0, TMap(TSeq(TChar), TInt), $Heap);
  var s''#1: Map Box Box;
  var ##c#7: DatatypeType;
  var ##s#8: Map Box Box;
  var ##t#5: Map Box Box;
  var ##c#8: DatatypeType;
  var ##s#9: Map Box Box;
  var ##t#6: Map Box Box;
  var _mcc#0#0: Seq Box;
  var _mcc#1#0: DatatypeType;
  var a#0: DatatypeType;
  var let#0_3_0#0#0: DatatypeType;
  var x#0: Seq Box;
  var let#0_3_1#0#0: Seq Box;
  var $initHeapForallStmt#1: Heap;

    // AddMethodImpl: SmallStep_plus_BigStep#, Impl$$_module.__default.SmallStep__plus__BigStep_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(325,12): initial state"} true;
    assume $IsA#_module.com(c#1);
    assume $IsA#_module.com(c'#1);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: Box, 
        $ih#c0#0: DatatypeType, 
        $ih#s0#0: Map Box Box, 
        $ih#c'0#0: DatatypeType, 
        $ih#s'0#0: Map Box Box, 
        $ih#t0#0: Map Box Box :: 
      $Is($ih#c0#0, Tclass._module.com())
           && $Is($ih#s0#0, TMap(TSeq(TChar), TInt))
           && $Is($ih#c'0#0, Tclass._module.com())
           && $Is($ih#s'0#0, TMap(TSeq(TChar), TInt))
           && $Is($ih#t0#0, TMap(TSeq(TChar), TInt))
           && _module.__default.small__step_h($LS($LZ), $ih#_k0#0, $ih#c0#0, $ih#s0#0, $ih#c'0#0, $ih#s'0#0)
           && (ORD#Less($ih#_k0#0, _k#0)
             || ($ih#_k0#0 == _k#0
               && (DtRank($ih#c0#0) < DtRank(c#1)
                 || (DtRank($ih#c0#0) == DtRank(c#1)
                   && ((Set#Subset(Map#Domain($ih#s0#0), Map#Domain(s#1))
                       && !Set#Subset(Map#Domain(s#1), Map#Domain($ih#s0#0)))
                     || (Set#Equal(Map#Domain($ih#s0#0), Map#Domain(s#1))
                       && (DtRank($ih#c'0#0) < DtRank(c'#1)
                         || (DtRank($ih#c'0#0) == DtRank(c'#1)
                           && ((Set#Subset(Map#Domain($ih#s'0#0), Map#Domain(s'#1))
                               && !Set#Subset(Map#Domain(s'#1), Map#Domain($ih#s'0#0)))
                             || (Set#Equal(Map#Domain($ih#s'0#0), Map#Domain(s'#1))
                               && 
                              Set#Subset(Map#Domain($ih#t0#0), Map#Domain(t#1))
                               && !Set#Subset(Map#Domain(t#1), Map#Domain($ih#t0#0))))))))))))
         ==> 
        _module.__default.big__step($LS($LZ), $ih#c'0#0, $ih#s'0#0, $ih#t0#0)
         ==> _module.__default.big__step($LS($LZ), $ih#c0#0, $ih#s0#0, $ih#t0#0));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(328,1)
    assume true;
    if (0 < ORD#Offset(_k#0))
    {
        assume true;
        havoc _mcc#7#0, _mcc#8#0;
        havoc _mcc#4#0, _mcc#5#0, _mcc#6#0;
        havoc _mcc#2#0, _mcc#3#0;
        havoc _mcc#0#0, _mcc#1#0;
        if (c#1 == #_module.com.Assign(_mcc#0#0, _mcc#1#0))
        {
            assume $Is(_mcc#0#0, TSeq(TChar)) && $IsAlloc(_mcc#0#0, TSeq(TChar), $Heap);
            assume $Is(_mcc#1#0, Tclass._module.aexp())
               && $IsAlloc(_mcc#1#0, Tclass._module.aexp(), $Heap);
            havoc a#0;
            assume $Is(a#0, Tclass._module.aexp()) && $IsAlloc(a#0, Tclass._module.aexp(), $Heap);
            assume let#0_3_0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0_3_0#0#0, Tclass._module.aexp());
            assume a#0 == let#0_3_0#0#0;
            havoc x#0;
            assume $Is(x#0, TSeq(TChar)) && $IsAlloc(x#0, TSeq(TChar), $Heap);
            assume let#0_3_1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0_3_1#0#0, TSeq(TChar));
            assume x#0 == let#0_3_1#0#0;
        }
        else if (c#1 == #_module.com.Seq(_mcc#2#0, _mcc#3#0))
        {
            assume $Is(_mcc#2#0, Tclass._module.com())
               && $IsAlloc(_mcc#2#0, Tclass._module.com(), $Heap);
            assume $Is(_mcc#3#0, Tclass._module.com())
               && $IsAlloc(_mcc#3#0, Tclass._module.com(), $Heap);
            havoc c1#0;
            assume $Is(c1#0, Tclass._module.com()) && $IsAlloc(c1#0, Tclass._module.com(), $Heap);
            assume let#0_2_0#0#0 == _mcc#3#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0_2_0#0#0, Tclass._module.com());
            assume c1#0 == let#0_2_0#0#0;
            havoc c0#0;
            assume $Is(c0#0, Tclass._module.com()) && $IsAlloc(c0#0, Tclass._module.com(), $Heap);
            assume let#0_2_1#0#0 == _mcc#2#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0_2_1#0#0, Tclass._module.com());
            assume c0#0 == let#0_2_1#0#0;
            // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(332,5)
            if (_module.com#Equal(c0#0, #_module.com.SKIP()))
            {
            }

            if (_module.com#Equal(c0#0, #_module.com.SKIP()) && _module.com#Equal(c'#1, c1#0))
            {
            }

            assume $IsA#_module.com(c0#0)
               && (_module.com#Equal(c0#0, #_module.com.SKIP())
                 ==> $IsA#_module.com(c'#1) && $IsA#_module.com(c1#0));
            if (_module.com#Equal(c0#0, #_module.com.SKIP())
               && _module.com#Equal(c'#1, c1#0)
               && Map#Equal(s'#1, s#1))
            {
            }
            else
            {
                // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(334,15)
                havoc c0'#1;
                if ($Is(c0'#1, Tclass._module.com()) && $IsAlloc(c0'#1, Tclass._module.com(), $Heap))
                {
                    if (_module.com#Equal(c'#1, #_module.com.Seq(c0'#1, c1#0)))
                    {
                        assert ORD#IsNat(Lit(ORD#FromNat(1)));
                        assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
                        ##_k#0 := ORD#Minus(_k#0, ORD#FromNat(1));
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##_k#0, TORDINAL, $Heap);
                        ##c#5 := c0#0;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##c#5, Tclass._module.com(), $Heap);
                        ##s#6 := s#1;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##s#6, TMap(TSeq(TChar), TInt), $Heap);
                        ##c'#1 := c0'#1;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##c'#1, Tclass._module.com(), $Heap);
                        ##s'#1 := s'#1;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##s'#1, TMap(TSeq(TChar), TInt), $Heap);
                        assume _module.__default.small__step_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), c0#0, s#1, c0'#1, s'#1);
                    }

                    assume $IsA#_module.com(c'#1)
                       && (_module.com#Equal(c'#1, #_module.com.Seq(c0'#1, c1#0))
                         ==> _module.__default.small__step_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), c0#0, s#1, c0'#1, s'#1));
                }

                assert ($Is(Lit(#_module.com.SKIP()), Tclass._module.com())
                     && 
                    _module.com#Equal(c'#1, #_module.com.Seq(Lit(#_module.com.SKIP()), c1#0))
                     && _module.__default.small__step_h($LS($LZ), 
                      ORD#Minus(_k#0, ORD#FromNat(1)), 
                      c0#0, 
                      s#1, 
                      Lit(#_module.com.SKIP()), 
                      s'#1))
                   || (exists $as#c0'0_2_0#0: DatatypeType :: 
                    $Is($as#c0'0_2_0#0, Tclass._module.com())
                       && 
                      _module.com#Equal(c'#1, #_module.com.Seq($as#c0'0_2_0#0, c1#0))
                       && _module.__default.small__step_h($LS($LZ), ORD#Minus(_k#0, ORD#FromNat(1)), c0#0, s#1, $as#c0'0_2_0#0, s'#1));
                havoc c0'#0;
                assume _module.com#Equal(c'#1, #_module.com.Seq(c0'#0, c1#0))
                   && _module.__default.small__step_h($LS($LZ), ORD#Minus(_k#0, ORD#FromNat(1)), c0#0, s#1, c0'#0, s'#1);
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(334,65)"} true;
                // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(335,7)
                ##c#6 := c'#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##c#6, Tclass._module.com(), $Heap);
                ##s#7 := s'#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#7, TMap(TSeq(TChar), TInt), $Heap);
                ##t#4 := t#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#4, TMap(TSeq(TChar), TInt), $Heap);
                assume _module.__default.big__step#canCall(c'#1, s'#1, t#1);
                assume _module.__default.big__step#canCall(c'#1, s'#1, t#1);
                if (_module.__default.big__step($LS($LZ), c'#1, s'#1, t#1))
                {
                    // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(336,17)
                    havoc s''#1;
                    if ($Is(s''#1, TMap(TSeq(TChar), TInt))
                       && $IsAlloc(s''#1, TMap(TSeq(TChar), TInt), $Heap))
                    {
                        ##c#7 := c0'#0;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##c#7, Tclass._module.com(), $Heap);
                        ##s#8 := s'#1;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##s#8, TMap(TSeq(TChar), TInt), $Heap);
                        ##t#5 := s''#1;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##t#5, TMap(TSeq(TChar), TInt), $Heap);
                        assume _module.__default.big__step#canCall(c0'#0, s'#1, s''#1);
                        if (_module.__default.big__step($LS($LZ), c0'#0, s'#1, s''#1))
                        {
                            ##c#8 := c1#0;
                            // assume allocatedness for argument to function
                            assume $IsAlloc(##c#8, Tclass._module.com(), $Heap);
                            ##s#9 := s''#1;
                            // assume allocatedness for argument to function
                            assume $IsAlloc(##s#9, TMap(TSeq(TChar), TInt), $Heap);
                            ##t#6 := t#1;
                            // assume allocatedness for argument to function
                            assume $IsAlloc(##t#6, TMap(TSeq(TChar), TInt), $Heap);
                            assume _module.__default.big__step#canCall(c1#0, s''#1, t#1);
                        }

                        assume _module.__default.big__step#canCall(c0'#0, s'#1, s''#1)
                           && (_module.__default.big__step($LS($LZ), c0'#0, s'#1, s''#1)
                             ==> _module.__default.big__step#canCall(c1#0, s''#1, t#1));
                    }

                    assert (exists $as#s''0_2_1_0#0: Map Box Box :: 
                      $Is($as#s''0_2_1_0#0, TMap(TSeq(TChar), TInt))
                         && 
                        _module.__default.big__step($LS($LZ), c0'#0, s'#1, $as#s''0_2_1_0#0)
                         && _module.__default.big__step($LS($LZ), c1#0, $as#s''0_2_1_0#0, t#1));
                    havoc s''#0;
                    assume _module.__default.big__step($LS($LZ), c0'#0, s'#1, s''#0)
                       && _module.__default.big__step($LS($LZ), c1#0, s''#0, t#1);
                    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(336,65)"} true;
                }
                else
                {
                }
            }
        }
        else if (c#1 == #_module.com.If(_mcc#4#0, _mcc#5#0, _mcc#6#0))
        {
            assume $Is(_mcc#4#0, Tclass._module.bexp())
               && $IsAlloc(_mcc#4#0, Tclass._module.bexp(), $Heap);
            assume $Is(_mcc#5#0, Tclass._module.com())
               && $IsAlloc(_mcc#5#0, Tclass._module.com(), $Heap);
            assume $Is(_mcc#6#0, Tclass._module.com())
               && $IsAlloc(_mcc#6#0, Tclass._module.com(), $Heap);
            havoc els#0;
            assume $Is(els#0, Tclass._module.com()) && $IsAlloc(els#0, Tclass._module.com(), $Heap);
            assume let#0_1_0#0#0 == _mcc#6#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0_1_0#0#0, Tclass._module.com());
            assume els#0 == let#0_1_0#0#0;
            havoc thn#0;
            assume $Is(thn#0, Tclass._module.com()) && $IsAlloc(thn#0, Tclass._module.com(), $Heap);
            assume let#0_1_1#0#0 == _mcc#5#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0_1_1#0#0, Tclass._module.com());
            assume thn#0 == let#0_1_1#0#0;
            havoc b#1;
            assume $Is(b#1, Tclass._module.bexp()) && $IsAlloc(b#1, Tclass._module.bexp(), $Heap);
            assume let#0_1_2#0#0 == _mcc#4#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0_1_2#0#0, Tclass._module.bexp());
            assume b#1 == let#0_1_2#0#0;
        }
        else if (c#1 == #_module.com.While(_mcc#7#0, _mcc#8#0))
        {
            assume $Is(_mcc#7#0, Tclass._module.bexp())
               && $IsAlloc(_mcc#7#0, Tclass._module.bexp(), $Heap);
            assume $Is(_mcc#8#0, Tclass._module.com())
               && $IsAlloc(_mcc#8#0, Tclass._module.com(), $Heap);
            havoc body#0;
            assume $Is(body#0, Tclass._module.com())
               && $IsAlloc(body#0, Tclass._module.com(), $Heap);
            assume let#0_0_0#0#0 == _mcc#8#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0_0_0#0#0, Tclass._module.com());
            assume body#0 == let#0_0_0#0#0;
            havoc b#0;
            assume $Is(b#0, Tclass._module.bexp()) && $IsAlloc(b#0, Tclass._module.bexp(), $Heap);
            assume let#0_0_1#0#0 == _mcc#7#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0_0_1#0#0, Tclass._module.bexp());
            assume b#0 == let#0_0_1#0#0;
            // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(341,5)
            if (_module.com#Equal(c'#1, 
              #_module.com.If(b#0, 
                #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                Lit(#_module.com.SKIP()))))
            {
            }

            assume $IsA#_module.com(c'#1);
            assert {:subsumption 0} _module.com#Equal(c'#1, 
              #_module.com.If(b#0, 
                #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                Lit(#_module.com.SKIP())));
            assert {:subsumption 0} Map#Equal(s'#1, s#1);
            assume _module.com#Equal(c'#1, 
                #_module.com.If(b#0, 
                  #_module.com.Seq(body#0, #_module.com.While(b#0, body#0)), 
                  Lit(#_module.com.SKIP())))
               && Map#Equal(s'#1, s#1);
            // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(342,5)
            ##c#3 := c'#1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##c#3, Tclass._module.com(), $Heap);
            ##s#3 := s'#1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#3, TMap(TSeq(TChar), TInt), $Heap);
            ##t#2 := t#1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#2, TMap(TSeq(TChar), TInt), $Heap);
            assume _module.__default.big__step#canCall(c'#1, s'#1, t#1);
            assume _module.__default.big__step#canCall(c'#1, s'#1, t#1);
            if (_module.__default.big__step($LS($LZ), c'#1, s'#1, t#1))
            {
                // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(343,7)
                ##b#0 := b#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##b#0, Tclass._module.bexp(), $Heap);
                ##s#4 := s'#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#4, TMap(TSeq(TChar), TInt), $Heap);
                assume _module.__default.bval#canCall(b#0, s'#1);
                if (_module.__default.bval($LS($LZ), b#0, s'#1))
                {
                }
                else
                {
                }

                ##c#4 := (if _module.__default.bval($LS($LZ), b#0, s'#1)
                   then #_module.com.Seq(body#0, #_module.com.While(b#0, body#0))
                   else #_module.com.SKIP());
                // assume allocatedness for argument to function
                assume $IsAlloc(##c#4, Tclass._module.com(), $Heap);
                ##s#5 := s'#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#5, TMap(TSeq(TChar), TInt), $Heap);
                ##t#3 := t#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#3, TMap(TSeq(TChar), TInt), $Heap);
                assume _module.__default.big__step#canCall((if _module.__default.bval($LS($LZ), b#0, s'#1)
                     then #_module.com.Seq(body#0, #_module.com.While(b#0, body#0))
                     else #_module.com.SKIP()), 
                  s'#1, 
                  t#1);
                assume _module.__default.bval#canCall(b#0, s'#1)
                   && _module.__default.big__step#canCall((if _module.__default.bval($LS($LZ), b#0, s'#1)
                       then #_module.com.Seq(body#0, #_module.com.While(b#0, body#0))
                       else #_module.com.SKIP()), 
                    s'#1, 
                    t#1);
                assert {:subsumption 0} _module.__default.big__step($LS($LS($LZ)), 
                  (if _module.__default.bval($LS($LS($LZ)), b#0, s'#1)
                     then #_module.com.Seq(body#0, #_module.com.While(b#0, body#0))
                     else #_module.com.SKIP()), 
                  s'#1, 
                  t#1);
                assume _module.__default.big__step($LS($LS($LZ)), 
                  (if _module.__default.bval($LS($LZ), b#0, s'#1)
                     then #_module.com.Seq(body#0, #_module.com.While(b#0, body#0))
                     else #_module.com.SKIP()), 
                  s'#1, 
                  t#1);
            }
            else
            {
            }
        }
        else if (c#1 == #_module.com.SKIP())
        {
            assert false;
        }
        else
        {
            assume false;
        }
    }
    else
    {
        // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(325,13)
        $initHeapForallStmt#1 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#1 == $Heap;
        assume (forall _k'#0: Box, 
            c#2: DatatypeType, 
            s#2: Map Box Box, 
            c'#2: DatatypeType, 
            s'#2: Map Box Box, 
            t#2: Map Box Box :: 
          $Is(c#2, Tclass._module.com())
               && $Is(s#2, TMap(TSeq(TChar), TInt))
               && $Is(c'#2, Tclass._module.com())
               && $Is(s'#2, TMap(TSeq(TChar), TInt))
               && $Is(t#2, TMap(TSeq(TChar), TInt))
               && 
              ORD#Less(_k'#0, _k#0)
               && _module.__default.small__step_h($LS($LZ), _k'#0, c#2, s#2, c'#2, s'#2)
             ==> 
            _module.__default.big__step($LS($LZ), c'#2, s'#2, t#2)
             ==> _module.__default.big__step($LS($LZ), c#2, s#2, t#2));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(325,12)"} true;
    }
}



procedure {:_induction c#0, s#0, t#0} CheckWellformed$$_module.__default.BigStep__SmallStepStar__Same(c#0: DatatypeType
       where $Is(c#0, Tclass._module.com())
         && $IsAlloc(c#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#0), 
    s#0: Map Box Box
       where $Is(s#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s#0, TMap(TSeq(TChar), TInt), $Heap), 
    t#0: Map Box Box
       where $Is(t#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(t#0, TMap(TSeq(TChar), TInt), $Heap));
  free requires 43 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction c#0, s#0, t#0} Call$$_module.__default.BigStep__SmallStepStar__Same(c#0: DatatypeType
       where $Is(c#0, Tclass._module.com())
         && $IsAlloc(c#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#0), 
    s#0: Map Box Box
       where $Is(s#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s#0, TMap(TSeq(TChar), TInt), $Heap), 
    t#0: Map Box Box
       where $Is(t#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(t#0, TMap(TSeq(TChar), TInt), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.big__step#canCall(c#0, s#0, t#0)
     && _module.__default.small__step__star#canCall(c#0, s#0, Lit(#_module.com.SKIP()), t#0);
  ensures _module.__default.big__step($LS($LS($LZ)), c#0, s#0, t#0)
     <==> _module.__default.small__step__star($LS($LS($LZ)), c#0, s#0, Lit(#_module.com.SKIP()), t#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction c#0, s#0, t#0} Impl$$_module.__default.BigStep__SmallStepStar__Same(c#0: DatatypeType
       where $Is(c#0, Tclass._module.com())
         && $IsAlloc(c#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#0), 
    s#0: Map Box Box
       where $Is(s#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s#0, TMap(TSeq(TChar), TInt), $Heap), 
    t#0: Map Box Box
       where $Is(t#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(t#0, TMap(TSeq(TChar), TInt), $Heap))
   returns ($_reverifyPost: bool);
  free requires 43 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.big__step#canCall(c#0, s#0, t#0)
     && _module.__default.small__step__star#canCall(c#0, s#0, Lit(#_module.com.SKIP()), t#0);
  ensures _module.__default.big__step($LS($LS($LZ)), c#0, s#0, t#0)
     <==> _module.__default.small__step__star($LS($LS($LZ)), c#0, s#0, Lit(#_module.com.SKIP()), t#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction c#0, s#0, t#0} Impl$$_module.__default.BigStep__SmallStepStar__Same(c#0: DatatypeType, s#0: Map Box Box, t#0: Map Box Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var ##c#2: DatatypeType;
  var ##s#2: Map Box Box;
  var ##t#1: Map Box Box;
  var c##0_0: DatatypeType;
  var s##0_0: Map Box Box;
  var t##0_0: Map Box Box;
  var ##c#3: DatatypeType;
  var ##s#3: Map Box Box;
  var ##c'#1: DatatypeType;
  var ##s'#1: Map Box Box;
  var c##1_0: DatatypeType;
  var s##1_0: Map Box Box;
  var t##1_0: Map Box Box;

    // AddMethodImpl: BigStep_SmallStepStar_Same, Impl$$_module.__default.BigStep__SmallStepStar__Same
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(350,0): initial state"} true;
    assume $IsA#_module.com(c#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#c0#0: DatatypeType, $ih#s0#0: Map Box Box, $ih#t0#0: Map Box Box :: 
      $Is($ih#c0#0, Tclass._module.com())
           && $Is($ih#s0#0, TMap(TSeq(TChar), TInt))
           && $Is($ih#t0#0, TMap(TSeq(TChar), TInt))
           && Lit(true)
           && (DtRank($ih#c0#0) < DtRank(c#0)
             || (DtRank($ih#c0#0) == DtRank(c#0)
               && ((Set#Subset(Map#Domain($ih#s0#0), Map#Domain(s#0))
                   && !Set#Subset(Map#Domain(s#0), Map#Domain($ih#s0#0)))
                 || (Set#Equal(Map#Domain($ih#s0#0), Map#Domain(s#0))
                   && 
                  Set#Subset(Map#Domain($ih#t0#0), Map#Domain(t#0))
                   && !Set#Subset(Map#Domain(t#0), Map#Domain($ih#t0#0))))))
         ==> (_module.__default.big__step($LS($LZ), $ih#c0#0, $ih#s0#0, $ih#t0#0)
           <==> _module.__default.small__step__star($LS($LZ), $ih#c0#0, $ih#s0#0, Lit(#_module.com.SKIP()), $ih#t0#0)));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(351,3)
    ##c#2 := c#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##c#2, Tclass._module.com(), $Heap);
    ##s#2 := s#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#2, TMap(TSeq(TChar), TInt), $Heap);
    ##t#1 := t#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##t#1, TMap(TSeq(TChar), TInt), $Heap);
    assume _module.__default.big__step#canCall(c#0, s#0, t#0);
    assume _module.__default.big__step#canCall(c#0, s#0, t#0);
    if (_module.__default.big__step($LS($LZ), c#0, s#0, t#0))
    {
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(352,34)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        c##0_0 := c#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        s##0_0 := s#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        t##0_0 := t#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.BigStep__implies__SmallStepStar(c##0_0, s##0_0, t##0_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(352,42)"} true;
    }
    else
    {
    }

    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(354,3)
    ##c#3 := c#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##c#3, Tclass._module.com(), $Heap);
    ##s#3 := s#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#3, TMap(TSeq(TChar), TInt), $Heap);
    ##c'#1 := Lit(#_module.com.SKIP());
    // assume allocatedness for argument to function
    assume $IsAlloc(##c'#1, Tclass._module.com(), $Heap);
    ##s'#1 := t#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s'#1, TMap(TSeq(TChar), TInt), $Heap);
    assume _module.__default.small__step__star#canCall(c#0, s#0, Lit(#_module.com.SKIP()), t#0);
    assume _module.__default.small__step__star#canCall(c#0, s#0, Lit(#_module.com.SKIP()), t#0);
    if (_module.__default.small__step__star($LS($LZ), c#0, s#0, Lit(#_module.com.SKIP()), t#0))
    {
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(355,34)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        c##1_0 := c#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        s##1_0 := s#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        t##1_0 := t#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.SmallStepStar__implies__BigStep(c##1_0, s##1_0, t##1_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(355,42)"} true;
    }
    else
    {
    }
}



// function declaration for _module._default.final
function _module.__default.final(c#0: DatatypeType, s#0: Map Box Box) : bool;

function _module.__default.final#canCall(c#0: DatatypeType, s#0: Map Box Box) : bool;

// consequence axiom for _module.__default.final
axiom 44 <= $FunctionContextHeight
   ==> (forall c#0: DatatypeType, s#0: Map Box Box :: 
    { _module.__default.final(c#0, s#0) } 
    _module.__default.final#canCall(c#0, s#0)
         || (44 != $FunctionContextHeight
           && 
          $Is(c#0, Tclass._module.com())
           && $Is(s#0, TMap(TSeq(TChar), TInt)))
       ==> true);

function _module.__default.final#requires(DatatypeType, Map Box Box) : bool;

// #requires axiom for _module.__default.final
axiom (forall c#0: DatatypeType, s#0: Map Box Box :: 
  { _module.__default.final#requires(c#0, s#0) } 
  $Is(c#0, Tclass._module.com()) && $Is(s#0, TMap(TSeq(TChar), TInt))
     ==> _module.__default.final#requires(c#0, s#0) == true);

// definition axiom for _module.__default.final (revealed)
axiom 44 <= $FunctionContextHeight
   ==> (forall c#0: DatatypeType, s#0: Map Box Box :: 
    { _module.__default.final(c#0, s#0) } 
    _module.__default.final#canCall(c#0, s#0)
         || (44 != $FunctionContextHeight
           && 
          $Is(c#0, Tclass._module.com())
           && $Is(s#0, TMap(TSeq(TChar), TInt)))
       ==> (forall c'#0: DatatypeType, s'#0: Map Box Box :: 
          { _module.__default.small__step($LS($LZ), c#0, s#0, c'#0, s'#0) } 
          $Is(c'#0, Tclass._module.com()) && $Is(s'#0, TMap(TSeq(TChar), TInt))
             ==> _module.__default.small__step#canCall(c#0, s#0, c'#0, s'#0))
         && _module.__default.final(c#0, s#0)
           == !(exists c'#0: DatatypeType, s'#0: Map Box Box :: 
            { _module.__default.small__step($LS($LZ), c#0, s#0, c'#0, s'#0) } 
            $Is(c'#0, Tclass._module.com())
               && $Is(s'#0, TMap(TSeq(TChar), TInt))
               && _module.__default.small__step($LS($LZ), c#0, s#0, c'#0, s'#0)));

// definition axiom for _module.__default.final for all literals (revealed)
axiom 44 <= $FunctionContextHeight
   ==> (forall c#0: DatatypeType, s#0: Map Box Box :: 
    {:weight 3} { _module.__default.final(Lit(c#0), Lit(s#0)) } 
    _module.__default.final#canCall(Lit(c#0), Lit(s#0))
         || (44 != $FunctionContextHeight
           && 
          $Is(c#0, Tclass._module.com())
           && $Is(s#0, TMap(TSeq(TChar), TInt)))
       ==> (forall c'#1: DatatypeType, s'#1: Map Box Box :: 
          { _module.__default.small__step($LS($LZ), c#0, s#0, c'#1, s'#1) } 
          $Is(c'#1, Tclass._module.com()) && $Is(s'#1, TMap(TSeq(TChar), TInt))
             ==> _module.__default.small__step#canCall(Lit(c#0), Lit(s#0), c'#1, s'#1))
         && _module.__default.final(Lit(c#0), Lit(s#0))
           == !(exists c'#1: DatatypeType, s'#1: Map Box Box :: 
            { _module.__default.small__step($LS($LZ), c#0, s#0, c'#1, s'#1) } 
            $Is(c'#1, Tclass._module.com())
               && $Is(s'#1, TMap(TSeq(TChar), TInt))
               && _module.__default.small__step($LS($LZ), Lit(c#0), Lit(s#0), c'#1, s'#1)));

procedure CheckWellformed$$_module.__default.final(c#0: DatatypeType where $Is(c#0, Tclass._module.com()), 
    s#0: Map Box Box where $Is(s#0, TMap(TSeq(TChar), TInt)));
  free requires 44 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.final(c#0: DatatypeType, s#0: Map Box Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var c'#2: DatatypeType;
  var s'#2: Map Box Box;
  var ##c#0: DatatypeType;
  var ##s#0: Map Box Box;
  var ##c'#0: DatatypeType;
  var ##s'#0: Map Box Box;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function final
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(359,10): initial state"} true;
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
        havoc c'#2;
        havoc s'#2;
        if ($Is(c'#2, Tclass._module.com()) && $Is(s'#2, TMap(TSeq(TChar), TInt)))
        {
            ##c#0 := c#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##c#0, Tclass._module.com(), $Heap);
            ##s#0 := s#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#0, TMap(TSeq(TChar), TInt), $Heap);
            ##c'#0 := c'#2;
            // assume allocatedness for argument to function
            assume $IsAlloc(##c'#0, Tclass._module.com(), $Heap);
            ##s'#0 := s'#2;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s'#0, TMap(TSeq(TChar), TInt), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.small__step#canCall(c#0, s#0, c'#2, s'#2);
        }

        // End Comprehension WF check
        assume _module.__default.final(c#0, s#0)
           == !(exists c'#3: DatatypeType, s'#3: Map Box Box :: 
            { _module.__default.small__step($LS($LZ), c#0, s#0, c'#3, s'#3) } 
            $Is(c'#3, Tclass._module.com())
               && $Is(s'#3, TMap(TSeq(TChar), TInt))
               && _module.__default.small__step($LS($LZ), c#0, s#0, c'#3, s'#3));
        assume (forall c'#3: DatatypeType, s'#3: Map Box Box :: 
          { _module.__default.small__step($LS($LZ), c#0, s#0, c'#3, s'#3) } 
          $Is(c'#3, Tclass._module.com()) && $Is(s'#3, TMap(TSeq(TChar), TInt))
             ==> _module.__default.small__step#canCall(c#0, s#0, c'#3, s'#3));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.final(c#0, s#0), TBool);
        assert b$reqreads#0;
    }
}



procedure CheckWellformed$$_module.__default.final__is__skip(c#0: DatatypeType
       where $Is(c#0, Tclass._module.com())
         && $IsAlloc(c#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#0), 
    s#0: Map Box Box
       where $Is(s#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s#0, TMap(TSeq(TChar), TInt), $Heap));
  free requires 46 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.final__is__skip(c#0: DatatypeType
       where $Is(c#0, Tclass._module.com())
         && $IsAlloc(c#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#0), 
    s#0: Map Box Box
       where $Is(s#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s#0, TMap(TSeq(TChar), TInt), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.final#canCall(c#0, s#0) && $IsA#_module.com(c#0);
  ensures _module.__default.final(c#0, s#0)
     <==> _module.com#Equal(c#0, #_module.com.SKIP());
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.final__is__skip(c#0: DatatypeType
       where $Is(c#0, Tclass._module.com())
         && $IsAlloc(c#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#0), 
    s#0: Map Box Box
       where $Is(s#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s#0, TMap(TSeq(TChar), TInt), $Heap))
   returns ($_reverifyPost: bool);
  free requires 46 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.final#canCall(c#0, s#0) && $IsA#_module.com(c#0);
  ensures _module.__default.final(c#0, s#0)
     <==> _module.com#Equal(c#0, #_module.com.SKIP());
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.final__is__skip(c#0: DatatypeType, s#0: Map Box Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##c#0_0: DatatypeType;
  var ##s#0_0: Map Box Box;
  var _v9#0: DatatypeType
     where $Is(_v9#0, Tclass._module.com()) && $IsAlloc(_v9#0, Tclass._module.com(), $Heap);
  var _v10#0: Map Box Box
     where $Is(_v10#0, TMap(TSeq(TChar), TInt))
       && $IsAlloc(_v10#0, TMap(TSeq(TChar), TInt), $Heap);
  var $rhs##0: DatatypeType
     where $Is($rhs##0, Tclass._module.com())
       && $IsAlloc($rhs##0, Tclass._module.com(), $Heap);
  var $rhs##1: Map Box Box
     where $Is($rhs##1, TMap(TSeq(TChar), TInt))
       && $IsAlloc($rhs##1, TMap(TSeq(TChar), TInt), $Heap);
  var c##0: DatatypeType;
  var s##0: Map Box Box;

    // AddMethodImpl: final_is_skip, Impl$$_module.__default.final__is__skip
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(367,0): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(368,3)
    assume $IsA#_module.com(c#0);
    if (_module.com#Equal(c#0, #_module.com.SKIP()))
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(369,5)
        ##c#0_0 := c#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#0_0, Tclass._module.com(), $Heap);
        ##s#0_0 := s#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#0_0, TMap(TSeq(TChar), TInt), $Heap);
        assume _module.__default.final#canCall(c#0, s#0);
        assume _module.__default.final#canCall(c#0, s#0);
        assert {:subsumption 0} _module.__default.final#canCall(c#0, s#0)
           ==> _module.__default.final(c#0, s#0)
             || !(exists c'#0_0: DatatypeType, s'#0_0: Map Box Box :: 
              { _module.__default.small__step($LS($LS($LZ)), c#0, s#0, c'#0_0, s'#0_0) } 
              $Is(c'#0_0, Tclass._module.com())
                 && $Is(s'#0_0, TMap(TSeq(TChar), TInt))
                 && _module.__default.small__step($LS($LS($LZ)), c#0, s#0, c'#0_0, s'#0_0));
        assume _module.__default.final(c#0, s#0);
    }
    else
    {
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(371,44)
        assume true;
        assume true;
        // TrCallStmt: Adding lhs with type com
        // TrCallStmt: Adding lhs with type state
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        c##0 := c#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        s##0 := s#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call $rhs##0, $rhs##1 := Call$$_module.__default.only__skip__has__no__next__state(c##0, s##0);
        // TrCallStmt: After ProcessCallStmt
        _v9#0 := $rhs##0;
        _v10#0 := $rhs##1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(371,49)"} true;
    }
}



procedure CheckWellformed$$_module.__default.only__skip__has__no__next__state(c#0: DatatypeType
       where $Is(c#0, Tclass._module.com())
         && $IsAlloc(c#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#0), 
    s#0: Map Box Box
       where $Is(s#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s#0, TMap(TSeq(TChar), TInt), $Heap))
   returns (c'#0: DatatypeType
       where $Is(c'#0, Tclass._module.com()) && $IsAlloc(c'#0, Tclass._module.com(), $Heap), 
    s'#0: Map Box Box
       where $Is(s'#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s'#0, TMap(TSeq(TChar), TInt), $Heap));
  free requires 45 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.only__skip__has__no__next__state(c#0: DatatypeType
       where $Is(c#0, Tclass._module.com())
         && $IsAlloc(c#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#0), 
    s#0: Map Box Box
       where $Is(s#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s#0, TMap(TSeq(TChar), TInt), $Heap))
   returns (c'#0: DatatypeType
       where $Is(c'#0, Tclass._module.com()) && $IsAlloc(c'#0, Tclass._module.com(), $Heap), 
    s'#0: Map Box Box
       where $Is(s'#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s'#0, TMap(TSeq(TChar), TInt), $Heap));
  // user-defined preconditions
  requires !_module.com#Equal(c#0, #_module.com.SKIP());
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.small__step#canCall(c#0, s#0, c'#0, s'#0);
  ensures _module.__default.small__step($LS($LS($LZ)), c#0, s#0, c'#0, s'#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.only__skip__has__no__next__state(c#0: DatatypeType
       where $Is(c#0, Tclass._module.com())
         && $IsAlloc(c#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#0), 
    s#0: Map Box Box
       where $Is(s#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s#0, TMap(TSeq(TChar), TInt), $Heap))
   returns (c'#0: DatatypeType
       where $Is(c'#0, Tclass._module.com()) && $IsAlloc(c'#0, Tclass._module.com(), $Heap), 
    s'#0: Map Box Box
       where $Is(s'#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s'#0, TMap(TSeq(TChar), TInt), $Heap), 
    $_reverifyPost: bool);
  free requires 45 == $FunctionContextHeight;
  // user-defined preconditions
  requires !_module.com#Equal(c#0, #_module.com.SKIP());
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.small__step#canCall(c#0, s#0, c'#0, s'#0);
  ensures _module.__default.small__step($LS($LS($LZ)), c#0, s#0, c'#0, s'#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.only__skip__has__no__next__state(c#0: DatatypeType, s#0: Map Box Box)
   returns (c'#0: DatatypeType, s'#0: Map Box Box, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#7#0_0: DatatypeType;
  var _mcc#8#0_0: DatatypeType;
  var body#0_0: DatatypeType;
  var let#0_0#0#0: DatatypeType;
  var b#0_0: DatatypeType;
  var let#0_1#0#0: DatatypeType;
  var $rhs#0_0: DatatypeType where $Is($rhs#0_0, Tclass._module.com());
  var $rhs#0_1: Map Box Box where $Is($rhs#0_1, TMap(TSeq(TChar), TInt));
  var _mcc#4#1_0: DatatypeType;
  var _mcc#5#1_0: DatatypeType;
  var _mcc#6#1_0: DatatypeType;
  var els#1_0: DatatypeType;
  var let#1_0#0#0: DatatypeType;
  var thn#1_0: DatatypeType;
  var let#1_1#0#0: DatatypeType;
  var b#1_0: DatatypeType;
  var let#1_2#0#0: DatatypeType;
  var $rhs#1_0: DatatypeType where $Is($rhs#1_0, Tclass._module.com());
  var ##b#1_0: DatatypeType;
  var ##s#1_0: Map Box Box;
  var $rhs#1_1: Map Box Box where $Is($rhs#1_1, TMap(TSeq(TChar), TInt));
  var _mcc#2#2_0: DatatypeType;
  var _mcc#3#2_0: DatatypeType;
  var c1#2_0: DatatypeType;
  var let#2_0#0#0: DatatypeType;
  var c0#2_0: DatatypeType;
  var let#2_1#0#0: DatatypeType;
  var $rhs#2_0_0: DatatypeType where $Is($rhs#2_0_0, Tclass._module.com());
  var $rhs#2_0_1: Map Box Box where $Is($rhs#2_0_1, TMap(TSeq(TChar), TInt));
  var $rhs##2_0: DatatypeType
     where $Is($rhs##2_0, Tclass._module.com())
       && $IsAlloc($rhs##2_0, Tclass._module.com(), $Heap);
  var $rhs##2_1: Map Box Box
     where $Is($rhs##2_1, TMap(TSeq(TChar), TInt))
       && $IsAlloc($rhs##2_1, TMap(TSeq(TChar), TInt), $Heap);
  var c##2_0: DatatypeType;
  var s##2_0: Map Box Box;
  var _mcc#0#3_0: Seq Box;
  var _mcc#1#3_0: DatatypeType;
  var a#3_0: DatatypeType;
  var let#3_0#0#0: DatatypeType;
  var x#3_0: Seq Box;
  var let#3_1#0#0: Seq Box;
  var $rhs#3_0: DatatypeType where $Is($rhs#3_0, Tclass._module.com());
  var $rhs#3_1: Map Box Box where $Is($rhs#3_1, TMap(TSeq(TChar), TInt));
  var ##a#3_0: DatatypeType;
  var ##s#3_0: Map Box Box;

    // AddMethodImpl: only_skip_has_no_next_state, Impl$$_module.__default.only__skip__has__no__next__state
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(377,0): initial state"} true;
    $_reverifyPost := false;
    assume true;
    havoc _mcc#7#0_0, _mcc#8#0_0;
    havoc _mcc#4#1_0, _mcc#5#1_0, _mcc#6#1_0;
    havoc _mcc#2#2_0, _mcc#3#2_0;
    havoc _mcc#0#3_0, _mcc#1#3_0;
    if (c#0 == #_module.com.SKIP())
    {
    }
    else if (c#0 == #_module.com.Assign(_mcc#0#3_0, _mcc#1#3_0))
    {
        assume $Is(_mcc#0#3_0, TSeq(TChar));
        assume $Is(_mcc#1#3_0, Tclass._module.aexp());
        havoc a#3_0;
        assume $Is(a#3_0, Tclass._module.aexp())
           && $IsAlloc(a#3_0, Tclass._module.aexp(), $Heap);
        assume let#3_0#0#0 == _mcc#1#3_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#3_0#0#0, Tclass._module.aexp());
        assume a#3_0 == let#3_0#0#0;
        havoc x#3_0;
        assume $Is(x#3_0, TSeq(TChar)) && $IsAlloc(x#3_0, TSeq(TChar), $Heap);
        assume let#3_1#0#0 == _mcc#0#3_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#3_1#0#0, TSeq(TChar));
        assume x#3_0 == let#3_1#0#0;
        // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(381,12)
        assume true;
        assume true;
        assume true;
        $rhs#3_0 := Lit(#_module.com.SKIP());
        ##a#3_0 := a#3_0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##a#3_0, Tclass._module.aexp(), $Heap);
        ##s#3_0 := s#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#3_0, TMap(TSeq(TChar), TInt), $Heap);
        assume _module.__default.aval#canCall(a#3_0, s#0);
        assume _module.__default.aval#canCall(a#3_0, s#0);
        $rhs#3_1 := Map#Build(s#0, $Box(x#3_0), $Box(_module.__default.aval($LS($LZ), a#3_0, s#0)));
        c'#0 := $rhs#3_0;
        s'#0 := $rhs#3_1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(381,38)"} true;
    }
    else if (c#0 == #_module.com.Seq(_mcc#2#2_0, _mcc#3#2_0))
    {
        assume $Is(_mcc#2#2_0, Tclass._module.com());
        assume $Is(_mcc#3#2_0, Tclass._module.com());
        havoc c1#2_0;
        assume $Is(c1#2_0, Tclass._module.com())
           && $IsAlloc(c1#2_0, Tclass._module.com(), $Heap);
        assume let#2_0#0#0 == _mcc#3#2_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#2_0#0#0, Tclass._module.com());
        assume c1#2_0 == let#2_0#0#0;
        havoc c0#2_0;
        assume $Is(c0#2_0, Tclass._module.com())
           && $IsAlloc(c0#2_0, Tclass._module.com(), $Heap);
        assume let#2_1#0#0 == _mcc#2#2_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#2_1#0#0, Tclass._module.com());
        assume c0#2_0 == let#2_1#0#0;
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(383,5)
        assume $IsA#_module.com(c0#2_0);
        if (_module.com#Equal(c0#2_0, #_module.com.SKIP()))
        {
            // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(384,14)
            assume true;
            assume true;
            assume true;
            $rhs#2_0_0 := c1#2_0;
            assume true;
            $rhs#2_0_1 := s#0;
            c'#0 := $rhs#2_0_0;
            s'#0 := $rhs#2_0_1;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(384,21)"} true;
        }
        else
        {
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(386,44)
            assume true;
            assume true;
            // TrCallStmt: Adding lhs with type com
            // TrCallStmt: Adding lhs with type state
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            c##2_0 := c0#2_0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            s##2_0 := s#0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(c##2_0) < DtRank(c#0)
               || (DtRank(c##2_0) == DtRank(c#0)
                 && 
                Set#Subset(Map#Domain(s##2_0), Map#Domain(s#0))
                 && !Set#Subset(Map#Domain(s#0), Map#Domain(s##2_0)));
            // ProcessCallStmt: Make the call
            call $rhs##2_0, $rhs##2_1 := Call$$_module.__default.only__skip__has__no__next__state(c##2_0, s##2_0);
            // TrCallStmt: After ProcessCallStmt
            c'#0 := $rhs##2_0;
            s'#0 := $rhs##2_1;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(386,50)"} true;
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(387,10)
            assume true;
            assume true;
            c'#0 := #_module.com.Seq(c'#0, c1#2_0);
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(387,23)"} true;
        }
    }
    else if (c#0 == #_module.com.If(_mcc#4#1_0, _mcc#5#1_0, _mcc#6#1_0))
    {
        assume $Is(_mcc#4#1_0, Tclass._module.bexp());
        assume $Is(_mcc#5#1_0, Tclass._module.com());
        assume $Is(_mcc#6#1_0, Tclass._module.com());
        havoc els#1_0;
        assume $Is(els#1_0, Tclass._module.com())
           && $IsAlloc(els#1_0, Tclass._module.com(), $Heap);
        assume let#1_0#0#0 == _mcc#6#1_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#1_0#0#0, Tclass._module.com());
        assume els#1_0 == let#1_0#0#0;
        havoc thn#1_0;
        assume $Is(thn#1_0, Tclass._module.com())
           && $IsAlloc(thn#1_0, Tclass._module.com(), $Heap);
        assume let#1_1#0#0 == _mcc#5#1_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#1_1#0#0, Tclass._module.com());
        assume thn#1_0 == let#1_1#0#0;
        havoc b#1_0;
        assume $Is(b#1_0, Tclass._module.bexp())
           && $IsAlloc(b#1_0, Tclass._module.bexp(), $Heap);
        assume let#1_2#0#0 == _mcc#4#1_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#1_2#0#0, Tclass._module.bexp());
        assume b#1_0 == let#1_2#0#0;
        // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(390,12)
        assume true;
        assume true;
        ##b#1_0 := b#1_0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##b#1_0, Tclass._module.bexp(), $Heap);
        ##s#1_0 := s#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#1_0, TMap(TSeq(TChar), TInt), $Heap);
        assume _module.__default.bval#canCall(b#1_0, s#0);
        if (_module.__default.bval($LS($LZ), b#1_0, s#0))
        {
        }
        else
        {
        }

        assume _module.__default.bval#canCall(b#1_0, s#0);
        $rhs#1_0 := (if _module.__default.bval($LS($LZ), b#1_0, s#0) then thn#1_0 else els#1_0);
        assume true;
        $rhs#1_1 := s#0;
        c'#0 := $rhs#1_0;
        s'#0 := $rhs#1_1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(390,48)"} true;
    }
    else if (c#0 == #_module.com.While(_mcc#7#0_0, _mcc#8#0_0))
    {
        assume $Is(_mcc#7#0_0, Tclass._module.bexp());
        assume $Is(_mcc#8#0_0, Tclass._module.com());
        havoc body#0_0;
        assume $Is(body#0_0, Tclass._module.com())
           && $IsAlloc(body#0_0, Tclass._module.com(), $Heap);
        assume let#0_0#0#0 == _mcc#8#0_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_0#0#0, Tclass._module.com());
        assume body#0_0 == let#0_0#0#0;
        havoc b#0_0;
        assume $Is(b#0_0, Tclass._module.bexp())
           && $IsAlloc(b#0_0, Tclass._module.bexp(), $Heap);
        assume let#0_1#0#0 == _mcc#7#0_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_1#0#0, Tclass._module.bexp());
        assume b#0_0 == let#0_1#0#0;
        // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(392,12)
        assume true;
        assume true;
        assume true;
        $rhs#0_0 := #_module.com.If(b#0_0, 
          #_module.com.Seq(body#0_0, #_module.com.While(b#0_0, body#0_0)), 
          Lit(#_module.com.SKIP()));
        assume true;
        $rhs#0_1 := s#0;
        c'#0 := $rhs#0_0;
        s'#0 := $rhs#0_1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(392,55)"} true;
    }
    else
    {
        assume false;
    }
}



procedure {:_induction c#0, s#0} CheckWellformed$$_module.__default.lemma__7__18(c#0: DatatypeType
       where $Is(c#0, Tclass._module.com())
         && $IsAlloc(c#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#0), 
    s#0: Map Box Box
       where $Is(s#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s#0, TMap(TSeq(TChar), TInt), $Heap));
  free requires 47 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction c#0, s#0} Call$$_module.__default.lemma__7__18(c#0: DatatypeType
       where $Is(c#0, Tclass._module.com())
         && $IsAlloc(c#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#0), 
    s#0: Map Box Box
       where $Is(s#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s#0, TMap(TSeq(TChar), TInt), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall t#1: Map Box Box :: 
      { _module.__default.big__step($LS($LZ), c#0, s#0, t#1) } 
      $Is(t#1, TMap(TSeq(TChar), TInt))
         ==> _module.__default.big__step#canCall(c#0, s#0, t#1))
     && (forall c'#1: DatatypeType, s'#1: Map Box Box :: 
      { _module.__default.final(c'#1, s'#1) } 
        { _module.__default.small__step__star($LS($LZ), c#0, s#0, c'#1, s'#1) } 
      $Is(c'#1, Tclass._module.com()) && $Is(s'#1, TMap(TSeq(TChar), TInt))
         ==> _module.__default.small__step__star#canCall(c#0, s#0, c'#1, s'#1)
           && (_module.__default.small__step__star($LS($LZ), c#0, s#0, c'#1, s'#1)
             ==> _module.__default.final#canCall(c'#1, s'#1)));
  ensures (exists t#1: Map Box Box :: 
      { _module.__default.big__step($LS($LS($LZ)), c#0, s#0, t#1) } 
      $Is(t#1, TMap(TSeq(TChar), TInt))
         && _module.__default.big__step($LS($LS($LZ)), c#0, s#0, t#1))
     <==> (exists c'#1: DatatypeType, s'#1: Map Box Box :: 
      { _module.__default.final(c'#1, s'#1) } 
        { _module.__default.small__step__star($LS($LS($LZ)), c#0, s#0, c'#1, s'#1) } 
      $Is(c'#1, Tclass._module.com())
         && $Is(s'#1, TMap(TSeq(TChar), TInt))
         && 
        _module.__default.small__step__star($LS($LS($LZ)), c#0, s#0, c'#1, s'#1)
         && _module.__default.final(c'#1, s'#1));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction c#0, s#0} Impl$$_module.__default.lemma__7__18(c#0: DatatypeType
       where $Is(c#0, Tclass._module.com())
         && $IsAlloc(c#0, Tclass._module.com(), $Heap)
         && $IsA#_module.com(c#0), 
    s#0: Map Box Box
       where $Is(s#0, TMap(TSeq(TChar), TInt))
         && $IsAlloc(s#0, TMap(TSeq(TChar), TInt), $Heap))
   returns ($_reverifyPost: bool);
  free requires 47 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall t#1: Map Box Box :: 
      { _module.__default.big__step($LS($LZ), c#0, s#0, t#1) } 
      $Is(t#1, TMap(TSeq(TChar), TInt))
         ==> _module.__default.big__step#canCall(c#0, s#0, t#1))
     && (forall c'#1: DatatypeType, s'#1: Map Box Box :: 
      { _module.__default.final(c'#1, s'#1) } 
        { _module.__default.small__step__star($LS($LZ), c#0, s#0, c'#1, s'#1) } 
      $Is(c'#1, Tclass._module.com()) && $Is(s'#1, TMap(TSeq(TChar), TInt))
         ==> _module.__default.small__step__star#canCall(c#0, s#0, c'#1, s'#1)
           && (_module.__default.small__step__star($LS($LZ), c#0, s#0, c'#1, s'#1)
             ==> _module.__default.final#canCall(c'#1, s'#1)));
  ensures (exists t#1: Map Box Box :: 
      { _module.__default.big__step($LS($LS($LZ)), c#0, s#0, t#1) } 
      $Is(t#1, TMap(TSeq(TChar), TInt))
         && _module.__default.big__step($LS($LS($LZ)), c#0, s#0, t#1))
     <==> (exists c'#1: DatatypeType, s'#1: Map Box Box :: 
      { _module.__default.final(c'#1, s'#1) } 
        { _module.__default.small__step__star($LS($LS($LZ)), c#0, s#0, c'#1, s'#1) } 
      $Is(c'#1, Tclass._module.com())
         && $Is(s'#1, TMap(TSeq(TChar), TInt))
         && 
        _module.__default.small__step__star($LS($LS($LZ)), c#0, s#0, c'#1, s'#1)
         && _module.__default.final(c'#1, s'#1));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction c#0, s#0} Impl$$_module.__default.lemma__7__18(c#0: DatatypeType, s#0: Map Box Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var t#3: Map Box Box;
  var ##c#3: DatatypeType;
  var ##s#3: Map Box Box;
  var ##t#1: Map Box Box;
  var t#0_0: Map Box Box
     where $Is(t#0_0, TMap(TSeq(TChar), TInt))
       && $IsAlloc(t#0_0, TMap(TSeq(TChar), TInt), $Heap);
  var t#0_1: Map Box Box;
  var ##c#0_0: DatatypeType;
  var ##s#0_0: Map Box Box;
  var ##t#0_0: Map Box Box;
  var c##0_0: DatatypeType;
  var s##0_0: Map Box Box;
  var t##0_0: Map Box Box;
  var ##c#0_0_0_0: DatatypeType;
  var ##s#0_0_0_0: Map Box Box;
  var ##c'#0_0_0_0: DatatypeType;
  var ##s'#0_0_0_0: Map Box Box;
  var ##c#0_0_0_1: DatatypeType;
  var ##s#0_0_0_1: Map Box Box;
  var ##c#0_0_0_2: DatatypeType;
  var ##s#0_0_0_2: Map Box Box;
  var ##c'#0_0_0_1: DatatypeType;
  var ##s'#0_0_0_1: Map Box Box;
  var ##c#0_0_0_3: DatatypeType;
  var ##s#0_0_0_3: Map Box Box;
  var ##c#0_0_1_0: DatatypeType;
  var ##s#0_0_1_0: Map Box Box;
  var ##t#0_0_1_0: Map Box Box;
  var ##c#0_0_1_1: DatatypeType;
  var ##s#0_0_1_1: Map Box Box;
  var ##c'#0_0_1_0: DatatypeType;
  var ##s'#0_0_1_0: Map Box Box;
  var ##c#0_0_2_0: DatatypeType;
  var ##s#0_0_2_0: Map Box Box;
  var ##t#0_0_2_0: Map Box Box;
  var c'#3: DatatypeType;
  var s'#3: Map Box Box;
  var ##c#4: DatatypeType;
  var ##s#4: Map Box Box;
  var ##c'#1: DatatypeType;
  var ##s'#1: Map Box Box;
  var ##c#5: DatatypeType;
  var ##s#5: Map Box Box;
  var c'#1_0: DatatypeType
     where $Is(c'#1_0, Tclass._module.com())
       && $IsAlloc(c'#1_0, Tclass._module.com(), $Heap);
  var s'#1_0: Map Box Box
     where $Is(s'#1_0, TMap(TSeq(TChar), TInt))
       && $IsAlloc(s'#1_0, TMap(TSeq(TChar), TInt), $Heap);
  var c'#1_1: DatatypeType;
  var s'#1_1: Map Box Box;
  var ##c#1_0: DatatypeType;
  var ##s#1_0: Map Box Box;
  var ##c'#1_0: DatatypeType;
  var ##s'#1_0: Map Box Box;
  var ##c#1_1: DatatypeType;
  var ##s#1_1: Map Box Box;
  var c##1_0: DatatypeType;
  var s##1_0: Map Box Box;
  var c##1_1: DatatypeType;
  var s##1_1: Map Box Box;
  var t##1_0: Map Box Box;

    // AddMethodImpl: lemma_7_18, Impl$$_module.__default.lemma__7__18
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(398,0): initial state"} true;
    assume $IsA#_module.com(c#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#c0#0: DatatypeType, $ih#s0#0: Map Box Box :: 
      $Is($ih#c0#0, Tclass._module.com())
           && $Is($ih#s0#0, TMap(TSeq(TChar), TInt))
           && Lit(true)
           && (DtRank($ih#c0#0) < DtRank(c#0)
             || (DtRank($ih#c0#0) == DtRank(c#0)
               && 
              Set#Subset(Map#Domain($ih#s0#0), Map#Domain(s#0))
               && !Set#Subset(Map#Domain(s#0), Map#Domain($ih#s0#0))))
         ==> ((exists t#2: Map Box Box :: 
            { _module.__default.big__step($LS($LZ), $ih#c0#0, $ih#s0#0, t#2) } 
            $Is(t#2, TMap(TSeq(TChar), TInt))
               && _module.__default.big__step($LS($LZ), $ih#c0#0, $ih#s0#0, t#2))
           <==> (exists c'#2: DatatypeType, s'#2: Map Box Box :: 
            { _module.__default.final(c'#2, s'#2) } 
              { _module.__default.small__step__star($LS($LZ), $ih#c0#0, $ih#s0#0, c'#2, s'#2) } 
            $Is(c'#2, Tclass._module.com())
               && $Is(s'#2, TMap(TSeq(TChar), TInt))
               && 
              _module.__default.small__step__star($LS($LZ), $ih#c0#0, $ih#s0#0, c'#2, s'#2)
               && _module.__default.final(c'#2, s'#2))));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(399,3)
    // Begin Comprehension WF check
    havoc t#3;
    if ($Is(t#3, TMap(TSeq(TChar), TInt)))
    {
        ##c#3 := c#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#3, Tclass._module.com(), $Heap);
        ##s#3 := s#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#3, TMap(TSeq(TChar), TInt), $Heap);
        ##t#1 := t#3;
        // assume allocatedness for argument to function
        assume $IsAlloc(##t#1, TMap(TSeq(TChar), TInt), $Heap);
        assume _module.__default.big__step#canCall(c#0, s#0, t#3);
    }

    // End Comprehension WF check
    assume (forall t#4: Map Box Box :: 
      { _module.__default.big__step($LS($LZ), c#0, s#0, t#4) } 
      $Is(t#4, TMap(TSeq(TChar), TInt))
         ==> _module.__default.big__step#canCall(c#0, s#0, t#4));
    if ((exists t#4: Map Box Box :: 
      { _module.__default.big__step($LS($LZ), c#0, s#0, t#4) } 
      $Is(t#4, TMap(TSeq(TChar), TInt))
         && _module.__default.big__step($LS($LZ), c#0, s#0, t#4)))
    {
        // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(400,11)
        havoc t#0_1;
        if ($Is(t#0_1, TMap(TSeq(TChar), TInt))
           && $IsAlloc(t#0_1, TMap(TSeq(TChar), TInt), $Heap))
        {
            ##c#0_0 := c#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##c#0_0, Tclass._module.com(), $Heap);
            ##s#0_0 := s#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#0_0, TMap(TSeq(TChar), TInt), $Heap);
            ##t#0_0 := t#0_1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#0_0, TMap(TSeq(TChar), TInt), $Heap);
            assume _module.__default.big__step#canCall(c#0, s#0, t#0_1);
            assume _module.__default.big__step#canCall(c#0, s#0, t#0_1);
        }

        assert (exists $as#t0_0#0_0: Map Box Box :: 
          $Is($as#t0_0#0_0, TMap(TSeq(TChar), TInt))
             && _module.__default.big__step($LS($LZ), c#0, s#0, $as#t0_0#0_0));
        havoc t#0_0;
        assume _module.__default.big__step($LS($LZ), c#0, s#0, t#0_0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(400,30)"} true;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(401,31)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        c##0_0 := c#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        s##0_0 := s#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        t##0_0 := t#0_0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.BigStep__SmallStepStar__Same(c##0_0, s##0_0, t##0_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(401,39)"} true;
        // ----- calc statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(402,5)
        // Assume Fuel Constant
        if (*)
        {
            // ----- assert wf[initial] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(402,5)
            assume true;
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(402,5)
            assume true;
            // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(402,5)
            assume true;
            // ----- Hint0 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(402,5)
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(402,5)
            ##c#0_0_2_0 := c#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##c#0_0_2_0, Tclass._module.com(), $Heap);
            ##s#0_0_2_0 := s#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#0_0_2_0, TMap(TSeq(TChar), TInt), $Heap);
            ##t#0_0_2_0 := t#0_0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#0_0_2_0, TMap(TSeq(TChar), TInt), $Heap);
            assume _module.__default.big__step#canCall(c#0, s#0, t#0_0);
            assume _module.__default.big__step#canCall(c#0, s#0, t#0_0);
            // ----- assert line0 ==> line1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(402,5)
            assert {:subsumption 0} Lit(true) ==> _module.__default.big__step($LS($LS($LZ)), c#0, s#0, t#0_0);
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(402,5)
            ##c#0_0_1_0 := c#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##c#0_0_1_0, Tclass._module.com(), $Heap);
            ##s#0_0_1_0 := s#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#0_0_1_0, TMap(TSeq(TChar), TInt), $Heap);
            ##t#0_0_1_0 := t#0_0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#0_0_1_0, TMap(TSeq(TChar), TInt), $Heap);
            assume _module.__default.big__step#canCall(c#0, s#0, t#0_0);
            assume _module.__default.big__step#canCall(c#0, s#0, t#0_0);
            // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(402,5)
            assume _module.__default.big__step($LS($LZ), c#0, s#0, t#0_0);
            // ----- Hint1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(402,5)
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(402,5)
            ##c#0_0_1_1 := c#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##c#0_0_1_1, Tclass._module.com(), $Heap);
            ##s#0_0_1_1 := s#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#0_0_1_1, TMap(TSeq(TChar), TInt), $Heap);
            ##c'#0_0_1_0 := Lit(#_module.com.SKIP());
            // assume allocatedness for argument to function
            assume $IsAlloc(##c'#0_0_1_0, Tclass._module.com(), $Heap);
            ##s'#0_0_1_0 := t#0_0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s'#0_0_1_0, TMap(TSeq(TChar), TInt), $Heap);
            assume _module.__default.small__step__star#canCall(c#0, s#0, Lit(#_module.com.SKIP()), t#0_0);
            assume _module.__default.small__step__star#canCall(c#0, s#0, Lit(#_module.com.SKIP()), t#0_0);
            // ----- assert line1 ==> line2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(402,5)
            assert {:subsumption 0} _module.__default.big__step($LS($LZ), c#0, s#0, t#0_0)
               ==> 
              _module.__default.small__step__star#canCall(c#0, s#0, Lit(#_module.com.SKIP()), t#0_0)
               ==> _module.__default.small__step__star($LS($LZ), c#0, s#0, Lit(#_module.com.SKIP()), t#0_0)
                 || 
                (_module.com#Equal(c#0, #_module.com.SKIP()) && Map#Equal(s#0, t#0_0))
                 || (exists c''#0_0_1_0: DatatypeType, s''#0_0_1_0: Map Box Box :: 
                  { _module.__default.small__step__star($LS($LS($LZ)), c''#0_0_1_0, s''#0_0_1_0, #_module.com.SKIP(), t#0_0) } 
                    { _module.__default.small__step($LS($LS($LZ)), c#0, s#0, c''#0_0_1_0, s''#0_0_1_0) } 
                  $Is(c''#0_0_1_0, Tclass._module.com())
                     && $Is(s''#0_0_1_0, TMap(TSeq(TChar), TInt))
                     && 
                    _module.__default.small__step($LS($LS($LZ)), c#0, s#0, c''#0_0_1_0, s''#0_0_1_0)
                     && _module.__default.small__step__star($LS($LS($LZ)), c''#0_0_1_0, s''#0_0_1_0, Lit(#_module.com.SKIP()), t#0_0));
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(402,5)
            ##c#0_0_0_0 := c#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##c#0_0_0_0, Tclass._module.com(), $Heap);
            ##s#0_0_0_0 := s#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#0_0_0_0, TMap(TSeq(TChar), TInt), $Heap);
            ##c'#0_0_0_0 := Lit(#_module.com.SKIP());
            // assume allocatedness for argument to function
            assume $IsAlloc(##c'#0_0_0_0, Tclass._module.com(), $Heap);
            ##s'#0_0_0_0 := t#0_0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s'#0_0_0_0, TMap(TSeq(TChar), TInt), $Heap);
            assume _module.__default.small__step__star#canCall(c#0, s#0, Lit(#_module.com.SKIP()), t#0_0);
            assume _module.__default.small__step__star#canCall(c#0, s#0, Lit(#_module.com.SKIP()), t#0_0);
            // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(402,5)
            assume _module.__default.small__step__star($LS($LZ), c#0, s#0, Lit(#_module.com.SKIP()), t#0_0);
            // ----- Hint2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(402,5)
            // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(406,9)
            ##c#0_0_0_1 := Lit(#_module.com.SKIP());
            // assume allocatedness for argument to function
            assume $IsAlloc(##c#0_0_0_1, Tclass._module.com(), $Heap);
            ##s#0_0_0_1 := t#0_0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#0_0_0_1, TMap(TSeq(TChar), TInt), $Heap);
            assume _module.__default.final#canCall(Lit(#_module.com.SKIP()), t#0_0);
            assume _module.__default.final#canCall(Lit(#_module.com.SKIP()), t#0_0);
            assert {:subsumption 0} _module.__default.final#canCall(Lit(#_module.com.SKIP()), t#0_0)
               ==> _module.__default.final(Lit(#_module.com.SKIP()), t#0_0)
                 || !(exists c'#0_0_0_0: DatatypeType, s'#0_0_0_0: Map Box Box :: 
                  { _module.__default.small__step($LS($LS($LZ)), #_module.com.SKIP(), t#0_0, c'#0_0_0_0, s'#0_0_0_0) } 
                  $Is(c'#0_0_0_0, Tclass._module.com())
                     && $Is(s'#0_0_0_0, TMap(TSeq(TChar), TInt))
                     && _module.__default.small__step($LS($LS($LZ)), Lit(#_module.com.SKIP()), t#0_0, c'#0_0_0_0, s'#0_0_0_0));
            assume _module.__default.final(Lit(#_module.com.SKIP()), t#0_0);
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(402,5)
            ##c#0_0_0_2 := c#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##c#0_0_0_2, Tclass._module.com(), $Heap);
            ##s#0_0_0_2 := s#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#0_0_0_2, TMap(TSeq(TChar), TInt), $Heap);
            ##c'#0_0_0_1 := Lit(#_module.com.SKIP());
            // assume allocatedness for argument to function
            assume $IsAlloc(##c'#0_0_0_1, Tclass._module.com(), $Heap);
            ##s'#0_0_0_1 := t#0_0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s'#0_0_0_1, TMap(TSeq(TChar), TInt), $Heap);
            assume _module.__default.small__step__star#canCall(c#0, s#0, Lit(#_module.com.SKIP()), t#0_0);
            if (_module.__default.small__step__star($LS($LZ), c#0, s#0, Lit(#_module.com.SKIP()), t#0_0))
            {
                ##c#0_0_0_3 := Lit(#_module.com.SKIP());
                // assume allocatedness for argument to function
                assume $IsAlloc(##c#0_0_0_3, Tclass._module.com(), $Heap);
                ##s#0_0_0_3 := t#0_0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#0_0_0_3, TMap(TSeq(TChar), TInt), $Heap);
                assume _module.__default.final#canCall(Lit(#_module.com.SKIP()), t#0_0);
            }

            assume _module.__default.small__step__star#canCall(c#0, s#0, Lit(#_module.com.SKIP()), t#0_0)
               && (_module.__default.small__step__star($LS($LZ), c#0, s#0, Lit(#_module.com.SKIP()), t#0_0)
                 ==> _module.__default.final#canCall(Lit(#_module.com.SKIP()), t#0_0));
            // ----- assert line2 ==> line3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(402,5)
            assert {:subsumption 0} _module.__default.small__step__star($LS($LZ), c#0, s#0, Lit(#_module.com.SKIP()), t#0_0)
               ==> 
              _module.__default.small__step__star#canCall(c#0, s#0, Lit(#_module.com.SKIP()), t#0_0)
               ==> _module.__default.small__step__star($LS($LZ), c#0, s#0, Lit(#_module.com.SKIP()), t#0_0)
                 || 
                (_module.com#Equal(c#0, #_module.com.SKIP()) && Map#Equal(s#0, t#0_0))
                 || (exists c''#0_0_0_0: DatatypeType, s''#0_0_0_0: Map Box Box :: 
                  { _module.__default.small__step__star($LS($LS($LZ)), c''#0_0_0_0, s''#0_0_0_0, #_module.com.SKIP(), t#0_0) } 
                    { _module.__default.small__step($LS($LS($LZ)), c#0, s#0, c''#0_0_0_0, s''#0_0_0_0) } 
                  $Is(c''#0_0_0_0, Tclass._module.com())
                     && $Is(s''#0_0_0_0, TMap(TSeq(TChar), TInt))
                     && 
                    _module.__default.small__step($LS($LS($LZ)), c#0, s#0, c''#0_0_0_0, s''#0_0_0_0)
                     && _module.__default.small__step__star($LS($LS($LZ)), c''#0_0_0_0, s''#0_0_0_0, Lit(#_module.com.SKIP()), t#0_0));
            assert {:subsumption 0} _module.__default.small__step__star($LS($LZ), c#0, s#0, Lit(#_module.com.SKIP()), t#0_0)
               ==> 
              _module.__default.final#canCall(Lit(#_module.com.SKIP()), t#0_0)
               ==> _module.__default.final(Lit(#_module.com.SKIP()), t#0_0)
                 || !(exists c'#0_0_0_1: DatatypeType, s'#0_0_0_1: Map Box Box :: 
                  { _module.__default.small__step($LS($LS($LZ)), #_module.com.SKIP(), t#0_0, c'#0_0_0_1, s'#0_0_0_1) } 
                  $Is(c'#0_0_0_1, Tclass._module.com())
                     && $Is(s'#0_0_0_1, TMap(TSeq(TChar), TInt))
                     && _module.__default.small__step($LS($LS($LZ)), Lit(#_module.com.SKIP()), t#0_0, c'#0_0_0_1, s'#0_0_0_1));
            assume false;
        }

        assume true
           ==> _module.__default.small__step__star($LS($LZ), c#0, s#0, Lit(#_module.com.SKIP()), t#0_0)
             && _module.__default.final(Lit(#_module.com.SKIP()), t#0_0);
    }
    else
    {
    }

    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(410,3)
    // Begin Comprehension WF check
    havoc c'#3;
    havoc s'#3;
    if ($Is(c'#3, Tclass._module.com()) && $Is(s'#3, TMap(TSeq(TChar), TInt)))
    {
        ##c#4 := c#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#4, Tclass._module.com(), $Heap);
        ##s#4 := s#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#4, TMap(TSeq(TChar), TInt), $Heap);
        ##c'#1 := c'#3;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c'#1, Tclass._module.com(), $Heap);
        ##s'#1 := s'#3;
        // assume allocatedness for argument to function
        assume $IsAlloc(##s'#1, TMap(TSeq(TChar), TInt), $Heap);
        assume _module.__default.small__step__star#canCall(c#0, s#0, c'#3, s'#3);
        if (_module.__default.small__step__star($LS($LZ), c#0, s#0, c'#3, s'#3))
        {
            ##c#5 := c'#3;
            // assume allocatedness for argument to function
            assume $IsAlloc(##c#5, Tclass._module.com(), $Heap);
            ##s#5 := s'#3;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#5, TMap(TSeq(TChar), TInt), $Heap);
            assume _module.__default.final#canCall(c'#3, s'#3);
        }
    }

    // End Comprehension WF check
    assume (forall c'#4: DatatypeType, s'#4: Map Box Box :: 
      { _module.__default.final(c'#4, s'#4) } 
        { _module.__default.small__step__star($LS($LZ), c#0, s#0, c'#4, s'#4) } 
      $Is(c'#4, Tclass._module.com()) && $Is(s'#4, TMap(TSeq(TChar), TInt))
         ==> _module.__default.small__step__star#canCall(c#0, s#0, c'#4, s'#4)
           && (_module.__default.small__step__star($LS($LZ), c#0, s#0, c'#4, s'#4)
             ==> _module.__default.final#canCall(c'#4, s'#4)));
    if ((exists c'#4: DatatypeType, s'#4: Map Box Box :: 
      { _module.__default.final(c'#4, s'#4) } 
        { _module.__default.small__step__star($LS($LZ), c#0, s#0, c'#4, s'#4) } 
      $Is(c'#4, Tclass._module.com())
         && $Is(s'#4, TMap(TSeq(TChar), TInt))
         && 
        _module.__default.small__step__star($LS($LZ), c#0, s#0, c'#4, s'#4)
         && _module.__default.final(c'#4, s'#4)))
    {
        // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(411,15)
        havoc c'#1_1;
        havoc s'#1_1;
        if ($Is(c'#1_1, Tclass._module.com())
           && $IsAlloc(c'#1_1, Tclass._module.com(), $Heap)
           && 
          $Is(s'#1_1, TMap(TSeq(TChar), TInt))
           && $IsAlloc(s'#1_1, TMap(TSeq(TChar), TInt), $Heap))
        {
            ##c#1_0 := c#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##c#1_0, Tclass._module.com(), $Heap);
            ##s#1_0 := s#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#1_0, TMap(TSeq(TChar), TInt), $Heap);
            ##c'#1_0 := c'#1_1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##c'#1_0, Tclass._module.com(), $Heap);
            ##s'#1_0 := s'#1_1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s'#1_0, TMap(TSeq(TChar), TInt), $Heap);
            assume _module.__default.small__step__star#canCall(c#0, s#0, c'#1_1, s'#1_1);
            if (_module.__default.small__step__star($LS($LZ), c#0, s#0, c'#1_1, s'#1_1))
            {
                ##c#1_1 := c'#1_1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##c#1_1, Tclass._module.com(), $Heap);
                ##s#1_1 := s'#1_1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#1_1, TMap(TSeq(TChar), TInt), $Heap);
                assume _module.__default.final#canCall(c'#1_1, s'#1_1);
            }

            assume _module.__default.small__step__star#canCall(c#0, s#0, c'#1_1, s'#1_1)
               && (_module.__default.small__step__star($LS($LZ), c#0, s#0, c'#1_1, s'#1_1)
                 ==> _module.__default.final#canCall(c'#1_1, s'#1_1));
        }

        assert (exists $as#s'1_0#1_0: Map Box Box :: 
            $Is($as#s'1_0#1_0, TMap(TSeq(TChar), TInt))
               && 
              $Is(Lit(#_module.com.SKIP()), Tclass._module.com())
               && 
              _module.__default.small__step__star($LS($LZ), c#0, s#0, Lit(#_module.com.SKIP()), $as#s'1_0#1_0)
               && _module.__default.final(Lit(#_module.com.SKIP()), $as#s'1_0#1_0))
           || (exists $as#c'1_0#1_0: DatatypeType, $as#s'1_0#1_0: Map Box Box :: 
            $Is($as#c'1_0#1_0, Tclass._module.com())
               && $Is($as#s'1_0#1_0, TMap(TSeq(TChar), TInt))
               && 
              _module.__default.small__step__star($LS($LZ), c#0, s#0, $as#c'1_0#1_0, $as#s'1_0#1_0)
               && _module.__default.final($as#c'1_0#1_0, $as#s'1_0#1_0));
        havoc c'#1_0, s'#1_0;
        assume _module.__default.small__step__star($LS($LZ), c#0, s#0, c'#1_0, s'#1_0)
           && _module.__default.final(c'#1_0, s'#1_0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(411,63)"} true;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(412,18)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        c##1_0 := c'#1_0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        s##1_0 := s'#1_0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.final__is__skip(c##1_0, s##1_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(412,25)"} true;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(413,31)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        c##1_1 := c#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        s##1_1 := s#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        t##1_0 := s'#1_0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.BigStep__SmallStepStar__Same(c##1_1, s##1_1, t##1_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/NipkowKlein-chapter7.dfy(413,40)"} true;
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

const unique tytagFamily$_#Func5: TyTagFamily;

const unique tytagFamily$_#PartialFunc5: TyTagFamily;

const unique tytagFamily$_#TotalFunc5: TyTagFamily;

const unique tytagFamily$_tuple#2: TyTagFamily;

const unique tytagFamily$_tuple#0: TyTagFamily;

const unique tytagFamily$List: TyTagFamily;

const unique tytagFamily$aexp: TyTagFamily;

const unique tytagFamily$bexp: TyTagFamily;

const unique tytagFamily$com: TyTagFamily;

const unique tytagFamily$_default: TyTagFamily;
