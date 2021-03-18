// Dafny 3.0.0.30204
// Command Line Options: -compile:0 -noVerify /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy -print:./BitvectorsMore.bpl

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

// Box/unbox axiom for bv7
axiom (forall bx: Box :: 
  { $IsBox(bx, TBitvector(7)) } 
  $IsBox(bx, TBitvector(7))
     ==> $Box($Unbox(bx): bv7) == bx && $Is($Unbox(bx): bv7, TBitvector(7)));

axiom (forall v: bv7 :: { $Is(v, TBitvector(7)) } $Is(v, TBitvector(7)));

axiom (forall v: bv7, heap: Heap :: 
  { $IsAlloc(v, TBitvector(7), heap) } 
  $IsAlloc(v, TBitvector(7), heap));

function {:bvbuiltin "bvand"} and_bv7(bv7, bv7) : bv7;

function {:bvbuiltin "bvor"} or_bv7(bv7, bv7) : bv7;

function {:bvbuiltin "bvxor"} xor_bv7(bv7, bv7) : bv7;

function {:bvbuiltin "bvnot"} not_bv7(bv7) : bv7;

function {:bvbuiltin "bvadd"} add_bv7(bv7, bv7) : bv7;

function {:bvbuiltin "bvsub"} sub_bv7(bv7, bv7) : bv7;

function {:bvbuiltin "bvmul"} mul_bv7(bv7, bv7) : bv7;

function {:bvbuiltin "bvudiv"} div_bv7(bv7, bv7) : bv7;

function {:bvbuiltin "bvurem"} mod_bv7(bv7, bv7) : bv7;

function {:bvbuiltin "bvult"} lt_bv7(bv7, bv7) : bool;

function {:bvbuiltin "bvule"} le_bv7(bv7, bv7) : bool;

function {:bvbuiltin "bvuge"} ge_bv7(bv7, bv7) : bool;

function {:bvbuiltin "bvugt"} gt_bv7(bv7, bv7) : bool;

function {:bvbuiltin "bvshl"} LeftShift_bv7(bv7, bv7) : bv7;

function {:bvbuiltin "bvlshr"} RightShift_bv7(bv7, bv7) : bv7;

function {:bvbuiltin "ext_rotate_left"} LeftRotate_bv7(bv7, bv7) : bv7;

function {:bvbuiltin "ext_rotate_right"} RightRotate_bv7(bv7, bv7) : bv7;

function {:bvbuiltin "(_ int2bv 7)"} nat_to_bv7(int) : bv7;

function {:bvbuiltin "bv2int"} smt_nat_from_bv7(bv7) : int;

function nat_from_bv7(bv7) : int;

axiom (forall b: bv7 :: 
  { nat_from_bv7(b) } 
  0 <= nat_from_bv7(b)
     && nat_from_bv7(b) < 128
     && nat_from_bv7(b) == smt_nat_from_bv7(b));

// Box/unbox axiom for bv137
axiom (forall bx: Box :: 
  { $IsBox(bx, TBitvector(137)) } 
  $IsBox(bx, TBitvector(137))
     ==> $Box($Unbox(bx): bv137) == bx && $Is($Unbox(bx): bv137, TBitvector(137)));

axiom (forall v: bv137 :: { $Is(v, TBitvector(137)) } $Is(v, TBitvector(137)));

axiom (forall v: bv137, heap: Heap :: 
  { $IsAlloc(v, TBitvector(137), heap) } 
  $IsAlloc(v, TBitvector(137), heap));

function {:bvbuiltin "bvand"} and_bv137(bv137, bv137) : bv137;

function {:bvbuiltin "bvor"} or_bv137(bv137, bv137) : bv137;

function {:bvbuiltin "bvxor"} xor_bv137(bv137, bv137) : bv137;

function {:bvbuiltin "bvnot"} not_bv137(bv137) : bv137;

function {:bvbuiltin "bvadd"} add_bv137(bv137, bv137) : bv137;

function {:bvbuiltin "bvsub"} sub_bv137(bv137, bv137) : bv137;

function {:bvbuiltin "bvmul"} mul_bv137(bv137, bv137) : bv137;

function {:bvbuiltin "bvudiv"} div_bv137(bv137, bv137) : bv137;

function {:bvbuiltin "bvurem"} mod_bv137(bv137, bv137) : bv137;

function {:bvbuiltin "bvult"} lt_bv137(bv137, bv137) : bool;

function {:bvbuiltin "bvule"} le_bv137(bv137, bv137) : bool;

function {:bvbuiltin "bvuge"} ge_bv137(bv137, bv137) : bool;

function {:bvbuiltin "bvugt"} gt_bv137(bv137, bv137) : bool;

function {:bvbuiltin "bvshl"} LeftShift_bv137(bv137, bv137) : bv137;

function {:bvbuiltin "bvlshr"} RightShift_bv137(bv137, bv137) : bv137;

function {:bvbuiltin "ext_rotate_left"} LeftRotate_bv137(bv137, bv137) : bv137;

function {:bvbuiltin "ext_rotate_right"} RightRotate_bv137(bv137, bv137) : bv137;

function {:bvbuiltin "(_ int2bv 137)"} nat_to_bv137(int) : bv137;

function {:bvbuiltin "bv2int"} smt_nat_from_bv137(bv137) : int;

function nat_from_bv137(bv137) : int;

axiom (forall b: bv137 :: 
  { nat_from_bv137(b) } 
  0 <= nat_from_bv137(b)
     && nat_from_bv137(b) < 174224571863520493293247799005065324265472
     && nat_from_bv137(b) == smt_nat_from_bv137(b));

function {:inline} and_bv0(Bv0, Bv0) : Bv0
{
  0
}

function {:inline} or_bv0(Bv0, Bv0) : Bv0
{
  0
}

function {:inline} xor_bv0(Bv0, Bv0) : Bv0
{
  0
}

function {:inline} not_bv0(Bv0) : Bv0
{
  0
}

function {:inline} add_bv0(Bv0, Bv0) : Bv0
{
  0
}

function {:inline} sub_bv0(Bv0, Bv0) : Bv0
{
  0
}

function {:inline} mul_bv0(Bv0, Bv0) : Bv0
{
  0
}

function {:inline} div_bv0(Bv0, Bv0) : Bv0
{
  0
}

function {:inline} mod_bv0(Bv0, Bv0) : Bv0
{
  0
}

function {:inline} lt_bv0(Bv0, Bv0) : bool
{
  false
}

function {:inline} le_bv0(Bv0, Bv0) : bool
{
  true
}

function {:inline} ge_bv0(Bv0, Bv0) : bool
{
  true
}

function {:inline} gt_bv0(Bv0, Bv0) : bool
{
  false
}

function {:inline} LeftShift_bv0(Bv0, Bv0) : Bv0
{
  0
}

function {:inline} RightShift_bv0(Bv0, Bv0) : Bv0
{
  0
}

function {:inline} LeftRotate_bv0(Bv0, Bv0) : Bv0
{
  0
}

function {:inline} RightRotate_bv0(Bv0, Bv0) : Bv0
{
  0
}

function {:inline} nat_to_bv0(int) : Bv0
{
  0
}

function {:inline} nat_from_bv0(Bv0) : int
{
  0
}

// Box/unbox axiom for bv10
axiom (forall bx: Box :: 
  { $IsBox(bx, TBitvector(10)) } 
  $IsBox(bx, TBitvector(10))
     ==> $Box($Unbox(bx): bv10) == bx && $Is($Unbox(bx): bv10, TBitvector(10)));

axiom (forall v: bv10 :: { $Is(v, TBitvector(10)) } $Is(v, TBitvector(10)));

axiom (forall v: bv10, heap: Heap :: 
  { $IsAlloc(v, TBitvector(10), heap) } 
  $IsAlloc(v, TBitvector(10), heap));

function {:bvbuiltin "bvand"} and_bv10(bv10, bv10) : bv10;

function {:bvbuiltin "bvor"} or_bv10(bv10, bv10) : bv10;

function {:bvbuiltin "bvxor"} xor_bv10(bv10, bv10) : bv10;

function {:bvbuiltin "bvnot"} not_bv10(bv10) : bv10;

function {:bvbuiltin "bvadd"} add_bv10(bv10, bv10) : bv10;

function {:bvbuiltin "bvsub"} sub_bv10(bv10, bv10) : bv10;

function {:bvbuiltin "bvmul"} mul_bv10(bv10, bv10) : bv10;

function {:bvbuiltin "bvudiv"} div_bv10(bv10, bv10) : bv10;

function {:bvbuiltin "bvurem"} mod_bv10(bv10, bv10) : bv10;

function {:bvbuiltin "bvult"} lt_bv10(bv10, bv10) : bool;

function {:bvbuiltin "bvule"} le_bv10(bv10, bv10) : bool;

function {:bvbuiltin "bvuge"} ge_bv10(bv10, bv10) : bool;

function {:bvbuiltin "bvugt"} gt_bv10(bv10, bv10) : bool;

function {:bvbuiltin "bvshl"} LeftShift_bv10(bv10, bv10) : bv10;

function {:bvbuiltin "bvlshr"} RightShift_bv10(bv10, bv10) : bv10;

function {:bvbuiltin "ext_rotate_left"} LeftRotate_bv10(bv10, bv10) : bv10;

function {:bvbuiltin "ext_rotate_right"} RightRotate_bv10(bv10, bv10) : bv10;

function {:bvbuiltin "(_ int2bv 10)"} nat_to_bv10(int) : bv10;

function {:bvbuiltin "bv2int"} smt_nat_from_bv10(bv10) : int;

function nat_from_bv10(bv10) : int;

axiom (forall b: bv10 :: 
  { nat_from_bv10(b) } 
  0 <= nat_from_bv10(b)
     && nat_from_bv10(b) < 1024
     && nat_from_bv10(b) == smt_nat_from_bv10(b));

// Box/unbox axiom for bv60
axiom (forall bx: Box :: 
  { $IsBox(bx, TBitvector(60)) } 
  $IsBox(bx, TBitvector(60))
     ==> $Box($Unbox(bx): bv60) == bx && $Is($Unbox(bx): bv60, TBitvector(60)));

axiom (forall v: bv60 :: { $Is(v, TBitvector(60)) } $Is(v, TBitvector(60)));

axiom (forall v: bv60, heap: Heap :: 
  { $IsAlloc(v, TBitvector(60), heap) } 
  $IsAlloc(v, TBitvector(60), heap));

function {:bvbuiltin "bvand"} and_bv60(bv60, bv60) : bv60;

function {:bvbuiltin "bvor"} or_bv60(bv60, bv60) : bv60;

function {:bvbuiltin "bvxor"} xor_bv60(bv60, bv60) : bv60;

function {:bvbuiltin "bvnot"} not_bv60(bv60) : bv60;

function {:bvbuiltin "bvadd"} add_bv60(bv60, bv60) : bv60;

function {:bvbuiltin "bvsub"} sub_bv60(bv60, bv60) : bv60;

function {:bvbuiltin "bvmul"} mul_bv60(bv60, bv60) : bv60;

function {:bvbuiltin "bvudiv"} div_bv60(bv60, bv60) : bv60;

function {:bvbuiltin "bvurem"} mod_bv60(bv60, bv60) : bv60;

function {:bvbuiltin "bvult"} lt_bv60(bv60, bv60) : bool;

function {:bvbuiltin "bvule"} le_bv60(bv60, bv60) : bool;

function {:bvbuiltin "bvuge"} ge_bv60(bv60, bv60) : bool;

function {:bvbuiltin "bvugt"} gt_bv60(bv60, bv60) : bool;

function {:bvbuiltin "bvshl"} LeftShift_bv60(bv60, bv60) : bv60;

function {:bvbuiltin "bvlshr"} RightShift_bv60(bv60, bv60) : bv60;

function {:bvbuiltin "ext_rotate_left"} LeftRotate_bv60(bv60, bv60) : bv60;

function {:bvbuiltin "ext_rotate_right"} RightRotate_bv60(bv60, bv60) : bv60;

function {:bvbuiltin "(_ int2bv 60)"} nat_to_bv60(int) : bv60;

function {:bvbuiltin "bv2int"} smt_nat_from_bv60(bv60) : int;

function nat_from_bv60(bv60) : int;

axiom (forall b: bv60 :: 
  { nat_from_bv60(b) } 
  0 <= nat_from_bv60(b)
     && nat_from_bv60(b) < 1152921504606846976
     && nat_from_bv60(b) == smt_nat_from_bv60(b));

// Box/unbox axiom for bv67
axiom (forall bx: Box :: 
  { $IsBox(bx, TBitvector(67)) } 
  $IsBox(bx, TBitvector(67))
     ==> $Box($Unbox(bx): bv67) == bx && $Is($Unbox(bx): bv67, TBitvector(67)));

axiom (forall v: bv67 :: { $Is(v, TBitvector(67)) } $Is(v, TBitvector(67)));

axiom (forall v: bv67, heap: Heap :: 
  { $IsAlloc(v, TBitvector(67), heap) } 
  $IsAlloc(v, TBitvector(67), heap));

function {:bvbuiltin "bvand"} and_bv67(bv67, bv67) : bv67;

function {:bvbuiltin "bvor"} or_bv67(bv67, bv67) : bv67;

function {:bvbuiltin "bvxor"} xor_bv67(bv67, bv67) : bv67;

function {:bvbuiltin "bvnot"} not_bv67(bv67) : bv67;

function {:bvbuiltin "bvadd"} add_bv67(bv67, bv67) : bv67;

function {:bvbuiltin "bvsub"} sub_bv67(bv67, bv67) : bv67;

function {:bvbuiltin "bvmul"} mul_bv67(bv67, bv67) : bv67;

function {:bvbuiltin "bvudiv"} div_bv67(bv67, bv67) : bv67;

function {:bvbuiltin "bvurem"} mod_bv67(bv67, bv67) : bv67;

function {:bvbuiltin "bvult"} lt_bv67(bv67, bv67) : bool;

function {:bvbuiltin "bvule"} le_bv67(bv67, bv67) : bool;

function {:bvbuiltin "bvuge"} ge_bv67(bv67, bv67) : bool;

function {:bvbuiltin "bvugt"} gt_bv67(bv67, bv67) : bool;

function {:bvbuiltin "bvshl"} LeftShift_bv67(bv67, bv67) : bv67;

function {:bvbuiltin "bvlshr"} RightShift_bv67(bv67, bv67) : bv67;

function {:bvbuiltin "ext_rotate_left"} LeftRotate_bv67(bv67, bv67) : bv67;

function {:bvbuiltin "ext_rotate_right"} RightRotate_bv67(bv67, bv67) : bv67;

function {:bvbuiltin "(_ int2bv 67)"} nat_to_bv67(int) : bv67;

function {:bvbuiltin "bv2int"} smt_nat_from_bv67(bv67) : int;

function nat_from_bv67(bv67) : int;

axiom (forall b: bv67 :: 
  { nat_from_bv67(b) } 
  0 <= nat_from_bv67(b)
     && nat_from_bv67(b) < 147573952589676412928
     && nat_from_bv67(b) == smt_nat_from_bv67(b));

// Box/unbox axiom for bv32
axiom (forall bx: Box :: 
  { $IsBox(bx, TBitvector(32)) } 
  $IsBox(bx, TBitvector(32))
     ==> $Box($Unbox(bx): bv32) == bx && $Is($Unbox(bx): bv32, TBitvector(32)));

axiom (forall v: bv32 :: { $Is(v, TBitvector(32)) } $Is(v, TBitvector(32)));

axiom (forall v: bv32, heap: Heap :: 
  { $IsAlloc(v, TBitvector(32), heap) } 
  $IsAlloc(v, TBitvector(32), heap));

function {:bvbuiltin "bvand"} and_bv32(bv32, bv32) : bv32;

function {:bvbuiltin "bvor"} or_bv32(bv32, bv32) : bv32;

function {:bvbuiltin "bvxor"} xor_bv32(bv32, bv32) : bv32;

function {:bvbuiltin "bvnot"} not_bv32(bv32) : bv32;

function {:bvbuiltin "bvadd"} add_bv32(bv32, bv32) : bv32;

function {:bvbuiltin "bvsub"} sub_bv32(bv32, bv32) : bv32;

function {:bvbuiltin "bvmul"} mul_bv32(bv32, bv32) : bv32;

function {:bvbuiltin "bvudiv"} div_bv32(bv32, bv32) : bv32;

function {:bvbuiltin "bvurem"} mod_bv32(bv32, bv32) : bv32;

function {:bvbuiltin "bvult"} lt_bv32(bv32, bv32) : bool;

function {:bvbuiltin "bvule"} le_bv32(bv32, bv32) : bool;

function {:bvbuiltin "bvuge"} ge_bv32(bv32, bv32) : bool;

function {:bvbuiltin "bvugt"} gt_bv32(bv32, bv32) : bool;

function {:bvbuiltin "bvshl"} LeftShift_bv32(bv32, bv32) : bv32;

function {:bvbuiltin "bvlshr"} RightShift_bv32(bv32, bv32) : bv32;

function {:bvbuiltin "ext_rotate_left"} LeftRotate_bv32(bv32, bv32) : bv32;

function {:bvbuiltin "ext_rotate_right"} RightRotate_bv32(bv32, bv32) : bv32;

function {:bvbuiltin "(_ int2bv 32)"} nat_to_bv32(int) : bv32;

function {:bvbuiltin "bv2int"} smt_nat_from_bv32(bv32) : int;

function nat_from_bv32(bv32) : int;

axiom (forall b: bv32 :: 
  { nat_from_bv32(b) } 
  0 <= nat_from_bv32(b)
     && nat_from_bv32(b) < 4294967296
     && nat_from_bv32(b) == smt_nat_from_bv32(b));

// Box/unbox axiom for bv2
axiom (forall bx: Box :: 
  { $IsBox(bx, TBitvector(2)) } 
  $IsBox(bx, TBitvector(2))
     ==> $Box($Unbox(bx): bv2) == bx && $Is($Unbox(bx): bv2, TBitvector(2)));

axiom (forall v: bv2 :: { $Is(v, TBitvector(2)) } $Is(v, TBitvector(2)));

axiom (forall v: bv2, heap: Heap :: 
  { $IsAlloc(v, TBitvector(2), heap) } 
  $IsAlloc(v, TBitvector(2), heap));

function {:bvbuiltin "bvand"} and_bv2(bv2, bv2) : bv2;

function {:bvbuiltin "bvor"} or_bv2(bv2, bv2) : bv2;

function {:bvbuiltin "bvxor"} xor_bv2(bv2, bv2) : bv2;

function {:bvbuiltin "bvnot"} not_bv2(bv2) : bv2;

function {:bvbuiltin "bvadd"} add_bv2(bv2, bv2) : bv2;

function {:bvbuiltin "bvsub"} sub_bv2(bv2, bv2) : bv2;

function {:bvbuiltin "bvmul"} mul_bv2(bv2, bv2) : bv2;

function {:bvbuiltin "bvudiv"} div_bv2(bv2, bv2) : bv2;

function {:bvbuiltin "bvurem"} mod_bv2(bv2, bv2) : bv2;

function {:bvbuiltin "bvult"} lt_bv2(bv2, bv2) : bool;

function {:bvbuiltin "bvule"} le_bv2(bv2, bv2) : bool;

function {:bvbuiltin "bvuge"} ge_bv2(bv2, bv2) : bool;

function {:bvbuiltin "bvugt"} gt_bv2(bv2, bv2) : bool;

function {:bvbuiltin "bvshl"} LeftShift_bv2(bv2, bv2) : bv2;

function {:bvbuiltin "bvlshr"} RightShift_bv2(bv2, bv2) : bv2;

function {:bvbuiltin "ext_rotate_left"} LeftRotate_bv2(bv2, bv2) : bv2;

function {:bvbuiltin "ext_rotate_right"} RightRotate_bv2(bv2, bv2) : bv2;

function {:bvbuiltin "(_ int2bv 2)"} nat_to_bv2(int) : bv2;

function {:bvbuiltin "bv2int"} smt_nat_from_bv2(bv2) : int;

function nat_from_bv2(bv2) : int;

axiom (forall b: bv2 :: 
  { nat_from_bv2(b) } 
  0 <= nat_from_bv2(b)
     && nat_from_bv2(b) < 4
     && nat_from_bv2(b) == smt_nat_from_bv2(b));

// Box/unbox axiom for bv5
axiom (forall bx: Box :: 
  { $IsBox(bx, TBitvector(5)) } 
  $IsBox(bx, TBitvector(5))
     ==> $Box($Unbox(bx): bv5) == bx && $Is($Unbox(bx): bv5, TBitvector(5)));

axiom (forall v: bv5 :: { $Is(v, TBitvector(5)) } $Is(v, TBitvector(5)));

axiom (forall v: bv5, heap: Heap :: 
  { $IsAlloc(v, TBitvector(5), heap) } 
  $IsAlloc(v, TBitvector(5), heap));

function {:bvbuiltin "bvand"} and_bv5(bv5, bv5) : bv5;

function {:bvbuiltin "bvor"} or_bv5(bv5, bv5) : bv5;

function {:bvbuiltin "bvxor"} xor_bv5(bv5, bv5) : bv5;

function {:bvbuiltin "bvnot"} not_bv5(bv5) : bv5;

function {:bvbuiltin "bvadd"} add_bv5(bv5, bv5) : bv5;

function {:bvbuiltin "bvsub"} sub_bv5(bv5, bv5) : bv5;

function {:bvbuiltin "bvmul"} mul_bv5(bv5, bv5) : bv5;

function {:bvbuiltin "bvudiv"} div_bv5(bv5, bv5) : bv5;

function {:bvbuiltin "bvurem"} mod_bv5(bv5, bv5) : bv5;

function {:bvbuiltin "bvult"} lt_bv5(bv5, bv5) : bool;

function {:bvbuiltin "bvule"} le_bv5(bv5, bv5) : bool;

function {:bvbuiltin "bvuge"} ge_bv5(bv5, bv5) : bool;

function {:bvbuiltin "bvugt"} gt_bv5(bv5, bv5) : bool;

function {:bvbuiltin "bvshl"} LeftShift_bv5(bv5, bv5) : bv5;

function {:bvbuiltin "bvlshr"} RightShift_bv5(bv5, bv5) : bv5;

function {:bvbuiltin "ext_rotate_left"} LeftRotate_bv5(bv5, bv5) : bv5;

function {:bvbuiltin "ext_rotate_right"} RightRotate_bv5(bv5, bv5) : bv5;

function {:bvbuiltin "(_ int2bv 5)"} nat_to_bv5(int) : bv5;

function {:bvbuiltin "bv2int"} smt_nat_from_bv5(bv5) : int;

function nat_from_bv5(bv5) : int;

axiom (forall b: bv5 :: 
  { nat_from_bv5(b) } 
  0 <= nat_from_bv5(b)
     && nat_from_bv5(b) < 32
     && nat_from_bv5(b) == smt_nat_from_bv5(b));

// Box/unbox axiom for bv8
axiom (forall bx: Box :: 
  { $IsBox(bx, TBitvector(8)) } 
  $IsBox(bx, TBitvector(8))
     ==> $Box($Unbox(bx): bv8) == bx && $Is($Unbox(bx): bv8, TBitvector(8)));

axiom (forall v: bv8 :: { $Is(v, TBitvector(8)) } $Is(v, TBitvector(8)));

axiom (forall v: bv8, heap: Heap :: 
  { $IsAlloc(v, TBitvector(8), heap) } 
  $IsAlloc(v, TBitvector(8), heap));

function {:bvbuiltin "bvand"} and_bv8(bv8, bv8) : bv8;

function {:bvbuiltin "bvor"} or_bv8(bv8, bv8) : bv8;

function {:bvbuiltin "bvxor"} xor_bv8(bv8, bv8) : bv8;

function {:bvbuiltin "bvnot"} not_bv8(bv8) : bv8;

function {:bvbuiltin "bvadd"} add_bv8(bv8, bv8) : bv8;

function {:bvbuiltin "bvsub"} sub_bv8(bv8, bv8) : bv8;

function {:bvbuiltin "bvmul"} mul_bv8(bv8, bv8) : bv8;

function {:bvbuiltin "bvudiv"} div_bv8(bv8, bv8) : bv8;

function {:bvbuiltin "bvurem"} mod_bv8(bv8, bv8) : bv8;

function {:bvbuiltin "bvult"} lt_bv8(bv8, bv8) : bool;

function {:bvbuiltin "bvule"} le_bv8(bv8, bv8) : bool;

function {:bvbuiltin "bvuge"} ge_bv8(bv8, bv8) : bool;

function {:bvbuiltin "bvugt"} gt_bv8(bv8, bv8) : bool;

function {:bvbuiltin "bvshl"} LeftShift_bv8(bv8, bv8) : bv8;

function {:bvbuiltin "bvlshr"} RightShift_bv8(bv8, bv8) : bv8;

function {:bvbuiltin "ext_rotate_left"} LeftRotate_bv8(bv8, bv8) : bv8;

function {:bvbuiltin "ext_rotate_right"} RightRotate_bv8(bv8, bv8) : bv8;

function {:bvbuiltin "(_ int2bv 8)"} nat_to_bv8(int) : bv8;

function {:bvbuiltin "bv2int"} smt_nat_from_bv8(bv8) : int;

function nat_from_bv8(bv8) : int;

axiom (forall b: bv8 :: 
  { nat_from_bv8(b) } 
  0 <= nat_from_bv8(b)
     && nat_from_bv8(b) < 256
     && nat_from_bv8(b) == smt_nat_from_bv8(b));

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

function Tclass._System.___hFunc11(Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty) : Ty;

const unique Tagclass._System.___hFunc11: TyTag;

// Tclass._System.___hFunc11 Tag
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R) } 
  Tag(Tclass._System.___hFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R))
       == Tagclass._System.___hFunc11
     && TagFamily(Tclass._System.___hFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R))
       == tytagFamily$_#Func11);

// Tclass._System.___hFunc11 injectivity 0
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R) } 
  Tclass._System.___hFunc11_0(Tclass._System.___hFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R))
     == #$T0);

function Tclass._System.___hFunc11_0(Ty) : Ty;

// Tclass._System.___hFunc11 injectivity 1
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R) } 
  Tclass._System.___hFunc11_1(Tclass._System.___hFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R))
     == #$T1);

function Tclass._System.___hFunc11_1(Ty) : Ty;

// Tclass._System.___hFunc11 injectivity 2
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R) } 
  Tclass._System.___hFunc11_2(Tclass._System.___hFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R))
     == #$T2);

function Tclass._System.___hFunc11_2(Ty) : Ty;

// Tclass._System.___hFunc11 injectivity 3
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R) } 
  Tclass._System.___hFunc11_3(Tclass._System.___hFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R))
     == #$T3);

function Tclass._System.___hFunc11_3(Ty) : Ty;

// Tclass._System.___hFunc11 injectivity 4
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R) } 
  Tclass._System.___hFunc11_4(Tclass._System.___hFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R))
     == #$T4);

function Tclass._System.___hFunc11_4(Ty) : Ty;

// Tclass._System.___hFunc11 injectivity 5
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R) } 
  Tclass._System.___hFunc11_5(Tclass._System.___hFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R))
     == #$T5);

function Tclass._System.___hFunc11_5(Ty) : Ty;

// Tclass._System.___hFunc11 injectivity 6
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R) } 
  Tclass._System.___hFunc11_6(Tclass._System.___hFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R))
     == #$T6);

function Tclass._System.___hFunc11_6(Ty) : Ty;

// Tclass._System.___hFunc11 injectivity 7
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R) } 
  Tclass._System.___hFunc11_7(Tclass._System.___hFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R))
     == #$T7);

function Tclass._System.___hFunc11_7(Ty) : Ty;

// Tclass._System.___hFunc11 injectivity 8
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R) } 
  Tclass._System.___hFunc11_8(Tclass._System.___hFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R))
     == #$T8);

function Tclass._System.___hFunc11_8(Ty) : Ty;

// Tclass._System.___hFunc11 injectivity 9
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R) } 
  Tclass._System.___hFunc11_9(Tclass._System.___hFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R))
     == #$T9);

function Tclass._System.___hFunc11_9(Ty) : Ty;

// Tclass._System.___hFunc11 injectivity 10
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R) } 
  Tclass._System.___hFunc11_10(Tclass._System.___hFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R))
     == #$T10);

function Tclass._System.___hFunc11_10(Ty) : Ty;

// Tclass._System.___hFunc11 injectivity 11
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R) } 
  Tclass._System.___hFunc11_11(Tclass._System.___hFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R))
     == #$R);

function Tclass._System.___hFunc11_11(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hFunc11
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$R: Ty, 
    bx: Box :: 
  { $IsBox(bx, 
      Tclass._System.___hFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R)) } 
  $IsBox(bx, 
      Tclass._System.___hFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, 
        Tclass._System.___hFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R)));

function Handle11([Heap,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box]Box, 
    [Heap,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box]bool, 
    [Heap,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box]Set Box)
   : HandleType;

function Apply11(Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Heap, 
    HandleType, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box)
   : Box;

function Requires11(Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Heap, 
    HandleType, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box)
   : bool;

function Reads11(Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Heap, 
    HandleType, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box)
   : Set Box;

axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    t6: Ty, 
    t7: Ty, 
    t8: Ty, 
    t9: Ty, 
    t10: Ty, 
    t11: Ty, 
    heap: Heap, 
    h: [Heap,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box]Box, 
    r: [Heap,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box]bool, 
    rd: [Heap,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box]Set Box, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box, 
    bx5: Box, 
    bx6: Box, 
    bx7: Box, 
    bx8: Box, 
    bx9: Box, 
    bx10: Box :: 
  { Apply11(t0, 
      t1, 
      t2, 
      t3, 
      t4, 
      t5, 
      t6, 
      t7, 
      t8, 
      t9, 
      t10, 
      t11, 
      heap, 
      Handle11(h, r, rd), 
      bx0, 
      bx1, 
      bx2, 
      bx3, 
      bx4, 
      bx5, 
      bx6, 
      bx7, 
      bx8, 
      bx9, 
      bx10) } 
  Apply11(t0, 
      t1, 
      t2, 
      t3, 
      t4, 
      t5, 
      t6, 
      t7, 
      t8, 
      t9, 
      t10, 
      t11, 
      heap, 
      Handle11(h, r, rd), 
      bx0, 
      bx1, 
      bx2, 
      bx3, 
      bx4, 
      bx5, 
      bx6, 
      bx7, 
      bx8, 
      bx9, 
      bx10)
     == h[heap, bx0, bx1, bx2, bx3, bx4, bx5, bx6, bx7, bx8, bx9, bx10]);

axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    t6: Ty, 
    t7: Ty, 
    t8: Ty, 
    t9: Ty, 
    t10: Ty, 
    t11: Ty, 
    heap: Heap, 
    h: [Heap,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box]Box, 
    r: [Heap,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box]bool, 
    rd: [Heap,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box]Set Box, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box, 
    bx5: Box, 
    bx6: Box, 
    bx7: Box, 
    bx8: Box, 
    bx9: Box, 
    bx10: Box :: 
  { Requires11(t0, 
      t1, 
      t2, 
      t3, 
      t4, 
      t5, 
      t6, 
      t7, 
      t8, 
      t9, 
      t10, 
      t11, 
      heap, 
      Handle11(h, r, rd), 
      bx0, 
      bx1, 
      bx2, 
      bx3, 
      bx4, 
      bx5, 
      bx6, 
      bx7, 
      bx8, 
      bx9, 
      bx10) } 
  r[heap, bx0, bx1, bx2, bx3, bx4, bx5, bx6, bx7, bx8, bx9, bx10]
     ==> Requires11(t0, 
      t1, 
      t2, 
      t3, 
      t4, 
      t5, 
      t6, 
      t7, 
      t8, 
      t9, 
      t10, 
      t11, 
      heap, 
      Handle11(h, r, rd), 
      bx0, 
      bx1, 
      bx2, 
      bx3, 
      bx4, 
      bx5, 
      bx6, 
      bx7, 
      bx8, 
      bx9, 
      bx10));

axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    t6: Ty, 
    t7: Ty, 
    t8: Ty, 
    t9: Ty, 
    t10: Ty, 
    t11: Ty, 
    heap: Heap, 
    h: [Heap,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box]Box, 
    r: [Heap,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box]bool, 
    rd: [Heap,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box]Set Box, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box, 
    bx5: Box, 
    bx6: Box, 
    bx7: Box, 
    bx8: Box, 
    bx9: Box, 
    bx10: Box, 
    bx: Box :: 
  { Reads11(t0, 
      t1, 
      t2, 
      t3, 
      t4, 
      t5, 
      t6, 
      t7, 
      t8, 
      t9, 
      t10, 
      t11, 
      heap, 
      Handle11(h, r, rd), 
      bx0, 
      bx1, 
      bx2, 
      bx3, 
      bx4, 
      bx5, 
      bx6, 
      bx7, 
      bx8, 
      bx9, 
      bx10)[bx] } 
  Reads11(t0, 
      t1, 
      t2, 
      t3, 
      t4, 
      t5, 
      t6, 
      t7, 
      t8, 
      t9, 
      t10, 
      t11, 
      heap, 
      Handle11(h, r, rd), 
      bx0, 
      bx1, 
      bx2, 
      bx3, 
      bx4, 
      bx5, 
      bx6, 
      bx7, 
      bx8, 
      bx9, 
      bx10)[bx]
     == rd[heap, bx0, bx1, bx2, bx3, bx4, bx5, bx6, bx7, bx8, bx9, bx10][bx]);

function {:inline} Requires11#canCall(t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    t6: Ty, 
    t7: Ty, 
    t8: Ty, 
    t9: Ty, 
    t10: Ty, 
    t11: Ty, 
    heap: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box, 
    bx5: Box, 
    bx6: Box, 
    bx7: Box, 
    bx8: Box, 
    bx9: Box, 
    bx10: Box)
   : bool
{
  true
}

function {:inline} Reads11#canCall(t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    t6: Ty, 
    t7: Ty, 
    t8: Ty, 
    t9: Ty, 
    t10: Ty, 
    t11: Ty, 
    heap: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box, 
    bx5: Box, 
    bx6: Box, 
    bx7: Box, 
    bx8: Box, 
    bx9: Box, 
    bx10: Box)
   : bool
{
  true
}

// frame axiom for Reads11
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    t6: Ty, 
    t7: Ty, 
    t8: Ty, 
    t9: Ty, 
    t10: Ty, 
    t11: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box, 
    bx5: Box, 
    bx6: Box, 
    bx7: Box, 
    bx8: Box, 
    bx9: Box, 
    bx10: Box :: 
  { $HeapSucc(h0, h1), Reads11(t0, 
      t1, 
      t2, 
      t3, 
      t4, 
      t5, 
      t6, 
      t7, 
      t8, 
      t9, 
      t10, 
      t11, 
      h1, 
      f, 
      bx0, 
      bx1, 
      bx2, 
      bx3, 
      bx4, 
      bx5, 
      bx6, 
      bx7, 
      bx8, 
      bx9, 
      bx10) } 
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
       && $IsBox(bx5, t5)
       && $IsBox(bx6, t6)
       && $IsBox(bx7, t7)
       && $IsBox(bx8, t8)
       && $IsBox(bx9, t9)
       && $IsBox(bx10, t10)
       && $Is(f, Tclass._System.___hFunc11(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11))
       && (forall<a> o: ref, fld: Field a :: 
        o != null
             && Reads11(t0, 
              t1, 
              t2, 
              t3, 
              t4, 
              t5, 
              t6, 
              t7, 
              t8, 
              t9, 
              t10, 
              t11, 
              h0, 
              f, 
              bx0, 
              bx1, 
              bx2, 
              bx3, 
              bx4, 
              bx5, 
              bx6, 
              bx7, 
              bx8, 
              bx9, 
              bx10)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads11(t0, 
        t1, 
        t2, 
        t3, 
        t4, 
        t5, 
        t6, 
        t7, 
        t8, 
        t9, 
        t10, 
        t11, 
        h0, 
        f, 
        bx0, 
        bx1, 
        bx2, 
        bx3, 
        bx4, 
        bx5, 
        bx6, 
        bx7, 
        bx8, 
        bx9, 
        bx10)
       == Reads11(t0, 
        t1, 
        t2, 
        t3, 
        t4, 
        t5, 
        t6, 
        t7, 
        t8, 
        t9, 
        t10, 
        t11, 
        h1, 
        f, 
        bx0, 
        bx1, 
        bx2, 
        bx3, 
        bx4, 
        bx5, 
        bx6, 
        bx7, 
        bx8, 
        bx9, 
        bx10));

// frame axiom for Reads11
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    t6: Ty, 
    t7: Ty, 
    t8: Ty, 
    t9: Ty, 
    t10: Ty, 
    t11: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box, 
    bx5: Box, 
    bx6: Box, 
    bx7: Box, 
    bx8: Box, 
    bx9: Box, 
    bx10: Box :: 
  { $HeapSucc(h0, h1), Reads11(t0, 
      t1, 
      t2, 
      t3, 
      t4, 
      t5, 
      t6, 
      t7, 
      t8, 
      t9, 
      t10, 
      t11, 
      h1, 
      f, 
      bx0, 
      bx1, 
      bx2, 
      bx3, 
      bx4, 
      bx5, 
      bx6, 
      bx7, 
      bx8, 
      bx9, 
      bx10) } 
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
       && $IsBox(bx5, t5)
       && $IsBox(bx6, t6)
       && $IsBox(bx7, t7)
       && $IsBox(bx8, t8)
       && $IsBox(bx9, t9)
       && $IsBox(bx10, t10)
       && $Is(f, Tclass._System.___hFunc11(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11))
       && (forall<a> o: ref, fld: Field a :: 
        o != null
             && Reads11(t0, 
              t1, 
              t2, 
              t3, 
              t4, 
              t5, 
              t6, 
              t7, 
              t8, 
              t9, 
              t10, 
              t11, 
              h1, 
              f, 
              bx0, 
              bx1, 
              bx2, 
              bx3, 
              bx4, 
              bx5, 
              bx6, 
              bx7, 
              bx8, 
              bx9, 
              bx10)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads11(t0, 
        t1, 
        t2, 
        t3, 
        t4, 
        t5, 
        t6, 
        t7, 
        t8, 
        t9, 
        t10, 
        t11, 
        h0, 
        f, 
        bx0, 
        bx1, 
        bx2, 
        bx3, 
        bx4, 
        bx5, 
        bx6, 
        bx7, 
        bx8, 
        bx9, 
        bx10)
       == Reads11(t0, 
        t1, 
        t2, 
        t3, 
        t4, 
        t5, 
        t6, 
        t7, 
        t8, 
        t9, 
        t10, 
        t11, 
        h1, 
        f, 
        bx0, 
        bx1, 
        bx2, 
        bx3, 
        bx4, 
        bx5, 
        bx6, 
        bx7, 
        bx8, 
        bx9, 
        bx10));

// frame axiom for Requires11
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    t6: Ty, 
    t7: Ty, 
    t8: Ty, 
    t9: Ty, 
    t10: Ty, 
    t11: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box, 
    bx5: Box, 
    bx6: Box, 
    bx7: Box, 
    bx8: Box, 
    bx9: Box, 
    bx10: Box :: 
  { $HeapSucc(h0, h1), Requires11(t0, 
      t1, 
      t2, 
      t3, 
      t4, 
      t5, 
      t6, 
      t7, 
      t8, 
      t9, 
      t10, 
      t11, 
      h1, 
      f, 
      bx0, 
      bx1, 
      bx2, 
      bx3, 
      bx4, 
      bx5, 
      bx6, 
      bx7, 
      bx8, 
      bx9, 
      bx10) } 
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
       && $IsBox(bx5, t5)
       && $IsBox(bx6, t6)
       && $IsBox(bx7, t7)
       && $IsBox(bx8, t8)
       && $IsBox(bx9, t9)
       && $IsBox(bx10, t10)
       && $Is(f, Tclass._System.___hFunc11(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11))
       && (forall<a> o: ref, fld: Field a :: 
        o != null
             && Reads11(t0, 
              t1, 
              t2, 
              t3, 
              t4, 
              t5, 
              t6, 
              t7, 
              t8, 
              t9, 
              t10, 
              t11, 
              h0, 
              f, 
              bx0, 
              bx1, 
              bx2, 
              bx3, 
              bx4, 
              bx5, 
              bx6, 
              bx7, 
              bx8, 
              bx9, 
              bx10)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires11(t0, 
        t1, 
        t2, 
        t3, 
        t4, 
        t5, 
        t6, 
        t7, 
        t8, 
        t9, 
        t10, 
        t11, 
        h0, 
        f, 
        bx0, 
        bx1, 
        bx2, 
        bx3, 
        bx4, 
        bx5, 
        bx6, 
        bx7, 
        bx8, 
        bx9, 
        bx10)
       == Requires11(t0, 
        t1, 
        t2, 
        t3, 
        t4, 
        t5, 
        t6, 
        t7, 
        t8, 
        t9, 
        t10, 
        t11, 
        h1, 
        f, 
        bx0, 
        bx1, 
        bx2, 
        bx3, 
        bx4, 
        bx5, 
        bx6, 
        bx7, 
        bx8, 
        bx9, 
        bx10));

// frame axiom for Requires11
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    t6: Ty, 
    t7: Ty, 
    t8: Ty, 
    t9: Ty, 
    t10: Ty, 
    t11: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box, 
    bx5: Box, 
    bx6: Box, 
    bx7: Box, 
    bx8: Box, 
    bx9: Box, 
    bx10: Box :: 
  { $HeapSucc(h0, h1), Requires11(t0, 
      t1, 
      t2, 
      t3, 
      t4, 
      t5, 
      t6, 
      t7, 
      t8, 
      t9, 
      t10, 
      t11, 
      h1, 
      f, 
      bx0, 
      bx1, 
      bx2, 
      bx3, 
      bx4, 
      bx5, 
      bx6, 
      bx7, 
      bx8, 
      bx9, 
      bx10) } 
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
       && $IsBox(bx5, t5)
       && $IsBox(bx6, t6)
       && $IsBox(bx7, t7)
       && $IsBox(bx8, t8)
       && $IsBox(bx9, t9)
       && $IsBox(bx10, t10)
       && $Is(f, Tclass._System.___hFunc11(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11))
       && (forall<a> o: ref, fld: Field a :: 
        o != null
             && Reads11(t0, 
              t1, 
              t2, 
              t3, 
              t4, 
              t5, 
              t6, 
              t7, 
              t8, 
              t9, 
              t10, 
              t11, 
              h1, 
              f, 
              bx0, 
              bx1, 
              bx2, 
              bx3, 
              bx4, 
              bx5, 
              bx6, 
              bx7, 
              bx8, 
              bx9, 
              bx10)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires11(t0, 
        t1, 
        t2, 
        t3, 
        t4, 
        t5, 
        t6, 
        t7, 
        t8, 
        t9, 
        t10, 
        t11, 
        h0, 
        f, 
        bx0, 
        bx1, 
        bx2, 
        bx3, 
        bx4, 
        bx5, 
        bx6, 
        bx7, 
        bx8, 
        bx9, 
        bx10)
       == Requires11(t0, 
        t1, 
        t2, 
        t3, 
        t4, 
        t5, 
        t6, 
        t7, 
        t8, 
        t9, 
        t10, 
        t11, 
        h1, 
        f, 
        bx0, 
        bx1, 
        bx2, 
        bx3, 
        bx4, 
        bx5, 
        bx6, 
        bx7, 
        bx8, 
        bx9, 
        bx10));

// frame axiom for Apply11
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    t6: Ty, 
    t7: Ty, 
    t8: Ty, 
    t9: Ty, 
    t10: Ty, 
    t11: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box, 
    bx5: Box, 
    bx6: Box, 
    bx7: Box, 
    bx8: Box, 
    bx9: Box, 
    bx10: Box :: 
  { $HeapSucc(h0, h1), Apply11(t0, 
      t1, 
      t2, 
      t3, 
      t4, 
      t5, 
      t6, 
      t7, 
      t8, 
      t9, 
      t10, 
      t11, 
      h1, 
      f, 
      bx0, 
      bx1, 
      bx2, 
      bx3, 
      bx4, 
      bx5, 
      bx6, 
      bx7, 
      bx8, 
      bx9, 
      bx10) } 
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
       && $IsBox(bx5, t5)
       && $IsBox(bx6, t6)
       && $IsBox(bx7, t7)
       && $IsBox(bx8, t8)
       && $IsBox(bx9, t9)
       && $IsBox(bx10, t10)
       && $Is(f, Tclass._System.___hFunc11(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11))
       && (forall<a> o: ref, fld: Field a :: 
        o != null
             && Reads11(t0, 
              t1, 
              t2, 
              t3, 
              t4, 
              t5, 
              t6, 
              t7, 
              t8, 
              t9, 
              t10, 
              t11, 
              h0, 
              f, 
              bx0, 
              bx1, 
              bx2, 
              bx3, 
              bx4, 
              bx5, 
              bx6, 
              bx7, 
              bx8, 
              bx9, 
              bx10)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply11(t0, 
        t1, 
        t2, 
        t3, 
        t4, 
        t5, 
        t6, 
        t7, 
        t8, 
        t9, 
        t10, 
        t11, 
        h0, 
        f, 
        bx0, 
        bx1, 
        bx2, 
        bx3, 
        bx4, 
        bx5, 
        bx6, 
        bx7, 
        bx8, 
        bx9, 
        bx10)
       == Apply11(t0, 
        t1, 
        t2, 
        t3, 
        t4, 
        t5, 
        t6, 
        t7, 
        t8, 
        t9, 
        t10, 
        t11, 
        h1, 
        f, 
        bx0, 
        bx1, 
        bx2, 
        bx3, 
        bx4, 
        bx5, 
        bx6, 
        bx7, 
        bx8, 
        bx9, 
        bx10));

// frame axiom for Apply11
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    t6: Ty, 
    t7: Ty, 
    t8: Ty, 
    t9: Ty, 
    t10: Ty, 
    t11: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box, 
    bx5: Box, 
    bx6: Box, 
    bx7: Box, 
    bx8: Box, 
    bx9: Box, 
    bx10: Box :: 
  { $HeapSucc(h0, h1), Apply11(t0, 
      t1, 
      t2, 
      t3, 
      t4, 
      t5, 
      t6, 
      t7, 
      t8, 
      t9, 
      t10, 
      t11, 
      h1, 
      f, 
      bx0, 
      bx1, 
      bx2, 
      bx3, 
      bx4, 
      bx5, 
      bx6, 
      bx7, 
      bx8, 
      bx9, 
      bx10) } 
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
       && $IsBox(bx5, t5)
       && $IsBox(bx6, t6)
       && $IsBox(bx7, t7)
       && $IsBox(bx8, t8)
       && $IsBox(bx9, t9)
       && $IsBox(bx10, t10)
       && $Is(f, Tclass._System.___hFunc11(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11))
       && (forall<a> o: ref, fld: Field a :: 
        o != null
             && Reads11(t0, 
              t1, 
              t2, 
              t3, 
              t4, 
              t5, 
              t6, 
              t7, 
              t8, 
              t9, 
              t10, 
              t11, 
              h1, 
              f, 
              bx0, 
              bx1, 
              bx2, 
              bx3, 
              bx4, 
              bx5, 
              bx6, 
              bx7, 
              bx8, 
              bx9, 
              bx10)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply11(t0, 
        t1, 
        t2, 
        t3, 
        t4, 
        t5, 
        t6, 
        t7, 
        t8, 
        t9, 
        t10, 
        t11, 
        h0, 
        f, 
        bx0, 
        bx1, 
        bx2, 
        bx3, 
        bx4, 
        bx5, 
        bx6, 
        bx7, 
        bx8, 
        bx9, 
        bx10)
       == Apply11(t0, 
        t1, 
        t2, 
        t3, 
        t4, 
        t5, 
        t6, 
        t7, 
        t8, 
        t9, 
        t10, 
        t11, 
        h1, 
        f, 
        bx0, 
        bx1, 
        bx2, 
        bx3, 
        bx4, 
        bx5, 
        bx6, 
        bx7, 
        bx8, 
        bx9, 
        bx10));

// empty-reads property for Reads11 
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    t6: Ty, 
    t7: Ty, 
    t8: Ty, 
    t9: Ty, 
    t10: Ty, 
    t11: Ty, 
    heap: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box, 
    bx5: Box, 
    bx6: Box, 
    bx7: Box, 
    bx8: Box, 
    bx9: Box, 
    bx10: Box :: 
  { Reads11(t0, 
      t1, 
      t2, 
      t3, 
      t4, 
      t5, 
      t6, 
      t7, 
      t8, 
      t9, 
      t10, 
      t11, 
      $OneHeap, 
      f, 
      bx0, 
      bx1, 
      bx2, 
      bx3, 
      bx4, 
      bx5, 
      bx6, 
      bx7, 
      bx8, 
      bx9, 
      bx10), $IsGoodHeap(heap) } 
    { Reads11(t0, 
      t1, 
      t2, 
      t3, 
      t4, 
      t5, 
      t6, 
      t7, 
      t8, 
      t9, 
      t10, 
      t11, 
      heap, 
      f, 
      bx0, 
      bx1, 
      bx2, 
      bx3, 
      bx4, 
      bx5, 
      bx6, 
      bx7, 
      bx8, 
      bx9, 
      bx10) } 
  $IsGoodHeap(heap)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $IsBox(bx4, t4)
       && $IsBox(bx5, t5)
       && $IsBox(bx6, t6)
       && $IsBox(bx7, t7)
       && $IsBox(bx8, t8)
       && $IsBox(bx9, t9)
       && $IsBox(bx10, t10)
       && $Is(f, Tclass._System.___hFunc11(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11))
     ==> (Set#Equal(Reads11(t0, 
          t1, 
          t2, 
          t3, 
          t4, 
          t5, 
          t6, 
          t7, 
          t8, 
          t9, 
          t10, 
          t11, 
          $OneHeap, 
          f, 
          bx0, 
          bx1, 
          bx2, 
          bx3, 
          bx4, 
          bx5, 
          bx6, 
          bx7, 
          bx8, 
          bx9, 
          bx10), 
        Set#Empty(): Set Box)
       <==> Set#Equal(Reads11(t0, 
          t1, 
          t2, 
          t3, 
          t4, 
          t5, 
          t6, 
          t7, 
          t8, 
          t9, 
          t10, 
          t11, 
          heap, 
          f, 
          bx0, 
          bx1, 
          bx2, 
          bx3, 
          bx4, 
          bx5, 
          bx6, 
          bx7, 
          bx8, 
          bx9, 
          bx10), 
        Set#Empty(): Set Box)));

// empty-reads property for Requires11
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    t6: Ty, 
    t7: Ty, 
    t8: Ty, 
    t9: Ty, 
    t10: Ty, 
    t11: Ty, 
    heap: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box, 
    bx5: Box, 
    bx6: Box, 
    bx7: Box, 
    bx8: Box, 
    bx9: Box, 
    bx10: Box :: 
  { Requires11(t0, 
      t1, 
      t2, 
      t3, 
      t4, 
      t5, 
      t6, 
      t7, 
      t8, 
      t9, 
      t10, 
      t11, 
      $OneHeap, 
      f, 
      bx0, 
      bx1, 
      bx2, 
      bx3, 
      bx4, 
      bx5, 
      bx6, 
      bx7, 
      bx8, 
      bx9, 
      bx10), $IsGoodHeap(heap) } 
    { Requires11(t0, 
      t1, 
      t2, 
      t3, 
      t4, 
      t5, 
      t6, 
      t7, 
      t8, 
      t9, 
      t10, 
      t11, 
      heap, 
      f, 
      bx0, 
      bx1, 
      bx2, 
      bx3, 
      bx4, 
      bx5, 
      bx6, 
      bx7, 
      bx8, 
      bx9, 
      bx10) } 
  $IsGoodHeap(heap)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $IsBox(bx4, t4)
       && $IsBox(bx5, t5)
       && $IsBox(bx6, t6)
       && $IsBox(bx7, t7)
       && $IsBox(bx8, t8)
       && $IsBox(bx9, t9)
       && $IsBox(bx10, t10)
       && $Is(f, Tclass._System.___hFunc11(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11))
       && Set#Equal(Reads11(t0, 
          t1, 
          t2, 
          t3, 
          t4, 
          t5, 
          t6, 
          t7, 
          t8, 
          t9, 
          t10, 
          t11, 
          $OneHeap, 
          f, 
          bx0, 
          bx1, 
          bx2, 
          bx3, 
          bx4, 
          bx5, 
          bx6, 
          bx7, 
          bx8, 
          bx9, 
          bx10), 
        Set#Empty(): Set Box)
     ==> Requires11(t0, 
        t1, 
        t2, 
        t3, 
        t4, 
        t5, 
        t6, 
        t7, 
        t8, 
        t9, 
        t10, 
        t11, 
        $OneHeap, 
        f, 
        bx0, 
        bx1, 
        bx2, 
        bx3, 
        bx4, 
        bx5, 
        bx6, 
        bx7, 
        bx8, 
        bx9, 
        bx10)
       == Requires11(t0, 
        t1, 
        t2, 
        t3, 
        t4, 
        t5, 
        t6, 
        t7, 
        t8, 
        t9, 
        t10, 
        t11, 
        heap, 
        f, 
        bx0, 
        bx1, 
        bx2, 
        bx3, 
        bx4, 
        bx5, 
        bx6, 
        bx7, 
        bx8, 
        bx9, 
        bx10));

axiom (forall f: HandleType, 
    t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    t6: Ty, 
    t7: Ty, 
    t8: Ty, 
    t9: Ty, 
    t10: Ty, 
    t11: Ty :: 
  { $Is(f, Tclass._System.___hFunc11(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11)) } 
  $Is(f, Tclass._System.___hFunc11(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11))
     <==> (forall h: Heap, 
        bx0: Box, 
        bx1: Box, 
        bx2: Box, 
        bx3: Box, 
        bx4: Box, 
        bx5: Box, 
        bx6: Box, 
        bx7: Box, 
        bx8: Box, 
        bx9: Box, 
        bx10: Box :: 
      { Apply11(t0, 
          t1, 
          t2, 
          t3, 
          t4, 
          t5, 
          t6, 
          t7, 
          t8, 
          t9, 
          t10, 
          t11, 
          h, 
          f, 
          bx0, 
          bx1, 
          bx2, 
          bx3, 
          bx4, 
          bx5, 
          bx6, 
          bx7, 
          bx8, 
          bx9, 
          bx10) } 
      $IsGoodHeap(h)
           && 
          $IsBox(bx0, t0)
           && $IsBox(bx1, t1)
           && $IsBox(bx2, t2)
           && $IsBox(bx3, t3)
           && $IsBox(bx4, t4)
           && $IsBox(bx5, t5)
           && $IsBox(bx6, t6)
           && $IsBox(bx7, t7)
           && $IsBox(bx8, t8)
           && $IsBox(bx9, t9)
           && $IsBox(bx10, t10)
           && Requires11(t0, 
            t1, 
            t2, 
            t3, 
            t4, 
            t5, 
            t6, 
            t7, 
            t8, 
            t9, 
            t10, 
            t11, 
            h, 
            f, 
            bx0, 
            bx1, 
            bx2, 
            bx3, 
            bx4, 
            bx5, 
            bx6, 
            bx7, 
            bx8, 
            bx9, 
            bx10)
         ==> $IsBox(Apply11(t0, 
            t1, 
            t2, 
            t3, 
            t4, 
            t5, 
            t6, 
            t7, 
            t8, 
            t9, 
            t10, 
            t11, 
            h, 
            f, 
            bx0, 
            bx1, 
            bx2, 
            bx3, 
            bx4, 
            bx5, 
            bx6, 
            bx7, 
            bx8, 
            bx9, 
            bx10), 
          t11)));

axiom (forall f: HandleType, 
    t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    t6: Ty, 
    t7: Ty, 
    t8: Ty, 
    t9: Ty, 
    t10: Ty, 
    t11: Ty, 
    u0: Ty, 
    u1: Ty, 
    u2: Ty, 
    u3: Ty, 
    u4: Ty, 
    u5: Ty, 
    u6: Ty, 
    u7: Ty, 
    u8: Ty, 
    u9: Ty, 
    u10: Ty, 
    u11: Ty :: 
  { $Is(f, Tclass._System.___hFunc11(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11)), $Is(f, Tclass._System.___hFunc11(u0, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11)) } 
  $Is(f, Tclass._System.___hFunc11(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11))
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
        { $IsBox(bx, u5) } { $IsBox(bx, t5) } 
        $IsBox(bx, u5) ==> $IsBox(bx, t5))
       && (forall bx: Box :: 
        { $IsBox(bx, u6) } { $IsBox(bx, t6) } 
        $IsBox(bx, u6) ==> $IsBox(bx, t6))
       && (forall bx: Box :: 
        { $IsBox(bx, u7) } { $IsBox(bx, t7) } 
        $IsBox(bx, u7) ==> $IsBox(bx, t7))
       && (forall bx: Box :: 
        { $IsBox(bx, u8) } { $IsBox(bx, t8) } 
        $IsBox(bx, u8) ==> $IsBox(bx, t8))
       && (forall bx: Box :: 
        { $IsBox(bx, u9) } { $IsBox(bx, t9) } 
        $IsBox(bx, u9) ==> $IsBox(bx, t9))
       && (forall bx: Box :: 
        { $IsBox(bx, u10) } { $IsBox(bx, t10) } 
        $IsBox(bx, u10) ==> $IsBox(bx, t10))
       && (forall bx: Box :: 
        { $IsBox(bx, t11) } { $IsBox(bx, u11) } 
        $IsBox(bx, t11) ==> $IsBox(bx, u11))
     ==> $Is(f, Tclass._System.___hFunc11(u0, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11)));

axiom (forall f: HandleType, 
    t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    t6: Ty, 
    t7: Ty, 
    t8: Ty, 
    t9: Ty, 
    t10: Ty, 
    t11: Ty, 
    h: Heap :: 
  { $IsAlloc(f, 
      Tclass._System.___hFunc11(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11), 
      h) } 
  $IsGoodHeap(h)
     ==> ($IsAlloc(f, 
        Tclass._System.___hFunc11(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11), 
        h)
       <==> (forall bx0: Box, 
          bx1: Box, 
          bx2: Box, 
          bx3: Box, 
          bx4: Box, 
          bx5: Box, 
          bx6: Box, 
          bx7: Box, 
          bx8: Box, 
          bx9: Box, 
          bx10: Box :: 
        { Apply11(t0, 
            t1, 
            t2, 
            t3, 
            t4, 
            t5, 
            t6, 
            t7, 
            t8, 
            t9, 
            t10, 
            t11, 
            h, 
            f, 
            bx0, 
            bx1, 
            bx2, 
            bx3, 
            bx4, 
            bx5, 
            bx6, 
            bx7, 
            bx8, 
            bx9, 
            bx10) } 
          { Reads11(t0, 
            t1, 
            t2, 
            t3, 
            t4, 
            t5, 
            t6, 
            t7, 
            t8, 
            t9, 
            t10, 
            t11, 
            h, 
            f, 
            bx0, 
            bx1, 
            bx2, 
            bx3, 
            bx4, 
            bx5, 
            bx6, 
            bx7, 
            bx8, 
            bx9, 
            bx10) } 
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
             && 
            $IsBox(bx5, t5)
             && $IsAllocBox(bx5, t5, h)
             && 
            $IsBox(bx6, t6)
             && $IsAllocBox(bx6, t6, h)
             && 
            $IsBox(bx7, t7)
             && $IsAllocBox(bx7, t7, h)
             && 
            $IsBox(bx8, t8)
             && $IsAllocBox(bx8, t8, h)
             && 
            $IsBox(bx9, t9)
             && $IsAllocBox(bx9, t9, h)
             && 
            $IsBox(bx10, t10)
             && $IsAllocBox(bx10, t10, h)
             && Requires11(t0, 
              t1, 
              t2, 
              t3, 
              t4, 
              t5, 
              t6, 
              t7, 
              t8, 
              t9, 
              t10, 
              t11, 
              h, 
              f, 
              bx0, 
              bx1, 
              bx2, 
              bx3, 
              bx4, 
              bx5, 
              bx6, 
              bx7, 
              bx8, 
              bx9, 
              bx10)
           ==> (forall r: ref :: 
            { Reads11(t0, 
                t1, 
                t2, 
                t3, 
                t4, 
                t5, 
                t6, 
                t7, 
                t8, 
                t9, 
                t10, 
                t11, 
                h, 
                f, 
                bx0, 
                bx1, 
                bx2, 
                bx3, 
                bx4, 
                bx5, 
                bx6, 
                bx7, 
                bx8, 
                bx9, 
                bx10)[$Box(r)] } 
            r != null
                 && Reads11(t0, 
                  t1, 
                  t2, 
                  t3, 
                  t4, 
                  t5, 
                  t6, 
                  t7, 
                  t8, 
                  t9, 
                  t10, 
                  t11, 
                  h, 
                  f, 
                  bx0, 
                  bx1, 
                  bx2, 
                  bx3, 
                  bx4, 
                  bx5, 
                  bx6, 
                  bx7, 
                  bx8, 
                  bx9, 
                  bx10)[$Box(r)]
               ==> read(h, r, alloc)))));

axiom (forall f: HandleType, 
    t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    t6: Ty, 
    t7: Ty, 
    t8: Ty, 
    t9: Ty, 
    t10: Ty, 
    t11: Ty, 
    h: Heap :: 
  { $IsAlloc(f, 
      Tclass._System.___hFunc11(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11), 
      h) } 
  $IsGoodHeap(h)
       && $IsAlloc(f, 
        Tclass._System.___hFunc11(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11), 
        h)
     ==> (forall bx0: Box, 
        bx1: Box, 
        bx2: Box, 
        bx3: Box, 
        bx4: Box, 
        bx5: Box, 
        bx6: Box, 
        bx7: Box, 
        bx8: Box, 
        bx9: Box, 
        bx10: Box :: 
      { Apply11(t0, 
          t1, 
          t2, 
          t3, 
          t4, 
          t5, 
          t6, 
          t7, 
          t8, 
          t9, 
          t10, 
          t11, 
          h, 
          f, 
          bx0, 
          bx1, 
          bx2, 
          bx3, 
          bx4, 
          bx5, 
          bx6, 
          bx7, 
          bx8, 
          bx9, 
          bx10) } 
      $IsAllocBox(bx0, t0, h)
           && $IsAllocBox(bx1, t1, h)
           && $IsAllocBox(bx2, t2, h)
           && $IsAllocBox(bx3, t3, h)
           && $IsAllocBox(bx4, t4, h)
           && $IsAllocBox(bx5, t5, h)
           && $IsAllocBox(bx6, t6, h)
           && $IsAllocBox(bx7, t7, h)
           && $IsAllocBox(bx8, t8, h)
           && $IsAllocBox(bx9, t9, h)
           && $IsAllocBox(bx10, t10, h)
           && Requires11(t0, 
            t1, 
            t2, 
            t3, 
            t4, 
            t5, 
            t6, 
            t7, 
            t8, 
            t9, 
            t10, 
            t11, 
            h, 
            f, 
            bx0, 
            bx1, 
            bx2, 
            bx3, 
            bx4, 
            bx5, 
            bx6, 
            bx7, 
            bx8, 
            bx9, 
            bx10)
         ==> $IsAllocBox(Apply11(t0, 
            t1, 
            t2, 
            t3, 
            t4, 
            t5, 
            t6, 
            t7, 
            t8, 
            t9, 
            t10, 
            t11, 
            h, 
            f, 
            bx0, 
            bx1, 
            bx2, 
            bx3, 
            bx4, 
            bx5, 
            bx6, 
            bx7, 
            bx8, 
            bx9, 
            bx10), 
          t11, 
          h)));

function Tclass._System.___hPartialFunc11(Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty) : Ty;

const unique Tagclass._System.___hPartialFunc11: TyTag;

// Tclass._System.___hPartialFunc11 Tag
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hPartialFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R) } 
  Tag(Tclass._System.___hPartialFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R))
       == Tagclass._System.___hPartialFunc11
     && TagFamily(Tclass._System.___hPartialFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R))
       == tytagFamily$_#PartialFunc11);

// Tclass._System.___hPartialFunc11 injectivity 0
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hPartialFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R) } 
  Tclass._System.___hPartialFunc11_0(Tclass._System.___hPartialFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R))
     == #$T0);

function Tclass._System.___hPartialFunc11_0(Ty) : Ty;

// Tclass._System.___hPartialFunc11 injectivity 1
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hPartialFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R) } 
  Tclass._System.___hPartialFunc11_1(Tclass._System.___hPartialFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R))
     == #$T1);

function Tclass._System.___hPartialFunc11_1(Ty) : Ty;

// Tclass._System.___hPartialFunc11 injectivity 2
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hPartialFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R) } 
  Tclass._System.___hPartialFunc11_2(Tclass._System.___hPartialFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R))
     == #$T2);

function Tclass._System.___hPartialFunc11_2(Ty) : Ty;

// Tclass._System.___hPartialFunc11 injectivity 3
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hPartialFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R) } 
  Tclass._System.___hPartialFunc11_3(Tclass._System.___hPartialFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R))
     == #$T3);

function Tclass._System.___hPartialFunc11_3(Ty) : Ty;

// Tclass._System.___hPartialFunc11 injectivity 4
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hPartialFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R) } 
  Tclass._System.___hPartialFunc11_4(Tclass._System.___hPartialFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R))
     == #$T4);

function Tclass._System.___hPartialFunc11_4(Ty) : Ty;

// Tclass._System.___hPartialFunc11 injectivity 5
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hPartialFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R) } 
  Tclass._System.___hPartialFunc11_5(Tclass._System.___hPartialFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R))
     == #$T5);

function Tclass._System.___hPartialFunc11_5(Ty) : Ty;

// Tclass._System.___hPartialFunc11 injectivity 6
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hPartialFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R) } 
  Tclass._System.___hPartialFunc11_6(Tclass._System.___hPartialFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R))
     == #$T6);

function Tclass._System.___hPartialFunc11_6(Ty) : Ty;

// Tclass._System.___hPartialFunc11 injectivity 7
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hPartialFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R) } 
  Tclass._System.___hPartialFunc11_7(Tclass._System.___hPartialFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R))
     == #$T7);

function Tclass._System.___hPartialFunc11_7(Ty) : Ty;

// Tclass._System.___hPartialFunc11 injectivity 8
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hPartialFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R) } 
  Tclass._System.___hPartialFunc11_8(Tclass._System.___hPartialFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R))
     == #$T8);

function Tclass._System.___hPartialFunc11_8(Ty) : Ty;

// Tclass._System.___hPartialFunc11 injectivity 9
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hPartialFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R) } 
  Tclass._System.___hPartialFunc11_9(Tclass._System.___hPartialFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R))
     == #$T9);

function Tclass._System.___hPartialFunc11_9(Ty) : Ty;

// Tclass._System.___hPartialFunc11 injectivity 10
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hPartialFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R) } 
  Tclass._System.___hPartialFunc11_10(Tclass._System.___hPartialFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R))
     == #$T10);

function Tclass._System.___hPartialFunc11_10(Ty) : Ty;

// Tclass._System.___hPartialFunc11 injectivity 11
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hPartialFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R) } 
  Tclass._System.___hPartialFunc11_11(Tclass._System.___hPartialFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R))
     == #$R);

function Tclass._System.___hPartialFunc11_11(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hPartialFunc11
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$R: Ty, 
    bx: Box :: 
  { $IsBox(bx, 
      Tclass._System.___hPartialFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R)) } 
  $IsBox(bx, 
      Tclass._System.___hPartialFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, 
        Tclass._System.___hPartialFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R)));

// _System._#PartialFunc11: subset type $Is
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$R: Ty, 
    f#0: HandleType :: 
  { $Is(f#0, 
      Tclass._System.___hPartialFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R)) } 
  $Is(f#0, 
      Tclass._System.___hPartialFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R))
     <==> $Is(f#0, 
        Tclass._System.___hFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R))
       && (forall x0#0: Box, 
          x1#0: Box, 
          x2#0: Box, 
          x3#0: Box, 
          x4#0: Box, 
          x5#0: Box, 
          x6#0: Box, 
          x7#0: Box, 
          x8#0: Box, 
          x9#0: Box, 
          x10#0: Box :: 
        $IsBox(x0#0, #$T0)
             && $IsBox(x1#0, #$T1)
             && $IsBox(x2#0, #$T2)
             && $IsBox(x3#0, #$T3)
             && $IsBox(x4#0, #$T4)
             && $IsBox(x5#0, #$T5)
             && $IsBox(x6#0, #$T6)
             && $IsBox(x7#0, #$T7)
             && $IsBox(x8#0, #$T8)
             && $IsBox(x9#0, #$T9)
             && $IsBox(x10#0, #$T10)
           ==> Set#Equal(Reads11(#$T0, 
              #$T1, 
              #$T2, 
              #$T3, 
              #$T4, 
              #$T5, 
              #$T6, 
              #$T7, 
              #$T8, 
              #$T9, 
              #$T10, 
              #$R, 
              $OneHeap, 
              f#0, 
              x0#0, 
              x1#0, 
              x2#0, 
              x3#0, 
              x4#0, 
              x5#0, 
              x6#0, 
              x7#0, 
              x8#0, 
              x9#0, 
              x10#0), 
            Set#Empty(): Set Box)));

// _System._#PartialFunc11: subset type $IsAlloc
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$R: Ty, 
    f#0: HandleType, 
    $h: Heap :: 
  { $IsAlloc(f#0, 
      Tclass._System.___hPartialFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R), 
      $h) } 
  $IsAlloc(f#0, 
      Tclass._System.___hPartialFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R), 
      $h)
     <==> $IsAlloc(f#0, 
      Tclass._System.___hFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R), 
      $h));

function Tclass._System.___hTotalFunc11(Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty) : Ty;

const unique Tagclass._System.___hTotalFunc11: TyTag;

// Tclass._System.___hTotalFunc11 Tag
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hTotalFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R) } 
  Tag(Tclass._System.___hTotalFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R))
       == Tagclass._System.___hTotalFunc11
     && TagFamily(Tclass._System.___hTotalFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R))
       == tytagFamily$_#TotalFunc11);

// Tclass._System.___hTotalFunc11 injectivity 0
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hTotalFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R) } 
  Tclass._System.___hTotalFunc11_0(Tclass._System.___hTotalFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R))
     == #$T0);

function Tclass._System.___hTotalFunc11_0(Ty) : Ty;

// Tclass._System.___hTotalFunc11 injectivity 1
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hTotalFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R) } 
  Tclass._System.___hTotalFunc11_1(Tclass._System.___hTotalFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R))
     == #$T1);

function Tclass._System.___hTotalFunc11_1(Ty) : Ty;

// Tclass._System.___hTotalFunc11 injectivity 2
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hTotalFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R) } 
  Tclass._System.___hTotalFunc11_2(Tclass._System.___hTotalFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R))
     == #$T2);

function Tclass._System.___hTotalFunc11_2(Ty) : Ty;

// Tclass._System.___hTotalFunc11 injectivity 3
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hTotalFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R) } 
  Tclass._System.___hTotalFunc11_3(Tclass._System.___hTotalFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R))
     == #$T3);

function Tclass._System.___hTotalFunc11_3(Ty) : Ty;

// Tclass._System.___hTotalFunc11 injectivity 4
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hTotalFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R) } 
  Tclass._System.___hTotalFunc11_4(Tclass._System.___hTotalFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R))
     == #$T4);

function Tclass._System.___hTotalFunc11_4(Ty) : Ty;

// Tclass._System.___hTotalFunc11 injectivity 5
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hTotalFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R) } 
  Tclass._System.___hTotalFunc11_5(Tclass._System.___hTotalFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R))
     == #$T5);

function Tclass._System.___hTotalFunc11_5(Ty) : Ty;

// Tclass._System.___hTotalFunc11 injectivity 6
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hTotalFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R) } 
  Tclass._System.___hTotalFunc11_6(Tclass._System.___hTotalFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R))
     == #$T6);

function Tclass._System.___hTotalFunc11_6(Ty) : Ty;

// Tclass._System.___hTotalFunc11 injectivity 7
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hTotalFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R) } 
  Tclass._System.___hTotalFunc11_7(Tclass._System.___hTotalFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R))
     == #$T7);

function Tclass._System.___hTotalFunc11_7(Ty) : Ty;

// Tclass._System.___hTotalFunc11 injectivity 8
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hTotalFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R) } 
  Tclass._System.___hTotalFunc11_8(Tclass._System.___hTotalFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R))
     == #$T8);

function Tclass._System.___hTotalFunc11_8(Ty) : Ty;

// Tclass._System.___hTotalFunc11 injectivity 9
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hTotalFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R) } 
  Tclass._System.___hTotalFunc11_9(Tclass._System.___hTotalFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R))
     == #$T9);

function Tclass._System.___hTotalFunc11_9(Ty) : Ty;

// Tclass._System.___hTotalFunc11 injectivity 10
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hTotalFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R) } 
  Tclass._System.___hTotalFunc11_10(Tclass._System.___hTotalFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R))
     == #$T10);

function Tclass._System.___hTotalFunc11_10(Ty) : Ty;

// Tclass._System.___hTotalFunc11 injectivity 11
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hTotalFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R) } 
  Tclass._System.___hTotalFunc11_11(Tclass._System.___hTotalFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R))
     == #$R);

function Tclass._System.___hTotalFunc11_11(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hTotalFunc11
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$R: Ty, 
    bx: Box :: 
  { $IsBox(bx, 
      Tclass._System.___hTotalFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R)) } 
  $IsBox(bx, 
      Tclass._System.___hTotalFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, 
        Tclass._System.___hTotalFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R)));

// _System._#TotalFunc11: subset type $Is
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$R: Ty, 
    f#0: HandleType :: 
  { $Is(f#0, 
      Tclass._System.___hTotalFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R)) } 
  $Is(f#0, 
      Tclass._System.___hTotalFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R))
     <==> $Is(f#0, 
        Tclass._System.___hPartialFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R))
       && (forall x0#0: Box, 
          x1#0: Box, 
          x2#0: Box, 
          x3#0: Box, 
          x4#0: Box, 
          x5#0: Box, 
          x6#0: Box, 
          x7#0: Box, 
          x8#0: Box, 
          x9#0: Box, 
          x10#0: Box :: 
        $IsBox(x0#0, #$T0)
             && $IsBox(x1#0, #$T1)
             && $IsBox(x2#0, #$T2)
             && $IsBox(x3#0, #$T3)
             && $IsBox(x4#0, #$T4)
             && $IsBox(x5#0, #$T5)
             && $IsBox(x6#0, #$T6)
             && $IsBox(x7#0, #$T7)
             && $IsBox(x8#0, #$T8)
             && $IsBox(x9#0, #$T9)
             && $IsBox(x10#0, #$T10)
           ==> Requires11(#$T0, 
            #$T1, 
            #$T2, 
            #$T3, 
            #$T4, 
            #$T5, 
            #$T6, 
            #$T7, 
            #$T8, 
            #$T9, 
            #$T10, 
            #$R, 
            $OneHeap, 
            f#0, 
            x0#0, 
            x1#0, 
            x2#0, 
            x3#0, 
            x4#0, 
            x5#0, 
            x6#0, 
            x7#0, 
            x8#0, 
            x9#0, 
            x10#0)));

// _System._#TotalFunc11: subset type $IsAlloc
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$R: Ty, 
    f#0: HandleType, 
    $h: Heap :: 
  { $IsAlloc(f#0, 
      Tclass._System.___hTotalFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R), 
      $h) } 
  $IsAlloc(f#0, 
      Tclass._System.___hTotalFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R), 
      $h)
     <==> $IsAlloc(f#0, 
      Tclass._System.___hPartialFunc11(#$T0, #$T1, #$T2, #$T3, #$T4, #$T5, #$T6, #$T7, #$T8, #$T9, #$T10, #$R), 
      $h));

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

procedure CheckWellformed$$_module.EvenInt(x#0: int);
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.EvenInt(x#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;


    // AddWellformednessCheck for newtype EvenInt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(90,8): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assert LitInt(2) != 0;
        assume Mod(x#0, LitInt(2)) == LitInt(0);
    }
    else
    {
        assume true;
        assert LitInt(Mod(0, LitInt(2))) == LitInt(0);
    }
}



function Tclass._module.EvenInt() : Ty;

const unique Tagclass._module.EvenInt: TyTag;

// Tclass._module.EvenInt Tag
axiom Tag(Tclass._module.EvenInt()) == Tagclass._module.EvenInt
   && TagFamily(Tclass._module.EvenInt()) == tytagFamily$EvenInt;

// Box/unbox axiom for Tclass._module.EvenInt
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.EvenInt()) } 
  $IsBox(bx, Tclass._module.EvenInt())
     ==> $Box($Unbox(bx): int) == bx && $Is($Unbox(bx): int, Tclass._module.EvenInt()));

// _module.EvenInt: newtype $Is
axiom (forall x#0: int :: 
  { $Is(x#0, Tclass._module.EvenInt()) } 
  $Is(x#0, Tclass._module.EvenInt()) <==> Mod(x#0, LitInt(2)) == LitInt(0));

// _module.EvenInt: newtype $IsAlloc
axiom (forall x#0: int, $h: Heap :: 
  { $IsAlloc(x#0, Tclass._module.EvenInt(), $h) } 
  $IsAlloc(x#0, Tclass._module.EvenInt(), $h));

const unique class._module.EvenInt: ClassName;

procedure CheckWellformed$$_module.SmallReal(r#0: real);
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.SmallReal(r#0: real)
{
  var $_Frame: <beta>[ref,Field beta]bool;


    // AddWellformednessCheck for newtype SmallReal
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(91,8): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        if (LitReal(-4e0) <= r#0)
        {
        }

        assume LitReal(-4e0) <= r#0 && r#0 < 3e2;
    }
    else
    {
        assume true;
        assert {:subsumption 0} LitReal(-4e0) <= LitReal(0e0);
        assert {:subsumption 0} 0e0 < 3e2;
    }
}



function Tclass._module.SmallReal() : Ty;

const unique Tagclass._module.SmallReal: TyTag;

// Tclass._module.SmallReal Tag
axiom Tag(Tclass._module.SmallReal()) == Tagclass._module.SmallReal
   && TagFamily(Tclass._module.SmallReal()) == tytagFamily$SmallReal;

// Box/unbox axiom for Tclass._module.SmallReal
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.SmallReal()) } 
  $IsBox(bx, Tclass._module.SmallReal())
     ==> $Box($Unbox(bx): real) == bx
       && $Is($Unbox(bx): real, Tclass._module.SmallReal()));

// _module.SmallReal: newtype $Is
axiom (forall r#0: real :: 
  { $Is(r#0, Tclass._module.SmallReal()) } 
  $Is(r#0, Tclass._module.SmallReal()) <==> LitReal(-4e0) <= r#0 && r#0 < 3e2);

// _module.SmallReal: newtype $IsAlloc
axiom (forall r#0: real, $h: Heap :: 
  { $IsAlloc(r#0, Tclass._module.SmallReal(), $h) } 
  $IsAlloc(r#0, Tclass._module.SmallReal(), $h));

const unique class._module.SmallReal: ClassName;

procedure CheckWellformed$$_module.Handful(x#0: int);
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Handful(x#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;


    // AddWellformednessCheck for newtype Handful
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(92,8): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        if (LitInt(0) <= x#0)
        {
        }

        assume LitInt(0) <= x#0 && x#0 < 80;
    }
    else
    {
        assume true;
        assert {:subsumption 0} LitInt(0) <= LitInt(0);
        assert {:subsumption 0} 0 < 80;
    }
}



function Tclass._module.Handful() : Ty;

const unique Tagclass._module.Handful: TyTag;

// Tclass._module.Handful Tag
axiom Tag(Tclass._module.Handful()) == Tagclass._module.Handful
   && TagFamily(Tclass._module.Handful()) == tytagFamily$Handful;

// Box/unbox axiom for Tclass._module.Handful
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Handful()) } 
  $IsBox(bx, Tclass._module.Handful())
     ==> $Box($Unbox(bx): int) == bx && $Is($Unbox(bx): int, Tclass._module.Handful()));

// _module.Handful: newtype $Is
axiom (forall x#0: int :: 
  { $Is(x#0, Tclass._module.Handful()) } 
  $Is(x#0, Tclass._module.Handful()) <==> LitInt(0) <= x#0 && x#0 < 80);

// _module.Handful: newtype $IsAlloc
axiom (forall x#0: int, $h: Heap :: 
  { $IsAlloc(x#0, Tclass._module.Handful(), $h) } 
  $IsAlloc(x#0, Tclass._module.Handful(), $h));

const unique class._module.Handful: ClassName;

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

procedure CheckWellformed$$_module.__default.M();
  free requires 13 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.M();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.M() returns ($_reverifyPost: bool);
  free requires 13 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.M() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var h#0: bv8;
  var k#0: bv8;

    // AddMethodImpl: M, Impl$$_module.__default.M
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(4,11): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(5,14)
    assume true;
    assume true;
    h#0 := Lit(5bv8);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(5,17)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(6,9)
    assume true;
    assert Lit(128bv8) != 0bv8;
    assume true;
    k#0 := div_bv8(mul_bv8(h#0, 128bv8), 128bv8);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(6,24)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(7,3)
    assume true;
    assert k#0 == Lit(1bv8);
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(8,5)
    assume true;
    assume true;
    h#0 := Lit(3bv8);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(8,8)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(9,5)
    assume true;
    assert Lit(128bv8) != 0bv8;
    assume true;
    k#0 := div_bv8(mul_bv8(h#0, 128bv8), 128bv8);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(9,20)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(10,3)
    assume true;
    assert k#0 == Lit(1bv8);
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(12,5)
    assume true;
    havoc h#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(12,8)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(13,5)
    assume true;
    assert h#0 != 0bv8;
    assume true;
    k#0 := div_bv8(k#0, h#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(13,12)"} true;
}



procedure CheckWellformed$$_module.__default.N0(x#0: bv7, y#0: bv7);
  free requires 14 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.N0(x#0: bv7, y#0: bv7);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.N0(x#0: bv7, y#0: bv7) returns ($_reverifyPost: bool);
  free requires 14 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.N0(x#0: bv7, y#0: bv7) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var z#0: bv7;

    // AddMethodImpl: N0, Impl$$_module.__default.N0
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(16,26): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(17,9)
    assume true;
    assert y#0 != 0bv7;
    assume true;
    z#0 := div_bv7(x#0, y#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(17,16)"} true;
}



procedure CheckWellformed$$_module.__default.N1(x#0: bv7, y#0: bv7);
  free requires 15 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.N1(x#0: bv7, y#0: bv7);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.N1(x#0: bv7, y#0: bv7) returns ($_reverifyPost: bool);
  free requires 15 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.N1(x#0: bv7, y#0: bv7) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var z#0: bv7;

    // AddMethodImpl: N1, Impl$$_module.__default.N1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(20,26): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(21,9)
    assume true;
    assert y#0 != 0bv7;
    assume true;
    z#0 := mod_bv7(x#0, y#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(21,16)"} true;
}



procedure CheckWellformed$$_module.__default.N2(x#0: bv137, y#0: bv137);
  free requires 16 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.N2(x#0: bv137, y#0: bv137);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.N2(x#0: bv137, y#0: bv137) returns ($_reverifyPost: bool);
  free requires 16 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.N2(x#0: bv137, y#0: bv137) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var z#0: bv137;

    // AddMethodImpl: N2, Impl$$_module.__default.N2
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(24,30): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(25,9)
    assume true;
    assert y#0 != 0bv137;
    assume true;
    z#0 := div_bv137(x#0, y#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(25,16)"} true;
}



procedure CheckWellformed$$_module.__default.N3(x#0: Bv0 where 0 == x#0, y#0: Bv0 where 0 == y#0);
  free requires 17 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.N3(x#0: Bv0 where 0 == x#0, y#0: Bv0 where 0 == y#0);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.N3(x#0: Bv0 where 0 == x#0, y#0: Bv0 where 0 == y#0) returns ($_reverifyPost: bool);
  free requires 17 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.N3(x#0: Bv0, y#0: Bv0) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var z#0_0: Bv0 where 0 == z#0_0;
  var z#0: Bv0 where 0 == z#0;

    // AddMethodImpl: N3, Impl$$_module.__default.N3
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(28,26): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(29,3)
    if (*)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(30,11)
        assume true;
        assert y#0 != 0;
        assume true;
        z#0_0 := div_bv0(x#0, y#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(30,18)"} true;
    }
    else
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(32,11)
        assume true;
        assert y#0 != 0;
        assume true;
        z#0 := mod_bv0(x#0, y#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(32,18)"} true;
    }
}



procedure CheckWellformed$$_module.__default.N4(x#0: Bv0 where 0 == x#0, y#0: Bv0 where 0 == y#0)
   returns (z#0: Bv0 where 0 == z#0);
  free requires 18 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.N4(x#0: Bv0 where 0 == x#0, y#0: Bv0 where 0 == y#0)
   returns (z#0: Bv0 where 0 == z#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures z#0 == LitInt(0);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.N4(x#0: Bv0 where 0 == x#0, y#0: Bv0 where 0 == y#0)
   returns (z#0: Bv0 where 0 == z#0, $_reverifyPost: bool);
  free requires 18 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures z#0 == LitInt(0);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.N4(x#0: Bv0, y#0: Bv0) returns (z#0: Bv0, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: N4, Impl$$_module.__default.N4
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(38,0): initial state"} true;
    $_reverifyPost := false;
    // ----- alternative statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(39,3)
    if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(40,20)
        assume true;
        assume true;
        z#0 := add_bv0(x#0, y#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(40,27)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(41,20)
        assume true;
        assume true;
        z#0 := sub_bv0(x#0, y#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(41,27)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(42,20)
        assume true;
        assume true;
        z#0 := mul_bv0(x#0, y#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(42,27)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(43,20)
        assume true;
        assume true;
        z#0 := and_bv0(x#0, y#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(43,27)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(44,20)
        assume true;
        assume true;
        z#0 := or_bv0(x#0, y#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(44,27)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(45,20)
        assume true;
        assume true;
        z#0 := xor_bv0(x#0, y#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(45,27)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(46,20)
        assume true;
        assume true;
        z#0 := not_bv0(x#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(46,24)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(47,20)
        assume true;
        assume true;
        z#0 := sub_bv0(0, x#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(47,24)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(49,18)
        assume true;
        assert !lt_bv0(x#0, y#0);
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(50,18)
        assume true;
        assert le_bv0(x#0, y#0);
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(51,18)
        assume true;
        assert ge_bv0(x#0, y#0);
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(52,18)
        assume true;
        assert !gt_bv0(x#0, y#0);
    }
    else
    {
        assume true;
        assume true;
        assume true;
        assume true;
        assume true;
        assume true;
        assume true;
        assume true;
        assume true;
        assume true;
        assume true;
        assume true;
        assume true;
        assume !Lit(true)
           && !Lit(true)
           && !Lit(true)
           && !Lit(true)
           && !Lit(true)
           && !Lit(true)
           && !Lit(true)
           && !Lit(true)
           && !Lit(true)
           && !Lit(true)
           && !Lit(true)
           && !Lit(true)
           && !Lit(true);
        assert false;
    }
}



procedure CheckWellformed$$_module.__default.P(x#0: Bv0 where 0 == x#0, y#0: Bv0 where 0 == y#0);
  free requires 19 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.P(x#0: Bv0 where 0 == x#0, y#0: Bv0 where 0 == y#0);
  // user-defined preconditions
  requires x#0 != y#0;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.P(x#0: Bv0 where 0 == x#0, y#0: Bv0 where 0 == y#0) returns ($_reverifyPost: bool);
  free requires 19 == $FunctionContextHeight;
  // user-defined preconditions
  requires x#0 != y#0;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.P(x#0: Bv0, y#0: Bv0) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: P, Impl$$_module.__default.P
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(58,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(59,3)
    assume true;
    assert false;
}



procedure CheckWellformed$$_module.__default.Q(x#0: bv10, y#0: bv10);
  free requires 20 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Q(x#0: bv10, y#0: bv10);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.Q(x#0: bv10, y#0: bv10) returns ($_reverifyPost: bool);
  free requires 20 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.Q(x#0: bv10, y#0: bv10) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var z#0_0: bv10;

    // AddMethodImpl: Q, Impl$$_module.__default.Q
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(63,0): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(64,3)
    assume true;
    if (lt_bv10(x#0, 0bv10))
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(66,11)
        assume true;
        assert y#0 != 0bv10;
        assume true;
        z#0_0 := div_bv10(x#0, y#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(66,18)"} true;
    }
    else
    {
    }
}



procedure CheckWellformed$$_module.__default.R(x#0: bv60, y#0: bv60);
  free requires 21 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.R(x#0: bv60, y#0: bv60);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.R(x#0: bv60, y#0: bv60) returns ($_reverifyPost: bool);
  free requires 21 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.R(x#0: bv60, y#0: bv60) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var a0#0: bool;
  var a1#0: bool;
  var $rhs#0: bool;
  var $rhs#1: bool;
  var $rhs#2: bool;
  var $rhs#3: bool;

    // AddMethodImpl: R, Impl$$_module.__default.R
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(71,0): initial state"} true;
    $_reverifyPost := false;
    havoc a0#0, a1#0;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(74,10)
    assume true;
    assume true;
    assume true;
    $rhs#0 := lt_bv60(x#0, y#0);
    assume true;
    $rhs#1 := gt_bv60(y#0, x#0);
    a0#0 := $rhs#0;
    a1#0 := $rhs#1;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(74,24)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(75,3)
    assume true;
    assert a0#0 == a1#0;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(77,10)
    assume true;
    assume true;
    assume true;
    $rhs#2 := le_bv60(x#0, y#0);
    assume true;
    $rhs#3 := ge_bv60(y#0, x#0);
    a0#0 := $rhs#2;
    a1#0 := $rhs#3;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(77,26)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(78,3)
    assume true;
    assert a0#0 == a1#0;
}



// function declaration for _module._default.PQ
function _module.__default.PQ(x#0: int, 
    n#0: int, 
    r#0: real, 
    even#0: int, 
    small#0: real, 
    b67#0: bv67, 
    w#0: bv32, 
    seven#0: bv7, 
    bb#0: bv2, 
    noll#0: Bv0, 
    h#0: int)
   : bool;

function _module.__default.PQ#canCall(x#0: int, 
    n#0: int, 
    r#0: real, 
    even#0: int, 
    small#0: real, 
    b67#0: bv67, 
    w#0: bv32, 
    seven#0: bv7, 
    bb#0: bv2, 
    noll#0: Bv0, 
    h#0: int)
   : bool;

// consequence axiom for _module.__default.PQ
axiom 4 <= $FunctionContextHeight
   ==> (forall x#0: int, 
      n#0: int, 
      r#0: real, 
      even#0: int, 
      small#0: real, 
      b67#0: bv67, 
      w#0: bv32, 
      seven#0: bv7, 
      bb#0: bv2, 
      noll#0: Bv0, 
      h#0: int :: 
    { _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0) } 
    _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
         || (4 != $FunctionContextHeight
           && 
          LitInt(0) <= n#0
           && Mod(even#0, LitInt(2)) == LitInt(0)
           && 
          LitReal(-4e0) <= small#0
           && small#0 < 3e2
           && 0 == noll#0
           && 
          LitInt(0) <= h#0
           && h#0 < 80)
       ==> true);

function _module.__default.PQ#requires(int, int, real, int, real, bv67, bv32, bv7, bv2, Bv0, int) : bool;

// #requires axiom for _module.__default.PQ
axiom (forall x#0: int, 
    n#0: int, 
    r#0: real, 
    even#0: int, 
    small#0: real, 
    b67#0: bv67, 
    w#0: bv32, 
    seven#0: bv7, 
    bb#0: bv2, 
    noll#0: Bv0, 
    h#0: int :: 
  { _module.__default.PQ#requires(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0) } 
  LitInt(0) <= n#0
       && Mod(even#0, LitInt(2)) == LitInt(0)
       && 
      LitReal(-4e0) <= small#0
       && small#0 < 3e2
       && 0 == noll#0
       && 
      LitInt(0) <= h#0
       && h#0 < 80
     ==> _module.__default.PQ#requires(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       == true);

// definition axiom for _module.__default.PQ (revealed)
axiom 4 <= $FunctionContextHeight
   ==> (forall x#0: int, 
      n#0: int, 
      r#0: real, 
      even#0: int, 
      small#0: real, 
      b67#0: bv67, 
      w#0: bv32, 
      seven#0: bv7, 
      bb#0: bv2, 
      noll#0: Bv0, 
      h#0: int :: 
    { _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0) } 
    _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
         || (4 != $FunctionContextHeight
           && 
          LitInt(0) <= n#0
           && Mod(even#0, LitInt(2)) == LitInt(0)
           && 
          LitReal(-4e0) <= small#0
           && small#0 < 3e2
           && 0 == noll#0
           && 
          LitInt(0) <= h#0
           && h#0 < 80)
       ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
         == (
          x#0 == x#0
           && n#0 == n#0
           && r#0 == r#0
           && even#0 == even#0
           && small#0 == small#0
           && b67#0 == b67#0
           && w#0 == w#0
           && seven#0 == seven#0
           && bb#0 == bb#0
           && noll#0 == noll#0
           && h#0 == h#0));

// definition axiom for _module.__default.PQ for all literals (revealed)
axiom 4 <= $FunctionContextHeight
   ==> (forall x#0: int, 
      n#0: int, 
      r#0: real, 
      even#0: int, 
      small#0: real, 
      b67#0: bv67, 
      w#0: bv32, 
      seven#0: bv7, 
      bb#0: bv2, 
      noll#0: Bv0, 
      h#0: int :: 
    {:weight 3} { _module.__default.PQ(LitInt(x#0), 
        LitInt(n#0), 
        LitReal(r#0), 
        LitInt(even#0), 
        LitReal(small#0), 
        Lit(b67#0), 
        Lit(w#0), 
        Lit(seven#0), 
        Lit(bb#0), 
        LitInt(noll#0), 
        LitInt(h#0)) } 
    _module.__default.PQ#canCall(LitInt(x#0), 
          LitInt(n#0), 
          LitReal(r#0), 
          LitInt(even#0), 
          LitReal(small#0), 
          Lit(b67#0), 
          Lit(w#0), 
          Lit(seven#0), 
          Lit(bb#0), 
          LitInt(noll#0), 
          LitInt(h#0))
         || (4 != $FunctionContextHeight
           && 
          LitInt(0) <= n#0
           && Mod(even#0, LitInt(2)) == LitInt(0)
           && 
          LitReal(-4e0) <= small#0
           && small#0 < 3e2
           && 0 == noll#0
           && 
          LitInt(0) <= h#0
           && h#0 < 80)
       ==> _module.__default.PQ(LitInt(x#0), 
          LitInt(n#0), 
          LitReal(r#0), 
          LitInt(even#0), 
          LitReal(small#0), 
          Lit(b67#0), 
          Lit(w#0), 
          Lit(seven#0), 
          Lit(bb#0), 
          LitInt(noll#0), 
          LitInt(h#0))
         == (
          LitInt(x#0) == LitInt(x#0)
           && LitInt(n#0) == LitInt(n#0)
           && LitReal(r#0) == LitReal(r#0)
           && LitInt(even#0) == LitInt(even#0)
           && LitReal(small#0) == LitReal(small#0)
           && Lit(b67#0) == Lit(b67#0)
           && Lit(w#0) == Lit(w#0)
           && Lit(seven#0) == Lit(seven#0)
           && Lit(bb#0) == Lit(bb#0)
           && LitInt(noll#0) == LitInt(noll#0)
           && LitInt(h#0) == LitInt(h#0)));

procedure CheckWellformed$$_module.__default.PQ(x#0: int, 
    n#0: int where LitInt(0) <= n#0, 
    r#0: real, 
    even#0: int where Mod(even#0, LitInt(2)) == LitInt(0), 
    small#0: real where LitReal(-4e0) <= small#0 && small#0 < 3e2, 
    b67#0: bv67, 
    w#0: bv32, 
    seven#0: bv7, 
    bb#0: bv2, 
    noll#0: Bv0 where 0 == noll#0, 
    h#0: int where LitInt(0) <= h#0 && h#0 < 80);
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure CheckWellformed$$_module.__default.Shifts0()
   returns (x#0: int, 
    n#0: int where LitInt(0) <= n#0, 
    r#0: real, 
    even#0: int where Mod(even#0, LitInt(2)) == LitInt(0), 
    small#0: real where LitReal(-4e0) <= small#0 && small#0 < 3e2, 
    b67#0: bv67, 
    w#0: bv32, 
    seven#0: bv7, 
    bb#0: bv2, 
    noll#0: Bv0 where 0 == noll#0, 
    h#0: int where LitInt(0) <= h#0 && h#0 < 80);
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Shifts0()
   returns (x#0: int, 
    n#0: int where LitInt(0) <= n#0, 
    r#0: real, 
    even#0: int where Mod(even#0, LitInt(2)) == LitInt(0), 
    small#0: real where LitReal(-4e0) <= small#0 && small#0 < 3e2, 
    b67#0: bv67, 
    w#0: bv32, 
    seven#0: bv7, 
    bb#0: bv2, 
    noll#0: Bv0 where 0 == noll#0, 
    h#0: int where LitInt(0) <= h#0 && h#0 < 80);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0);
  free ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     && 
    _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     && 
    x#0 == x#0
     && n#0 == n#0
     && r#0 == r#0
     && even#0 == even#0
     && small#0 == small#0
     && b67#0 == b67#0
     && w#0 == w#0
     && seven#0 == seven#0
     && bb#0 == bb#0
     && noll#0 == noll#0
     && h#0 == h#0;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.Shifts0()
   returns (x#0: int, 
    n#0: int where LitInt(0) <= n#0, 
    r#0: real, 
    even#0: int where Mod(even#0, LitInt(2)) == LitInt(0), 
    small#0: real where LitReal(-4e0) <= small#0 && small#0 < 3e2, 
    b67#0: bv67, 
    w#0: bv32, 
    seven#0: bv7, 
    bb#0: bv2, 
    noll#0: Bv0 where 0 == noll#0, 
    h#0: int where LitInt(0) <= h#0 && h#0 < 80, 
    $_reverifyPost: bool);
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0);
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || x#0 == x#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || n#0 == n#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || r#0 == r#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || even#0 == even#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || small#0 == small#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || b67#0 == b67#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || w#0 == w#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || seven#0 == seven#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || bb#0 == bb#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || noll#0 == noll#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || h#0 == h#0;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.Shifts0()
   returns (x#0: int, 
    n#0: int, 
    r#0: real, 
    even#0: int, 
    small#0: real, 
    b67#0: bv67, 
    w#0: bv32, 
    seven#0: bv7, 
    bb#0: bv2, 
    noll#0: Bv0, 
    h#0: int, 
    $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Shifts0, Impl$$_module.__default.Shifts0
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(102,0): initial state"} true;
    $_reverifyPost := false;
    // ----- alternative statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(103,3)
    if (*)
    {
        assume true;
        assume x#0 < 20;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(104,28)
        assume true;
        assert 0 <= x#0;
        assert x#0 <= 67;
        assume true;
        b67#0 := LeftShift_bv67(b67#0, nat_to_bv67(x#0));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(104,38)"} true;
    }
    else if (*)
    {
        assume true;
        assume LitInt(0) <= x#0;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(105,29)
        assume true;
        assert 0 <= x#0;
        assert x#0 <= 67;
        assume true;
        b67#0 := LeftShift_bv67(b67#0, nat_to_bv67(x#0));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(105,39)"} true;
    }
    else if (*)
    {
        if (LitInt(0) <= x#0)
        {
        }

        assume true;
        assume LitInt(0) <= x#0 && x#0 < 67;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(106,29)
        assume true;
        assert 0 <= x#0;
        assert x#0 <= 67;
        assume true;
        b67#0 := LeftShift_bv67(b67#0, nat_to_bv67(x#0));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(106,39)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(107,28)
        assume true;
        assert 0 <= n#0;
        assert n#0 <= 67;
        assume true;
        b67#0 := LeftShift_bv67(b67#0, nat_to_bv67(n#0));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(107,38)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(108,28)
        assume true;
        assert 0 <= h#0;
        assert h#0 <= 67;
        assume true;
        b67#0 := LeftShift_bv67(b67#0, nat_to_bv67(h#0));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(108,38)"} true;
    }
    else
    {
        assume true;
        assume true;
        assume true;
        assume true;
        assume true;
        assume 20 <= x#0
           && x#0 < LitInt(0)
           && !
          (LitInt(0) <= x#0
           && x#0 < 67)
           && !Lit(true)
           && !Lit(true);
        assert false;
    }
}



procedure CheckWellformed$$_module.__default.Shifts1()
   returns (x#0: int, 
    n#0: int where LitInt(0) <= n#0, 
    r#0: real, 
    even#0: int where Mod(even#0, LitInt(2)) == LitInt(0), 
    small#0: real where LitReal(-4e0) <= small#0 && small#0 < 3e2, 
    b67#0: bv67, 
    w#0: bv32, 
    seven#0: bv7, 
    bb#0: bv2, 
    noll#0: Bv0 where 0 == noll#0, 
    h#0: int where LitInt(0) <= h#0 && h#0 < 80);
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Shifts1()
   returns (x#0: int, 
    n#0: int where LitInt(0) <= n#0, 
    r#0: real, 
    even#0: int where Mod(even#0, LitInt(2)) == LitInt(0), 
    small#0: real where LitReal(-4e0) <= small#0 && small#0 < 3e2, 
    b67#0: bv67, 
    w#0: bv32, 
    seven#0: bv7, 
    bb#0: bv2, 
    noll#0: Bv0 where 0 == noll#0, 
    h#0: int where LitInt(0) <= h#0 && h#0 < 80);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0);
  free ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     && 
    _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     && 
    x#0 == x#0
     && n#0 == n#0
     && r#0 == r#0
     && even#0 == even#0
     && small#0 == small#0
     && b67#0 == b67#0
     && w#0 == w#0
     && seven#0 == seven#0
     && bb#0 == bb#0
     && noll#0 == noll#0
     && h#0 == h#0;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.Shifts1()
   returns (x#0: int, 
    n#0: int where LitInt(0) <= n#0, 
    r#0: real, 
    even#0: int where Mod(even#0, LitInt(2)) == LitInt(0), 
    small#0: real where LitReal(-4e0) <= small#0 && small#0 < 3e2, 
    b67#0: bv67, 
    w#0: bv32, 
    seven#0: bv7, 
    bb#0: bv2, 
    noll#0: Bv0 where 0 == noll#0, 
    h#0: int where LitInt(0) <= h#0 && h#0 < 80, 
    $_reverifyPost: bool);
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0);
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || x#0 == x#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || n#0 == n#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || r#0 == r#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || even#0 == even#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || small#0 == small#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || b67#0 == b67#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || w#0 == w#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || seven#0 == seven#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || bb#0 == bb#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || noll#0 == noll#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || h#0 == h#0;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.Shifts1()
   returns (x#0: int, 
    n#0: int, 
    r#0: real, 
    even#0: int, 
    small#0: real, 
    b67#0: bv67, 
    w#0: bv32, 
    seven#0: bv7, 
    bb#0: bv2, 
    noll#0: Bv0, 
    h#0: int, 
    $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var newtype$check#0_0: int;
  var newtype$check#0_1: int;
  var newtype$check#1_0: int;
  var newtype$check#2_0: int;

    // AddMethodImpl: Shifts1, Impl$$_module.__default.Shifts1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(113,0): initial state"} true;
    $_reverifyPost := false;
    // ----- alternative statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(114,3)
    if (*)
    {
        newtype$check#2_0 := LitInt(66);
        assert Mod(newtype$check#2_0, LitInt(2)) == LitInt(0);
        assume true;
        assume even#0 <= LitInt(66);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(115,33)
        assume true;
        assert 0 <= even#0;
        assert even#0 <= 67;
        assume true;
        b67#0 := LeftShift_bv67(b67#0, nat_to_bv67(even#0));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(115,46)"} true;
    }
    else if (*)
    {
        newtype$check#1_0 := LitInt(0);
        assert Mod(newtype$check#1_0, LitInt(2)) == LitInt(0);
        assume true;
        assume LitInt(0) <= even#0;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(116,33)
        assume true;
        assert 0 <= even#0;
        assert even#0 <= 67;
        assume true;
        b67#0 := LeftShift_bv67(b67#0, nat_to_bv67(even#0));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(116,46)"} true;
    }
    else if (*)
    {
        newtype$check#0_0 := LitInt(0);
        assert Mod(newtype$check#0_0, LitInt(2)) == LitInt(0);
        if (LitInt(0) <= even#0)
        {
            newtype$check#0_1 := LitInt(66);
            assert Mod(newtype$check#0_1, LitInt(2)) == LitInt(0);
        }

        assume true;
        assume LitInt(0) <= even#0 && even#0 <= LitInt(66);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(117,34)
        assume true;
        assert 0 <= even#0;
        assert even#0 <= 67;
        assume true;
        b67#0 := LeftShift_bv67(b67#0, nat_to_bv67(even#0));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(117,47)"} true;
    }
    else
    {
        assume true;
        assume true;
        assume true;
        assume LitInt(66) < even#0
           && even#0 < LitInt(0)
           && !
          (LitInt(0) <= even#0
           && even#0 <= LitInt(66));
        assert false;
    }
}



procedure CheckWellformed$$_module.__default.Shifts2()
   returns (x#0: int, 
    n#0: int where LitInt(0) <= n#0, 
    r#0: real, 
    even#0: int where Mod(even#0, LitInt(2)) == LitInt(0), 
    small#0: real where LitReal(-4e0) <= small#0 && small#0 < 3e2, 
    b67#0: bv67, 
    w#0: bv32, 
    seven#0: bv7, 
    bb#0: bv2, 
    noll#0: Bv0 where 0 == noll#0, 
    h#0: int where LitInt(0) <= h#0 && h#0 < 80);
  free requires 7 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Shifts2()
   returns (x#0: int, 
    n#0: int where LitInt(0) <= n#0, 
    r#0: real, 
    even#0: int where Mod(even#0, LitInt(2)) == LitInt(0), 
    small#0: real where LitReal(-4e0) <= small#0 && small#0 < 3e2, 
    b67#0: bv67, 
    w#0: bv32, 
    seven#0: bv7, 
    bb#0: bv2, 
    noll#0: Bv0 where 0 == noll#0, 
    h#0: int where LitInt(0) <= h#0 && h#0 < 80);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0);
  free ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     && 
    _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     && 
    x#0 == x#0
     && n#0 == n#0
     && r#0 == r#0
     && even#0 == even#0
     && small#0 == small#0
     && b67#0 == b67#0
     && w#0 == w#0
     && seven#0 == seven#0
     && bb#0 == bb#0
     && noll#0 == noll#0
     && h#0 == h#0;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.Shifts2()
   returns (x#0: int, 
    n#0: int where LitInt(0) <= n#0, 
    r#0: real, 
    even#0: int where Mod(even#0, LitInt(2)) == LitInt(0), 
    small#0: real where LitReal(-4e0) <= small#0 && small#0 < 3e2, 
    b67#0: bv67, 
    w#0: bv32, 
    seven#0: bv7, 
    bb#0: bv2, 
    noll#0: Bv0 where 0 == noll#0, 
    h#0: int where LitInt(0) <= h#0 && h#0 < 80, 
    $_reverifyPost: bool);
  free requires 7 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0);
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || x#0 == x#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || n#0 == n#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || r#0 == r#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || even#0 == even#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || small#0 == small#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || b67#0 == b67#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || w#0 == w#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || seven#0 == seven#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || bb#0 == bb#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || noll#0 == noll#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || h#0 == h#0;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.Shifts2()
   returns (x#0: int, 
    n#0: int, 
    r#0: real, 
    even#0: int, 
    small#0: real, 
    b67#0: bv67, 
    w#0: bv32, 
    seven#0: bv7, 
    bb#0: bv2, 
    noll#0: Bv0, 
    h#0: int, 
    $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Shifts2, Impl$$_module.__default.Shifts2
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(122,0): initial state"} true;
    $_reverifyPost := false;
    // ----- alternative statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(123,3)
    if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(124,22)
        assume true;
        assert le_bv67(b67#0, 67bv67);
        assume true;
        b67#0 := LeftShift_bv67(b67#0, b67#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(124,34)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(125,22)
        assume true;
        assert le_bv32(w#0, 67bv32);
        assume true;
        b67#0 := LeftShift_bv67(b67#0, (0bv35 ++ w#0): bv67);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(125,32)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(126,22)
        assume true;
        assert Lit(2bv7) != 0bv7;
        assert le_bv7(div_bv7(seven#0, 2bv7), 67bv7);
        assume true;
        b67#0 := LeftShift_bv67(b67#0, (0bv60 ++ div_bv7(seven#0, 2bv7)): bv67);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(126,40)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(127,22)
        assume true;
        assume true;
        b67#0 := LeftShift_bv67(b67#0, (0bv65 ++ bb#0): bv67);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(127,33)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(128,22)
        assume true;
        assume true;
        b67#0 := LeftShift_bv67(b67#0, 0bv67);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(128,35)"} true;
    }
    else
    {
        assume true;
        assume true;
        assume true;
        assume true;
        assume true;
        assume !Lit(true) && !Lit(true) && !Lit(true) && !Lit(true) && !Lit(true);
        assert false;
    }
}



procedure CheckWellformed$$_module.__default.Shifts3()
   returns (x#0: int, 
    n#0: int where LitInt(0) <= n#0, 
    r#0: real, 
    even#0: int where Mod(even#0, LitInt(2)) == LitInt(0), 
    small#0: real where LitReal(-4e0) <= small#0 && small#0 < 3e2, 
    b67#0: bv67, 
    w#0: bv32, 
    seven#0: bv7, 
    bb#0: bv2, 
    noll#0: Bv0 where 0 == noll#0, 
    h#0: int where LitInt(0) <= h#0 && h#0 < 80);
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Shifts3()
   returns (x#0: int, 
    n#0: int where LitInt(0) <= n#0, 
    r#0: real, 
    even#0: int where Mod(even#0, LitInt(2)) == LitInt(0), 
    small#0: real where LitReal(-4e0) <= small#0 && small#0 < 3e2, 
    b67#0: bv67, 
    w#0: bv32, 
    seven#0: bv7, 
    bb#0: bv2, 
    noll#0: Bv0 where 0 == noll#0, 
    h#0: int where LitInt(0) <= h#0 && h#0 < 80);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0);
  free ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     && 
    _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     && 
    x#0 == x#0
     && n#0 == n#0
     && r#0 == r#0
     && even#0 == even#0
     && small#0 == small#0
     && b67#0 == b67#0
     && w#0 == w#0
     && seven#0 == seven#0
     && bb#0 == bb#0
     && noll#0 == noll#0
     && h#0 == h#0;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.Shifts3()
   returns (x#0: int, 
    n#0: int where LitInt(0) <= n#0, 
    r#0: real, 
    even#0: int where Mod(even#0, LitInt(2)) == LitInt(0), 
    small#0: real where LitReal(-4e0) <= small#0 && small#0 < 3e2, 
    b67#0: bv67, 
    w#0: bv32, 
    seven#0: bv7, 
    bb#0: bv2, 
    noll#0: Bv0 where 0 == noll#0, 
    h#0: int where LitInt(0) <= h#0 && h#0 < 80, 
    $_reverifyPost: bool);
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0);
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || x#0 == x#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || n#0 == n#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || r#0 == r#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || even#0 == even#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || small#0 == small#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || b67#0 == b67#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || w#0 == w#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || seven#0 == seven#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || bb#0 == bb#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || noll#0 == noll#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || h#0 == h#0;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.Shifts3()
   returns (x#0: int, 
    n#0: int, 
    r#0: real, 
    even#0: int, 
    small#0: real, 
    b67#0: bv67, 
    w#0: bv32, 
    seven#0: bv7, 
    bb#0: bv2, 
    noll#0: Bv0, 
    h#0: int, 
    $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Shifts3, Impl$$_module.__default.Shifts3
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(133,0): initial state"} true;
    $_reverifyPost := false;
    // ----- alternative statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(134,3)
    if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(135,20)
        assume true;
        assert le_bv67(b67#0, 32bv67);
        assume true;
        w#0 := LeftShift_bv32(w#0, b67#0[32:0]);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(135,30)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(136,20)
        assume true;
        assert le_bv32(w#0, 32bv32);
        assume true;
        w#0 := LeftShift_bv32(w#0, w#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(136,28)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(137,20)
        assume true;
        assert le_bv7(seven#0, 32bv7);
        assume true;
        w#0 := LeftShift_bv32(w#0, (0bv25 ++ seven#0): bv32);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(137,32)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(138,20)
        assume true;
        assume true;
        w#0 := LeftShift_bv32(w#0, (0bv30 ++ bb#0): bv32);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(138,29)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(139,20)
        assume true;
        assume true;
        w#0 := LeftShift_bv32(w#0, 0bv32);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(139,31)"} true;
    }
    else
    {
        assume true;
        assume true;
        assume true;
        assume true;
        assume true;
        assume !Lit(true) && !Lit(true) && !Lit(true) && !Lit(true) && !Lit(true);
        assert false;
    }
}



procedure CheckWellformed$$_module.__default.Shifts4()
   returns (x#0: int, 
    n#0: int where LitInt(0) <= n#0, 
    r#0: real, 
    even#0: int where Mod(even#0, LitInt(2)) == LitInt(0), 
    small#0: real where LitReal(-4e0) <= small#0 && small#0 < 3e2, 
    b67#0: bv67, 
    w#0: bv32, 
    seven#0: bv7, 
    bb#0: bv2, 
    noll#0: Bv0 where 0 == noll#0, 
    h#0: int where LitInt(0) <= h#0 && h#0 < 80);
  free requires 9 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Shifts4()
   returns (x#0: int, 
    n#0: int where LitInt(0) <= n#0, 
    r#0: real, 
    even#0: int where Mod(even#0, LitInt(2)) == LitInt(0), 
    small#0: real where LitReal(-4e0) <= small#0 && small#0 < 3e2, 
    b67#0: bv67, 
    w#0: bv32, 
    seven#0: bv7, 
    bb#0: bv2, 
    noll#0: Bv0 where 0 == noll#0, 
    h#0: int where LitInt(0) <= h#0 && h#0 < 80);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0);
  free ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     && 
    _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     && 
    x#0 == x#0
     && n#0 == n#0
     && r#0 == r#0
     && even#0 == even#0
     && small#0 == small#0
     && b67#0 == b67#0
     && w#0 == w#0
     && seven#0 == seven#0
     && bb#0 == bb#0
     && noll#0 == noll#0
     && h#0 == h#0;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.Shifts4()
   returns (x#0: int, 
    n#0: int where LitInt(0) <= n#0, 
    r#0: real, 
    even#0: int where Mod(even#0, LitInt(2)) == LitInt(0), 
    small#0: real where LitReal(-4e0) <= small#0 && small#0 < 3e2, 
    b67#0: bv67, 
    w#0: bv32, 
    seven#0: bv7, 
    bb#0: bv2, 
    noll#0: Bv0 where 0 == noll#0, 
    h#0: int where LitInt(0) <= h#0 && h#0 < 80, 
    $_reverifyPost: bool);
  free requires 9 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0);
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || x#0 == x#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || n#0 == n#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || r#0 == r#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || even#0 == even#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || small#0 == small#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || b67#0 == b67#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || w#0 == w#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || seven#0 == seven#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || bb#0 == bb#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || noll#0 == noll#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || h#0 == h#0;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.Shifts4()
   returns (x#0: int, 
    n#0: int, 
    r#0: real, 
    even#0: int, 
    small#0: real, 
    b67#0: bv67, 
    w#0: bv32, 
    seven#0: bv7, 
    bb#0: bv2, 
    noll#0: Bv0, 
    h#0: int, 
    $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Shifts4, Impl$$_module.__default.Shifts4
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(144,0): initial state"} true;
    $_reverifyPost := false;
    // ----- alternative statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(145,3)
    if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(146,24)
        assume true;
        assert le_bv67(b67#0, 7bv67);
        assume true;
        seven#0 := LeftShift_bv7(seven#0, b67#0[7:0]);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(146,38)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(147,24)
        assume true;
        assert le_bv32(w#0, 7bv32);
        assume true;
        seven#0 := LeftShift_bv7(seven#0, w#0[7:0]);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(147,36)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(148,24)
        assume true;
        assert le_bv7(seven#0, 7bv7);
        assume true;
        seven#0 := LeftShift_bv7(seven#0, seven#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(148,40)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(149,24)
        assume true;
        assume true;
        seven#0 := LeftShift_bv7(seven#0, (0bv5 ++ bb#0): bv7);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(149,37)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(150,24)
        assume true;
        assume true;
        seven#0 := LeftShift_bv7(seven#0, 0bv7);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(150,39)"} true;
    }
    else
    {
        assume true;
        assume true;
        assume true;
        assume true;
        assume true;
        assume !Lit(true) && !Lit(true) && !Lit(true) && !Lit(true) && !Lit(true);
        assert false;
    }
}



procedure CheckWellformed$$_module.__default.Shifts5()
   returns (x#0: int, 
    n#0: int where LitInt(0) <= n#0, 
    r#0: real, 
    even#0: int where Mod(even#0, LitInt(2)) == LitInt(0), 
    small#0: real where LitReal(-4e0) <= small#0 && small#0 < 3e2, 
    b67#0: bv67, 
    w#0: bv32, 
    seven#0: bv7, 
    bb#0: bv2, 
    noll#0: Bv0 where 0 == noll#0, 
    h#0: int where LitInt(0) <= h#0 && h#0 < 80);
  free requires 10 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Shifts5()
   returns (x#0: int, 
    n#0: int where LitInt(0) <= n#0, 
    r#0: real, 
    even#0: int where Mod(even#0, LitInt(2)) == LitInt(0), 
    small#0: real where LitReal(-4e0) <= small#0 && small#0 < 3e2, 
    b67#0: bv67, 
    w#0: bv32, 
    seven#0: bv7, 
    bb#0: bv2, 
    noll#0: Bv0 where 0 == noll#0, 
    h#0: int where LitInt(0) <= h#0 && h#0 < 80);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0);
  free ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     && 
    _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     && 
    x#0 == x#0
     && n#0 == n#0
     && r#0 == r#0
     && even#0 == even#0
     && small#0 == small#0
     && b67#0 == b67#0
     && w#0 == w#0
     && seven#0 == seven#0
     && bb#0 == bb#0
     && noll#0 == noll#0
     && h#0 == h#0;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.Shifts5()
   returns (x#0: int, 
    n#0: int where LitInt(0) <= n#0, 
    r#0: real, 
    even#0: int where Mod(even#0, LitInt(2)) == LitInt(0), 
    small#0: real where LitReal(-4e0) <= small#0 && small#0 < 3e2, 
    b67#0: bv67, 
    w#0: bv32, 
    seven#0: bv7, 
    bb#0: bv2, 
    noll#0: Bv0 where 0 == noll#0, 
    h#0: int where LitInt(0) <= h#0 && h#0 < 80, 
    $_reverifyPost: bool);
  free requires 10 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0);
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || x#0 == x#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || n#0 == n#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || r#0 == r#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || even#0 == even#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || small#0 == small#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || b67#0 == b67#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || w#0 == w#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || seven#0 == seven#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || bb#0 == bb#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || noll#0 == noll#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || h#0 == h#0;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.Shifts5()
   returns (x#0: int, 
    n#0: int, 
    r#0: real, 
    even#0: int, 
    small#0: real, 
    b67#0: bv67, 
    w#0: bv32, 
    seven#0: bv7, 
    bb#0: bv2, 
    noll#0: Bv0, 
    h#0: int, 
    $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Shifts5, Impl$$_module.__default.Shifts5
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(155,0): initial state"} true;
    $_reverifyPost := false;
    // ----- alternative statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(156,3)
    if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(157,21)
        assume true;
        assert le_bv67(b67#0, 2bv67);
        assume true;
        bb#0 := LeftShift_bv2(bb#0, b67#0[2:0]);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(157,32)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(158,21)
        assume true;
        assert le_bv32(w#0, 2bv32);
        assume true;
        bb#0 := LeftShift_bv2(bb#0, w#0[2:0]);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(158,30)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(159,21)
        assume true;
        assert le_bv7(seven#0, 2bv7);
        assume true;
        bb#0 := LeftShift_bv2(bb#0, seven#0[2:0]);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(159,34)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(160,21)
        assume true;
        assert le_bv2(bb#0, 2bv2);
        assume true;
        bb#0 := LeftShift_bv2(bb#0, bb#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(160,31)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(161,21)
        assume true;
        assume true;
        bb#0 := LeftShift_bv2(bb#0, 0bv2);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(161,33)"} true;
    }
    else
    {
        assume true;
        assume true;
        assume true;
        assume true;
        assume true;
        assume !Lit(true) && !Lit(true) && !Lit(true) && !Lit(true) && !Lit(true);
        assert false;
    }
}



procedure CheckWellformed$$_module.__default.Shifts6()
   returns (x#0: int, 
    n#0: int where LitInt(0) <= n#0, 
    r#0: real, 
    even#0: int where Mod(even#0, LitInt(2)) == LitInt(0), 
    small#0: real where LitReal(-4e0) <= small#0 && small#0 < 3e2, 
    b67#0: bv67, 
    w#0: bv32, 
    seven#0: bv7, 
    bb#0: bv2, 
    noll#0: Bv0 where 0 == noll#0, 
    h#0: int where LitInt(0) <= h#0 && h#0 < 80);
  free requires 11 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Shifts6()
   returns (x#0: int, 
    n#0: int where LitInt(0) <= n#0, 
    r#0: real, 
    even#0: int where Mod(even#0, LitInt(2)) == LitInt(0), 
    small#0: real where LitReal(-4e0) <= small#0 && small#0 < 3e2, 
    b67#0: bv67, 
    w#0: bv32, 
    seven#0: bv7, 
    bb#0: bv2, 
    noll#0: Bv0 where 0 == noll#0, 
    h#0: int where LitInt(0) <= h#0 && h#0 < 80);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0);
  free ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     && 
    _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     && 
    x#0 == x#0
     && n#0 == n#0
     && r#0 == r#0
     && even#0 == even#0
     && small#0 == small#0
     && b67#0 == b67#0
     && w#0 == w#0
     && seven#0 == seven#0
     && bb#0 == bb#0
     && noll#0 == noll#0
     && h#0 == h#0;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.Shifts6()
   returns (x#0: int, 
    n#0: int where LitInt(0) <= n#0, 
    r#0: real, 
    even#0: int where Mod(even#0, LitInt(2)) == LitInt(0), 
    small#0: real where LitReal(-4e0) <= small#0 && small#0 < 3e2, 
    b67#0: bv67, 
    w#0: bv32, 
    seven#0: bv7, 
    bb#0: bv2, 
    noll#0: Bv0 where 0 == noll#0, 
    h#0: int where LitInt(0) <= h#0 && h#0 < 80, 
    $_reverifyPost: bool);
  free requires 11 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0);
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || x#0 == x#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || n#0 == n#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || r#0 == r#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || even#0 == even#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || small#0 == small#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || b67#0 == b67#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || w#0 == w#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || seven#0 == seven#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || bb#0 == bb#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || noll#0 == noll#0;
  ensures _module.__default.PQ#canCall(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
     ==> _module.__default.PQ(x#0, n#0, r#0, even#0, small#0, b67#0, w#0, seven#0, bb#0, noll#0, h#0)
       || h#0 == h#0;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.Shifts6()
   returns (x#0: int, 
    n#0: int, 
    r#0: real, 
    even#0: int, 
    small#0: real, 
    b67#0: bv67, 
    w#0: bv32, 
    seven#0: bv7, 
    bb#0: bv2, 
    noll#0: Bv0, 
    h#0: int, 
    $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Shifts6, Impl$$_module.__default.Shifts6
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(166,0): initial state"} true;
    $_reverifyPost := false;
    // ----- alternative statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(167,3)
    if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(168,23)
        assume true;
        assert le_bv67(b67#0, 0bv67);
        assume true;
        noll#0 := LeftShift_bv0(noll#0, 0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(168,36)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(169,23)
        assume true;
        assert le_bv32(w#0, 0bv32);
        assume true;
        noll#0 := LeftShift_bv0(noll#0, 0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(169,34)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(170,23)
        assume true;
        assert le_bv7(seven#0, 0bv7);
        assume true;
        noll#0 := LeftShift_bv0(noll#0, 0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(170,38)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(171,23)
        assume true;
        assert le_bv2(bb#0, 0bv2);
        assume true;
        noll#0 := LeftShift_bv0(noll#0, 0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(171,35)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(172,23)
        assume true;
        assert le_bv0(noll#0, 0);
        assume true;
        noll#0 := LeftShift_bv0(noll#0, noll#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(172,37)"} true;
    }
    else
    {
        assume true;
        assume true;
        assume true;
        assume true;
        assume true;
        assume !Lit(true) && !Lit(true) && !Lit(true) && !Lit(true) && !Lit(true);
        assert false;
    }
}



procedure CheckWellformed$$_module.__default.TestActualShifting();
  free requires 22 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.TestActualShifting();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.TestActualShifting() returns ($_reverifyPost: bool);
  free requires 22 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.TestActualShifting() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var a#0: bv67;
  var b#0: bv5;

    // AddMethodImpl: TestActualShifting, Impl$$_module.__default.TestActualShifting
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(177,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(178,15)
    assume true;
    assume true;
    a#0 := Lit(3bv67);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(178,18)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(179,3)
    assert {:subsumption 0} 0 <= LitInt(2);
    assert {:subsumption 0} LitInt(2) <= 67;
    assume true;
    assert LeftShift_bv67(a#0, 2bv67) == Lit(12bv67);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(180,3)
    assert {:subsumption 0} 0 <= LitInt(0);
    assert {:subsumption 0} LitInt(0) <= 67;
    assume true;
    assert RightShift_bv67(a#0, 0bv67) == Lit(3bv67);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(181,3)
    assert {:subsumption 0} 0 <= LitInt(1);
    assert {:subsumption 0} LitInt(1) <= 67;
    assume true;
    assert RightShift_bv67(a#0, 1bv67) == Lit(1bv67);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(182,3)
    assert {:subsumption 0} 0 <= LitInt(2);
    assert {:subsumption 0} LitInt(2) <= 67;
    assume true;
    assert RightShift_bv67(a#0, 2bv67) == Lit(0bv67);
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(184,14)
    assume true;
    assume true;
    b#0 := Lit(24bv5);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(184,20)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(185,3)
    assert {:subsumption 0} 0 <= LitInt(1);
    assert {:subsumption 0} LitInt(1) <= 5;
    assume true;
    assert LeftShift_bv5(b#0, 1bv5) == Lit(16bv5);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(186,3)
    assert {:subsumption 0} 0 <= LitInt(0);
    assert {:subsumption 0} LitInt(0) <= 5;
    assume true;
    assert RightShift_bv5(b#0, 0bv5) == Lit(24bv5);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(187,3)
    assert {:subsumption 0} 0 <= LitInt(1);
    assert {:subsumption 0} LitInt(1) <= 5;
    assume true;
    assert RightShift_bv5(b#0, 1bv5) == Lit(12bv5);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(188,3)
    assert {:subsumption 0} 0 <= LitInt(2);
    assert {:subsumption 0} LitInt(2) <= 5;
    assume true;
    assert RightShift_bv5(b#0, 2bv5) == Lit(6bv5);
}



procedure CheckWellformed$$_module.__default.Rotate() returns (x#0: int where LitInt(0) <= x#0, bb#0: bv5);
  free requires 12 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Rotate() returns (x#0: int where LitInt(0) <= x#0, bb#0: bv5);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.Rotate() returns (x#0: int where LitInt(0) <= x#0, bb#0: bv5, $_reverifyPost: bool);
  free requires 12 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.Rotate() returns (x#0: int, bb#0: bv5, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Rotate, Impl$$_module.__default.Rotate
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(191,42): initial state"} true;
    $_reverifyPost := false;
    // ----- alternative statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(192,4)
    if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(193,21)
        assume true;
        assert 0 <= x#0;
        assert x#0 <= 5;
        assume true;
        bb#0 := LeftRotate_bv5(bb#0, nat_to_bv5(x#0));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(193,39)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(194,21)
        assume true;
        assert 0 <= x#0;
        assert x#0 <= 5;
        assume true;
        bb#0 := RightRotate_bv5(bb#0, nat_to_bv5(x#0));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(194,40)"} true;
    }
    else
    {
        assume true;
        assume true;
        assume !Lit(true) && !Lit(true);
        assert false;
    }
}



procedure CheckWellformed$$_module.__default.TestActualRotate();
  free requires 23 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.TestActualRotate();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.TestActualRotate() returns ($_reverifyPost: bool);
  free requires 23 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.TestActualRotate() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var a#0: bv5;

    // AddMethodImpl: TestActualRotate, Impl$$_module.__default.TestActualRotate
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(198,26): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(199,14)
    assume true;
    assume true;
    a#0 := Lit(12bv5);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(199,18)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/BitvectorsMore.dfy(200,2)
    assert {:subsumption 0} 0 <= LitInt(3);
    assert {:subsumption 0} LitInt(3) <= 5;
    assert {:subsumption 0} 0 <= LitInt(3);
    assert {:subsumption 0} LitInt(3) <= 5;
    assume true;
    assert a#0 == RightRotate_bv5(LeftRotate_bv5(a#0, 3bv5), 3bv5);
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

const unique tytagFamily$_#Func11: TyTagFamily;

const unique tytagFamily$_#PartialFunc11: TyTagFamily;

const unique tytagFamily$_#TotalFunc11: TyTagFamily;

const unique tytagFamily$_tuple#2: TyTagFamily;

const unique tytagFamily$_tuple#0: TyTagFamily;

const unique tytagFamily$EvenInt: TyTagFamily;

const unique tytagFamily$SmallReal: TyTagFamily;

const unique tytagFamily$Handful: TyTagFamily;

const unique tytagFamily$_default: TyTagFamily;
