// Dafny 3.0.0.30204
// Command Line Options: -compile:0 -noVerify /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy -print:./Array.bpl

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

procedure CheckWellformed$$_module.A.M(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.A())
         && $IsAlloc(this, Tclass._module.A(), $Heap));
  free requires 29 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.A.M(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.A())
         && $IsAlloc(this, Tclass._module.A(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.A.M(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.A())
         && $IsAlloc(this, Tclass._module.A(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 29 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.A.M(this: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var y#0: ref
     where $Is(y#0, Tclass._System.array(Tclass._module.A?()))
       && $IsAlloc(y#0, Tclass._System.array(Tclass._module.A?()), $Heap);
  var $nw: ref;
  var $rhs#0: ref where $Is($rhs#0, Tclass._module.A?());

    // AddMethodImpl: M, Impl$$_module.A.M
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(5,13): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(6,11)
    assume true;
    assert 0 <= LitInt(100);
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._System.array?(Tclass._module.A?());
    assume !read($Heap, $nw, alloc);
    assume _System.array.Length($nw) == LitInt(100);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    y#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(6,24)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(7,10)
    assert y#0 != null;
    assert 0 <= LitInt(5) && LitInt(5) < _System.array.Length(y#0);
    assume true;
    assert $_Frame[y#0, IndexField(LitInt(5))];
    assume true;
    $rhs#0 := null;
    $Heap := update($Heap, y#0, IndexField(LitInt(5)), $Box($rhs#0));
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(7,16)"} true;
}



procedure CheckWellformed$$_module.A.N0(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.A())
         && $IsAlloc(this, Tclass._module.A(), $Heap));
  free requires 30 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.A.N0(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.A())
         && $IsAlloc(this, Tclass._module.A(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.A.N0(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.A())
         && $IsAlloc(this, Tclass._module.A(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 30 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.A.N0(this: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var a#0: ref
     where $Is(a#0, Tclass._System.array(TInt))
       && $IsAlloc(a#0, Tclass._System.array(TInt), $Heap);
  var $rhs#0_0: int;

    // AddMethodImpl: N0, Impl$$_module.A.N0
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(10,14): initial state"} true;
    $_reverifyPost := false;
    havoc a#0 /* where $Is(a#0, Tclass._System.array(TInt))
       && $IsAlloc(a#0, Tclass._System.array(TInt), $Heap) */;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(12,5)
    assert a#0 != null;
    assume true;
    if (5 < _System.array.Length(a#0))
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(13,12)
        assert a#0 != null;
        assert 0 <= LitInt(5) && LitInt(5) < _System.array.Length(a#0);
        assume true;
        assert $_Frame[a#0, IndexField(LitInt(5))];
        assume true;
        $rhs#0_0 := LitInt(12);
        $Heap := update($Heap, a#0, IndexField(LitInt(5)), $Box($rhs#0_0));
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(13,16)"} true;
    }
    else
    {
    }
}



procedure CheckWellformed$$_module.A.N1(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.A())
         && $IsAlloc(this, Tclass._module.A(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._System.array?(TInt))
         && $IsAlloc(a#0, Tclass._System.array?(TInt), $Heap));
  free requires 34 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.A.N1(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.A())
         && $IsAlloc(this, Tclass._module.A(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._System.array?(TInt))
         && $IsAlloc(a#0, Tclass._System.array?(TInt), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == a#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.A.N1(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.A())
         && $IsAlloc(this, Tclass._module.A(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._System.array?(TInt))
         && $IsAlloc(a#0, Tclass._System.array?(TInt), $Heap))
   returns ($_reverifyPost: bool);
  free requires 34 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == a#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.A.N1(this: ref, a#0: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b#0: int;

    // AddMethodImpl: N1, Impl$$_module.A.N1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == a#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(19,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(20,11)
    assume true;
    assert a#0 != null;
    assume true;
    b#0 := _System.array.Length(a#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(20,21)"} true;
}



procedure CheckWellformed$$_module.A.N2(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.A())
         && $IsAlloc(this, Tclass._module.A(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._System.array(TInt))
         && $IsAlloc(a#0, Tclass._System.array(TInt), $Heap));
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.A.N2(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.A())
         && $IsAlloc(this, Tclass._module.A(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._System.array(TInt))
         && $IsAlloc(a#0, Tclass._System.array(TInt), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == a#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.A.N2(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.A())
         && $IsAlloc(this, Tclass._module.A(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._System.array(TInt))
         && $IsAlloc(a#0, Tclass._System.array(TInt), $Heap))
   returns ($_reverifyPost: bool);
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == a#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.A.N2(this: ref, a#0: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: int;

    // AddMethodImpl: N2, Impl$$_module.A.N2
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == a#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(25,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(26,10)
    assert a#0 != null;
    assert 0 <= LitInt(5) && LitInt(5) < _System.array.Length(a#0);
    assume true;
    assert $_Frame[a#0, IndexField(LitInt(5))];
    assume true;
    $rhs#0 := LitInt(12);
    $Heap := update($Heap, a#0, IndexField(LitInt(5)), $Box($rhs#0));
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(26,14)"} true;
}



procedure CheckWellformed$$_module.A.N3(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.A())
         && $IsAlloc(this, Tclass._module.A(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._System.array(TInt))
         && $IsAlloc(a#0, Tclass._System.array(TInt), $Heap));
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.A.N3(this: ref, a#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var i#0: int;

    // AddMethodImpl: N3, CheckWellformed$$_module.A.N3
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == a#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(29,9): initial state"} true;
    assert a#0 != null;
    assume 5 < _System.array.Length(a#0);
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc)
         ==> $Heap[$o] == old($Heap)[$o] || $o == a#0);
    assume $HeapSucc(old($Heap), $Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(32,12): post-state"} true;
    // Begin Comprehension WF check
    havoc i#0;
    if (true)
    {
        if (LitInt(0) <= i#0)
        {
            assert a#0 != null;
        }

        if (LitInt(0) <= i#0 && i#0 < _System.array.Length(a#0))
        {
            assert a#0 != null;
            assert 0 <= i#0 && i#0 < _System.array.Length(a#0);
            assert a#0 != null;
            assert $IsAlloc(a#0, Tclass._System.array?(TInt), old($Heap));
            assert 0 <= i#0 && i#0 < _System.array.Length(a#0);
            if ($Unbox(read($Heap, a#0, IndexField(i#0))): int
               != $Unbox(read(old($Heap), a#0, IndexField(i#0))): int)
            {
                if (i#0 == LitInt(5))
                {
                    assert a#0 != null;
                    assert 0 <= i#0 && i#0 < _System.array.Length(a#0);
                }
            }
        }
    }

    // End Comprehension WF check
    assume (forall i#1: int :: 
      { $Unbox(read(old($Heap), a#0, IndexField(i#1))): int } 
        { $Unbox(read($Heap, a#0, IndexField(i#1))): int } 
      true
         ==> 
        LitInt(0) <= i#1 && i#1 < _System.array.Length(a#0)
         ==> $Unbox(read($Heap, a#0, IndexField(i#1))): int
             == $Unbox(read(old($Heap), a#0, IndexField(i#1))): int
           || (i#1 == LitInt(5)
             && $Unbox(read($Heap, a#0, IndexField(i#1))): int == LitInt(12)));
}



procedure Call$$_module.A.N3(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.A())
         && $IsAlloc(this, Tclass._module.A(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._System.array(TInt))
         && $IsAlloc(a#0, Tclass._System.array(TInt), $Heap));
  // user-defined preconditions
  requires 5 < _System.array.Length(a#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures (forall i#1: int :: 
    { $Unbox(read(old($Heap), a#0, IndexField(i#1))): int } 
      { $Unbox(read($Heap, a#0, IndexField(i#1))): int } 
    true
       ==> 
      LitInt(0) <= i#1 && i#1 < _System.array.Length(a#0)
       ==> $Unbox(read($Heap, a#0, IndexField(i#1))): int
           == $Unbox(read(old($Heap), a#0, IndexField(i#1))): int
         || (i#1 == LitInt(5)
           && $Unbox(read($Heap, a#0, IndexField(i#1))): int == LitInt(12)));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == a#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.A.N3(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.A())
         && $IsAlloc(this, Tclass._module.A(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._System.array(TInt))
         && $IsAlloc(a#0, Tclass._System.array(TInt), $Heap))
   returns ($_reverifyPost: bool);
  free requires 2 == $FunctionContextHeight;
  // user-defined preconditions
  requires 5 < _System.array.Length(a#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures (forall i#1: int :: 
    { $Unbox(read(old($Heap), a#0, IndexField(i#1))): int } 
      { $Unbox(read($Heap, a#0, IndexField(i#1))): int } 
    true
       ==> 
      LitInt(0) <= i#1 && i#1 < _System.array.Length(a#0)
       ==> $Unbox(read($Heap, a#0, IndexField(i#1))): int
           == $Unbox(read(old($Heap), a#0, IndexField(i#1))): int
         || (i#1 == LitInt(5)
           && $Unbox(read($Heap, a#0, IndexField(i#1))): int == LitInt(12)));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == a#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.A.N3(this: ref, a#0: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: int;

    // AddMethodImpl: N3, Impl$$_module.A.N3
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == a#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(33,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(34,10)
    assert a#0 != null;
    assert 0 <= LitInt(5) && LitInt(5) < _System.array.Length(a#0);
    assume true;
    assert $_Frame[a#0, IndexField(LitInt(5))];
    assume true;
    $rhs#0 := LitInt(12);
    $Heap := update($Heap, a#0, IndexField(LitInt(5)), $Box($rhs#0));
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(34,14)"} true;
}



axiom FDim(_module.A.zz0) == 0
   && FieldOfDecl(class._module.A?, field$zz0) == _module.A.zz0
   && !$IsGhostField(_module.A.zz0);

const _module.A.zz0: Field ref;

// A.zz0: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.A.zz0) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.A?()
     ==> $Is(read($h, $o, _module.A.zz0), Tclass._System.array(Tclass._module.A?())));

// A.zz0: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.A.zz0) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.A?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.A.zz0), Tclass._System.array(Tclass._module.A?()), $h));

axiom FDim(_module.A.zz1) == 0
   && FieldOfDecl(class._module.A?, field$zz1) == _module.A.zz1
   && !$IsGhostField(_module.A.zz1);

const _module.A.zz1: Field ref;

function Tclass._module.B?() : Ty;

const unique Tagclass._module.B?: TyTag;

// Tclass._module.B? Tag
axiom Tag(Tclass._module.B?()) == Tagclass._module.B?
   && TagFamily(Tclass._module.B?()) == tytagFamily$B;

// Box/unbox axiom for Tclass._module.B?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.B?()) } 
  $IsBox(bx, Tclass._module.B?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.B?()));

// A.zz1: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.A.zz1) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.A?()
     ==> $Is(read($h, $o, _module.A.zz1), Tclass._System.array(Tclass._module.B?())));

// A.zz1: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.A.zz1) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.A?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.A.zz1), Tclass._System.array(Tclass._module.B?()), $h));

procedure CheckWellformed$$_module.A.O(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.A())
         && $IsAlloc(this, Tclass._module.A(), $Heap));
  free requires 31 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.A.O(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.A())
         && $IsAlloc(this, Tclass._module.A(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.A.O(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.A())
         && $IsAlloc(this, Tclass._module.A(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 31 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.A.O(this: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var zz2#0: ref
     where $Is(zz2#0, Tclass._System.array(Tclass._module.A?()))
       && $IsAlloc(zz2#0, Tclass._System.array(Tclass._module.A?()), $Heap);
  var $nw: ref;
  var o#0: ref
     where $Is(o#0, Tclass._System.object?())
       && $IsAlloc(o#0, Tclass._System.object?(), $Heap);

    // AddMethodImpl: O, Impl$$_module.A.O
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(39,13): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(40,13)
    assume true;
    assert 0 <= LitInt(25);
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._System.array?(Tclass._module.A?());
    assume !read($Heap, $nw, alloc);
    assume _System.array.Length($nw) == LitInt(25);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    zz2#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(40,25)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(41,5)
    assume true;
    assert zz2#0 != read($Heap, this, _module.A.zz0);
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(42,20)
    assume true;
    assume true;
    o#0 := read($Heap, this, _module.A.zz0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(42,25)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(43,5)
    assume true;
    assert this != o#0;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(45,5)
    assert read($Heap, this, _module.A.zz0) != null;
    if (LitInt(2) <= _System.array.Length(read($Heap, this, _module.A.zz0)))
    {
        assert read($Heap, this, _module.A.zz0) != null;
        assert read($Heap, this, _module.A.zz1) != null;
    }

    assume true;
    if (LitInt(2) <= _System.array.Length(read($Heap, this, _module.A.zz0))
       && _System.array.Length(read($Heap, this, _module.A.zz0))
         == _System.array.Length(read($Heap, this, _module.A.zz1)))
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(46,9)
        assume true;
        assert read($Heap, this, _module.A.zz1) != null;
        assert 0 <= LitInt(1)
           && LitInt(1) < _System.array.Length(read($Heap, this, _module.A.zz1));
        assume true;
        o#0 := $Unbox(read($Heap, read($Heap, this, _module.A.zz1), IndexField(LitInt(1)))): ref;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(46,17)"} true;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(47,7)
        assert read($Heap, this, _module.A.zz0) != null;
        assert {:subsumption 0} 0 <= LitInt(1)
           && LitInt(1) < _System.array.Length(read($Heap, this, _module.A.zz0));
        if ($Unbox(read($Heap, read($Heap, this, _module.A.zz0), IndexField(LitInt(1)))): ref
           == o#0)
        {
        }

        assume true;
        assert {:subsumption 0} $Unbox(read($Heap, read($Heap, this, _module.A.zz0), IndexField(LitInt(1)))): ref
             == o#0
           ==> o#0 == null;
        assume $Unbox(read($Heap, read($Heap, this, _module.A.zz0), IndexField(LitInt(1)))): ref
             == o#0
           ==> o#0 == null;
    }
    else
    {
    }

    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(50,5)
    assert zz2#0 != null;
    assert {:subsumption 0} 0 <= LitInt(20) && LitInt(20) < _System.array.Length(zz2#0);
    assume true;
    assert $Unbox(read($Heap, zz2#0, IndexField(LitInt(20)))): ref == null;
}



axiom FDim(_module.A.x) == 0
   && FieldOfDecl(class._module.A?, field$x) == _module.A.x
   && !$IsGhostField(_module.A.x);

const _module.A.x: Field ref;

// A.x: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.A.x) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.A?()
     ==> $Is(read($h, $o, _module.A.x), Tclass._System.array(TInt)));

// A.x: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.A.x) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.A?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.A.x), Tclass._System.array(TInt), $h));

procedure CheckWellformed$$_module.A.P0(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.A())
         && $IsAlloc(this, Tclass._module.A(), $Heap));
  free requires 35 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.A.P0(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.A())
         && $IsAlloc(this, Tclass._module.A(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.A.P0(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.A())
         && $IsAlloc(this, Tclass._module.A(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 35 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.A.P0(this: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0_0: int;

    // AddMethodImpl: P0, Impl$$_module.A.P0
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(56,2): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(57,5)
    assert read($Heap, this, _module.A.x) != null;
    assume true;
    if (LitInt(100) <= _System.array.Length(read($Heap, this, _module.A.x)))
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(58,12)
        assert read($Heap, this, _module.A.x) != null;
        assert 0 <= LitInt(5)
           && LitInt(5) < _System.array.Length(read($Heap, this, _module.A.x));
        assume true;
        assert $_Frame[read($Heap, this, _module.A.x), IndexField(LitInt(5))];
        assume true;
        $rhs#0_0 := LitInt(12);
        $Heap := update($Heap, read($Heap, this, _module.A.x), IndexField(LitInt(5)), $Box($rhs#0_0));
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(58,16)"} true;
    }
    else
    {
    }
}



procedure CheckWellformed$$_module.A.P1(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.A())
         && $IsAlloc(this, Tclass._module.A(), $Heap));
  free requires 36 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.A.P1(this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: P1, CheckWellformed$$_module.A.P1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this && $f == _module.A.x);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(61,9): initial state"} true;
    assert this != null;
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc)
         ==> $Heap[$o] == old($Heap)[$o] || $o == this);
    assume (forall<alpha> $o: ref, $f: Field alpha :: 
      { read($Heap, $o, $f) } 
      $o != null && read(old($Heap), $o, alloc)
         ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
           || ($o == this && $f == _module.A.x));
    assume $HeapSucc(old($Heap), $Heap);
}



procedure Call$$_module.A.P1(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.A())
         && $IsAlloc(this, Tclass._module.A(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // frame condition: field granularity
  free ensures (forall<alpha> $o: ref, $f: Field alpha :: 
    { read($Heap, $o, $f) } 
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
         || ($o == this && $f == _module.A.x));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.A.P1(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.A())
         && $IsAlloc(this, Tclass._module.A(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 36 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // frame condition: field granularity
  free ensures (forall<alpha> $o: ref, $f: Field alpha :: 
    { read($Heap, $o, $f) } 
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
         || ($o == this && $f == _module.A.x));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.A.P1(this: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0_0: int;

    // AddMethodImpl: P1, Impl$$_module.A.P1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this && $f == _module.A.x);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(63,2): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(64,5)
    assert read($Heap, this, _module.A.x) != null;
    assume true;
    if (LitInt(100) <= _System.array.Length(read($Heap, this, _module.A.x)))
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(65,12)
        assert read($Heap, this, _module.A.x) != null;
        assert 0 <= LitInt(5)
           && LitInt(5) < _System.array.Length(read($Heap, this, _module.A.x));
        assume true;
        assert $_Frame[read($Heap, this, _module.A.x), IndexField(LitInt(5))];
        assume true;
        $rhs#0_0 := LitInt(12);
        $Heap := update($Heap, read($Heap, this, _module.A.x), IndexField(LitInt(5)), $Box($rhs#0_0));
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(65,16)"} true;
    }
    else
    {
    }
}



procedure CheckWellformed$$_module.A.P2(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.A())
         && $IsAlloc(this, Tclass._module.A(), $Heap));
  free requires 37 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.A.P2(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.A())
         && $IsAlloc(this, Tclass._module.A(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == read(old($Heap), this, _module.A.x));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.A.P2(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.A())
         && $IsAlloc(this, Tclass._module.A(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 37 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == read(old($Heap), this, _module.A.x));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.A.P2(this: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0_0: int;

    // AddMethodImpl: P2, Impl$$_module.A.P2
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == read($Heap, this, _module.A.x));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(70,2): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(71,5)
    assert read($Heap, this, _module.A.x) != null;
    assume true;
    if (LitInt(100) <= _System.array.Length(read($Heap, this, _module.A.x)))
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(72,12)
        assert read($Heap, this, _module.A.x) != null;
        assert 0 <= LitInt(5)
           && LitInt(5) < _System.array.Length(read($Heap, this, _module.A.x));
        assume true;
        assert $_Frame[read($Heap, this, _module.A.x), IndexField(LitInt(5))];
        assume true;
        $rhs#0_0 := LitInt(12);
        $Heap := update($Heap, read($Heap, this, _module.A.x), IndexField(LitInt(5)), $Box($rhs#0_0));
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(72,16)"} true;
    }
    else
    {
    }
}



procedure CheckWellformed$$_module.A.Q(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.A())
         && $IsAlloc(this, Tclass._module.A(), $Heap));
  free requires 32 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.A.Q(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.A())
         && $IsAlloc(this, Tclass._module.A(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.A.Q(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.A())
         && $IsAlloc(this, Tclass._module.A(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 32 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.A.Q(this: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var a#0: ref
     where $Is(a#0, Tclass._System.array(TInt))
       && $IsAlloc(a#0, Tclass._System.array(TInt), $Heap);
  var $nw: ref;
  var $obj0: ref;
  var $index0: Field Box;
  var $obj1: ref;
  var $index1: Field Box;
  var $obj2: ref;
  var $index2: Field Box;
  var $obj3: ref;
  var $index3: Field Box;
  var $obj4: ref;
  var $index4: Field Box;
  var $rhs#0: int;
  var $rhs#1: int;
  var $rhs#2: int;
  var $rhs#3: int;
  var $rhs#4: int;
  var i#0: int;
  var i#2: int;

    // AddMethodImpl: Q, Impl$$_module.A.Q
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(76,13): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(77,11)
    assume true;
    assert 0 <= LitInt(5);
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._System.array?(TInt);
    assume !read($Heap, $nw, alloc);
    assume _System.array.Length($nw) == LitInt(5);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    a#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(77,23)"} true;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(78,30)
    assert a#0 != null;
    assert 0 <= LitInt(0) && LitInt(0) < _System.array.Length(a#0);
    assume true;
    $obj0 := a#0;
    $index0 := IndexField(LitInt(0));
    assert $_Frame[$obj0, $index0];
    assert a#0 != null;
    assert 0 <= LitInt(1) && LitInt(1) < _System.array.Length(a#0);
    assume true;
    $obj1 := a#0;
    $index1 := IndexField(LitInt(1));
    assert $_Frame[$obj1, $index1];
    assert a#0 != null;
    assert 0 <= LitInt(2) && LitInt(2) < _System.array.Length(a#0);
    assume true;
    $obj2 := a#0;
    $index2 := IndexField(LitInt(2));
    assert $_Frame[$obj2, $index2];
    assert a#0 != null;
    assert 0 <= LitInt(3) && LitInt(3) < _System.array.Length(a#0);
    assume true;
    $obj3 := a#0;
    $index3 := IndexField(LitInt(3));
    assert $_Frame[$obj3, $index3];
    assert a#0 != null;
    assert 0 <= LitInt(4) && LitInt(4) < _System.array.Length(a#0);
    assume true;
    $obj4 := a#0;
    $index4 := IndexField(LitInt(4));
    assert $_Frame[$obj4, $index4];
    assume true;
    $rhs#0 := LitInt(0);
    assume true;
    $rhs#1 := LitInt(1);
    assume true;
    $rhs#2 := LitInt(2);
    assume true;
    $rhs#3 := LitInt(3);
    assume true;
    $rhs#4 := LitInt(4);
    assert a#0 != a#0 || LitInt(1) != LitInt(0) || $Box($rhs#1) == $Box($rhs#0);
    assert a#0 != a#0 || LitInt(2) != LitInt(0) || $Box($rhs#2) == $Box($rhs#0);
    assert a#0 != a#0 || LitInt(2) != LitInt(1) || $Box($rhs#2) == $Box($rhs#1);
    assert a#0 != a#0 || LitInt(3) != LitInt(0) || $Box($rhs#3) == $Box($rhs#0);
    assert a#0 != a#0 || LitInt(3) != LitInt(1) || $Box($rhs#3) == $Box($rhs#1);
    assert a#0 != a#0 || LitInt(3) != LitInt(2) || $Box($rhs#3) == $Box($rhs#2);
    assert a#0 != a#0 || LitInt(4) != LitInt(0) || $Box($rhs#4) == $Box($rhs#0);
    assert a#0 != a#0 || LitInt(4) != LitInt(1) || $Box($rhs#4) == $Box($rhs#1);
    assert a#0 != a#0 || LitInt(4) != LitInt(2) || $Box($rhs#4) == $Box($rhs#2);
    assert a#0 != a#0 || LitInt(4) != LitInt(3) || $Box($rhs#4) == $Box($rhs#3);
    $Heap := update($Heap, $obj0, $index0, $Box($rhs#0));
    assume $IsGoodHeap($Heap);
    $Heap := update($Heap, $obj1, $index1, $Box($rhs#1));
    assume $IsGoodHeap($Heap);
    $Heap := update($Heap, $obj2, $index2, $Box($rhs#2));
    assume $IsGoodHeap($Heap);
    $Heap := update($Heap, $obj3, $index3, $Box($rhs#3));
    assume $IsGoodHeap($Heap);
    $Heap := update($Heap, $obj4, $index4, $Box($rhs#4));
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(78,41)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(80,5)
    assert a#0 != null;
    assert {:subsumption 0} 0 <= LitInt(1) && LitInt(1) <= _System.array.Length(a#0);
    assume true;
    assert Seq#Equal(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(1))), $Box(LitInt(2))), 
          $Box(LitInt(3))), 
        $Box(LitInt(4))), 
      Seq#Drop(Seq#FromArray($Heap, a#0), LitInt(1)));
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(81,5)
    assert a#0 != null;
    assert {:subsumption 0} 0 <= LitInt(1) && LitInt(1) <= _System.array.Length(a#0);
    assert {:subsumption 0} a#0 != null;
    assert {:subsumption 0} LitInt(1) <= _System.array.Length(a#0)
       && _System.array.Length(a#0) <= _System.array.Length(a#0);
    assume true;
    assert Seq#Equal(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(1))), $Box(LitInt(2))), 
          $Box(LitInt(3))), 
        $Box(LitInt(4))), 
      Seq#Drop(Seq#Take(Seq#FromArray($Heap, a#0), _System.array.Length(a#0)), LitInt(1)));
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(82,5)
    assert a#0 != null;
    assert {:subsumption 0} 0 <= LitInt(1) && LitInt(1) <= _System.array.Length(a#0);
    assert {:subsumption 0} LitInt(1) <= LitInt(2) && LitInt(2) <= _System.array.Length(a#0);
    assume true;
    assert Seq#Equal(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(1))), 
      Seq#Drop(Seq#Take(Seq#FromArray($Heap, a#0), LitInt(2)), LitInt(1)));
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(83,5)
    assert a#0 != null;
    assert {:subsumption 0} 0 <= LitInt(2) && LitInt(2) <= _System.array.Length(a#0);
    assume true;
    assert Seq#Equal(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0))), $Box(LitInt(1))), 
      Seq#Take(Seq#FromArray($Heap, a#0), LitInt(2)));
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(84,5)
    assert a#0 != null;
    assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) <= _System.array.Length(a#0);
    assert {:subsumption 0} LitInt(0) <= LitInt(2) && LitInt(2) <= _System.array.Length(a#0);
    assume true;
    assert Seq#Equal(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0))), $Box(LitInt(1))), 
      Seq#Drop(Seq#Take(Seq#FromArray($Heap, a#0), LitInt(2)), LitInt(0)));
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(85,5)
    // Begin Comprehension WF check
    havoc i#0;
    if (true)
    {
        if (LitInt(0) <= i#0)
        {
            assert {:subsumption 0} a#0 != null;
        }

        if (LitInt(0) <= i#0 && i#0 <= _System.array.Length(a#0))
        {
            assert a#0 != null;
            assert {:subsumption 0} 0 <= i#0 && i#0 <= _System.array.Length(a#0);
            assert {:subsumption 0} i#0 <= i#0 && i#0 <= _System.array.Length(a#0);
        }
    }

    // End Comprehension WF check
    assume true;
    assert (forall i#1: int :: 
      { Seq#Drop(Seq#Take(Seq#FromArray($Heap, a#0), i#1), i#1) } 
      true
         ==> 
        LitInt(0) <= i#1 && i#1 <= _System.array.Length(a#0)
         ==> Seq#Equal(Seq#Empty(): Seq Box, Seq#Drop(Seq#Take(Seq#FromArray($Heap, a#0), i#1), i#1)));
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(86,5)
    assert a#0 != null;
    assume true;
    assert Seq#Equal(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0))), $Box(LitInt(1))), 
            $Box(LitInt(2))), 
          $Box(LitInt(3))), 
        $Box(LitInt(4))), 
      Seq#FromArray($Heap, a#0));
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(87,5)
    // Begin Comprehension WF check
    havoc i#2;
    if (true)
    {
        if (LitInt(0) <= i#2)
        {
            assert {:subsumption 0} a#0 != null;
        }

        if (LitInt(0) <= i#2 && i#2 < _System.array.Length(a#0))
        {
            assert a#0 != null;
            assert {:subsumption 0} 0 <= i#2 && i#2 < _System.array.Length(a#0);
        }
    }

    // End Comprehension WF check
    assume true;
    assert (forall i#3: int :: 
      { $Unbox(read($Heap, a#0, IndexField(i#3))): int } 
      true
         ==> 
        LitInt(0) <= i#3 && i#3 < _System.array.Length(a#0)
         ==> $Unbox(read($Heap, a#0, IndexField(i#3))): int == i#3);
}



procedure CheckWellformed$$_module.A.ArrayToSequenceTests(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.A())
         && $IsAlloc(this, Tclass._module.A(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._System.array(TInt))
         && $IsAlloc(a#0, Tclass._System.array(TInt), $Heap), 
    lo#0: int, 
    hi#0: int);
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.A.ArrayToSequenceTests(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.A())
         && $IsAlloc(this, Tclass._module.A(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._System.array(TInt))
         && $IsAlloc(a#0, Tclass._System.array(TInt), $Heap), 
    lo#0: int, 
    hi#0: int);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.A.ArrayToSequenceTests(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.A())
         && $IsAlloc(this, Tclass._module.A(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._System.array(TInt))
         && $IsAlloc(a#0, Tclass._System.array(TInt), $Heap), 
    lo#0: int, 
    hi#0: int)
   returns ($_reverifyPost: bool);
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.A.ArrayToSequenceTests(this: ref, a#0: ref, lo#0: int, hi#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var s#0_0: Seq Box
     where $Is(s#0_0, TSeq(TInt)) && $IsAlloc(s#0_0, TSeq(TInt), $Heap);
  var s#2_0: Seq Box
     where $Is(s#2_0, TSeq(TInt)) && $IsAlloc(s#2_0, TSeq(TInt), $Heap);
  var s#3_0: Seq Box
     where $Is(s#3_0, TSeq(TInt)) && $IsAlloc(s#3_0, TSeq(TInt), $Heap);

    // AddMethodImpl: ArrayToSequenceTests, Impl$$_module.A.ArrayToSequenceTests
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(91,2): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(92,5)
    assert a#0 != null;
    assume true;
    if (_System.array.Length(a#0) == LitInt(10))
    {
        havoc s#0_0 /* where $Is(s#0_0, TSeq(TInt)) && $IsAlloc(s#0_0, TSeq(TInt), $Heap) */;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(94,9)
        assume true;
        assert a#0 != null;
        assert 0 <= LitInt(2) && LitInt(2) <= _System.array.Length(a#0);
        assert LitInt(2) <= LitInt(5) && LitInt(5) <= _System.array.Length(a#0);
        assume true;
        s#0_0 := Seq#Drop(Seq#Take(Seq#FromArray($Heap, a#0), LitInt(5)), LitInt(2));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(94,18)"} true;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(95,7)
        assume true;
        assert Seq#Length(s#0_0) == LitInt(3);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(96,9)
        assume true;
        assert a#0 != null;
        assert 0 <= LitInt(5) && LitInt(5) <= _System.array.Length(a#0);
        assume true;
        s#0_0 := Seq#Take(Seq#FromArray($Heap, a#0), LitInt(5));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(96,17)"} true;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(97,7)
        assume true;
        assert Seq#Length(s#0_0) == LitInt(5);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(98,9)
        assume true;
        assert a#0 != null;
        assert 0 <= LitInt(2) && LitInt(2) <= _System.array.Length(a#0);
        assume true;
        s#0_0 := Seq#Drop(Seq#FromArray($Heap, a#0), LitInt(2));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(98,17)"} true;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(99,7)
        assume true;
        assert Seq#Length(s#0_0) == LitInt(8);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(100,9)
        assume true;
        assert a#0 != null;
        assume true;
        s#0_0 := Seq#FromArray($Heap, a#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(100,16)"} true;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(101,7)
        assume true;
        assert Seq#Length(s#0_0) == LitInt(10);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(102,9)
        assume true;
        assert a#0 != null;
        assert 0 <= LitInt(10) && LitInt(10) <= _System.array.Length(a#0);
        assert a#0 != null;
        assert 0 <= LitInt(0) && LitInt(0) <= _System.array.Length(a#0);
        assume true;
        s#0_0 := Seq#Append(Seq#Take(Seq#FromArray($Heap, a#0), LitInt(10)), 
          Seq#Drop(Seq#FromArray($Heap, a#0), LitInt(0)));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(102,27)"} true;
    }
    else
    {
        // ----- alternative statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(104,7)
        if (*)
        {
            if (LitInt(0) <= lo#0)
            {
                assert a#0 != null;
            }

            assume true;
            assume LitInt(0) <= lo#0 && lo#0 <= _System.array.Length(a#0);
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(106,17)
            assume true;
            assert a#0 != null;
            assert 0 <= lo#0 && lo#0 <= _System.array.Length(a#0);
            assert a#0 != null;
            assert 0 <= lo#0 && lo#0 <= _System.array.Length(a#0);
            assume true;
            s#3_0 := Seq#Append(Seq#Drop(Seq#FromArray($Heap, a#0), lo#0), 
              Seq#Take(Seq#FromArray($Heap, a#0), lo#0));
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(106,36)"} true;
        }
        else if (*)
        {
            if (LitInt(0) <= lo#0)
            {
                assert a#0 != null;
            }

            if (LitInt(0) <= lo#0 && lo#0 <= _System.array.Length(a#0))
            {
                if (LitInt(0) <= hi#0)
                {
                    assert a#0 != null;
                }
            }

            assume true;
            assume LitInt(0) <= lo#0
               && lo#0 <= _System.array.Length(a#0)
               && 
              LitInt(0) <= hi#0
               && hi#0 <= _System.array.Length(a#0);
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(108,17)
            assume true;
            assert a#0 != null;
            assert 0 <= lo#0 && lo#0 <= _System.array.Length(a#0);
            assert lo#0 <= hi#0 && hi#0 <= _System.array.Length(a#0);
            assume true;
            s#2_0 := Seq#Drop(Seq#Take(Seq#FromArray($Heap, a#0), hi#0), lo#0);
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(108,28)"} true;
        }
        else if (*)
        {
            assume true;
            assume Lit(true);
        }
        else
        {
            assume true;
            assume true;
            assume true;
            assume !
              (LitInt(0) <= lo#0
               && lo#0 <= _System.array.Length(a#0))
               && !
              (
              LitInt(0) <= lo#0
               && lo#0 <= _System.array.Length(a#0)
               && 
              LitInt(0) <= hi#0
               && hi#0 <= _System.array.Length(a#0))
               && !Lit(true);
            assert false;
        }
    }
}



// function declaration for _module.A.BadRangeReads
function _module.A.BadRangeReads(this: ref, a#0: ref, all#0: bool) : bool;

function _module.A.BadRangeReads#canCall(this: ref, a#0: ref, all#0: bool) : bool;

// consequence axiom for _module.A.BadRangeReads
axiom 4 <= $FunctionContextHeight
   ==> (forall this: ref, a#0: ref, all#0: bool :: 
    { _module.A.BadRangeReads(this, a#0, all#0) } 
    _module.A.BadRangeReads#canCall(this, a#0, all#0)
         || (4 != $FunctionContextHeight
           && 
          this != null
           && $Is(this, Tclass._module.A())
           && $Is(a#0, Tclass._System.array(TInt)))
       ==> true);

function _module.A.BadRangeReads#requires(ref, ref, bool) : bool;

// #requires axiom for _module.A.BadRangeReads
axiom (forall $Heap: Heap, this: ref, a#0: ref, all#0: bool :: 
  { _module.A.BadRangeReads#requires(this, a#0, all#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.A())
       && $IsAlloc(this, Tclass._module.A(), $Heap)
       && $Is(a#0, Tclass._System.array(TInt))
     ==> _module.A.BadRangeReads#requires(this, a#0, all#0) == true);

// definition axiom for _module.A.BadRangeReads (revealed)
axiom 4 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref, a#0: ref, all#0: bool :: 
    { _module.A.BadRangeReads(this, a#0, all#0), $IsGoodHeap($Heap) } 
    _module.A.BadRangeReads#canCall(this, a#0, all#0)
         || (4 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.A())
           && $IsAlloc(this, Tclass._module.A(), $Heap)
           && $Is(a#0, Tclass._System.array(TInt)))
       ==> _module.A.BadRangeReads(this, a#0, all#0)
         == (_System.array.Length(a#0) == LitInt(10)
           && (if all#0
             then Seq#Equal(Seq#FromArray($Heap, a#0), Seq#Empty(): Seq Box)
             else Seq#Equal(Seq#Append(Seq#Append(Seq#Drop(Seq#Take(Seq#FromArray($Heap, a#0), LitInt(5)), LitInt(2)), 
                  Seq#Take(Seq#FromArray($Heap, a#0), LitInt(5))), 
                Seq#Drop(Seq#FromArray($Heap, a#0), LitInt(2))), 
              Seq#Empty(): Seq Box))));

// definition axiom for _module.A.BadRangeReads for decreasing-related literals (revealed)
axiom 4 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref, a#0: ref, all#0: bool :: 
    {:weight 3} { _module.A.BadRangeReads(this, Lit(a#0), Lit(all#0)), $IsGoodHeap($Heap) } 
    _module.A.BadRangeReads#canCall(this, Lit(a#0), Lit(all#0))
         || (4 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.A())
           && $IsAlloc(this, Tclass._module.A(), $Heap)
           && $Is(a#0, Tclass._System.array(TInt)))
       ==> _module.A.BadRangeReads(this, Lit(a#0), Lit(all#0))
         == (LitInt(_System.array.Length(Lit(a#0))) == LitInt(10)
           && (if all#0
             then Seq#Equal(Seq#FromArray($Heap, Lit(a#0)), Seq#Empty(): Seq Box)
             else Seq#Equal(Seq#Append(Seq#Append(Seq#Drop(Seq#Take(Seq#FromArray($Heap, Lit(a#0)), LitInt(5)), LitInt(2)), 
                  Seq#Take(Seq#FromArray($Heap, Lit(a#0)), LitInt(5))), 
                Seq#Drop(Seq#FromArray($Heap, Lit(a#0)), LitInt(2))), 
              Seq#Empty(): Seq Box))));

// definition axiom for _module.A.BadRangeReads for all literals (revealed)
axiom 4 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref, a#0: ref, all#0: bool :: 
    {:weight 3} { _module.A.BadRangeReads(Lit(this), Lit(a#0), Lit(all#0)), $IsGoodHeap($Heap) } 
    _module.A.BadRangeReads#canCall(Lit(this), Lit(a#0), Lit(all#0))
         || (4 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.A())
           && $IsAlloc(this, Tclass._module.A(), $Heap)
           && $Is(a#0, Tclass._System.array(TInt)))
       ==> _module.A.BadRangeReads(Lit(this), Lit(a#0), Lit(all#0))
         == (LitInt(_System.array.Length(Lit(a#0))) == LitInt(10)
           && (if all#0
             then Seq#Equal(Seq#FromArray($Heap, Lit(a#0)), Seq#Empty(): Seq Box)
             else Seq#Equal(Seq#Append(Seq#Append(Seq#Drop(Seq#Take(Seq#FromArray($Heap, Lit(a#0)), LitInt(5)), LitInt(2)), 
                  Seq#Take(Seq#FromArray($Heap, Lit(a#0)), LitInt(5))), 
                Seq#Drop(Seq#FromArray($Heap, Lit(a#0)), LitInt(2))), 
              Seq#Empty(): Seq Box))));

procedure CheckWellformed$$_module.A.BadRangeReads(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.A())
         && $IsAlloc(this, Tclass._module.A(), $Heap), 
    a#0: ref where $Is(a#0, Tclass._System.array(TInt)), 
    all#0: bool);
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.A.BadRangeReads(this: ref, a#0: ref, all#0: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;
  var b$reqreads#2: bool;
  var b$reqreads#3: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;
    b$reqreads#3 := true;

    // AddWellformednessCheck for function BadRangeReads
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(114,11): initial state"} true;
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
        assert a#0 != null;
        if (_System.array.Length(a#0) == LitInt(10))
        {
            if (all#0)
            {
                assert a#0 != null;
                b$reqreads#0 := (forall $i: int :: 
                  { $_Frame[a#0, IndexField($i)] } 
                  0 <= $i && $i < _System.array.Length(a#0) ==> $_Frame[a#0, IndexField($i)]);
            }
            else
            {
                assert a#0 != null;
                assert 0 <= LitInt(2) && LitInt(2) <= _System.array.Length(a#0);
                assert LitInt(2) <= LitInt(5) && LitInt(5) <= _System.array.Length(a#0);
                b$reqreads#1 := (forall $i: int :: 
                  { $_Frame[a#0, IndexField($i)] } 
                  LitInt(2) <= $i && $i < LitInt(5) ==> $_Frame[a#0, IndexField($i)]);
                assert a#0 != null;
                assert 0 <= LitInt(5) && LitInt(5) <= _System.array.Length(a#0);
                b$reqreads#2 := (forall $i: int :: 
                  { $_Frame[a#0, IndexField($i)] } 
                  0 <= $i && $i < LitInt(5) ==> $_Frame[a#0, IndexField($i)]);
                assert a#0 != null;
                assert 0 <= LitInt(2) && LitInt(2) <= _System.array.Length(a#0);
                b$reqreads#3 := (forall $i: int :: 
                  { $_Frame[a#0, IndexField($i)] } 
                  LitInt(2) <= $i && $i < _System.array.Length(a#0)
                     ==> $_Frame[a#0, IndexField($i)]);
            }
        }

        assume _module.A.BadRangeReads(this, a#0, all#0)
           == (_System.array.Length(a#0) == LitInt(10)
             && (if all#0
               then Seq#Equal(Seq#FromArray($Heap, a#0), Seq#Empty(): Seq Box)
               else Seq#Equal(Seq#Append(Seq#Append(Seq#Drop(Seq#Take(Seq#FromArray($Heap, a#0), LitInt(5)), LitInt(2)), 
                    Seq#Take(Seq#FromArray($Heap, a#0), LitInt(5))), 
                  Seq#Drop(Seq#FromArray($Heap, a#0), LitInt(2))), 
                Seq#Empty(): Seq Box)));
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.A.BadRangeReads(this, a#0, all#0), TBool);
        assert b$reqreads#0;
        assert b$reqreads#1;
        assert b$reqreads#2;
        assert b$reqreads#3;
    }
}



// function declaration for _module.A.GoodRangeReads
function _module.A.GoodRangeReads($heap: Heap, this: ref, a#0: ref, all#0: bool) : bool;

function _module.A.GoodRangeReads#canCall($heap: Heap, this: ref, a#0: ref, all#0: bool) : bool;

// frame axiom for _module.A.GoodRangeReads
axiom (forall $h0: Heap, $h1: Heap, this: ref, a#0: ref, all#0: bool :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.A.GoodRangeReads($h1, this, a#0, all#0) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.A())
       && (_module.A.GoodRangeReads#canCall($h0, this, a#0, all#0)
         || $Is(a#0, Tclass._System.array(TInt)))
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && $o == a#0 ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.A.GoodRangeReads($h0, this, a#0, all#0)
       == _module.A.GoodRangeReads($h1, this, a#0, all#0));

// consequence axiom for _module.A.GoodRangeReads
axiom 5 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref, a#0: ref, all#0: bool :: 
    { _module.A.GoodRangeReads($Heap, this, a#0, all#0) } 
    _module.A.GoodRangeReads#canCall($Heap, this, a#0, all#0)
         || (5 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.A())
           && $IsAlloc(this, Tclass._module.A(), $Heap)
           && $Is(a#0, Tclass._System.array(TInt)))
       ==> true);

function _module.A.GoodRangeReads#requires(Heap, ref, ref, bool) : bool;

// #requires axiom for _module.A.GoodRangeReads
axiom (forall $Heap: Heap, this: ref, a#0: ref, all#0: bool :: 
  { _module.A.GoodRangeReads#requires($Heap, this, a#0, all#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.A())
       && $IsAlloc(this, Tclass._module.A(), $Heap)
       && $Is(a#0, Tclass._System.array(TInt))
     ==> _module.A.GoodRangeReads#requires($Heap, this, a#0, all#0) == true);

// definition axiom for _module.A.GoodRangeReads (revealed)
axiom 5 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref, a#0: ref, all#0: bool :: 
    { _module.A.GoodRangeReads($Heap, this, a#0, all#0), $IsGoodHeap($Heap) } 
    _module.A.GoodRangeReads#canCall($Heap, this, a#0, all#0)
         || (5 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.A())
           && $IsAlloc(this, Tclass._module.A(), $Heap)
           && $Is(a#0, Tclass._System.array(TInt)))
       ==> _module.A.GoodRangeReads($Heap, this, a#0, all#0)
         == (_System.array.Length(a#0) == LitInt(10)
           && (if all#0
             then Seq#Equal(Seq#FromArray($Heap, a#0), Seq#Empty(): Seq Box)
             else Seq#Equal(Seq#Append(Seq#Append(Seq#Drop(Seq#Take(Seq#FromArray($Heap, a#0), LitInt(5)), LitInt(2)), 
                  Seq#Take(Seq#FromArray($Heap, a#0), LitInt(5))), 
                Seq#Drop(Seq#FromArray($Heap, a#0), LitInt(2))), 
              Seq#Empty(): Seq Box))));

procedure CheckWellformed$$_module.A.GoodRangeReads(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.A())
         && $IsAlloc(this, Tclass._module.A(), $Heap), 
    a#0: ref where $Is(a#0, Tclass._System.array(TInt)), 
    all#0: bool);
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.A.GoodRangeReads(this: ref, a#0: ref, all#0: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;
  var b$reqreads#2: bool;
  var b$reqreads#3: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;
    b$reqreads#3 := true;

    // AddWellformednessCheck for function GoodRangeReads
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(124,11): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == a#0);
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> $o == a#0);
        assert a#0 != null;
        if (_System.array.Length(a#0) == LitInt(10))
        {
            if (all#0)
            {
                assert a#0 != null;
                b$reqreads#0 := (forall $i: int :: 
                  { $_Frame[a#0, IndexField($i)] } 
                  0 <= $i && $i < _System.array.Length(a#0) ==> $_Frame[a#0, IndexField($i)]);
            }
            else
            {
                assert a#0 != null;
                assert 0 <= LitInt(2) && LitInt(2) <= _System.array.Length(a#0);
                assert LitInt(2) <= LitInt(5) && LitInt(5) <= _System.array.Length(a#0);
                b$reqreads#1 := (forall $i: int :: 
                  { $_Frame[a#0, IndexField($i)] } 
                  LitInt(2) <= $i && $i < LitInt(5) ==> $_Frame[a#0, IndexField($i)]);
                assert a#0 != null;
                assert 0 <= LitInt(5) && LitInt(5) <= _System.array.Length(a#0);
                b$reqreads#2 := (forall $i: int :: 
                  { $_Frame[a#0, IndexField($i)] } 
                  0 <= $i && $i < LitInt(5) ==> $_Frame[a#0, IndexField($i)]);
                assert a#0 != null;
                assert 0 <= LitInt(2) && LitInt(2) <= _System.array.Length(a#0);
                b$reqreads#3 := (forall $i: int :: 
                  { $_Frame[a#0, IndexField($i)] } 
                  LitInt(2) <= $i && $i < _System.array.Length(a#0)
                     ==> $_Frame[a#0, IndexField($i)]);
            }
        }

        assume _module.A.GoodRangeReads($Heap, this, a#0, all#0)
           == (_System.array.Length(a#0) == LitInt(10)
             && (if all#0
               then Seq#Equal(Seq#FromArray($Heap, a#0), Seq#Empty(): Seq Box)
               else Seq#Equal(Seq#Append(Seq#Append(Seq#Drop(Seq#Take(Seq#FromArray($Heap, a#0), LitInt(5)), LitInt(2)), 
                    Seq#Take(Seq#FromArray($Heap, a#0), LitInt(5))), 
                  Seq#Drop(Seq#FromArray($Heap, a#0), LitInt(2))), 
                Seq#Empty(): Seq Box)));
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.A.GoodRangeReads($Heap, this, a#0, all#0), TBool);
        assert b$reqreads#0;
        assert b$reqreads#1;
        assert b$reqreads#2;
        assert b$reqreads#3;
    }
}



// function declaration for _module.A.AnotherGoodRangeReads
function _module.A.AnotherGoodRangeReads(this: ref, a#0: ref, j#0: int) : bool;

function _module.A.AnotherGoodRangeReads#canCall(this: ref, a#0: ref, j#0: int) : bool;

// consequence axiom for _module.A.AnotherGoodRangeReads
axiom 6 <= $FunctionContextHeight
   ==> (forall this: ref, a#0: ref, j#0: int :: 
    { _module.A.AnotherGoodRangeReads(this, a#0, j#0) } 
    _module.A.AnotherGoodRangeReads#canCall(this, a#0, j#0)
         || (6 != $FunctionContextHeight
           && 
          this != null
           && $Is(this, Tclass._module.A())
           && $Is(a#0, Tclass._System.array(TInt)))
       ==> true);

function _module.A.AnotherGoodRangeReads#requires(ref, ref, int) : bool;

// #requires axiom for _module.A.AnotherGoodRangeReads
axiom (forall $Heap: Heap, this: ref, a#0: ref, j#0: int :: 
  { _module.A.AnotherGoodRangeReads#requires(this, a#0, j#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.A())
       && $IsAlloc(this, Tclass._module.A(), $Heap)
       && $Is(a#0, Tclass._System.array(TInt))
     ==> _module.A.AnotherGoodRangeReads#requires(this, a#0, j#0) == true);

// definition axiom for _module.A.AnotherGoodRangeReads (revealed)
axiom 6 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref, a#0: ref, j#0: int :: 
    { _module.A.AnotherGoodRangeReads(this, a#0, j#0), $IsGoodHeap($Heap) } 
    _module.A.AnotherGoodRangeReads#canCall(this, a#0, j#0)
         || (6 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.A())
           && $IsAlloc(this, Tclass._module.A(), $Heap)
           && $Is(a#0, Tclass._System.array(TInt)))
       ==> _module.A.AnotherGoodRangeReads(this, a#0, j#0)
         == (
          LitInt(0) <= j#0
           && j#0 <= _System.array.Length(a#0)
           && Seq#Equal(Seq#Drop(Seq#Take(Seq#FromArray($Heap, a#0), j#0), j#0), Seq#Empty(): Seq Box)));

// definition axiom for _module.A.AnotherGoodRangeReads for decreasing-related literals (revealed)
axiom 6 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref, a#0: ref, j#0: int :: 
    {:weight 3} { _module.A.AnotherGoodRangeReads(this, Lit(a#0), LitInt(j#0)), $IsGoodHeap($Heap) } 
    _module.A.AnotherGoodRangeReads#canCall(this, Lit(a#0), LitInt(j#0))
         || (6 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.A())
           && $IsAlloc(this, Tclass._module.A(), $Heap)
           && $Is(a#0, Tclass._System.array(TInt)))
       ==> _module.A.AnotherGoodRangeReads(this, Lit(a#0), LitInt(j#0))
         == (
          LitInt(0) <= LitInt(j#0)
           && LitInt(j#0) <= LitInt(_System.array.Length(Lit(a#0)))
           && Seq#Equal(Seq#Drop(Seq#Take(Seq#FromArray($Heap, Lit(a#0)), LitInt(j#0)), LitInt(j#0)), 
            Seq#Empty(): Seq Box)));

// definition axiom for _module.A.AnotherGoodRangeReads for all literals (revealed)
axiom 6 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref, a#0: ref, j#0: int :: 
    {:weight 3} { _module.A.AnotherGoodRangeReads(Lit(this), Lit(a#0), LitInt(j#0)), $IsGoodHeap($Heap) } 
    _module.A.AnotherGoodRangeReads#canCall(Lit(this), Lit(a#0), LitInt(j#0))
         || (6 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.A())
           && $IsAlloc(this, Tclass._module.A(), $Heap)
           && $Is(a#0, Tclass._System.array(TInt)))
       ==> _module.A.AnotherGoodRangeReads(Lit(this), Lit(a#0), LitInt(j#0))
         == (
          LitInt(0) <= LitInt(j#0)
           && LitInt(j#0) <= LitInt(_System.array.Length(Lit(a#0)))
           && Seq#Equal(Seq#Drop(Seq#Take(Seq#FromArray($Heap, Lit(a#0)), LitInt(j#0)), LitInt(j#0)), 
            Seq#Empty(): Seq Box)));

procedure CheckWellformed$$_module.A.AnotherGoodRangeReads(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.A())
         && $IsAlloc(this, Tclass._module.A(), $Heap), 
    a#0: ref where $Is(a#0, Tclass._System.array(TInt)), 
    j#0: int);
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.A.AnotherGoodRangeReads(this: ref, a#0: ref, j#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function AnotherGoodRangeReads
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(133,11): initial state"} true;
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
        if (LitInt(0) <= j#0)
        {
            assert a#0 != null;
        }

        if (LitInt(0) <= j#0 && j#0 <= _System.array.Length(a#0))
        {
            assert a#0 != null;
            assert 0 <= j#0 && j#0 <= _System.array.Length(a#0);
            assert j#0 <= j#0 && j#0 <= _System.array.Length(a#0);
            b$reqreads#0 := (forall $i: int :: 
              { $_Frame[a#0, IndexField($i)] } 
              j#0 <= $i && $i < j#0 ==> $_Frame[a#0, IndexField($i)]);
        }

        assume _module.A.AnotherGoodRangeReads(this, a#0, j#0)
           == (
            LitInt(0) <= j#0
             && j#0 <= _System.array.Length(a#0)
             && Seq#Equal(Seq#Drop(Seq#Take(Seq#FromArray($Heap, a#0), j#0), j#0), Seq#Empty(): Seq Box));
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.A.AnotherGoodRangeReads(this, a#0, j#0), TBool);
        assert b$reqreads#0;
    }
}



// function declaration for _module.A.Q0
function _module.A.Q0(this: ref, s#0: Seq Box) : bool;

function _module.A.Q0#canCall(this: ref, s#0: Seq Box) : bool;

// consequence axiom for _module.A.Q0
axiom 7 <= $FunctionContextHeight
   ==> (forall this: ref, s#0: Seq Box :: 
    { _module.A.Q0(this, s#0) } 
    _module.A.Q0#canCall(this, s#0)
         || (7 != $FunctionContextHeight
           && 
          this != null
           && $Is(this, Tclass._module.A())
           && $Is(s#0, TSeq(TInt)))
       ==> true);

function _module.A.Q0#requires(ref, Seq Box) : bool;

// #requires axiom for _module.A.Q0
axiom (forall this: ref, s#0: Seq Box :: 
  { _module.A.Q0#requires(this, s#0) } 
  this != null && $Is(this, Tclass._module.A()) && $Is(s#0, TSeq(TInt))
     ==> _module.A.Q0#requires(this, s#0) == true);

procedure CheckWellformed$$_module.A.Q0(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.A())
         && $IsAlloc(this, Tclass._module.A(), $Heap), 
    s#0: Seq Box where $Is(s#0, TSeq(TInt)));
  free requires 7 == $FunctionContextHeight;
  modifies $Heap, $Tick;



// function declaration for _module.A.Q1
function _module.A.Q1(this: ref, s#0: Seq Box) : bool;

function _module.A.Q1#canCall(this: ref, s#0: Seq Box) : bool;

// consequence axiom for _module.A.Q1
axiom 8 <= $FunctionContextHeight
   ==> (forall this: ref, s#0: Seq Box :: 
    { _module.A.Q1(this, s#0) } 
    _module.A.Q1#canCall(this, s#0)
         || (8 != $FunctionContextHeight
           && 
          this != null
           && $Is(this, Tclass._module.A())
           && $Is(s#0, TSeq(TInt)))
       ==> true);

function _module.A.Q1#requires(ref, Seq Box) : bool;

// #requires axiom for _module.A.Q1
axiom (forall this: ref, s#0: Seq Box :: 
  { _module.A.Q1#requires(this, s#0) } 
  this != null && $Is(this, Tclass._module.A()) && $Is(s#0, TSeq(TInt))
     ==> _module.A.Q1#requires(this, s#0) == true);

procedure CheckWellformed$$_module.A.Q1(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.A())
         && $IsAlloc(this, Tclass._module.A(), $Heap), 
    s#0: Seq Box where $Is(s#0, TSeq(TInt)));
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure CheckWellformed$$_module.A.FrameTest(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.A())
         && $IsAlloc(this, Tclass._module.A(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._System.array(TInt))
         && $IsAlloc(a#0, Tclass._System.array(TInt), $Heap))
   returns (b#0: ref
       where $Is(b#0, Tclass._System.array(TInt))
         && $IsAlloc(b#0, Tclass._System.array(TInt), $Heap));
  free requires 10 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.A.FrameTest(this: ref, a#0: ref) returns (b#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##s#0: Seq Box;

    // AddMethodImpl: FrameTest, CheckWellformed$$_module.A.FrameTest
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(141,9): initial state"} true;
    assert a#0 != null;
    ##s#0 := Seq#FromArray($Heap, a#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#0, TSeq(TInt), $Heap);
    assume _module.A.Q0#canCall(this, Seq#FromArray($Heap, a#0));
    assume _module.A.Q0(this, Seq#FromArray($Heap, a#0));
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
    assume $HeapSucc(old($Heap), $Heap);
    havoc b#0;
}



procedure Call$$_module.A.FrameTest(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.A())
         && $IsAlloc(this, Tclass._module.A(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._System.array(TInt))
         && $IsAlloc(a#0, Tclass._System.array(TInt), $Heap))
   returns (b#0: ref
       where $Is(b#0, Tclass._System.array(TInt))
         && $IsAlloc(b#0, Tclass._System.array(TInt), $Heap));
  // user-defined preconditions
  requires _module.A.Q0(this, Seq#FromArray($Heap, a#0));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.A.FrameTest(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.A())
         && $IsAlloc(this, Tclass._module.A(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._System.array(TInt))
         && $IsAlloc(a#0, Tclass._System.array(TInt), $Heap))
   returns (b#0: ref
       where $Is(b#0, Tclass._System.array(TInt))
         && $IsAlloc(b#0, Tclass._System.array(TInt), $Heap), 
    $_reverifyPost: bool);
  free requires 10 == $FunctionContextHeight;
  // user-defined preconditions
  requires _module.A.Q0(this, Seq#FromArray($Heap, a#0));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.A.FrameTest(this: ref, a#0: ref) returns (b#0: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs##0: ref
     where $Is($rhs##0, Tclass._System.array(TInt))
       && $IsAlloc($rhs##0, Tclass._System.array(TInt), $Heap);
  var a##0: ref;
  var ##s#1: Seq Box;
  var ##s#2: Seq Box;

    // AddMethodImpl: FrameTest, Impl$$_module.A.FrameTest
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(143,2): initial state"} true;
    $_reverifyPost := false;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(144,21)
    assume true;
    // TrCallStmt: Adding lhs with type array<int>
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##0 := a#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0 := Call$$_module.A.CreateArray(this, a##0);
    // TrCallStmt: After ProcessCallStmt
    b#0 := $rhs##0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(144,23)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(145,5)
    assert a#0 != null;
    ##s#1 := Seq#FromArray($Heap, a#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#1, TSeq(TInt), $Heap);
    assume _module.A.Q0#canCall(this, Seq#FromArray($Heap, a#0));
    assume _module.A.Q0#canCall(this, Seq#FromArray($Heap, a#0));
    assert _module.A.Q0(this, Seq#FromArray($Heap, a#0));
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(146,5)
    assert b#0 != null;
    ##s#2 := Seq#FromArray($Heap, b#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#2, TSeq(TInt), $Heap);
    assume _module.A.Q1#canCall(this, Seq#FromArray($Heap, b#0));
    assume _module.A.Q1#canCall(this, Seq#FromArray($Heap, b#0));
    assert _module.A.Q1(this, Seq#FromArray($Heap, b#0));
}



procedure CheckWellformed$$_module.A.CreateArray(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.A())
         && $IsAlloc(this, Tclass._module.A(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._System.array(TInt))
         && $IsAlloc(a#0, Tclass._System.array(TInt), $Heap))
   returns (b#0: ref
       where $Is(b#0, Tclass._System.array(TInt))
         && $IsAlloc(b#0, Tclass._System.array(TInt), $Heap));
  free requires 9 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.A.CreateArray(this: ref, a#0: ref) returns (b#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##s#0: Seq Box;

    // AddMethodImpl: CreateArray, CheckWellformed$$_module.A.CreateArray
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(148,9): initial state"} true;
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
    assume $HeapSucc(old($Heap), $Heap);
    havoc b#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(149,21): post-state"} true;
    assume b#0 != null && !read(old($Heap), b#0, alloc);
    assert b#0 != null;
    ##s#0 := Seq#FromArray($Heap, b#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#0, TSeq(TInt), $Heap);
    assume _module.A.Q1#canCall(this, Seq#FromArray($Heap, b#0));
    assume _module.A.Q1(this, Seq#FromArray($Heap, b#0));
}



procedure Call$$_module.A.CreateArray(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.A())
         && $IsAlloc(this, Tclass._module.A(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._System.array(TInt))
         && $IsAlloc(a#0, Tclass._System.array(TInt), $Heap))
   returns (b#0: ref
       where $Is(b#0, Tclass._System.array(TInt))
         && $IsAlloc(b#0, Tclass._System.array(TInt), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures b#0 != null && !read(old($Heap), b#0, alloc)
     ==> _module.A.Q1#canCall(this, Seq#FromArray($Heap, b#0));
  ensures b#0 != null && !read(old($Heap), b#0, alloc);
  ensures _module.A.Q1(this, Seq#FromArray($Heap, b#0));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



// _module.A: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.A()) } 
  $Is(c#0, Tclass._module.A()) <==> $Is(c#0, Tclass._module.A?()) && c#0 != null);

// _module.A: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.A(), $h) } 
  $IsAlloc(c#0, Tclass._module.A(), $h)
     <==> $IsAlloc(c#0, Tclass._module.A?(), $h));

const unique class._module.B?: ClassName;

// B: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.B?()) } 
  $Is($o, Tclass._module.B?()) <==> $o == null || dtype($o) == Tclass._module.B?());

// B: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.B?(), $h) } 
  $IsAlloc($o, Tclass._module.B?(), $h) <==> $o == null || read($h, $o, alloc));

function Tclass._module.B() : Ty;

const unique Tagclass._module.B: TyTag;

// Tclass._module.B Tag
axiom Tag(Tclass._module.B()) == Tagclass._module.B
   && TagFamily(Tclass._module.B()) == tytagFamily$B;

// Box/unbox axiom for Tclass._module.B
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.B()) } 
  $IsBox(bx, Tclass._module.B())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.B()));

// _module.B: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.B()) } 
  $Is(c#0, Tclass._module.B()) <==> $Is(c#0, Tclass._module.B?()) && c#0 != null);

// _module.B: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.B(), $h) } 
  $IsAlloc(c#0, Tclass._module.B(), $h)
     <==> $IsAlloc(c#0, Tclass._module.B?(), $h));

const unique class._module.ArrayTests?: ClassName;

function Tclass._module.ArrayTests?() : Ty;

const unique Tagclass._module.ArrayTests?: TyTag;

// Tclass._module.ArrayTests? Tag
axiom Tag(Tclass._module.ArrayTests?()) == Tagclass._module.ArrayTests?
   && TagFamily(Tclass._module.ArrayTests?()) == tytagFamily$ArrayTests;

// Box/unbox axiom for Tclass._module.ArrayTests?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.ArrayTests?()) } 
  $IsBox(bx, Tclass._module.ArrayTests?())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.ArrayTests?()));

// ArrayTests: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.ArrayTests?()) } 
  $Is($o, Tclass._module.ArrayTests?())
     <==> $o == null || dtype($o) == Tclass._module.ArrayTests?());

// ArrayTests: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.ArrayTests?(), $h) } 
  $IsAlloc($o, Tclass._module.ArrayTests?(), $h)
     <==> $o == null || read($h, $o, alloc));

// function declaration for _module.ArrayTests.F0
function _module.ArrayTests.F0(this: ref, a#0: ref) : bool;

function _module.ArrayTests.F0#canCall(this: ref, a#0: ref) : bool;

function Tclass._module.ArrayTests() : Ty;

const unique Tagclass._module.ArrayTests: TyTag;

// Tclass._module.ArrayTests Tag
axiom Tag(Tclass._module.ArrayTests()) == Tagclass._module.ArrayTests
   && TagFamily(Tclass._module.ArrayTests()) == tytagFamily$ArrayTests;

// Box/unbox axiom for Tclass._module.ArrayTests
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.ArrayTests()) } 
  $IsBox(bx, Tclass._module.ArrayTests())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.ArrayTests()));

// consequence axiom for _module.ArrayTests.F0
axiom 11 <= $FunctionContextHeight
   ==> (forall this: ref, a#0: ref :: 
    { _module.ArrayTests.F0(this, a#0) } 
    _module.ArrayTests.F0#canCall(this, a#0)
         || (11 != $FunctionContextHeight
           && 
          this != null
           && $Is(this, Tclass._module.ArrayTests())
           && $Is(a#0, Tclass._System.array(TInt)))
       ==> true);

function _module.ArrayTests.F0#requires(ref, ref) : bool;

// #requires axiom for _module.ArrayTests.F0
axiom (forall $Heap: Heap, this: ref, a#0: ref :: 
  { _module.ArrayTests.F0#requires(this, a#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.ArrayTests())
       && $IsAlloc(this, Tclass._module.ArrayTests(), $Heap)
       && $Is(a#0, Tclass._System.array(TInt))
     ==> _module.ArrayTests.F0#requires(this, a#0) == true);

// definition axiom for _module.ArrayTests.F0 (revealed)
axiom 11 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref, a#0: ref :: 
    { _module.ArrayTests.F0(this, a#0), $IsGoodHeap($Heap) } 
    _module.ArrayTests.F0#canCall(this, a#0)
         || (11 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.ArrayTests())
           && $IsAlloc(this, Tclass._module.ArrayTests(), $Heap)
           && $Is(a#0, Tclass._System.array(TInt)))
       ==> _module.ArrayTests.F0(this, a#0)
         == (LitInt(10) <= _System.array.Length(a#0)
           && $Unbox(read($Heap, a#0, IndexField(LitInt(7)))): int == LitInt(13)));

// definition axiom for _module.ArrayTests.F0 for decreasing-related literals (revealed)
axiom 11 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref, a#0: ref :: 
    {:weight 3} { _module.ArrayTests.F0(this, Lit(a#0)), $IsGoodHeap($Heap) } 
    _module.ArrayTests.F0#canCall(this, Lit(a#0))
         || (11 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.ArrayTests())
           && $IsAlloc(this, Tclass._module.ArrayTests(), $Heap)
           && $Is(a#0, Tclass._System.array(TInt)))
       ==> _module.ArrayTests.F0(this, Lit(a#0))
         == (LitInt(10) <= LitInt(_System.array.Length(Lit(a#0)))
           && $Unbox(read($Heap, Lit(a#0), IndexField(LitInt(7)))): int == LitInt(13)));

// definition axiom for _module.ArrayTests.F0 for all literals (revealed)
axiom 11 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref, a#0: ref :: 
    {:weight 3} { _module.ArrayTests.F0(Lit(this), Lit(a#0)), $IsGoodHeap($Heap) } 
    _module.ArrayTests.F0#canCall(Lit(this), Lit(a#0))
         || (11 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.ArrayTests())
           && $IsAlloc(this, Tclass._module.ArrayTests(), $Heap)
           && $Is(a#0, Tclass._System.array(TInt)))
       ==> _module.ArrayTests.F0(Lit(this), Lit(a#0))
         == (LitInt(10) <= LitInt(_System.array.Length(Lit(a#0)))
           && $Unbox(read($Heap, Lit(a#0), IndexField(LitInt(7)))): int == LitInt(13)));

procedure CheckWellformed$$_module.ArrayTests.F0(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.ArrayTests())
         && $IsAlloc(this, Tclass._module.ArrayTests(), $Heap), 
    a#0: ref where $Is(a#0, Tclass._System.array(TInt)));
  free requires 11 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.ArrayTests.F0(this: ref, a#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function F0
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(157,11): initial state"} true;
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
        assert a#0 != null;
        if (LitInt(10) <= _System.array.Length(a#0))
        {
            assert a#0 != null;
            assert 0 <= LitInt(7) && LitInt(7) < _System.array.Length(a#0);
            b$reqreads#0 := $_Frame[a#0, IndexField(LitInt(7))];
        }

        assume _module.ArrayTests.F0(this, a#0)
           == (LitInt(10) <= _System.array.Length(a#0)
             && $Unbox(read($Heap, a#0, IndexField(LitInt(7)))): int == LitInt(13));
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.ArrayTests.F0(this, a#0), TBool);
        assert b$reqreads#0;
    }
}



axiom FDim(_module.ArrayTests.b) == 0
   && FieldOfDecl(class._module.ArrayTests?, field$b) == _module.ArrayTests.b
   && !$IsGhostField(_module.ArrayTests.b);

const _module.ArrayTests.b: Field ref;

// ArrayTests.b: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.ArrayTests.b) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.ArrayTests?()
     ==> $Is(read($h, $o, _module.ArrayTests.b), Tclass._System.array(TInt)));

// ArrayTests.b: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.ArrayTests.b) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.ArrayTests?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.ArrayTests.b), Tclass._System.array(TInt), $h));

// function declaration for _module.ArrayTests.F1
function _module.ArrayTests.F1($heap: Heap, this: ref) : bool;

function _module.ArrayTests.F1#canCall($heap: Heap, this: ref) : bool;

// frame axiom for _module.ArrayTests.F1
axiom (forall $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.ArrayTests.F1($h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.ArrayTests())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && $o == this ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.ArrayTests.F1($h0, this) == _module.ArrayTests.F1($h1, this));

// consequence axiom for _module.ArrayTests.F1
axiom 38 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref :: 
    { _module.ArrayTests.F1($Heap, this) } 
    _module.ArrayTests.F1#canCall($Heap, this)
         || (38 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.ArrayTests())
           && $IsAlloc(this, Tclass._module.ArrayTests(), $Heap))
       ==> true);

function _module.ArrayTests.F1#requires(Heap, ref) : bool;

// #requires axiom for _module.ArrayTests.F1
axiom (forall $Heap: Heap, this: ref :: 
  { _module.ArrayTests.F1#requires($Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.ArrayTests())
       && $IsAlloc(this, Tclass._module.ArrayTests(), $Heap)
     ==> _module.ArrayTests.F1#requires($Heap, this) == true);

// definition axiom for _module.ArrayTests.F1 (revealed)
axiom 38 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref :: 
    { _module.ArrayTests.F1($Heap, this), $IsGoodHeap($Heap) } 
    _module.ArrayTests.F1#canCall($Heap, this)
         || (38 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.ArrayTests())
           && $IsAlloc(this, Tclass._module.ArrayTests(), $Heap))
       ==> _module.ArrayTests.F1($Heap, this)
         == (LitInt(10) <= _System.array.Length(read($Heap, this, _module.ArrayTests.b))
           && $Unbox(read($Heap, read($Heap, this, _module.ArrayTests.b), IndexField(LitInt(7)))): int
             == LitInt(13)));

procedure CheckWellformed$$_module.ArrayTests.F1(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.ArrayTests())
         && $IsAlloc(this, Tclass._module.ArrayTests(), $Heap));
  free requires 38 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.ArrayTests.F1(this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;
  var b$reqreads#2: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;

    // AddWellformednessCheck for function F1
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(164,11): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> $o == this);
        b$reqreads#0 := $_Frame[this, _module.ArrayTests.b];
        assert read($Heap, this, _module.ArrayTests.b) != null;
        if (LitInt(10) <= _System.array.Length(read($Heap, this, _module.ArrayTests.b)))
        {
            b$reqreads#1 := $_Frame[this, _module.ArrayTests.b];
            assert read($Heap, this, _module.ArrayTests.b) != null;
            assert 0 <= LitInt(7)
               && LitInt(7) < _System.array.Length(read($Heap, this, _module.ArrayTests.b));
            b$reqreads#2 := $_Frame[read($Heap, this, _module.ArrayTests.b), IndexField(LitInt(7))];
        }

        assume _module.ArrayTests.F1($Heap, this)
           == (LitInt(10) <= _System.array.Length(read($Heap, this, _module.ArrayTests.b))
             && $Unbox(read($Heap, read($Heap, this, _module.ArrayTests.b), IndexField(LitInt(7)))): int
               == LitInt(13));
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.ArrayTests.F1($Heap, this), TBool);
        assert b$reqreads#0;
        assert b$reqreads#1;
        assert b$reqreads#2;
    }
}



// function declaration for _module.ArrayTests.F2
function _module.ArrayTests.F2($heap: Heap, this: ref, a#0: ref) : bool;

function _module.ArrayTests.F2#canCall($heap: Heap, this: ref, a#0: ref) : bool;

// frame axiom for _module.ArrayTests.F2
axiom (forall $h0: Heap, $h1: Heap, this: ref, a#0: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.ArrayTests.F2($h1, this, a#0) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.ArrayTests())
       && (_module.ArrayTests.F2#canCall($h0, this, a#0)
         || $Is(a#0, Tclass._System.array(TInt)))
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && ($o == this || $o == read($h0, this, _module.ArrayTests.b) || $o == a#0)
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.ArrayTests.F2($h0, this, a#0) == _module.ArrayTests.F2($h1, this, a#0));

// consequence axiom for _module.ArrayTests.F2
axiom 12 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref, a#0: ref :: 
    { _module.ArrayTests.F2($Heap, this, a#0) } 
    _module.ArrayTests.F2#canCall($Heap, this, a#0)
         || (12 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.ArrayTests())
           && $IsAlloc(this, Tclass._module.ArrayTests(), $Heap)
           && $Is(a#0, Tclass._System.array(TInt)))
       ==> true);

function _module.ArrayTests.F2#requires(Heap, ref, ref) : bool;

// #requires axiom for _module.ArrayTests.F2
axiom (forall $Heap: Heap, this: ref, a#0: ref :: 
  { _module.ArrayTests.F2#requires($Heap, this, a#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.ArrayTests())
       && $IsAlloc(this, Tclass._module.ArrayTests(), $Heap)
       && $Is(a#0, Tclass._System.array(TInt))
     ==> _module.ArrayTests.F2#requires($Heap, this, a#0) == true);

// definition axiom for _module.ArrayTests.F2 (revealed)
axiom 12 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref, a#0: ref :: 
    { _module.ArrayTests.F2($Heap, this, a#0), $IsGoodHeap($Heap) } 
    _module.ArrayTests.F2#canCall($Heap, this, a#0)
         || (12 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.ArrayTests())
           && $IsAlloc(this, Tclass._module.ArrayTests(), $Heap)
           && $Is(a#0, Tclass._System.array(TInt)))
       ==> _module.ArrayTests.F2($Heap, this, a#0)
         == (
          LitInt(10) <= _System.array.Length(a#0)
           && $Unbox(read($Heap, a#0, IndexField(LitInt(7)))): int == LitInt(13)
           && LitInt(10) <= _System.array.Length(read($Heap, this, _module.ArrayTests.b))
           && $Unbox(read($Heap, read($Heap, this, _module.ArrayTests.b), IndexField(LitInt(7)))): int
             == LitInt(13)));

procedure CheckWellformed$$_module.ArrayTests.F2(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.ArrayTests())
         && $IsAlloc(this, Tclass._module.ArrayTests(), $Heap), 
    a#0: ref where $Is(a#0, Tclass._System.array(TInt)));
  free requires 12 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.ArrayTests.F2(this: ref, a#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
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

    // AddWellformednessCheck for function F2
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(171,11): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> $o == this || $o == read($Heap, this, _module.ArrayTests.b) || $o == a#0);
    b$reqreads#0 := $_Frame[this, _module.ArrayTests.b];
    assert b$reqreads#0;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc)
             ==> $o == this || $o == read($Heap, this, _module.ArrayTests.b) || $o == a#0);
        assert a#0 != null;
        if (LitInt(10) <= _System.array.Length(a#0))
        {
            assert a#0 != null;
            assert 0 <= LitInt(7) && LitInt(7) < _System.array.Length(a#0);
            b$reqreads#1 := $_Frame[a#0, IndexField(LitInt(7))];
        }

        if (LitInt(10) <= _System.array.Length(a#0)
           && $Unbox(read($Heap, a#0, IndexField(LitInt(7)))): int == LitInt(13))
        {
            b$reqreads#2 := $_Frame[this, _module.ArrayTests.b];
            assert read($Heap, this, _module.ArrayTests.b) != null;
        }

        if (LitInt(10) <= _System.array.Length(a#0)
           && $Unbox(read($Heap, a#0, IndexField(LitInt(7)))): int == LitInt(13)
           && LitInt(10) <= _System.array.Length(read($Heap, this, _module.ArrayTests.b)))
        {
            b$reqreads#3 := $_Frame[this, _module.ArrayTests.b];
            assert read($Heap, this, _module.ArrayTests.b) != null;
            assert 0 <= LitInt(7)
               && LitInt(7) < _System.array.Length(read($Heap, this, _module.ArrayTests.b));
            b$reqreads#4 := $_Frame[read($Heap, this, _module.ArrayTests.b), IndexField(LitInt(7))];
        }

        assume _module.ArrayTests.F2($Heap, this, a#0)
           == (
            LitInt(10) <= _System.array.Length(a#0)
             && $Unbox(read($Heap, a#0, IndexField(LitInt(7)))): int == LitInt(13)
             && LitInt(10) <= _System.array.Length(read($Heap, this, _module.ArrayTests.b))
             && $Unbox(read($Heap, read($Heap, this, _module.ArrayTests.b), IndexField(LitInt(7)))): int
               == LitInt(13));
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.ArrayTests.F2($Heap, this, a#0), TBool);
        assert b$reqreads#1;
        assert b$reqreads#2;
        assert b$reqreads#3;
        assert b$reqreads#4;
    }
}



procedure CheckWellformed$$_module.ArrayTests.M0(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.ArrayTests())
         && $IsAlloc(this, Tclass._module.ArrayTests(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._System.array(TInt))
         && $IsAlloc(a#0, Tclass._System.array(TInt), $Heap));
  free requires 13 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.ArrayTests.M0(this: ref, a#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: M0, CheckWellformed$$_module.ArrayTests.M0
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(181,9): initial state"} true;
    assert a#0 != null;
    assume LitInt(10) <= _System.array.Length(a#0);
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
    assume $HeapSucc(old($Heap), $Heap);
}



procedure Call$$_module.ArrayTests.M0(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.ArrayTests())
         && $IsAlloc(this, Tclass._module.ArrayTests(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._System.array(TInt))
         && $IsAlloc(a#0, Tclass._System.array(TInt), $Heap));
  // user-defined preconditions
  requires LitInt(10) <= _System.array.Length(a#0);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.ArrayTests.M0(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.ArrayTests())
         && $IsAlloc(this, Tclass._module.ArrayTests(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._System.array(TInt))
         && $IsAlloc(a#0, Tclass._System.array(TInt), $Heap))
   returns ($_reverifyPost: bool);
  free requires 13 == $FunctionContextHeight;
  // user-defined preconditions
  requires LitInt(10) <= _System.array.Length(a#0);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.ArrayTests.M0(this: ref, a#0: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: int;

    // AddMethodImpl: M0, Impl$$_module.ArrayTests.M0
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(183,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(184,10)
    assert a#0 != null;
    assert 0 <= LitInt(7) && LitInt(7) < _System.array.Length(a#0);
    assume true;
    assert $_Frame[a#0, IndexField(LitInt(7))];
    assume true;
    $rhs#0 := LitInt(13);
    $Heap := update($Heap, a#0, IndexField(LitInt(7)), $Box($rhs#0));
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(184,14)"} true;
}



procedure CheckWellformed$$_module.ArrayTests.M1(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.ArrayTests())
         && $IsAlloc(this, Tclass._module.ArrayTests(), $Heap));
  free requires 39 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.ArrayTests.M1(this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: M1, CheckWellformed$$_module.ArrayTests.M1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(187,9): initial state"} true;
    assert read($Heap, this, _module.ArrayTests.b) != null;
    assume LitInt(10) <= _System.array.Length(read($Heap, this, _module.ArrayTests.b));
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc)
         ==> $Heap[$o] == old($Heap)[$o] || $o == this);
    assume $HeapSucc(old($Heap), $Heap);
}



procedure Call$$_module.ArrayTests.M1(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.ArrayTests())
         && $IsAlloc(this, Tclass._module.ArrayTests(), $Heap));
  // user-defined preconditions
  requires LitInt(10) <= _System.array.Length(read($Heap, this, _module.ArrayTests.b));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.ArrayTests.M1(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.ArrayTests())
         && $IsAlloc(this, Tclass._module.ArrayTests(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 39 == $FunctionContextHeight;
  // user-defined preconditions
  requires LitInt(10) <= _System.array.Length(read($Heap, this, _module.ArrayTests.b));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.ArrayTests.M1(this: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: int;

    // AddMethodImpl: M1, Impl$$_module.ArrayTests.M1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(190,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(191,10)
    assert read($Heap, this, _module.ArrayTests.b) != null;
    assert 0 <= LitInt(7)
       && LitInt(7) < _System.array.Length(read($Heap, this, _module.ArrayTests.b));
    assume true;
    assert $_Frame[read($Heap, this, _module.ArrayTests.b), IndexField(LitInt(7))];
    assume true;
    $rhs#0 := LitInt(13);
    $Heap := update($Heap, 
      read($Heap, this, _module.ArrayTests.b), 
      IndexField(LitInt(7)), 
      $Box($rhs#0));
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(191,14)"} true;
}



procedure CheckWellformed$$_module.ArrayTests.M2(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.ArrayTests())
         && $IsAlloc(this, Tclass._module.ArrayTests(), $Heap));
  free requires 33 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.ArrayTests.M2(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.ArrayTests())
         && $IsAlloc(this, Tclass._module.ArrayTests(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.ArrayTests.M2(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.ArrayTests())
         && $IsAlloc(this, Tclass._module.ArrayTests(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 33 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.ArrayTests.M2(this: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var bb#0: ref
     where $Is(bb#0, Tclass._System.array(TInt))
       && $IsAlloc(bb#0, Tclass._System.array(TInt), $Heap);
  var $nw: ref;
  var $rhs#0: ref where $Is($rhs#0, Tclass._System.array(TInt));

    // AddMethodImpl: M2, Impl$$_module.ArrayTests.M2
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(196,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(197,12)
    assume true;
    assert 0 <= LitInt(75);
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._System.array?(TInt);
    assume !read($Heap, $nw, alloc);
    assume _System.array.Length($nw) == LitInt(75);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    bb#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(197,25)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(198,7)
    assume true;
    assert $_Frame[this, _module.ArrayTests.b];
    assume true;
    $rhs#0 := bb#0;
    $Heap := update($Heap, this, _module.ArrayTests.b, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(198,11)"} true;
}



procedure CheckWellformed$$_module.ArrayTests.M3(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.ArrayTests())
         && $IsAlloc(this, Tclass._module.ArrayTests(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._System.array(TInt))
         && $IsAlloc(a#0, Tclass._System.array(TInt), $Heap));
  free requires 14 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.ArrayTests.M3(this: ref, a#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: M3, CheckWellformed$$_module.ArrayTests.M3
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> $o == this || $o == read($Heap, this, _module.ArrayTests.b) || $o == a#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(201,9): initial state"} true;
    assert a#0 != null;
    assume LitInt(10) <= _System.array.Length(a#0);
    assert read($Heap, this, _module.ArrayTests.b) != null;
    assume LitInt(10) <= _System.array.Length(read($Heap, this, _module.ArrayTests.b));
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc)
         ==> $Heap[$o] == old($Heap)[$o]
           || 
          $o == this
           || $o == read(old($Heap), this, _module.ArrayTests.b)
           || $o == a#0);
    assume $HeapSucc(old($Heap), $Heap);
}



procedure Call$$_module.ArrayTests.M3(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.ArrayTests())
         && $IsAlloc(this, Tclass._module.ArrayTests(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._System.array(TInt))
         && $IsAlloc(a#0, Tclass._System.array(TInt), $Heap));
  // user-defined preconditions
  requires LitInt(10) <= _System.array.Length(a#0);
  requires LitInt(10) <= _System.array.Length(read($Heap, this, _module.ArrayTests.b));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || 
        $o == this
         || $o == read(old($Heap), this, _module.ArrayTests.b)
         || $o == a#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.ArrayTests.M3(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.ArrayTests())
         && $IsAlloc(this, Tclass._module.ArrayTests(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._System.array(TInt))
         && $IsAlloc(a#0, Tclass._System.array(TInt), $Heap))
   returns ($_reverifyPost: bool);
  free requires 14 == $FunctionContextHeight;
  // user-defined preconditions
  requires LitInt(10) <= _System.array.Length(a#0);
  requires LitInt(10) <= _System.array.Length(read($Heap, this, _module.ArrayTests.b));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || 
        $o == this
         || $o == read(old($Heap), this, _module.ArrayTests.b)
         || $o == a#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.ArrayTests.M3(this: ref, a#0: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: int;
  var $rhs#1: int;

    // AddMethodImpl: M3, Impl$$_module.ArrayTests.M3
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> $o == this || $o == read($Heap, this, _module.ArrayTests.b) || $o == a#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(205,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(206,10)
    assert a#0 != null;
    assert 0 <= LitInt(7) && LitInt(7) < _System.array.Length(a#0);
    assume true;
    assert $_Frame[a#0, IndexField(LitInt(7))];
    assume true;
    $rhs#0 := LitInt(13);
    $Heap := update($Heap, a#0, IndexField(LitInt(7)), $Box($rhs#0));
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(206,14)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(207,10)
    assert read($Heap, this, _module.ArrayTests.b) != null;
    assert 0 <= LitInt(7)
       && LitInt(7) < _System.array.Length(read($Heap, this, _module.ArrayTests.b));
    assume true;
    assert $_Frame[read($Heap, this, _module.ArrayTests.b), IndexField(LitInt(7))];
    assume true;
    $rhs#1 := LitInt(13);
    $Heap := update($Heap, 
      read($Heap, this, _module.ArrayTests.b), 
      IndexField(LitInt(7)), 
      $Box($rhs#1));
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(207,14)"} true;
}



// _module.ArrayTests: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.ArrayTests()) } 
  $Is(c#0, Tclass._module.ArrayTests())
     <==> $Is(c#0, Tclass._module.ArrayTests?()) && c#0 != null);

// _module.ArrayTests: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.ArrayTests(), $h) } 
  $IsAlloc(c#0, Tclass._module.ArrayTests(), $h)
     <==> $IsAlloc(c#0, Tclass._module.ArrayTests?(), $h));

const unique class._module.Cdefg?: ClassName;

function Tclass._module.Cdefg?(Ty) : Ty;

const unique Tagclass._module.Cdefg?: TyTag;

// Tclass._module.Cdefg? Tag
axiom (forall _module.Cdefg$T: Ty :: 
  { Tclass._module.Cdefg?(_module.Cdefg$T) } 
  Tag(Tclass._module.Cdefg?(_module.Cdefg$T)) == Tagclass._module.Cdefg?
     && TagFamily(Tclass._module.Cdefg?(_module.Cdefg$T)) == tytagFamily$Cdefg);

// Tclass._module.Cdefg? injectivity 0
axiom (forall _module.Cdefg$T: Ty :: 
  { Tclass._module.Cdefg?(_module.Cdefg$T) } 
  Tclass._module.Cdefg?_0(Tclass._module.Cdefg?(_module.Cdefg$T))
     == _module.Cdefg$T);

function Tclass._module.Cdefg?_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.Cdefg?
axiom (forall _module.Cdefg$T: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.Cdefg?(_module.Cdefg$T)) } 
  $IsBox(bx, Tclass._module.Cdefg?(_module.Cdefg$T))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.Cdefg?(_module.Cdefg$T)));

// Cdefg: Class $Is
axiom (forall _module.Cdefg$T: Ty, $o: ref :: 
  { $Is($o, Tclass._module.Cdefg?(_module.Cdefg$T)) } 
  $Is($o, Tclass._module.Cdefg?(_module.Cdefg$T))
     <==> $o == null || dtype($o) == Tclass._module.Cdefg?(_module.Cdefg$T));

// Cdefg: Class $IsAlloc
axiom (forall _module.Cdefg$T: Ty, $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.Cdefg?(_module.Cdefg$T), $h) } 
  $IsAlloc($o, Tclass._module.Cdefg?(_module.Cdefg$T), $h)
     <==> $o == null || read($h, $o, alloc));

axiom FDim(_module.Cdefg.t) == 0
   && FieldOfDecl(class._module.Cdefg?, field$t) == _module.Cdefg.t
   && !$IsGhostField(_module.Cdefg.t);

const _module.Cdefg.t: Field Box;

// Cdefg.t: Type axiom
axiom (forall _module.Cdefg$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.Cdefg.t), Tclass._module.Cdefg?(_module.Cdefg$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Cdefg?(_module.Cdefg$T)
     ==> $IsBox(read($h, $o, _module.Cdefg.t), _module.Cdefg$T));

// Cdefg.t: Allocation axiom
axiom (forall _module.Cdefg$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.Cdefg.t), Tclass._module.Cdefg?(_module.Cdefg$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Cdefg?(_module.Cdefg$T)
       && read($h, $o, alloc)
     ==> $IsAllocBox(read($h, $o, _module.Cdefg.t), _module.Cdefg$T, $h));

function Tclass._module.Cdefg(Ty) : Ty;

const unique Tagclass._module.Cdefg: TyTag;

// Tclass._module.Cdefg Tag
axiom (forall _module.Cdefg$T: Ty :: 
  { Tclass._module.Cdefg(_module.Cdefg$T) } 
  Tag(Tclass._module.Cdefg(_module.Cdefg$T)) == Tagclass._module.Cdefg
     && TagFamily(Tclass._module.Cdefg(_module.Cdefg$T)) == tytagFamily$Cdefg);

// Tclass._module.Cdefg injectivity 0
axiom (forall _module.Cdefg$T: Ty :: 
  { Tclass._module.Cdefg(_module.Cdefg$T) } 
  Tclass._module.Cdefg_0(Tclass._module.Cdefg(_module.Cdefg$T)) == _module.Cdefg$T);

function Tclass._module.Cdefg_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.Cdefg
axiom (forall _module.Cdefg$T: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.Cdefg(_module.Cdefg$T)) } 
  $IsBox(bx, Tclass._module.Cdefg(_module.Cdefg$T))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.Cdefg(_module.Cdefg$T)));

procedure CheckWellformed$$_module.Cdefg.__ctor(_module.Cdefg$T: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Cdefg(_module.Cdefg$T))
         && $IsAlloc(this, Tclass._module.Cdefg(_module.Cdefg$T), $Heap), 
    t#0: Box
       where $IsBox(t#0, _module.Cdefg$T) && $IsAllocBox(t#0, _module.Cdefg$T, $Heap));
  free requires 40 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Cdefg.__ctor(_module.Cdefg$T: Ty, 
    t#0: Box
       where $IsBox(t#0, _module.Cdefg$T) && $IsAllocBox(t#0, _module.Cdefg$T, $Heap))
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Cdefg(_module.Cdefg$T))
         && $IsAlloc(this, Tclass._module.Cdefg(_module.Cdefg$T), $Heap));
  modifies $Heap, $Tick;
  // constructor allocates the object
  ensures !read(old($Heap), this, alloc);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Cdefg.__ctor(_module.Cdefg$T: Ty, 
    t#0: Box
       where $IsBox(t#0, _module.Cdefg$T) && $IsAllocBox(t#0, _module.Cdefg$T, $Heap))
   returns (this: ref where this != null && $Is(this, Tclass._module.Cdefg(_module.Cdefg$T)), 
    $_reverifyPost: bool);
  free requires 40 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Cdefg.__ctor(_module.Cdefg$T: Ty, t#0: Box) returns (this: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var this.t: Box;
  var defass#this.t: bool;

    // AddMethodImpl: _ctor, Impl$$_module.Cdefg.__ctor
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(266,21): initial state"} true;
    $_reverifyPost := false;
    // ----- divided block before new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(266,22)
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(267,12)
    assume true;
    assume true;
    this.t := t#0;
    defass#this.t := true;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(267,15)"} true;
    // ----- new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(266,22)
    assert defass#this.t;
    assume !read($Heap, this, alloc);
    assume read($Heap, this, _module.Cdefg.t) == this.t;
    $Heap := update($Heap, this, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    // ----- divided block after new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(266,22)
}



// _module.Cdefg: subset type $Is
axiom (forall _module.Cdefg$T: Ty, c#0: ref :: 
  { $Is(c#0, Tclass._module.Cdefg(_module.Cdefg$T)) } 
  $Is(c#0, Tclass._module.Cdefg(_module.Cdefg$T))
     <==> $Is(c#0, Tclass._module.Cdefg?(_module.Cdefg$T)) && c#0 != null);

// _module.Cdefg: subset type $IsAlloc
axiom (forall _module.Cdefg$T: Ty, c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.Cdefg(_module.Cdefg$T), $h) } 
  $IsAlloc(c#0, Tclass._module.Cdefg(_module.Cdefg$T), $h)
     <==> $IsAlloc(c#0, Tclass._module.Cdefg?(_module.Cdefg$T), $h));

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

axiom FDim(_module.MyClass.Repr) == 0
   && FieldOfDecl(class._module.MyClass?, field$Repr) == _module.MyClass.Repr
   && $IsGhostField(_module.MyClass.Repr);

const _module.MyClass.Repr: Field (Set Box);

// MyClass.Repr: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.MyClass.Repr) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.MyClass?()
     ==> $Is(read($h, $o, _module.MyClass.Repr), TSet(Tclass._System.object())));

// MyClass.Repr: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.MyClass.Repr) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.MyClass?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.MyClass.Repr), TSet(Tclass._System.object()), $h));

// function declaration for _module.MyClass.Valid
function _module.MyClass.Valid($heap: Heap, this: ref) : bool;

function _module.MyClass.Valid#canCall($heap: Heap, this: ref) : bool;

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

// frame axiom for _module.MyClass.Valid
axiom (forall $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.MyClass.Valid($h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.MyClass())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && ($o == this || read($h0, this, _module.MyClass.Repr)[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.MyClass.Valid($h0, this) == _module.MyClass.Valid($h1, this));

// consequence axiom for _module.MyClass.Valid
axiom 25 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref :: 
    { _module.MyClass.Valid($Heap, this) } 
    _module.MyClass.Valid#canCall($Heap, this)
         || (25 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.MyClass())
           && $IsAlloc(this, Tclass._module.MyClass(), $Heap))
       ==> true);

function _module.MyClass.Valid#requires(Heap, ref) : bool;

// #requires axiom for _module.MyClass.Valid
axiom (forall $Heap: Heap, this: ref :: 
  { _module.MyClass.Valid#requires($Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.MyClass())
       && $IsAlloc(this, Tclass._module.MyClass(), $Heap)
     ==> _module.MyClass.Valid#requires($Heap, this) == true);

procedure CheckWellformed$$_module.MyClass.Valid(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.MyClass())
         && $IsAlloc(this, Tclass._module.MyClass(), $Heap));
  free requires 25 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.MyClass.Valid(this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function Valid
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(275,12): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> $o == this || read($Heap, this, _module.MyClass.Repr)[$Box($o)]);
    b$reqreads#0 := $_Frame[this, _module.MyClass.Repr];
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

const unique class._module.AssignSuchThat?: ClassName;

function Tclass._module.AssignSuchThat?() : Ty;

const unique Tagclass._module.AssignSuchThat?: TyTag;

// Tclass._module.AssignSuchThat? Tag
axiom Tag(Tclass._module.AssignSuchThat?()) == Tagclass._module.AssignSuchThat?
   && TagFamily(Tclass._module.AssignSuchThat?()) == tytagFamily$AssignSuchThat;

// Box/unbox axiom for Tclass._module.AssignSuchThat?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.AssignSuchThat?()) } 
  $IsBox(bx, Tclass._module.AssignSuchThat?())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.AssignSuchThat?()));

// AssignSuchThat: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.AssignSuchThat?()) } 
  $Is($o, Tclass._module.AssignSuchThat?())
     <==> $o == null || dtype($o) == Tclass._module.AssignSuchThat?());

// AssignSuchThat: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.AssignSuchThat?(), $h) } 
  $IsAlloc($o, Tclass._module.AssignSuchThat?(), $h)
     <==> $o == null || read($h, $o, alloc));

axiom FDim(_module.AssignSuchThat.x) == 0
   && FieldOfDecl(class._module.AssignSuchThat?, field$x) == _module.AssignSuchThat.x
   && !$IsGhostField(_module.AssignSuchThat.x);

const _module.AssignSuchThat.x: Field int;

// AssignSuchThat.x: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.AssignSuchThat.x) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.AssignSuchThat?()
     ==> $Is(read($h, $o, _module.AssignSuchThat.x), TInt));

// AssignSuchThat.x: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.AssignSuchThat.x) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.AssignSuchThat?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.AssignSuchThat.x), TInt, $h));

function Tclass._module.AssignSuchThat() : Ty;

const unique Tagclass._module.AssignSuchThat: TyTag;

// Tclass._module.AssignSuchThat Tag
axiom Tag(Tclass._module.AssignSuchThat()) == Tagclass._module.AssignSuchThat
   && TagFamily(Tclass._module.AssignSuchThat()) == tytagFamily$AssignSuchThat;

// Box/unbox axiom for Tclass._module.AssignSuchThat
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.AssignSuchThat()) } 
  $IsBox(bx, Tclass._module.AssignSuchThat())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.AssignSuchThat()));

procedure CheckWellformed$$_module.AssignSuchThat.P(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AssignSuchThat())
         && $IsAlloc(this, Tclass._module.AssignSuchThat(), $Heap));
  free requires 41 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.AssignSuchThat.P(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AssignSuchThat())
         && $IsAlloc(this, Tclass._module.AssignSuchThat(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.AssignSuchThat.P(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AssignSuchThat())
         && $IsAlloc(this, Tclass._module.AssignSuchThat(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 41 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.AssignSuchThat.P(this: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: int;

    // AddMethodImpl: P, Impl$$_module.AssignSuchThat.P
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(331,13): initial state"} true;
    $_reverifyPost := false;
    // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(332,7)
    assume true;
    assert $_Frame[this, _module.AssignSuchThat.x];
    havoc $rhs#0;
    $Heap := update($Heap, this, _module.AssignSuchThat.x, $rhs#0);
    assume $IsGoodHeap($Heap);
    if (true)
    {
        assume true;
    }

    havoc ;
    assume read($Heap, this, _module.AssignSuchThat.x) == LitInt(10);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(332,23)"} true;
}



procedure CheckWellformed$$_module.AssignSuchThat.Q0(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AssignSuchThat())
         && $IsAlloc(this, Tclass._module.AssignSuchThat(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._System.array(TInt))
         && $IsAlloc(a#0, Tclass._System.array(TInt), $Heap));
  free requires 15 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.AssignSuchThat.Q0(this: ref, a#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Q0, CheckWellformed$$_module.AssignSuchThat.Q0
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(335,9): initial state"} true;
    assert a#0 != null;
    assume _System.array.Length(a#0) == LitInt(50);
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
    assume $HeapSucc(old($Heap), $Heap);
}



procedure Call$$_module.AssignSuchThat.Q0(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AssignSuchThat())
         && $IsAlloc(this, Tclass._module.AssignSuchThat(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._System.array(TInt))
         && $IsAlloc(a#0, Tclass._System.array(TInt), $Heap));
  // user-defined preconditions
  requires _System.array.Length(a#0) == LitInt(50);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.AssignSuchThat.Q0(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AssignSuchThat())
         && $IsAlloc(this, Tclass._module.AssignSuchThat(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._System.array(TInt))
         && $IsAlloc(a#0, Tclass._System.array(TInt), $Heap))
   returns ($_reverifyPost: bool);
  free requires 15 == $FunctionContextHeight;
  // user-defined preconditions
  requires _System.array.Length(a#0) == LitInt(50);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.AssignSuchThat.Q0(this: ref, a#0: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: int;

    // AddMethodImpl: Q0, Impl$$_module.AssignSuchThat.Q0
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(337,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(338,11)
    assert a#0 != null;
    assert 0 <= LitInt(22) && LitInt(22) < _System.array.Length(a#0);
    assume true;
    assert $_Frame[a#0, IndexField(LitInt(22))];
    havoc $rhs#0;
    $Heap := update($Heap, a#0, IndexField(LitInt(22)), $Box($rhs#0));
    assume $IsGoodHeap($Heap);
    if (true)
    {
        assert a#0 != null;
        assert {:subsumption 0} 0 <= LitInt(22) && LitInt(22) < _System.array.Length(a#0);
        assume true;
    }

    havoc ;
    assume $Unbox(read($Heap, a#0, IndexField(LitInt(22)))): int == LitInt(12);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(338,31)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(339,5)
    assert a#0 != null;
    assert {:subsumption 0} 0 <= LitInt(22) && LitInt(22) < _System.array.Length(a#0);
    assume true;
    assert $Unbox(read($Heap, a#0, IndexField(LitInt(22)))): int == LitInt(12);
}



procedure CheckWellformed$$_module.AssignSuchThat.Q1(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AssignSuchThat())
         && $IsAlloc(this, Tclass._module.AssignSuchThat(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._System.array(TInt))
         && $IsAlloc(a#0, Tclass._System.array(TInt), $Heap));
  free requires 16 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.AssignSuchThat.Q1(this: ref, a#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Q1, CheckWellformed$$_module.AssignSuchThat.Q1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == a#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(341,9): initial state"} true;
    assert a#0 != null;
    assume _System.array.Length(a#0) == LitInt(50);
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc)
         ==> $Heap[$o] == old($Heap)[$o] || $o == a#0);
    assume $HeapSucc(old($Heap), $Heap);
}



procedure Call$$_module.AssignSuchThat.Q1(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AssignSuchThat())
         && $IsAlloc(this, Tclass._module.AssignSuchThat(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._System.array(TInt))
         && $IsAlloc(a#0, Tclass._System.array(TInt), $Heap));
  // user-defined preconditions
  requires _System.array.Length(a#0) == LitInt(50);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == a#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.AssignSuchThat.Q1(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AssignSuchThat())
         && $IsAlloc(this, Tclass._module.AssignSuchThat(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._System.array(TInt))
         && $IsAlloc(a#0, Tclass._System.array(TInt), $Heap))
   returns ($_reverifyPost: bool);
  free requires 16 == $FunctionContextHeight;
  // user-defined preconditions
  requires _System.array.Length(a#0) == LitInt(50);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == a#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.AssignSuchThat.Q1(this: ref, a#0: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: int;

    // AddMethodImpl: Q1, Impl$$_module.AssignSuchThat.Q1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == a#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(344,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(345,11)
    assert a#0 != null;
    assert 0 <= LitInt(22) && LitInt(22) < _System.array.Length(a#0);
    assume true;
    assert $_Frame[a#0, IndexField(LitInt(22))];
    havoc $rhs#0;
    $Heap := update($Heap, a#0, IndexField(LitInt(22)), $Box($rhs#0));
    assume $IsGoodHeap($Heap);
    if (true)
    {
        assert a#0 != null;
        assert {:subsumption 0} 0 <= LitInt(22) && LitInt(22) < _System.array.Length(a#0);
        assume true;
    }

    havoc ;
    assume $Unbox(read($Heap, a#0, IndexField(LitInt(22)))): int == LitInt(12);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(345,31)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(346,5)
    assert a#0 != null;
    assert {:subsumption 0} 0 <= LitInt(22) && LitInt(22) < _System.array.Length(a#0);
    assume true;
    assert $Unbox(read($Heap, a#0, IndexField(LitInt(22)))): int == LitInt(12);
}



procedure CheckWellformed$$_module.AssignSuchThat.Q2(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AssignSuchThat())
         && $IsAlloc(this, Tclass._module.AssignSuchThat(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._System.array(TInt))
         && $IsAlloc(a#0, Tclass._System.array(TInt), $Heap));
  free requires 17 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.AssignSuchThat.Q2(this: ref, a#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Q2, CheckWellformed$$_module.AssignSuchThat.Q2
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == a#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(348,9): initial state"} true;
    assert a#0 != null;
    assume _System.array.Length(a#0) == LitInt(50);
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc)
         ==> $Heap[$o] == old($Heap)[$o] || $o == a#0);
    assume $HeapSucc(old($Heap), $Heap);
}



procedure Call$$_module.AssignSuchThat.Q2(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AssignSuchThat())
         && $IsAlloc(this, Tclass._module.AssignSuchThat(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._System.array(TInt))
         && $IsAlloc(a#0, Tclass._System.array(TInt), $Heap));
  // user-defined preconditions
  requires _System.array.Length(a#0) == LitInt(50);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == a#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.AssignSuchThat.Q2(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AssignSuchThat())
         && $IsAlloc(this, Tclass._module.AssignSuchThat(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._System.array(TInt))
         && $IsAlloc(a#0, Tclass._System.array(TInt), $Heap))
   returns ($_reverifyPost: bool);
  free requires 17 == $FunctionContextHeight;
  // user-defined preconditions
  requires _System.array.Length(a#0) == LitInt(50);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == a#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.AssignSuchThat.Q2(this: ref, a#0: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: int;

    // AddMethodImpl: Q2, Impl$$_module.AssignSuchThat.Q2
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == a#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(351,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(352,11)
    assert a#0 != null;
    assert 0 <= LitInt(22) && LitInt(22) < _System.array.Length(a#0);
    assume true;
    assert $_Frame[a#0, IndexField(LitInt(22))];
    havoc $rhs#0;
    $Heap := update($Heap, a#0, IndexField(LitInt(22)), $Box($rhs#0));
    assume $IsGoodHeap($Heap);
    if (true)
    {
        assert a#0 != null;
        assert {:subsumption 0} 0 <= LitInt(22) && LitInt(22) < _System.array.Length(a#0);
        assume true;
    }

    havoc ;
    assume $Unbox(read($Heap, a#0, IndexField(LitInt(22)))): int == LitInt(12);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(352,31)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(353,5)
    assert a#0 != null;
    assert {:subsumption 0} 0 <= LitInt(22) && LitInt(22) < _System.array.Length(a#0);
    assume true;
    assert $Unbox(read($Heap, a#0, IndexField(LitInt(22)))): int == LitInt(0);
}



procedure CheckWellformed$$_module.AssignSuchThat.R(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AssignSuchThat())
         && $IsAlloc(this, Tclass._module.AssignSuchThat(), $Heap), 
    that#0: ref
       where $Is(that#0, Tclass._module.AssignSuchThat())
         && $IsAlloc(that#0, Tclass._module.AssignSuchThat(), $Heap));
  free requires 19 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.AssignSuchThat.R(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AssignSuchThat())
         && $IsAlloc(this, Tclass._module.AssignSuchThat(), $Heap), 
    that#0: ref
       where $Is(that#0, Tclass._module.AssignSuchThat())
         && $IsAlloc(that#0, Tclass._module.AssignSuchThat(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this || $o == that#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.AssignSuchThat.R(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AssignSuchThat())
         && $IsAlloc(this, Tclass._module.AssignSuchThat(), $Heap), 
    that#0: ref
       where $Is(that#0, Tclass._module.AssignSuchThat())
         && $IsAlloc(that#0, Tclass._module.AssignSuchThat(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 19 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this || $o == that#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.AssignSuchThat.R(this: ref, that#0: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $obj0: ref;
  var $obj1: ref;
  var $rhs#0: int;
  var $rhs#1: int;

    // AddMethodImpl: R, Impl$$_module.AssignSuchThat.R
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this || $o == that#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(357,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(358,20)
    assert that#0 != this;
    assume true;
    $obj0 := this;
    assert $_Frame[$obj0, _module.AssignSuchThat.x];
    assert that#0 != null;
    assume true;
    $obj1 := that#0;
    assert $_Frame[$obj1, _module.AssignSuchThat.x];
    havoc $rhs#0;
    havoc $rhs#1;
    $Heap := update($Heap, $obj0, _module.AssignSuchThat.x, $rhs#0);
    assume $IsGoodHeap($Heap);
    $Heap := update($Heap, $obj1, _module.AssignSuchThat.x, $rhs#1);
    assume $IsGoodHeap($Heap);
    if (true)
    {
        if (read($Heap, this, _module.AssignSuchThat.x) == LitInt(5))
        {
            assert {:subsumption 0} that#0 != null;
        }

        assume true;
    }

    havoc ;
    assume read($Heap, this, _module.AssignSuchThat.x) == LitInt(5)
       && read($Heap, that#0, _module.AssignSuchThat.x) == LitInt(5);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(358,55)"} true;
}



// _module.AssignSuchThat: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.AssignSuchThat()) } 
  $Is(c#0, Tclass._module.AssignSuchThat())
     <==> $Is(c#0, Tclass._module.AssignSuchThat?()) && c#0 != null);

// _module.AssignSuchThat: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.AssignSuchThat(), $h) } 
  $IsAlloc(c#0, Tclass._module.AssignSuchThat(), $h)
     <==> $IsAlloc(c#0, Tclass._module.AssignSuchThat?(), $h));

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

procedure CheckWellformed$$_module.__default.Fill__I(s#0: Seq Box where $Is(s#0, TSeq(TInt)) && $IsAlloc(s#0, TSeq(TInt), $Heap));
  free requires 42 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Fill__I(s#0: Seq Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var i#0: int;
  var i#2: int;
  var j#0: int;

    // AddMethodImpl: Fill_I, CheckWellformed$$_module.__default.Fill__I
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(213,13): initial state"} true;
    havoc i#0;
    assume true;
    if (*)
    {
        assume LitInt(1) <= i#0;
        assume i#0 < Seq#Length(s#0);
        assert 0 <= i#0 - 1 && i#0 - 1 < Seq#Length(s#0);
        assert 0 <= i#0 && i#0 < Seq#Length(s#0);
        assume $Unbox(Seq#Index(s#0, i#0 - 1)): int <= $Unbox(Seq#Index(s#0, i#0)): int;
    }
    else
    {
        assume LitInt(1) <= i#0 && i#0 < Seq#Length(s#0)
           ==> $Unbox(Seq#Index(s#0, i#0 - 1)): int <= $Unbox(Seq#Index(s#0, i#0)): int;
    }

    assume (forall i#1: int, _t#0#0: int :: 
      { $Unbox(Seq#Index(s#0, i#1)): int, $Unbox(Seq#Index(s#0, _t#0#0)): int } 
      _t#0#0 == i#1 - 1
         ==> 
        LitInt(1) <= i#1 && i#1 < Seq#Length(s#0)
         ==> $Unbox(Seq#Index(s#0, _t#0#0)): int <= $Unbox(Seq#Index(s#0, i#1)): int);
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(215,10): post-state"} true;
    havoc i#2;
    havoc j#0;
    assume true;
    if (*)
    {
        assume LitInt(0) <= i#2;
        assume i#2 < j#0;
        assume j#0 < Seq#Length(s#0);
        assert 0 <= i#2 && i#2 < Seq#Length(s#0);
        assert 0 <= j#0 && j#0 < Seq#Length(s#0);
        assume $Unbox(Seq#Index(s#0, i#2)): int <= $Unbox(Seq#Index(s#0, j#0)): int;
    }
    else
    {
        assume LitInt(0) <= i#2 && i#2 < j#0 && j#0 < Seq#Length(s#0)
           ==> $Unbox(Seq#Index(s#0, i#2)): int <= $Unbox(Seq#Index(s#0, j#0)): int;
    }

    assume (forall i#3: int, j#1: int :: 
      {:induction i#3} {:_induction i#3} { $Unbox(Seq#Index(s#0, j#1)): int, $Unbox(Seq#Index(s#0, i#3)): int } 
      true
         ==> 
        LitInt(0) <= i#3 && i#3 < j#1 && j#1 < Seq#Length(s#0)
         ==> $Unbox(Seq#Index(s#0, i#3)): int <= $Unbox(Seq#Index(s#0, j#1)): int);
}



procedure Call$$_module.__default.Fill__I(s#0: Seq Box where $Is(s#0, TSeq(TInt)) && $IsAlloc(s#0, TSeq(TInt), $Heap));
  // user-defined preconditions
  requires (forall i#1: int, _t#0#0: int :: 
    { $Unbox(Seq#Index(s#0, i#1)): int, $Unbox(Seq#Index(s#0, _t#0#0)): int } 
    _t#0#0 == i#1 - 1
       ==> 
      LitInt(1) <= i#1 && i#1 < Seq#Length(s#0)
       ==> $Unbox(Seq#Index(s#0, _t#0#0)): int <= $Unbox(Seq#Index(s#0, i#1)): int);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  free ensures (forall i#3: int, j#1: int :: 
    {:induction i#3} {:_induction i#3} { $Unbox(Seq#Index(s#0, j#1)): int, $Unbox(Seq#Index(s#0, i#3)): int } 
    true
       ==> 
      LitInt(0) <= i#3 && i#3 < j#1 && j#1 < Seq#Length(s#0)
       ==> $Unbox(Seq#Index(s#0, i#3)): int <= $Unbox(Seq#Index(s#0, j#1)): int);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.Fill__I(s#0: Seq Box where $Is(s#0, TSeq(TInt)) && $IsAlloc(s#0, TSeq(TInt), $Heap))
   returns ($_reverifyPost: bool);
  free requires 42 == $FunctionContextHeight;
  // user-defined preconditions
  requires (forall i#1: int, _t#0#0: int :: 
    { $Unbox(Seq#Index(s#0, i#1)): int, $Unbox(Seq#Index(s#0, _t#0#0)): int } 
    _t#0#0 == i#1 - 1
       ==> 
      LitInt(1) <= i#1 && i#1 < Seq#Length(s#0)
       ==> $Unbox(Seq#Index(s#0, _t#0#0)): int <= $Unbox(Seq#Index(s#0, i#1)): int);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures (forall i#3: int, j#1: int :: 
    { $Unbox(Seq#Index(s#0, j#1)): int, $Unbox(Seq#Index(s#0, i#3)): int } 
    (forall i$ih#1#0: int :: 
          { $Unbox(Seq#Index(s#0, j#1)): int, $Unbox(Seq#Index(s#0, i$ih#1#0)): int } 
          true
             ==> 
            0 <= i$ih#1#0 && i$ih#1#0 < i#3
             ==> 
            LitInt(0) <= i$ih#1#0 && i$ih#1#0 < j#1 && j#1 < Seq#Length(s#0)
             ==> $Unbox(Seq#Index(s#0, i$ih#1#0)): int <= $Unbox(Seq#Index(s#0, j#1)): int)
         && true
       ==> 
      LitInt(0) <= i#3 && i#3 < j#1 && j#1 < Seq#Length(s#0)
       ==> $Unbox(Seq#Index(s#0, i#3)): int <= $Unbox(Seq#Index(s#0, j#1)): int);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.Fill__I(s#0: Seq Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Fill_I, Impl$$_module.__default.Fill__I
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(216,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.Fill__J(s#0: Seq Box where $Is(s#0, TSeq(TInt)) && $IsAlloc(s#0, TSeq(TInt), $Heap));
  free requires 43 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Fill__J(s#0: Seq Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var i#0: int;
  var i#2: int;
  var j#0: int;

    // AddMethodImpl: Fill_J, CheckWellformed$$_module.__default.Fill__J
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(219,13): initial state"} true;
    havoc i#0;
    assume true;
    if (*)
    {
        assume LitInt(1) <= i#0;
        assume i#0 < Seq#Length(s#0);
        assert 0 <= i#0 - 1 && i#0 - 1 < Seq#Length(s#0);
        assert 0 <= i#0 && i#0 < Seq#Length(s#0);
        assume $Unbox(Seq#Index(s#0, i#0 - 1)): int <= $Unbox(Seq#Index(s#0, i#0)): int;
    }
    else
    {
        assume LitInt(1) <= i#0 && i#0 < Seq#Length(s#0)
           ==> $Unbox(Seq#Index(s#0, i#0 - 1)): int <= $Unbox(Seq#Index(s#0, i#0)): int;
    }

    assume (forall i#1: int, _t#0#0: int :: 
      { $Unbox(Seq#Index(s#0, i#1)): int, $Unbox(Seq#Index(s#0, _t#0#0)): int } 
      _t#0#0 == i#1 - 1
         ==> 
        LitInt(1) <= i#1 && i#1 < Seq#Length(s#0)
         ==> $Unbox(Seq#Index(s#0, _t#0#0)): int <= $Unbox(Seq#Index(s#0, i#1)): int);
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(221,10): post-state"} true;
    havoc i#2;
    havoc j#0;
    assume true;
    if (*)
    {
        assume LitInt(0) <= i#2;
        assume i#2 < j#0;
        assume j#0 < Seq#Length(s#0);
        assert 0 <= i#2 && i#2 < Seq#Length(s#0);
        assert 0 <= j#0 && j#0 < Seq#Length(s#0);
        assume $Unbox(Seq#Index(s#0, i#2)): int <= $Unbox(Seq#Index(s#0, j#0)): int;
    }
    else
    {
        assume LitInt(0) <= i#2 && i#2 < j#0 && j#0 < Seq#Length(s#0)
           ==> $Unbox(Seq#Index(s#0, i#2)): int <= $Unbox(Seq#Index(s#0, j#0)): int;
    }

    assume (forall i#3: int, j#1: int :: 
      {:induction j#1} {:_induction j#1} { $Unbox(Seq#Index(s#0, j#1)): int, $Unbox(Seq#Index(s#0, i#3)): int } 
      true
         ==> 
        LitInt(0) <= i#3 && i#3 < j#1 && j#1 < Seq#Length(s#0)
         ==> $Unbox(Seq#Index(s#0, i#3)): int <= $Unbox(Seq#Index(s#0, j#1)): int);
}



procedure Call$$_module.__default.Fill__J(s#0: Seq Box where $Is(s#0, TSeq(TInt)) && $IsAlloc(s#0, TSeq(TInt), $Heap));
  // user-defined preconditions
  requires (forall i#1: int, _t#0#0: int :: 
    { $Unbox(Seq#Index(s#0, i#1)): int, $Unbox(Seq#Index(s#0, _t#0#0)): int } 
    _t#0#0 == i#1 - 1
       ==> 
      LitInt(1) <= i#1 && i#1 < Seq#Length(s#0)
       ==> $Unbox(Seq#Index(s#0, _t#0#0)): int <= $Unbox(Seq#Index(s#0, i#1)): int);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  free ensures (forall i#3: int, j#1: int :: 
    {:induction j#1} {:_induction j#1} { $Unbox(Seq#Index(s#0, j#1)): int, $Unbox(Seq#Index(s#0, i#3)): int } 
    true
       ==> 
      LitInt(0) <= i#3 && i#3 < j#1 && j#1 < Seq#Length(s#0)
       ==> $Unbox(Seq#Index(s#0, i#3)): int <= $Unbox(Seq#Index(s#0, j#1)): int);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.Fill__J(s#0: Seq Box where $Is(s#0, TSeq(TInt)) && $IsAlloc(s#0, TSeq(TInt), $Heap))
   returns ($_reverifyPost: bool);
  free requires 43 == $FunctionContextHeight;
  // user-defined preconditions
  requires (forall i#1: int, _t#0#0: int :: 
    { $Unbox(Seq#Index(s#0, i#1)): int, $Unbox(Seq#Index(s#0, _t#0#0)): int } 
    _t#0#0 == i#1 - 1
       ==> 
      LitInt(1) <= i#1 && i#1 < Seq#Length(s#0)
       ==> $Unbox(Seq#Index(s#0, _t#0#0)): int <= $Unbox(Seq#Index(s#0, i#1)): int);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures (forall i#3: int, j#1: int :: 
    { $Unbox(Seq#Index(s#0, j#1)): int, $Unbox(Seq#Index(s#0, i#3)): int } 
    (forall j$ih#1#0: int :: 
          { $Unbox(Seq#Index(s#0, j$ih#1#0)): int, $Unbox(Seq#Index(s#0, i#3)): int } 
          true
             ==> 
            0 <= j$ih#1#0 && j$ih#1#0 < j#1
             ==> 
            LitInt(0) <= i#3 && i#3 < j$ih#1#0 && j$ih#1#0 < Seq#Length(s#0)
             ==> $Unbox(Seq#Index(s#0, i#3)): int <= $Unbox(Seq#Index(s#0, j$ih#1#0)): int)
         && true
       ==> 
      LitInt(0) <= i#3 && i#3 < j#1 && j#1 < Seq#Length(s#0)
       ==> $Unbox(Seq#Index(s#0, i#3)): int <= $Unbox(Seq#Index(s#0, j#1)): int);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.Fill__J(s#0: Seq Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Fill_J, Impl$$_module.__default.Fill__J
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(222,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.Fill__All(s#0: Seq Box where $Is(s#0, TSeq(TInt)) && $IsAlloc(s#0, TSeq(TInt), $Heap));
  free requires 44 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Fill__All(s#0: Seq Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var i#0: int;
  var i#2: int;
  var j#0: int;

    // AddMethodImpl: Fill_All, CheckWellformed$$_module.__default.Fill__All
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(225,13): initial state"} true;
    havoc i#0;
    assume true;
    if (*)
    {
        assume LitInt(1) <= i#0;
        assume i#0 < Seq#Length(s#0);
        assert 0 <= i#0 - 1 && i#0 - 1 < Seq#Length(s#0);
        assert 0 <= i#0 && i#0 < Seq#Length(s#0);
        assume $Unbox(Seq#Index(s#0, i#0 - 1)): int <= $Unbox(Seq#Index(s#0, i#0)): int;
    }
    else
    {
        assume LitInt(1) <= i#0 && i#0 < Seq#Length(s#0)
           ==> $Unbox(Seq#Index(s#0, i#0 - 1)): int <= $Unbox(Seq#Index(s#0, i#0)): int;
    }

    assume (forall i#1: int, _t#0#0: int :: 
      { $Unbox(Seq#Index(s#0, i#1)): int, $Unbox(Seq#Index(s#0, _t#0#0)): int } 
      _t#0#0 == i#1 - 1
         ==> 
        LitInt(1) <= i#1 && i#1 < Seq#Length(s#0)
         ==> $Unbox(Seq#Index(s#0, _t#0#0)): int <= $Unbox(Seq#Index(s#0, i#1)): int);
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(227,10): post-state"} true;
    havoc i#2;
    havoc j#0;
    assume true;
    if (*)
    {
        assume LitInt(0) <= i#2;
        assume i#2 < j#0;
        assume j#0 < Seq#Length(s#0);
        assert 0 <= i#2 && i#2 < Seq#Length(s#0);
        assert 0 <= j#0 && j#0 < Seq#Length(s#0);
        assume $Unbox(Seq#Index(s#0, i#2)): int <= $Unbox(Seq#Index(s#0, j#0)): int;
    }
    else
    {
        assume LitInt(0) <= i#2 && i#2 < j#0 && j#0 < Seq#Length(s#0)
           ==> $Unbox(Seq#Index(s#0, i#2)): int <= $Unbox(Seq#Index(s#0, j#0)): int;
    }

    assume (forall i#3: int, j#1: int :: 
      {:induction i#3, j#1} {:_induction i#3, j#1} { $Unbox(Seq#Index(s#0, j#1)): int, $Unbox(Seq#Index(s#0, i#3)): int } 
      true
         ==> 
        LitInt(0) <= i#3 && i#3 < j#1 && j#1 < Seq#Length(s#0)
         ==> $Unbox(Seq#Index(s#0, i#3)): int <= $Unbox(Seq#Index(s#0, j#1)): int);
}



procedure Call$$_module.__default.Fill__All(s#0: Seq Box where $Is(s#0, TSeq(TInt)) && $IsAlloc(s#0, TSeq(TInt), $Heap));
  // user-defined preconditions
  requires (forall i#1: int, _t#0#0: int :: 
    { $Unbox(Seq#Index(s#0, i#1)): int, $Unbox(Seq#Index(s#0, _t#0#0)): int } 
    _t#0#0 == i#1 - 1
       ==> 
      LitInt(1) <= i#1 && i#1 < Seq#Length(s#0)
       ==> $Unbox(Seq#Index(s#0, _t#0#0)): int <= $Unbox(Seq#Index(s#0, i#1)): int);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  free ensures (forall i#3: int, j#1: int :: 
    {:induction i#3, j#1} {:_induction i#3, j#1} { $Unbox(Seq#Index(s#0, j#1)): int, $Unbox(Seq#Index(s#0, i#3)): int } 
    true
       ==> 
      LitInt(0) <= i#3 && i#3 < j#1 && j#1 < Seq#Length(s#0)
       ==> $Unbox(Seq#Index(s#0, i#3)): int <= $Unbox(Seq#Index(s#0, j#1)): int);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.Fill__All(s#0: Seq Box where $Is(s#0, TSeq(TInt)) && $IsAlloc(s#0, TSeq(TInt), $Heap))
   returns ($_reverifyPost: bool);
  free requires 44 == $FunctionContextHeight;
  // user-defined preconditions
  requires (forall i#1: int, _t#0#0: int :: 
    { $Unbox(Seq#Index(s#0, i#1)): int, $Unbox(Seq#Index(s#0, _t#0#0)): int } 
    _t#0#0 == i#1 - 1
       ==> 
      LitInt(1) <= i#1 && i#1 < Seq#Length(s#0)
       ==> $Unbox(Seq#Index(s#0, _t#0#0)): int <= $Unbox(Seq#Index(s#0, i#1)): int);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures (forall i#3: int, j#1: int :: 
    { $Unbox(Seq#Index(s#0, j#1)): int, $Unbox(Seq#Index(s#0, i#3)): int } 
    (forall i$ih#1#0: int, j$ih#1#0: int :: 
          { $Unbox(Seq#Index(s#0, j$ih#1#0)): int, $Unbox(Seq#Index(s#0, i$ih#1#0)): int } 
          true
             ==> 
            (0 <= i$ih#1#0 && i$ih#1#0 < i#3)
               || (i$ih#1#0 == i#3 && 0 <= j$ih#1#0 && j$ih#1#0 < j#1)
             ==> 
            LitInt(0) <= i$ih#1#0 && i$ih#1#0 < j$ih#1#0 && j$ih#1#0 < Seq#Length(s#0)
             ==> $Unbox(Seq#Index(s#0, i$ih#1#0)): int <= $Unbox(Seq#Index(s#0, j$ih#1#0)): int)
         && true
       ==> 
      LitInt(0) <= i#3 && i#3 < j#1 && j#1 < Seq#Length(s#0)
       ==> $Unbox(Seq#Index(s#0, i#3)): int <= $Unbox(Seq#Index(s#0, j#1)): int);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.Fill__All(s#0: Seq Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Fill_All, Impl$$_module.__default.Fill__All
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(228,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.Fill__True(s#0: Seq Box where $Is(s#0, TSeq(TInt)) && $IsAlloc(s#0, TSeq(TInt), $Heap));
  free requires 45 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Fill__True(s#0: Seq Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var i#0: int;
  var i#2: int;
  var j#0: int;

    // AddMethodImpl: Fill_True, CheckWellformed$$_module.__default.Fill__True
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(231,13): initial state"} true;
    havoc i#0;
    assume true;
    if (*)
    {
        assume LitInt(1) <= i#0;
        assume i#0 < Seq#Length(s#0);
        assert 0 <= i#0 - 1 && i#0 - 1 < Seq#Length(s#0);
        assert 0 <= i#0 && i#0 < Seq#Length(s#0);
        assume $Unbox(Seq#Index(s#0, i#0 - 1)): int <= $Unbox(Seq#Index(s#0, i#0)): int;
    }
    else
    {
        assume LitInt(1) <= i#0 && i#0 < Seq#Length(s#0)
           ==> $Unbox(Seq#Index(s#0, i#0 - 1)): int <= $Unbox(Seq#Index(s#0, i#0)): int;
    }

    assume (forall i#1: int, _t#0#0: int :: 
      { $Unbox(Seq#Index(s#0, i#1)): int, $Unbox(Seq#Index(s#0, _t#0#0)): int } 
      _t#0#0 == i#1 - 1
         ==> 
        LitInt(1) <= i#1 && i#1 < Seq#Length(s#0)
         ==> $Unbox(Seq#Index(s#0, _t#0#0)): int <= $Unbox(Seq#Index(s#0, i#1)): int);
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(233,10): post-state"} true;
    havoc i#2;
    havoc j#0;
    assume true;
    if (*)
    {
        assume LitInt(0) <= i#2;
        assume i#2 < j#0;
        assume j#0 < Seq#Length(s#0);
        assert 0 <= i#2 && i#2 < Seq#Length(s#0);
        assert 0 <= j#0 && j#0 < Seq#Length(s#0);
        assume $Unbox(Seq#Index(s#0, i#2)): int <= $Unbox(Seq#Index(s#0, j#0)): int;
    }
    else
    {
        assume LitInt(0) <= i#2 && i#2 < j#0 && j#0 < Seq#Length(s#0)
           ==> $Unbox(Seq#Index(s#0, i#2)): int <= $Unbox(Seq#Index(s#0, j#0)): int;
    }

    assume (forall i#3: int, j#1: int :: 
      {:induction} {:_induction i#3, j#1} { $Unbox(Seq#Index(s#0, j#1)): int, $Unbox(Seq#Index(s#0, i#3)): int } 
      true
         ==> 
        LitInt(0) <= i#3 && i#3 < j#1 && j#1 < Seq#Length(s#0)
         ==> $Unbox(Seq#Index(s#0, i#3)): int <= $Unbox(Seq#Index(s#0, j#1)): int);
}



procedure Call$$_module.__default.Fill__True(s#0: Seq Box where $Is(s#0, TSeq(TInt)) && $IsAlloc(s#0, TSeq(TInt), $Heap));
  // user-defined preconditions
  requires (forall i#1: int, _t#0#0: int :: 
    { $Unbox(Seq#Index(s#0, i#1)): int, $Unbox(Seq#Index(s#0, _t#0#0)): int } 
    _t#0#0 == i#1 - 1
       ==> 
      LitInt(1) <= i#1 && i#1 < Seq#Length(s#0)
       ==> $Unbox(Seq#Index(s#0, _t#0#0)): int <= $Unbox(Seq#Index(s#0, i#1)): int);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  free ensures (forall i#3: int, j#1: int :: 
    {:induction} {:_induction i#3, j#1} { $Unbox(Seq#Index(s#0, j#1)): int, $Unbox(Seq#Index(s#0, i#3)): int } 
    true
       ==> 
      LitInt(0) <= i#3 && i#3 < j#1 && j#1 < Seq#Length(s#0)
       ==> $Unbox(Seq#Index(s#0, i#3)): int <= $Unbox(Seq#Index(s#0, j#1)): int);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.Fill__True(s#0: Seq Box where $Is(s#0, TSeq(TInt)) && $IsAlloc(s#0, TSeq(TInt), $Heap))
   returns ($_reverifyPost: bool);
  free requires 45 == $FunctionContextHeight;
  // user-defined preconditions
  requires (forall i#1: int, _t#0#0: int :: 
    { $Unbox(Seq#Index(s#0, i#1)): int, $Unbox(Seq#Index(s#0, _t#0#0)): int } 
    _t#0#0 == i#1 - 1
       ==> 
      LitInt(1) <= i#1 && i#1 < Seq#Length(s#0)
       ==> $Unbox(Seq#Index(s#0, _t#0#0)): int <= $Unbox(Seq#Index(s#0, i#1)): int);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures (forall i#3: int, j#1: int :: 
    { $Unbox(Seq#Index(s#0, j#1)): int, $Unbox(Seq#Index(s#0, i#3)): int } 
    (forall i$ih#1#0: int, j$ih#1#0: int :: 
          { $Unbox(Seq#Index(s#0, j$ih#1#0)): int, $Unbox(Seq#Index(s#0, i$ih#1#0)): int } 
          true
             ==> 
            (0 <= i$ih#1#0 && i$ih#1#0 < i#3)
               || (i$ih#1#0 == i#3 && 0 <= j$ih#1#0 && j$ih#1#0 < j#1)
             ==> 
            LitInt(0) <= i$ih#1#0 && i$ih#1#0 < j$ih#1#0 && j$ih#1#0 < Seq#Length(s#0)
             ==> $Unbox(Seq#Index(s#0, i$ih#1#0)): int <= $Unbox(Seq#Index(s#0, j$ih#1#0)): int)
         && true
       ==> 
      LitInt(0) <= i#3 && i#3 < j#1 && j#1 < Seq#Length(s#0)
       ==> $Unbox(Seq#Index(s#0, i#3)): int <= $Unbox(Seq#Index(s#0, j#1)): int);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.Fill__True(s#0: Seq Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Fill_True, Impl$$_module.__default.Fill__True
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(234,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.Fill__False(s#0: Seq Box where $Is(s#0, TSeq(TInt)) && $IsAlloc(s#0, TSeq(TInt), $Heap));
  free requires 46 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Fill__False(s#0: Seq Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var i#0: int;
  var i#2: int;
  var j#0: int;

    // AddMethodImpl: Fill_False, CheckWellformed$$_module.__default.Fill__False
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(237,13): initial state"} true;
    havoc i#0;
    assume true;
    if (*)
    {
        assume LitInt(1) <= i#0;
        assume i#0 < Seq#Length(s#0);
        assert 0 <= i#0 - 1 && i#0 - 1 < Seq#Length(s#0);
        assert 0 <= i#0 && i#0 < Seq#Length(s#0);
        assume $Unbox(Seq#Index(s#0, i#0 - 1)): int <= $Unbox(Seq#Index(s#0, i#0)): int;
    }
    else
    {
        assume LitInt(1) <= i#0 && i#0 < Seq#Length(s#0)
           ==> $Unbox(Seq#Index(s#0, i#0 - 1)): int <= $Unbox(Seq#Index(s#0, i#0)): int;
    }

    assume (forall i#1: int, _t#0#0: int :: 
      { $Unbox(Seq#Index(s#0, i#1)): int, $Unbox(Seq#Index(s#0, _t#0#0)): int } 
      _t#0#0 == i#1 - 1
         ==> 
        LitInt(1) <= i#1 && i#1 < Seq#Length(s#0)
         ==> $Unbox(Seq#Index(s#0, _t#0#0)): int <= $Unbox(Seq#Index(s#0, i#1)): int);
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(239,10): post-state"} true;
    havoc i#2;
    havoc j#0;
    assume true;
    if (*)
    {
        assume LitInt(0) <= i#2;
        assume i#2 < j#0;
        assume j#0 < Seq#Length(s#0);
        assert 0 <= i#2 && i#2 < Seq#Length(s#0);
        assert 0 <= j#0 && j#0 < Seq#Length(s#0);
        assume $Unbox(Seq#Index(s#0, i#2)): int <= $Unbox(Seq#Index(s#0, j#0)): int;
    }
    else
    {
        assume LitInt(0) <= i#2 && i#2 < j#0 && j#0 < Seq#Length(s#0)
           ==> $Unbox(Seq#Index(s#0, i#2)): int <= $Unbox(Seq#Index(s#0, j#0)): int;
    }

    assume (forall i#3: int, j#1: int :: 
      {:induction false} { $Unbox(Seq#Index(s#0, j#1)): int, $Unbox(Seq#Index(s#0, i#3)): int } 
      true
         ==> 
        LitInt(0) <= i#3 && i#3 < j#1 && j#1 < Seq#Length(s#0)
         ==> $Unbox(Seq#Index(s#0, i#3)): int <= $Unbox(Seq#Index(s#0, j#1)): int);
}



procedure Call$$_module.__default.Fill__False(s#0: Seq Box where $Is(s#0, TSeq(TInt)) && $IsAlloc(s#0, TSeq(TInt), $Heap));
  // user-defined preconditions
  requires (forall i#1: int, _t#0#0: int :: 
    { $Unbox(Seq#Index(s#0, i#1)): int, $Unbox(Seq#Index(s#0, _t#0#0)): int } 
    _t#0#0 == i#1 - 1
       ==> 
      LitInt(1) <= i#1 && i#1 < Seq#Length(s#0)
       ==> $Unbox(Seq#Index(s#0, _t#0#0)): int <= $Unbox(Seq#Index(s#0, i#1)): int);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures (forall i#3: int, j#1: int :: 
    {:induction false} { $Unbox(Seq#Index(s#0, j#1)): int, $Unbox(Seq#Index(s#0, i#3)): int } 
    true
       ==> 
      LitInt(0) <= i#3 && i#3 < j#1 && j#1 < Seq#Length(s#0)
       ==> $Unbox(Seq#Index(s#0, i#3)): int <= $Unbox(Seq#Index(s#0, j#1)): int);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.Fill__False(s#0: Seq Box where $Is(s#0, TSeq(TInt)) && $IsAlloc(s#0, TSeq(TInt), $Heap))
   returns ($_reverifyPost: bool);
  free requires 46 == $FunctionContextHeight;
  // user-defined preconditions
  requires (forall i#1: int, _t#0#0: int :: 
    { $Unbox(Seq#Index(s#0, i#1)): int, $Unbox(Seq#Index(s#0, _t#0#0)): int } 
    _t#0#0 == i#1 - 1
       ==> 
      LitInt(1) <= i#1 && i#1 < Seq#Length(s#0)
       ==> $Unbox(Seq#Index(s#0, _t#0#0)): int <= $Unbox(Seq#Index(s#0, i#1)): int);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures (forall i#3: int, j#1: int :: 
    {:induction false} { $Unbox(Seq#Index(s#0, j#1)): int, $Unbox(Seq#Index(s#0, i#3)): int } 
    true
       ==> 
      LitInt(0) <= i#3 && i#3 < j#1 && j#1 < Seq#Length(s#0)
       ==> $Unbox(Seq#Index(s#0, i#3)): int <= $Unbox(Seq#Index(s#0, j#1)): int);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.Fill__False(s#0: Seq Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Fill_False, Impl$$_module.__default.Fill__False
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(240,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.Fill__None(s#0: Seq Box where $Is(s#0, TSeq(TInt)) && $IsAlloc(s#0, TSeq(TInt), $Heap));
  free requires 47 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Fill__None(s#0: Seq Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var i#0: int;
  var i#2: int;
  var j#0: int;

    // AddMethodImpl: Fill_None, CheckWellformed$$_module.__default.Fill__None
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(243,13): initial state"} true;
    havoc i#0;
    assume true;
    if (*)
    {
        assume LitInt(1) <= i#0;
        assume i#0 < Seq#Length(s#0);
        assert 0 <= i#0 - 1 && i#0 - 1 < Seq#Length(s#0);
        assert 0 <= i#0 && i#0 < Seq#Length(s#0);
        assume $Unbox(Seq#Index(s#0, i#0 - 1)): int <= $Unbox(Seq#Index(s#0, i#0)): int;
    }
    else
    {
        assume LitInt(1) <= i#0 && i#0 < Seq#Length(s#0)
           ==> $Unbox(Seq#Index(s#0, i#0 - 1)): int <= $Unbox(Seq#Index(s#0, i#0)): int;
    }

    assume (forall i#1: int, _t#0#0: int :: 
      { $Unbox(Seq#Index(s#0, i#1)): int, $Unbox(Seq#Index(s#0, _t#0#0)): int } 
      _t#0#0 == i#1 - 1
         ==> 
        LitInt(1) <= i#1 && i#1 < Seq#Length(s#0)
         ==> $Unbox(Seq#Index(s#0, _t#0#0)): int <= $Unbox(Seq#Index(s#0, i#1)): int);
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(245,10): post-state"} true;
    havoc i#2;
    havoc j#0;
    assume true;
    if (*)
    {
        assume LitInt(0) <= i#2;
        assume i#2 < j#0;
        assume j#0 < Seq#Length(s#0);
        assert 0 <= i#2 && i#2 < Seq#Length(s#0);
        assert 0 <= j#0 && j#0 < Seq#Length(s#0);
        assume $Unbox(Seq#Index(s#0, i#2)): int <= $Unbox(Seq#Index(s#0, j#0)): int;
    }
    else
    {
        assume LitInt(0) <= i#2 && i#2 < j#0 && j#0 < Seq#Length(s#0)
           ==> $Unbox(Seq#Index(s#0, i#2)): int <= $Unbox(Seq#Index(s#0, j#0)): int;
    }

    assume (forall i#3: int, j#1: int :: 
      { $Unbox(Seq#Index(s#0, j#1)): int, $Unbox(Seq#Index(s#0, i#3)): int } 
      true
         ==> 
        LitInt(0) <= i#3 && i#3 < j#1 && j#1 < Seq#Length(s#0)
         ==> $Unbox(Seq#Index(s#0, i#3)): int <= $Unbox(Seq#Index(s#0, j#1)): int);
}



procedure Call$$_module.__default.Fill__None(s#0: Seq Box where $Is(s#0, TSeq(TInt)) && $IsAlloc(s#0, TSeq(TInt), $Heap));
  // user-defined preconditions
  requires (forall i#1: int, _t#0#0: int :: 
    { $Unbox(Seq#Index(s#0, i#1)): int, $Unbox(Seq#Index(s#0, _t#0#0)): int } 
    _t#0#0 == i#1 - 1
       ==> 
      LitInt(1) <= i#1 && i#1 < Seq#Length(s#0)
       ==> $Unbox(Seq#Index(s#0, _t#0#0)): int <= $Unbox(Seq#Index(s#0, i#1)): int);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures (forall i#3: int, j#1: int :: 
    { $Unbox(Seq#Index(s#0, j#1)): int, $Unbox(Seq#Index(s#0, i#3)): int } 
    true
       ==> 
      LitInt(0) <= i#3 && i#3 < j#1 && j#1 < Seq#Length(s#0)
       ==> $Unbox(Seq#Index(s#0, i#3)): int <= $Unbox(Seq#Index(s#0, j#1)): int);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.Fill__None(s#0: Seq Box where $Is(s#0, TSeq(TInt)) && $IsAlloc(s#0, TSeq(TInt), $Heap))
   returns ($_reverifyPost: bool);
  free requires 47 == $FunctionContextHeight;
  // user-defined preconditions
  requires (forall i#1: int, _t#0#0: int :: 
    { $Unbox(Seq#Index(s#0, i#1)): int, $Unbox(Seq#Index(s#0, _t#0#0)): int } 
    _t#0#0 == i#1 - 1
       ==> 
      LitInt(1) <= i#1 && i#1 < Seq#Length(s#0)
       ==> $Unbox(Seq#Index(s#0, _t#0#0)): int <= $Unbox(Seq#Index(s#0, i#1)): int);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures (forall i#3: int, j#1: int :: 
    { $Unbox(Seq#Index(s#0, j#1)): int, $Unbox(Seq#Index(s#0, i#3)): int } 
    true
       ==> 
      LitInt(0) <= i#3 && i#3 < j#1 && j#1 < Seq#Length(s#0)
       ==> $Unbox(Seq#Index(s#0, i#3)): int <= $Unbox(Seq#Index(s#0, j#1)): int);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.Fill__None(s#0: Seq Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Fill_None, Impl$$_module.__default.Fill__None
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(246,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.Test__ArrayElementLhsOfCall(a#0: ref
       where $Is(a#0, Tclass._System.array(Tclass._System.nat()))
         && $IsAlloc(a#0, Tclass._System.array(Tclass._System.nat()), $Heap), 
    i#0: int, 
    c#0: ref
       where $Is(c#0, Tclass._module.Cdefg(Tclass._System.nat()))
         && $IsAlloc(c#0, Tclass._module.Cdefg(Tclass._System.nat()), $Heap))
   returns (x#0: int);
  free requires 22 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Test__ArrayElementLhsOfCall(a#0: ref
       where $Is(a#0, Tclass._System.array(Tclass._System.nat()))
         && $IsAlloc(a#0, Tclass._System.array(Tclass._System.nat()), $Heap), 
    i#0: int, 
    c#0: ref
       where $Is(c#0, Tclass._module.Cdefg(Tclass._System.nat()))
         && $IsAlloc(c#0, Tclass._module.Cdefg(Tclass._System.nat()), $Heap))
   returns (x#0: int);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == a#0 || $o == c#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.Test__ArrayElementLhsOfCall(a#0: ref
       where $Is(a#0, Tclass._System.array(Tclass._System.nat()))
         && $IsAlloc(a#0, Tclass._System.array(Tclass._System.nat()), $Heap), 
    i#0: int, 
    c#0: ref
       where $Is(c#0, Tclass._module.Cdefg(Tclass._System.nat()))
         && $IsAlloc(c#0, Tclass._module.Cdefg(Tclass._System.nat()), $Heap))
   returns (x#0: int, $_reverifyPost: bool);
  free requires 22 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == a#0 || $o == c#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.Test__ArrayElementLhsOfCall(a#0: ref, i#0: int, c#0: ref) returns (x#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0_0: int where LitInt(0) <= $rhs#0_0;
  var $obj0: ref;
  var $index0: Field Box;
  var $rhs##0_0: int;
  var a##0_0: ref;
  var i##0_0: int;
  var c##0_0: ref;
  var $rhs#0_1: int where LitInt(0) <= $rhs#0_1;
  var $rhs##0_1: int;
  var a##0_1: ref;
  var i##0_1: int;
  var c##0_1: ref;
  var n#0_0: int where LitInt(0) <= n#0_0;
  var $rhs##0_2: int;
  var a##0_2: ref;
  var i##0_2: int;
  var c##0_2: ref;

    // AddMethodImpl: Test_ArrayElementLhsOfCall, Impl$$_module.__default.Test__ArrayElementLhsOfCall
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == a#0 || $o == c#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(253,0): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(254,3)
    if (LitInt(0) <= i#0)
    {
        assert a#0 != null;
    }

    assume true;
    if (LitInt(0) <= i#0 && i#0 < _System.array.Length(a#0))
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(255,10)
        assert a#0 != null;
        assert 0 <= i#0 && i#0 < _System.array.Length(a#0);
        assume true;
        assert $_Frame[a#0, IndexField(i#0)];
        assume true;
        assert $Is(x#0, Tclass._System.nat());
        $rhs#0_0 := x#0;
        $Heap := update($Heap, a#0, IndexField(i#0), $Box($rhs#0_0));
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(255,13)"} true;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(256,39)
        assert a#0 != null;
        assert 0 <= i#0 && i#0 < _System.array.Length(a#0);
        assume true;
        $obj0 := a#0;
        $index0 := IndexField(i#0);
        assert $_Frame[$obj0, $index0];
        // TrCallStmt: Adding lhs with type nat
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        a##0_0 := a#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        i##0_0 := i#0 - 1;
        assume true;
        // ProcessCallStmt: CheckSubrange
        c##0_0 := c#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) && ($o == a##0_0 || $o == c##0_0)
             ==> $_Frame[$o, $f]);
        assert 0 <= i#0 || (a##0_0 == null && a#0 != null) || i##0_0 == i#0;
        assert (a##0_0 == null && a#0 != null)
           || ((a##0_0 != null <==> a#0 != null)
             && (i##0_0 < i#0 || (i##0_0 == i#0 && c##0_0 == null && c#0 != null)));
        // ProcessCallStmt: Make the call
        call $rhs##0_0 := Call$$_module.__default.Test__ArrayElementLhsOfCall(a##0_0, i##0_0, c##0_0);
        // TrCallStmt: After ProcessCallStmt
        assert $Is($rhs##0_0, Tclass._System.nat());
        $Heap := update($Heap, $obj0, $index0, $Box($rhs##0_0));
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(256,49)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(257,9)
        assert c#0 != null;
        assume true;
        assert $_Frame[c#0, _module.Cdefg.t];
        assume true;
        assert $Is(x#0 - 1, Tclass._System.nat());
        $rhs#0_1 := x#0 - 1;
        $Heap := update($Heap, c#0, _module.Cdefg.t, $Box($rhs#0_1));
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(257,14)"} true;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(258,38)
        assert c#0 != null;
        assume true;
        $obj0 := c#0;
        assert $_Frame[$obj0, _module.Cdefg.t];
        // TrCallStmt: Adding lhs with type nat
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        a##0_1 := a#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        i##0_1 := i#0 - 1;
        assume true;
        // ProcessCallStmt: CheckSubrange
        c##0_1 := c#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) && ($o == a##0_1 || $o == c##0_1)
             ==> $_Frame[$o, $f]);
        assert 0 <= i#0 || (a##0_1 == null && a#0 != null) || i##0_1 == i#0;
        assert (a##0_1 == null && a#0 != null)
           || ((a##0_1 != null <==> a#0 != null)
             && (i##0_1 < i#0 || (i##0_1 == i#0 && c##0_1 == null && c#0 != null)));
        // ProcessCallStmt: Make the call
        call $rhs##0_1 := Call$$_module.__default.Test__ArrayElementLhsOfCall(a##0_1, i##0_1, c##0_1);
        // TrCallStmt: After ProcessCallStmt
        assert $Is($rhs##0_1, Tclass._System.nat());
        $Heap := update($Heap, $obj0, _module.Cdefg.t, $Box($rhs##0_1));
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(258,48)"} true;
        havoc n#0_0 /* where LitInt(0) <= n#0_0 */;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(260,36)
        assume true;
        // TrCallStmt: Adding lhs with type nat
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        a##0_2 := a#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        i##0_2 := i#0 - 1;
        assume true;
        // ProcessCallStmt: CheckSubrange
        c##0_2 := c#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) && ($o == a##0_2 || $o == c##0_2)
             ==> $_Frame[$o, $f]);
        assert 0 <= i#0 || (a##0_2 == null && a#0 != null) || i##0_2 == i#0;
        assert (a##0_2 == null && a#0 != null)
           || ((a##0_2 != null <==> a#0 != null)
             && (i##0_2 < i#0 || (i##0_2 == i#0 && c##0_2 == null && c#0 != null)));
        // ProcessCallStmt: Make the call
        call $rhs##0_2 := Call$$_module.__default.Test__ArrayElementLhsOfCall(a##0_2, i##0_2, c##0_2);
        // TrCallStmt: After ProcessCallStmt
        assert $Is($rhs##0_2, Tclass._System.nat());
        n#0_0 := $rhs##0_2;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(260,46)"} true;
    }
    else
    {
    }
}



procedure CheckWellformed$$_module.__default.AllocationBusiness0(a#0: ref
       where $Is(a#0, Tclass._System.array(Tclass._module.MyClass()))
         && $IsAlloc(a#0, Tclass._System.array(Tclass._module.MyClass()), $Heap), 
    j#0: int);
  free requires 24 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.AllocationBusiness0(a#0: ref, j#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: AllocationBusiness0, CheckWellformed$$_module.__default.AllocationBusiness0
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(279,7): initial state"} true;
    if (LitInt(0) <= j#0)
    {
        assert a#0 != null;
    }

    assume LitInt(0) <= j#0 && j#0 < _System.array.Length(a#0);
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
    assume $HeapSucc(old($Heap), $Heap);
}



procedure Call$$_module.__default.AllocationBusiness0(a#0: ref
       where $Is(a#0, Tclass._System.array(Tclass._module.MyClass()))
         && $IsAlloc(a#0, Tclass._System.array(Tclass._module.MyClass()), $Heap), 
    j#0: int);
  // user-defined preconditions
  requires LitInt(0) <= j#0;
  requires j#0 < _System.array.Length(a#0);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.AllocationBusiness0(a#0: ref
       where $Is(a#0, Tclass._System.array(Tclass._module.MyClass()))
         && $IsAlloc(a#0, Tclass._System.array(Tclass._module.MyClass()), $Heap), 
    j#0: int)
   returns ($_reverifyPost: bool);
  free requires 24 == $FunctionContextHeight;
  // user-defined preconditions
  requires LitInt(0) <= j#0;
  requires j#0 < _System.array.Length(a#0);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.AllocationBusiness0(a#0: ref, j#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var c#0: ref
     where $Is(c#0, Tclass._module.MyClass())
       && $IsAlloc(c#0, Tclass._module.MyClass(), $Heap);
  var $nw: ref;

    // AddMethodImpl: AllocationBusiness0, Impl$$_module.__default.AllocationBusiness0
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(281,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(282,9)
    assume true;
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._module.MyClass?();
    assume !read($Heap, $nw, alloc);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    c#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(282,22)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(283,3)
    assert a#0 != null;
    assert {:subsumption 0} 0 <= j#0 && j#0 < _System.array.Length(a#0);
    assert {:subsumption 0} $Unbox(read($Heap, a#0, IndexField(j#0))): ref != null;
    assume true;
    assert !read($Heap, $Unbox(read($Heap, a#0, IndexField(j#0))): ref, _module.MyClass.Repr)[$Box(c#0)];
}



procedure CheckWellformed$$_module.__default.AllocationBusiness1(a#0: ref
       where $Is(a#0, Tclass._System.array(Tclass._module.MyClass()))
         && $IsAlloc(a#0, Tclass._System.array(Tclass._module.MyClass()), $Heap), 
    j#0: int);
  free requires 26 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.AllocationBusiness1(a#0: ref, j#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: AllocationBusiness1, CheckWellformed$$_module.__default.AllocationBusiness1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(286,7): initial state"} true;
    if (LitInt(0) <= j#0)
    {
        assert a#0 != null;
    }

    assume LitInt(0) <= j#0 && j#0 < _System.array.Length(a#0);
    assert a#0 != null;
    assert 0 <= j#0 && j#0 < _System.array.Length(a#0);
    assert $Unbox(read($Heap, a#0, IndexField(j#0))): ref != null;
    assume _module.MyClass.Valid#canCall($Heap, $Unbox(read($Heap, a#0, IndexField(j#0))): ref);
    assume _module.MyClass.Valid($Heap, $Unbox(read($Heap, a#0, IndexField(j#0))): ref);
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
    assume $HeapSucc(old($Heap), $Heap);
}



procedure Call$$_module.__default.AllocationBusiness1(a#0: ref
       where $Is(a#0, Tclass._System.array(Tclass._module.MyClass()))
         && $IsAlloc(a#0, Tclass._System.array(Tclass._module.MyClass()), $Heap), 
    j#0: int);
  // user-defined preconditions
  requires LitInt(0) <= j#0;
  requires j#0 < _System.array.Length(a#0);
  requires _module.MyClass.Valid($Heap, $Unbox(read($Heap, a#0, IndexField(j#0))): ref);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.AllocationBusiness1(a#0: ref
       where $Is(a#0, Tclass._System.array(Tclass._module.MyClass()))
         && $IsAlloc(a#0, Tclass._System.array(Tclass._module.MyClass()), $Heap), 
    j#0: int)
   returns ($_reverifyPost: bool);
  free requires 26 == $FunctionContextHeight;
  // user-defined preconditions
  requires LitInt(0) <= j#0;
  requires j#0 < _System.array.Length(a#0);
  requires _module.MyClass.Valid($Heap, $Unbox(read($Heap, a#0, IndexField(j#0))): ref);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.AllocationBusiness1(a#0: ref, j#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var c#0: ref
     where $Is(c#0, Tclass._module.MyClass())
       && $IsAlloc(c#0, Tclass._module.MyClass(), $Heap);
  var $nw: ref;

    // AddMethodImpl: AllocationBusiness1, Impl$$_module.__default.AllocationBusiness1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(289,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(290,9)
    assume true;
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._module.MyClass?();
    assume !read($Heap, $nw, alloc);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    c#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(290,22)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(291,3)
    assert a#0 != null;
    assert {:subsumption 0} 0 <= j#0 && j#0 < _System.array.Length(a#0);
    assert {:subsumption 0} $Unbox(read($Heap, a#0, IndexField(j#0))): ref != null;
    assume _module.MyClass.Valid#canCall($Heap, $Unbox(read($Heap, a#0, IndexField(j#0))): ref);
    assume _module.MyClass.Valid#canCall($Heap, $Unbox(read($Heap, a#0, IndexField(j#0))): ref);
    assert _module.MyClass.Valid($Heap, $Unbox(read($Heap, a#0, IndexField(j#0))): ref);
}



procedure CheckWellformed$$_module.__default.AllocationBusiness2(a#0: ref
       where $Is(a#0, Tclass._System.array2(Tclass._module.MyClass()))
         && $IsAlloc(a#0, Tclass._System.array2(Tclass._module.MyClass()), $Heap), 
    i#0: int, 
    j#0: int);
  free requires 28 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.AllocationBusiness2(a#0: ref, i#0: int, j#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: AllocationBusiness2, CheckWellformed$$_module.__default.AllocationBusiness2
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(294,7): initial state"} true;
    if (LitInt(0) <= i#0)
    {
        assert a#0 != null;
    }

    assume LitInt(0) <= i#0 && i#0 < _System.array2.Length0(a#0);
    if (LitInt(0) <= j#0)
    {
        assert a#0 != null;
    }

    assume LitInt(0) <= j#0 && j#0 < _System.array2.Length1(a#0);
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
    assume $HeapSucc(old($Heap), $Heap);
}



procedure Call$$_module.__default.AllocationBusiness2(a#0: ref
       where $Is(a#0, Tclass._System.array2(Tclass._module.MyClass()))
         && $IsAlloc(a#0, Tclass._System.array2(Tclass._module.MyClass()), $Heap), 
    i#0: int, 
    j#0: int);
  // user-defined preconditions
  requires LitInt(0) <= i#0;
  requires i#0 < _System.array2.Length0(a#0);
  requires LitInt(0) <= j#0;
  requires j#0 < _System.array2.Length1(a#0);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.AllocationBusiness2(a#0: ref
       where $Is(a#0, Tclass._System.array2(Tclass._module.MyClass()))
         && $IsAlloc(a#0, Tclass._System.array2(Tclass._module.MyClass()), $Heap), 
    i#0: int, 
    j#0: int)
   returns ($_reverifyPost: bool);
  free requires 28 == $FunctionContextHeight;
  // user-defined preconditions
  requires LitInt(0) <= i#0;
  requires i#0 < _System.array2.Length0(a#0);
  requires LitInt(0) <= j#0;
  requires j#0 < _System.array2.Length1(a#0);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.AllocationBusiness2(a#0: ref, i#0: int, j#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var c#0: ref
     where $Is(c#0, Tclass._module.MyClass())
       && $IsAlloc(c#0, Tclass._module.MyClass(), $Heap);
  var $nw: ref;

    // AddMethodImpl: AllocationBusiness2, Impl$$_module.__default.AllocationBusiness2
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(296,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(297,9)
    assume true;
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._module.MyClass?();
    assume !read($Heap, $nw, alloc);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    c#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(297,22)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Array.dfy(298,3)
    assert a#0 != null;
    assert {:subsumption 0} 0 <= i#0 && i#0 < _System.array2.Length0(a#0);
    assert {:subsumption 0} 0 <= j#0 && j#0 < _System.array2.Length1(a#0);
    assert {:subsumption 0} $Unbox(read($Heap, a#0, MultiIndexField(IndexField(i#0), j#0))): ref != null;
    assume true;
    assert !read($Heap, 
      $Unbox(read($Heap, a#0, MultiIndexField(IndexField(i#0), j#0))): ref, 
      _module.MyClass.Repr)[$Box(c#0)];
}



const unique class.DtypeRegression.__default: ClassName;

function Tclass.DtypeRegression.__default() : Ty;

const unique Tagclass.DtypeRegression.__default: TyTag;

// Tclass.DtypeRegression.__default Tag
axiom Tag(Tclass.DtypeRegression.__default()) == Tagclass.DtypeRegression.__default
   && TagFamily(Tclass.DtypeRegression.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.DtypeRegression.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.DtypeRegression.__default()) } 
  $IsBox(bx, Tclass.DtypeRegression.__default())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.DtypeRegression.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.DtypeRegression.__default()) } 
  $Is($o, Tclass.DtypeRegression.__default())
     <==> $o == null || dtype($o) == Tclass.DtypeRegression.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.DtypeRegression.__default(), $h) } 
  $IsAlloc($o, Tclass.DtypeRegression.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

// function declaration for DtypeRegression._default.array_equal
function DtypeRegression.__default.array__equal($heap: Heap, a#0: ref, b#0: ref) : bool;

function DtypeRegression.__default.array__equal#canCall($heap: Heap, a#0: ref, b#0: ref) : bool;

// frame axiom for DtypeRegression.__default.array__equal
axiom (forall $h0: Heap, $h1: Heap, a#0: ref, b#0: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), DtypeRegression.__default.array__equal($h1, a#0, b#0) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && (DtypeRegression.__default.array__equal#canCall($h0, a#0, b#0)
         || ($Is(a#0, Tclass._System.array(TInt)) && $Is(b#0, Tclass._System.array(TInt))))
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && ($o == a#0 || $o == b#0)
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> DtypeRegression.__default.array__equal($h0, a#0, b#0)
       == DtypeRegression.__default.array__equal($h1, a#0, b#0));

// consequence axiom for DtypeRegression.__default.array__equal
axiom true
   ==> (forall $Heap: Heap, a#0: ref, b#0: ref :: 
    { DtypeRegression.__default.array__equal($Heap, a#0, b#0) } 
    DtypeRegression.__default.array__equal#canCall($Heap, a#0, b#0)
         || (
          $IsGoodHeap($Heap)
           && $Is(a#0, Tclass._System.array(TInt))
           && $Is(b#0, Tclass._System.array(TInt)))
       ==> true);

function DtypeRegression.__default.array__equal#requires(Heap, ref, ref) : bool;

// #requires axiom for DtypeRegression.__default.array__equal
axiom (forall $Heap: Heap, a#0: ref, b#0: ref :: 
  { DtypeRegression.__default.array__equal#requires($Heap, a#0, b#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && $Is(a#0, Tclass._System.array(TInt))
       && $Is(b#0, Tclass._System.array(TInt))
     ==> DtypeRegression.__default.array__equal#requires($Heap, a#0, b#0) == true);

// definition axiom for DtypeRegression.__default.array__equal (revealed)
axiom true
   ==> (forall $Heap: Heap, a#0: ref, b#0: ref :: 
    { DtypeRegression.__default.array__equal($Heap, a#0, b#0), $IsGoodHeap($Heap) } 
    DtypeRegression.__default.array__equal#canCall($Heap, a#0, b#0)
         || (
          $IsGoodHeap($Heap)
           && $Is(a#0, Tclass._System.array(TInt))
           && $Is(b#0, Tclass._System.array(TInt)))
       ==> DtypeRegression.__default.array__equal($Heap, a#0, b#0)
         == Seq#Equal(Seq#FromArray($Heap, a#0), Seq#FromArray($Heap, b#0)));

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

const unique tytagFamily$array2: TyTagFamily;

const unique tytagFamily$_tuple#2: TyTagFamily;

const unique tytagFamily$_tuple#0: TyTagFamily;

const unique tytagFamily$A: TyTagFamily;

const unique tytagFamily$B: TyTagFamily;

const unique tytagFamily$ArrayTests: TyTagFamily;

const unique tytagFamily$Cdefg: TyTagFamily;

const unique tytagFamily$MyClass: TyTagFamily;

const unique tytagFamily$AssignSuchThat: TyTagFamily;

const unique tytagFamily$_default: TyTagFamily;

const unique field$zz0: NameFamily;

const unique field$zz1: NameFamily;

const unique field$x: NameFamily;

const unique field$b: NameFamily;

const unique field$t: NameFamily;

const unique field$Repr: NameFamily;
