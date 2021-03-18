// Dafny 3.0.0.30204
// Command Line Options: -compile:0 -noVerify /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy -print:./datatypes.bpl

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

procedure CheckWellformed$$_module.uint32(i#0: int);
  free requires 0 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.uint32(i#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;


    // AddWellformednessCheck for newtype uint32
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(4,8): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        if (LitInt(0) <= i#0)
        {
        }

        assume LitInt(0) <= i#0 && i#0 < 4294967296;
    }
    else
    {
        assume true;
        assert {:subsumption 0} LitInt(0) <= LitInt(0);
        assert {:subsumption 0} 0 < 4294967296;
    }
}



function Tclass._module.uint32() : Ty;

const unique Tagclass._module.uint32: TyTag;

// Tclass._module.uint32 Tag
axiom Tag(Tclass._module.uint32()) == Tagclass._module.uint32
   && TagFamily(Tclass._module.uint32()) == tytagFamily$uint32;

// Box/unbox axiom for Tclass._module.uint32
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.uint32()) } 
  $IsBox(bx, Tclass._module.uint32())
     ==> $Box($Unbox(bx): int) == bx && $Is($Unbox(bx): int, Tclass._module.uint32()));

// _module.uint32: newtype $Is
axiom (forall i#0: int :: 
  { $Is(i#0, Tclass._module.uint32()) } 
  $Is(i#0, Tclass._module.uint32()) <==> LitInt(0) <= i#0 && i#0 < 4294967296);

// _module.uint32: newtype $IsAlloc
axiom (forall i#0: int, $h: Heap :: 
  { $IsAlloc(i#0, Tclass._module.uint32(), $h) } 
  $IsAlloc(i#0, Tclass._module.uint32(), $h));

const unique class._module.uint32: ClassName;

// Constructor function declaration
function #_module.Op.NoOp() : DatatypeType;

const unique ##_module.Op.NoOp: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#_module.Op.NoOp()) == ##_module.Op.NoOp;

function _module.Op.NoOp_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Op.NoOp_q(d) } 
  _module.Op.NoOp_q(d) <==> DatatypeCtorId(d) == ##_module.Op.NoOp);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Op.NoOp_q(d) } 
  _module.Op.NoOp_q(d) ==> d == #_module.Op.NoOp());

function Tclass._module.Op() : Ty;

const unique Tagclass._module.Op: TyTag;

// Tclass._module.Op Tag
axiom Tag(Tclass._module.Op()) == Tagclass._module.Op
   && TagFamily(Tclass._module.Op()) == tytagFamily$Op;

// Box/unbox axiom for Tclass._module.Op
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Op()) } 
  $IsBox(bx, Tclass._module.Op())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Op()));

// Constructor $Is
axiom $Is(#_module.Op.NoOp(), Tclass._module.Op());

// Constructor $IsAlloc
axiom (forall $h: Heap :: 
  { $IsAlloc(#_module.Op.NoOp(), Tclass._module.Op(), $h) } 
  $IsGoodHeap($h) ==> $IsAlloc(#_module.Op.NoOp(), Tclass._module.Op(), $h));

// Constructor literal
axiom #_module.Op.NoOp() == Lit(#_module.Op.NoOp());

// Constructor function declaration
function #_module.Op.PushOp(int) : DatatypeType;

const unique ##_module.Op.PushOp: DtCtorId;

// Constructor identifier
axiom (forall a#5#0#0: int :: 
  { #_module.Op.PushOp(a#5#0#0) } 
  DatatypeCtorId(#_module.Op.PushOp(a#5#0#0)) == ##_module.Op.PushOp);

function _module.Op.PushOp_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Op.PushOp_q(d) } 
  _module.Op.PushOp_q(d) <==> DatatypeCtorId(d) == ##_module.Op.PushOp);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Op.PushOp_q(d) } 
  _module.Op.PushOp_q(d)
     ==> (exists a#6#0#0: int :: d == #_module.Op.PushOp(a#6#0#0)));

// Constructor $Is
axiom (forall a#7#0#0: int :: 
  { $Is(#_module.Op.PushOp(a#7#0#0), Tclass._module.Op()) } 
  $Is(#_module.Op.PushOp(a#7#0#0), Tclass._module.Op()) <==> $Is(a#7#0#0, TInt));

// Constructor $IsAlloc
axiom (forall a#8#0#0: int, $h: Heap :: 
  { $IsAlloc(#_module.Op.PushOp(a#8#0#0), Tclass._module.Op(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Op.PushOp(a#8#0#0), Tclass._module.Op(), $h)
       <==> $IsAlloc(a#8#0#0, TInt, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Op.id(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Op.PushOp_q(d)
       && $IsAlloc(d, Tclass._module.Op(), $h)
     ==> $IsAlloc(_module.Op.id(d), TInt, $h));

// Constructor literal
axiom (forall a#9#0#0: int :: 
  { #_module.Op.PushOp(LitInt(a#9#0#0)) } 
  #_module.Op.PushOp(LitInt(a#9#0#0)) == Lit(#_module.Op.PushOp(a#9#0#0)));

function _module.Op.id(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#10#0#0: int :: 
  { #_module.Op.PushOp(a#10#0#0) } 
  _module.Op.id(#_module.Op.PushOp(a#10#0#0)) == a#10#0#0);

// Depth-one case-split function
function $IsA#_module.Op(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.Op(d) } 
  $IsA#_module.Op(d) ==> _module.Op.NoOp_q(d) || _module.Op.PushOp_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.Op.PushOp_q(d), $Is(d, Tclass._module.Op()) } 
    { _module.Op.NoOp_q(d), $Is(d, Tclass._module.Op()) } 
  $Is(d, Tclass._module.Op()) ==> _module.Op.NoOp_q(d) || _module.Op.PushOp_q(d));

// Datatype extensional equality declaration
function _module.Op#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.Op.NoOp
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Op#Equal(a, b), _module.Op.NoOp_q(a) } 
    { _module.Op#Equal(a, b), _module.Op.NoOp_q(b) } 
  _module.Op.NoOp_q(a) && _module.Op.NoOp_q(b)
     ==> (_module.Op#Equal(a, b) <==> true));

// Datatype extensional equality definition: #_module.Op.PushOp
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Op#Equal(a, b), _module.Op.PushOp_q(a) } 
    { _module.Op#Equal(a, b), _module.Op.PushOp_q(b) } 
  _module.Op.PushOp_q(a) && _module.Op.PushOp_q(b)
     ==> (_module.Op#Equal(a, b) <==> _module.Op.id(a) == _module.Op.id(b)));

// Datatype extensionality axiom: _module.Op
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Op#Equal(a, b) } 
  _module.Op#Equal(a, b) <==> a == b);

const unique class._module.Op: ClassName;

// Constructor function declaration
function #_module.Example1.Example1(int, bool) : DatatypeType;

const unique ##_module.Example1.Example1: DtCtorId;

// Constructor identifier
axiom (forall a#11#0#0: int, a#11#1#0: bool :: 
  { #_module.Example1.Example1(a#11#0#0, a#11#1#0) } 
  DatatypeCtorId(#_module.Example1.Example1(a#11#0#0, a#11#1#0))
     == ##_module.Example1.Example1);

function _module.Example1.Example1_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Example1.Example1_q(d) } 
  _module.Example1.Example1_q(d)
     <==> DatatypeCtorId(d) == ##_module.Example1.Example1);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Example1.Example1_q(d) } 
  _module.Example1.Example1_q(d)
     ==> (exists a#12#0#0: int, a#12#1#0: bool :: 
      d == #_module.Example1.Example1(a#12#0#0, a#12#1#0)));

function Tclass._module.Example1() : Ty;

const unique Tagclass._module.Example1: TyTag;

// Tclass._module.Example1 Tag
axiom Tag(Tclass._module.Example1()) == Tagclass._module.Example1
   && TagFamily(Tclass._module.Example1()) == tytagFamily$Example1;

// Box/unbox axiom for Tclass._module.Example1
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Example1()) } 
  $IsBox(bx, Tclass._module.Example1())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Example1()));

// Constructor $Is
axiom (forall a#13#0#0: int, a#13#1#0: bool :: 
  { $Is(#_module.Example1.Example1(a#13#0#0, a#13#1#0), Tclass._module.Example1()) } 
  $Is(#_module.Example1.Example1(a#13#0#0, a#13#1#0), Tclass._module.Example1())
     <==> $Is(a#13#0#0, Tclass._module.uint32()) && $Is(a#13#1#0, TBool));

// Constructor $IsAlloc
axiom (forall a#14#0#0: int, a#14#1#0: bool, $h: Heap :: 
  { $IsAlloc(#_module.Example1.Example1(a#14#0#0, a#14#1#0), Tclass._module.Example1(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Example1.Example1(a#14#0#0, a#14#1#0), Tclass._module.Example1(), $h)
       <==> $IsAlloc(a#14#0#0, Tclass._module.uint32(), $h) && $IsAlloc(a#14#1#0, TBool, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Example1.u(d), Tclass._module.uint32(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.Example1.Example1_q(d)
       && $IsAlloc(d, Tclass._module.Example1(), $h)
     ==> $IsAlloc(_module.Example1.u(d), Tclass._module.uint32(), $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Example1.b(d), TBool, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Example1.Example1_q(d)
       && $IsAlloc(d, Tclass._module.Example1(), $h)
     ==> $IsAlloc(_module.Example1.b(d), TBool, $h));

// Constructor literal
axiom (forall a#15#0#0: int, a#15#1#0: bool :: 
  { #_module.Example1.Example1(LitInt(a#15#0#0), Lit(a#15#1#0)) } 
  #_module.Example1.Example1(LitInt(a#15#0#0), Lit(a#15#1#0))
     == Lit(#_module.Example1.Example1(a#15#0#0, a#15#1#0)));

function _module.Example1.u(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#16#0#0: int, a#16#1#0: bool :: 
  { #_module.Example1.Example1(a#16#0#0, a#16#1#0) } 
  _module.Example1.u(#_module.Example1.Example1(a#16#0#0, a#16#1#0)) == a#16#0#0);

function _module.Example1.b(DatatypeType) : bool;

// Constructor injectivity
axiom (forall a#17#0#0: int, a#17#1#0: bool :: 
  { #_module.Example1.Example1(a#17#0#0, a#17#1#0) } 
  _module.Example1.b(#_module.Example1.Example1(a#17#0#0, a#17#1#0)) == a#17#1#0);

// Depth-one case-split function
function $IsA#_module.Example1(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.Example1(d) } 
  $IsA#_module.Example1(d) ==> _module.Example1.Example1_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.Example1.Example1_q(d), $Is(d, Tclass._module.Example1()) } 
  $Is(d, Tclass._module.Example1()) ==> _module.Example1.Example1_q(d));

// Datatype extensional equality declaration
function _module.Example1#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.Example1.Example1
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Example1#Equal(a, b) } 
  true
     ==> (_module.Example1#Equal(a, b)
       <==> _module.Example1.u(a) == _module.Example1.u(b)
         && _module.Example1.b(a) == _module.Example1.b(b)));

// Datatype extensionality axiom: _module.Example1
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Example1#Equal(a, b) } 
  _module.Example1#Equal(a, b) <==> a == b);

const unique class._module.Example1: ClassName;

// Constructor function declaration
function #_module.Example2.Ex2a(int) : DatatypeType;

const unique ##_module.Example2.Ex2a: DtCtorId;

// Constructor identifier
axiom (forall a#18#0#0: int :: 
  { #_module.Example2.Ex2a(a#18#0#0) } 
  DatatypeCtorId(#_module.Example2.Ex2a(a#18#0#0)) == ##_module.Example2.Ex2a);

function _module.Example2.Ex2a_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Example2.Ex2a_q(d) } 
  _module.Example2.Ex2a_q(d) <==> DatatypeCtorId(d) == ##_module.Example2.Ex2a);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Example2.Ex2a_q(d) } 
  _module.Example2.Ex2a_q(d)
     ==> (exists a#19#0#0: int :: d == #_module.Example2.Ex2a(a#19#0#0)));

function Tclass._module.Example2() : Ty;

const unique Tagclass._module.Example2: TyTag;

// Tclass._module.Example2 Tag
axiom Tag(Tclass._module.Example2()) == Tagclass._module.Example2
   && TagFamily(Tclass._module.Example2()) == tytagFamily$Example2;

// Box/unbox axiom for Tclass._module.Example2
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Example2()) } 
  $IsBox(bx, Tclass._module.Example2())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Example2()));

// Constructor $Is
axiom (forall a#20#0#0: int :: 
  { $Is(#_module.Example2.Ex2a(a#20#0#0), Tclass._module.Example2()) } 
  $Is(#_module.Example2.Ex2a(a#20#0#0), Tclass._module.Example2())
     <==> $Is(a#20#0#0, Tclass._module.uint32()));

// Constructor $IsAlloc
axiom (forall a#21#0#0: int, $h: Heap :: 
  { $IsAlloc(#_module.Example2.Ex2a(a#21#0#0), Tclass._module.Example2(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Example2.Ex2a(a#21#0#0), Tclass._module.Example2(), $h)
       <==> $IsAlloc(a#21#0#0, Tclass._module.uint32(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Example2.u(d), Tclass._module.uint32(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.Example2.Ex2a_q(d)
       && $IsAlloc(d, Tclass._module.Example2(), $h)
     ==> $IsAlloc(_module.Example2.u(d), Tclass._module.uint32(), $h));

// Constructor literal
axiom (forall a#22#0#0: int :: 
  { #_module.Example2.Ex2a(LitInt(a#22#0#0)) } 
  #_module.Example2.Ex2a(LitInt(a#22#0#0))
     == Lit(#_module.Example2.Ex2a(a#22#0#0)));

function _module.Example2.u(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#23#0#0: int :: 
  { #_module.Example2.Ex2a(a#23#0#0) } 
  _module.Example2.u(#_module.Example2.Ex2a(a#23#0#0)) == a#23#0#0);

// Constructor function declaration
function #_module.Example2.Ex2b(bool) : DatatypeType;

const unique ##_module.Example2.Ex2b: DtCtorId;

// Constructor identifier
axiom (forall a#24#0#0: bool :: 
  { #_module.Example2.Ex2b(a#24#0#0) } 
  DatatypeCtorId(#_module.Example2.Ex2b(a#24#0#0)) == ##_module.Example2.Ex2b);

function _module.Example2.Ex2b_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Example2.Ex2b_q(d) } 
  _module.Example2.Ex2b_q(d) <==> DatatypeCtorId(d) == ##_module.Example2.Ex2b);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Example2.Ex2b_q(d) } 
  _module.Example2.Ex2b_q(d)
     ==> (exists a#25#0#0: bool :: d == #_module.Example2.Ex2b(a#25#0#0)));

// Constructor $Is
axiom (forall a#26#0#0: bool :: 
  { $Is(#_module.Example2.Ex2b(a#26#0#0), Tclass._module.Example2()) } 
  $Is(#_module.Example2.Ex2b(a#26#0#0), Tclass._module.Example2())
     <==> $Is(a#26#0#0, TBool));

// Constructor $IsAlloc
axiom (forall a#27#0#0: bool, $h: Heap :: 
  { $IsAlloc(#_module.Example2.Ex2b(a#27#0#0), Tclass._module.Example2(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Example2.Ex2b(a#27#0#0), Tclass._module.Example2(), $h)
       <==> $IsAlloc(a#27#0#0, TBool, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Example2.b(d), TBool, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Example2.Ex2b_q(d)
       && $IsAlloc(d, Tclass._module.Example2(), $h)
     ==> $IsAlloc(_module.Example2.b(d), TBool, $h));

// Constructor literal
axiom (forall a#28#0#0: bool :: 
  { #_module.Example2.Ex2b(Lit(a#28#0#0)) } 
  #_module.Example2.Ex2b(Lit(a#28#0#0)) == Lit(#_module.Example2.Ex2b(a#28#0#0)));

function _module.Example2.b(DatatypeType) : bool;

// Constructor injectivity
axiom (forall a#29#0#0: bool :: 
  { #_module.Example2.Ex2b(a#29#0#0) } 
  _module.Example2.b(#_module.Example2.Ex2b(a#29#0#0)) == a#29#0#0);

// Depth-one case-split function
function $IsA#_module.Example2(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.Example2(d) } 
  $IsA#_module.Example2(d)
     ==> _module.Example2.Ex2a_q(d) || _module.Example2.Ex2b_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.Example2.Ex2b_q(d), $Is(d, Tclass._module.Example2()) } 
    { _module.Example2.Ex2a_q(d), $Is(d, Tclass._module.Example2()) } 
  $Is(d, Tclass._module.Example2())
     ==> _module.Example2.Ex2a_q(d) || _module.Example2.Ex2b_q(d));

// Datatype extensional equality declaration
function _module.Example2#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.Example2.Ex2a
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Example2#Equal(a, b), _module.Example2.Ex2a_q(a) } 
    { _module.Example2#Equal(a, b), _module.Example2.Ex2a_q(b) } 
  _module.Example2.Ex2a_q(a) && _module.Example2.Ex2a_q(b)
     ==> (_module.Example2#Equal(a, b)
       <==> _module.Example2.u(a) == _module.Example2.u(b)));

// Datatype extensional equality definition: #_module.Example2.Ex2b
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Example2#Equal(a, b), _module.Example2.Ex2b_q(a) } 
    { _module.Example2#Equal(a, b), _module.Example2.Ex2b_q(b) } 
  _module.Example2.Ex2b_q(a) && _module.Example2.Ex2b_q(b)
     ==> (_module.Example2#Equal(a, b)
       <==> _module.Example2.b(a) == _module.Example2.b(b)));

// Datatype extensionality axiom: _module.Example2
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Example2#Equal(a, b) } 
  _module.Example2#Equal(a, b) <==> a == b);

const unique class._module.Example2: ClassName;

// Constructor function declaration
function #_module.Example3.Example3(DatatypeType) : DatatypeType;

const unique ##_module.Example3.Example3: DtCtorId;

// Constructor identifier
axiom (forall a#30#0#0: DatatypeType :: 
  { #_module.Example3.Example3(a#30#0#0) } 
  DatatypeCtorId(#_module.Example3.Example3(a#30#0#0))
     == ##_module.Example3.Example3);

function _module.Example3.Example3_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Example3.Example3_q(d) } 
  _module.Example3.Example3_q(d)
     <==> DatatypeCtorId(d) == ##_module.Example3.Example3);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Example3.Example3_q(d) } 
  _module.Example3.Example3_q(d)
     ==> (exists a#31#0#0: DatatypeType :: d == #_module.Example3.Example3(a#31#0#0)));

function Tclass._module.Example3() : Ty;

const unique Tagclass._module.Example3: TyTag;

// Tclass._module.Example3 Tag
axiom Tag(Tclass._module.Example3()) == Tagclass._module.Example3
   && TagFamily(Tclass._module.Example3()) == tytagFamily$Example3;

// Box/unbox axiom for Tclass._module.Example3
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Example3()) } 
  $IsBox(bx, Tclass._module.Example3())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Example3()));

// Constructor $Is
axiom (forall a#32#0#0: DatatypeType :: 
  { $Is(#_module.Example3.Example3(a#32#0#0), Tclass._module.Example3()) } 
  $Is(#_module.Example3.Example3(a#32#0#0), Tclass._module.Example3())
     <==> $Is(a#32#0#0, Tclass._module.Example1()));

// Constructor $IsAlloc
axiom (forall a#33#0#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#_module.Example3.Example3(a#33#0#0), Tclass._module.Example3(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Example3.Example3(a#33#0#0), Tclass._module.Example3(), $h)
       <==> $IsAlloc(a#33#0#0, Tclass._module.Example1(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Example3.e(d), Tclass._module.Example1(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.Example3.Example3_q(d)
       && $IsAlloc(d, Tclass._module.Example3(), $h)
     ==> $IsAlloc(_module.Example3.e(d), Tclass._module.Example1(), $h));

// Constructor literal
axiom (forall a#34#0#0: DatatypeType :: 
  { #_module.Example3.Example3(Lit(a#34#0#0)) } 
  #_module.Example3.Example3(Lit(a#34#0#0))
     == Lit(#_module.Example3.Example3(a#34#0#0)));

function _module.Example3.e(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#35#0#0: DatatypeType :: 
  { #_module.Example3.Example3(a#35#0#0) } 
  _module.Example3.e(#_module.Example3.Example3(a#35#0#0)) == a#35#0#0);

// Inductive rank
axiom (forall a#36#0#0: DatatypeType :: 
  { #_module.Example3.Example3(a#36#0#0) } 
  DtRank(a#36#0#0) < DtRank(#_module.Example3.Example3(a#36#0#0)));

// Depth-one case-split function
function $IsA#_module.Example3(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.Example3(d) } 
  $IsA#_module.Example3(d) ==> _module.Example3.Example3_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.Example3.Example3_q(d), $Is(d, Tclass._module.Example3()) } 
  $Is(d, Tclass._module.Example3()) ==> _module.Example3.Example3_q(d));

// Datatype extensional equality declaration
function _module.Example3#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.Example3.Example3
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Example3#Equal(a, b) } 
  true
     ==> (_module.Example3#Equal(a, b)
       <==> _module.Example1#Equal(_module.Example3.e(a), _module.Example3.e(b))));

// Datatype extensionality axiom: _module.Example3
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Example3#Equal(a, b) } 
  _module.Example3#Equal(a, b) <==> a == b);

const unique class._module.Example3: ClassName;

// Constructor function declaration
function #_module.Example4.Ex4a() : DatatypeType;

const unique ##_module.Example4.Ex4a: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#_module.Example4.Ex4a()) == ##_module.Example4.Ex4a;

function _module.Example4.Ex4a_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Example4.Ex4a_q(d) } 
  _module.Example4.Ex4a_q(d) <==> DatatypeCtorId(d) == ##_module.Example4.Ex4a);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Example4.Ex4a_q(d) } 
  _module.Example4.Ex4a_q(d) ==> d == #_module.Example4.Ex4a());

function Tclass._module.Example4() : Ty;

const unique Tagclass._module.Example4: TyTag;

// Tclass._module.Example4 Tag
axiom Tag(Tclass._module.Example4()) == Tagclass._module.Example4
   && TagFamily(Tclass._module.Example4()) == tytagFamily$Example4;

// Box/unbox axiom for Tclass._module.Example4
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Example4()) } 
  $IsBox(bx, Tclass._module.Example4())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Example4()));

// Constructor $Is
axiom $Is(#_module.Example4.Ex4a(), Tclass._module.Example4());

// Constructor $IsAlloc
axiom (forall $h: Heap :: 
  { $IsAlloc(#_module.Example4.Ex4a(), Tclass._module.Example4(), $h) } 
  $IsGoodHeap($h)
     ==> $IsAlloc(#_module.Example4.Ex4a(), Tclass._module.Example4(), $h));

// Constructor literal
axiom #_module.Example4.Ex4a() == Lit(#_module.Example4.Ex4a());

// Constructor function declaration
function #_module.Example4.Ex4b() : DatatypeType;

const unique ##_module.Example4.Ex4b: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#_module.Example4.Ex4b()) == ##_module.Example4.Ex4b;

function _module.Example4.Ex4b_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Example4.Ex4b_q(d) } 
  _module.Example4.Ex4b_q(d) <==> DatatypeCtorId(d) == ##_module.Example4.Ex4b);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Example4.Ex4b_q(d) } 
  _module.Example4.Ex4b_q(d) ==> d == #_module.Example4.Ex4b());

// Constructor $Is
axiom $Is(#_module.Example4.Ex4b(), Tclass._module.Example4());

// Constructor $IsAlloc
axiom (forall $h: Heap :: 
  { $IsAlloc(#_module.Example4.Ex4b(), Tclass._module.Example4(), $h) } 
  $IsGoodHeap($h)
     ==> $IsAlloc(#_module.Example4.Ex4b(), Tclass._module.Example4(), $h));

// Constructor literal
axiom #_module.Example4.Ex4b() == Lit(#_module.Example4.Ex4b());

// Depth-one case-split function
function $IsA#_module.Example4(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.Example4(d) } 
  $IsA#_module.Example4(d)
     ==> _module.Example4.Ex4a_q(d) || _module.Example4.Ex4b_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.Example4.Ex4b_q(d), $Is(d, Tclass._module.Example4()) } 
    { _module.Example4.Ex4a_q(d), $Is(d, Tclass._module.Example4()) } 
  $Is(d, Tclass._module.Example4())
     ==> _module.Example4.Ex4a_q(d) || _module.Example4.Ex4b_q(d));

// Datatype extensional equality declaration
function _module.Example4#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.Example4.Ex4a
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Example4#Equal(a, b), _module.Example4.Ex4a_q(a) } 
    { _module.Example4#Equal(a, b), _module.Example4.Ex4a_q(b) } 
  _module.Example4.Ex4a_q(a) && _module.Example4.Ex4a_q(b)
     ==> (_module.Example4#Equal(a, b) <==> true));

// Datatype extensional equality definition: #_module.Example4.Ex4b
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Example4#Equal(a, b), _module.Example4.Ex4b_q(a) } 
    { _module.Example4#Equal(a, b), _module.Example4.Ex4b_q(b) } 
  _module.Example4.Ex4b_q(a) && _module.Example4.Ex4b_q(b)
     ==> (_module.Example4#Equal(a, b) <==> true));

// Datatype extensionality axiom: _module.Example4
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Example4#Equal(a, b) } 
  _module.Example4#Equal(a, b) <==> a == b);

const unique class._module.Example4: ClassName;

// Constructor function declaration
function #_module.Example5.Ex5a(Box) : DatatypeType;

const unique ##_module.Example5.Ex5a: DtCtorId;

// Constructor identifier
axiom (forall a#47#0#0: Box :: 
  { #_module.Example5.Ex5a(a#47#0#0) } 
  DatatypeCtorId(#_module.Example5.Ex5a(a#47#0#0)) == ##_module.Example5.Ex5a);

function _module.Example5.Ex5a_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Example5.Ex5a_q(d) } 
  _module.Example5.Ex5a_q(d) <==> DatatypeCtorId(d) == ##_module.Example5.Ex5a);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Example5.Ex5a_q(d) } 
  _module.Example5.Ex5a_q(d)
     ==> (exists a#48#0#0: Box :: d == #_module.Example5.Ex5a(a#48#0#0)));

function Tclass._module.Example5(Ty) : Ty;

const unique Tagclass._module.Example5: TyTag;

// Tclass._module.Example5 Tag
axiom (forall _module.Example5$V: Ty :: 
  { Tclass._module.Example5(_module.Example5$V) } 
  Tag(Tclass._module.Example5(_module.Example5$V)) == Tagclass._module.Example5
     && TagFamily(Tclass._module.Example5(_module.Example5$V)) == tytagFamily$Example5);

// Tclass._module.Example5 injectivity 0
axiom (forall _module.Example5$V: Ty :: 
  { Tclass._module.Example5(_module.Example5$V) } 
  Tclass._module.Example5_0(Tclass._module.Example5(_module.Example5$V))
     == _module.Example5$V);

function Tclass._module.Example5_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.Example5
axiom (forall _module.Example5$V: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.Example5(_module.Example5$V)) } 
  $IsBox(bx, Tclass._module.Example5(_module.Example5$V))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Example5(_module.Example5$V)));

// Constructor $Is
axiom (forall _module.Example5$V: Ty, a#49#0#0: Box :: 
  { $Is(#_module.Example5.Ex5a(a#49#0#0), Tclass._module.Example5(_module.Example5$V)) } 
  $Is(#_module.Example5.Ex5a(a#49#0#0), Tclass._module.Example5(_module.Example5$V))
     <==> $IsBox(a#49#0#0, _module.Example5$V));

// Constructor $IsAlloc
axiom (forall _module.Example5$V: Ty, a#50#0#0: Box, $h: Heap :: 
  { $IsAlloc(#_module.Example5.Ex5a(a#50#0#0), 
      Tclass._module.Example5(_module.Example5$V), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Example5.Ex5a(a#50#0#0), 
        Tclass._module.Example5(_module.Example5$V), 
        $h)
       <==> $IsAllocBox(a#50#0#0, _module.Example5$V, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _module.Example5$V: Ty, $h: Heap :: 
  { $IsAllocBox(_module.Example5.v(d), _module.Example5$V, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Example5.Ex5a_q(d)
       && $IsAlloc(d, Tclass._module.Example5(_module.Example5$V), $h)
     ==> $IsAllocBox(_module.Example5.v(d), _module.Example5$V, $h));

// Constructor literal
axiom (forall a#51#0#0: Box :: 
  { #_module.Example5.Ex5a(Lit(a#51#0#0)) } 
  #_module.Example5.Ex5a(Lit(a#51#0#0)) == Lit(#_module.Example5.Ex5a(a#51#0#0)));

function _module.Example5.v(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#52#0#0: Box :: 
  { #_module.Example5.Ex5a(a#52#0#0) } 
  _module.Example5.v(#_module.Example5.Ex5a(a#52#0#0)) == a#52#0#0);

// Inductive rank
axiom (forall a#53#0#0: Box :: 
  { #_module.Example5.Ex5a(a#53#0#0) } 
  BoxRank(a#53#0#0) < DtRank(#_module.Example5.Ex5a(a#53#0#0)));

// Constructor function declaration
function #_module.Example5.Ex5b(bool) : DatatypeType;

const unique ##_module.Example5.Ex5b: DtCtorId;

// Constructor identifier
axiom (forall a#54#0#0: bool :: 
  { #_module.Example5.Ex5b(a#54#0#0) } 
  DatatypeCtorId(#_module.Example5.Ex5b(a#54#0#0)) == ##_module.Example5.Ex5b);

function _module.Example5.Ex5b_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Example5.Ex5b_q(d) } 
  _module.Example5.Ex5b_q(d) <==> DatatypeCtorId(d) == ##_module.Example5.Ex5b);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Example5.Ex5b_q(d) } 
  _module.Example5.Ex5b_q(d)
     ==> (exists a#55#0#0: bool :: d == #_module.Example5.Ex5b(a#55#0#0)));

// Constructor $Is
axiom (forall _module.Example5$V: Ty, a#56#0#0: bool :: 
  { $Is(#_module.Example5.Ex5b(a#56#0#0), Tclass._module.Example5(_module.Example5$V)) } 
  $Is(#_module.Example5.Ex5b(a#56#0#0), Tclass._module.Example5(_module.Example5$V))
     <==> $Is(a#56#0#0, TBool));

// Constructor $IsAlloc
axiom (forall _module.Example5$V: Ty, a#57#0#0: bool, $h: Heap :: 
  { $IsAlloc(#_module.Example5.Ex5b(a#57#0#0), 
      Tclass._module.Example5(_module.Example5$V), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Example5.Ex5b(a#57#0#0), 
        Tclass._module.Example5(_module.Example5$V), 
        $h)
       <==> $IsAlloc(a#57#0#0, TBool, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Example5.b(d), TBool, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Example5.Ex5b_q(d)
       && (exists _module.Example5$V: Ty :: 
        { $IsAlloc(d, Tclass._module.Example5(_module.Example5$V), $h) } 
        $IsAlloc(d, Tclass._module.Example5(_module.Example5$V), $h))
     ==> $IsAlloc(_module.Example5.b(d), TBool, $h));

// Constructor literal
axiom (forall a#58#0#0: bool :: 
  { #_module.Example5.Ex5b(Lit(a#58#0#0)) } 
  #_module.Example5.Ex5b(Lit(a#58#0#0)) == Lit(#_module.Example5.Ex5b(a#58#0#0)));

function _module.Example5.b(DatatypeType) : bool;

// Constructor injectivity
axiom (forall a#59#0#0: bool :: 
  { #_module.Example5.Ex5b(a#59#0#0) } 
  _module.Example5.b(#_module.Example5.Ex5b(a#59#0#0)) == a#59#0#0);

// Depth-one case-split function
function $IsA#_module.Example5(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.Example5(d) } 
  $IsA#_module.Example5(d)
     ==> _module.Example5.Ex5a_q(d) || _module.Example5.Ex5b_q(d));

// Questionmark data type disjunctivity
axiom (forall _module.Example5$V: Ty, d: DatatypeType :: 
  { _module.Example5.Ex5b_q(d), $Is(d, Tclass._module.Example5(_module.Example5$V)) } 
    { _module.Example5.Ex5a_q(d), $Is(d, Tclass._module.Example5(_module.Example5$V)) } 
  $Is(d, Tclass._module.Example5(_module.Example5$V))
     ==> _module.Example5.Ex5a_q(d) || _module.Example5.Ex5b_q(d));

// Datatype extensional equality declaration
function _module.Example5#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.Example5.Ex5a
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Example5#Equal(a, b), _module.Example5.Ex5a_q(a) } 
    { _module.Example5#Equal(a, b), _module.Example5.Ex5a_q(b) } 
  _module.Example5.Ex5a_q(a) && _module.Example5.Ex5a_q(b)
     ==> (_module.Example5#Equal(a, b)
       <==> _module.Example5.v(a) == _module.Example5.v(b)));

// Datatype extensional equality definition: #_module.Example5.Ex5b
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Example5#Equal(a, b), _module.Example5.Ex5b_q(a) } 
    { _module.Example5#Equal(a, b), _module.Example5.Ex5b_q(b) } 
  _module.Example5.Ex5b_q(a) && _module.Example5.Ex5b_q(b)
     ==> (_module.Example5#Equal(a, b)
       <==> _module.Example5.b(a) == _module.Example5.b(b)));

// Datatype extensionality axiom: _module.Example5
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Example5#Equal(a, b) } 
  _module.Example5#Equal(a, b) <==> a == b);

const unique class._module.Example5: ClassName;

// Constructor function declaration
function #_module.Example6.Ex6a(int) : DatatypeType;

const unique ##_module.Example6.Ex6a: DtCtorId;

// Constructor identifier
axiom (forall a#60#0#0: int :: 
  { #_module.Example6.Ex6a(a#60#0#0) } 
  DatatypeCtorId(#_module.Example6.Ex6a(a#60#0#0)) == ##_module.Example6.Ex6a);

function _module.Example6.Ex6a_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Example6.Ex6a_q(d) } 
  _module.Example6.Ex6a_q(d) <==> DatatypeCtorId(d) == ##_module.Example6.Ex6a);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Example6.Ex6a_q(d) } 
  _module.Example6.Ex6a_q(d)
     ==> (exists a#61#0#0: int :: d == #_module.Example6.Ex6a(a#61#0#0)));

function Tclass._module.Example6() : Ty;

const unique Tagclass._module.Example6: TyTag;

// Tclass._module.Example6 Tag
axiom Tag(Tclass._module.Example6()) == Tagclass._module.Example6
   && TagFamily(Tclass._module.Example6()) == tytagFamily$Example6;

// Box/unbox axiom for Tclass._module.Example6
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Example6()) } 
  $IsBox(bx, Tclass._module.Example6())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Example6()));

// Constructor $Is
axiom (forall a#62#0#0: int :: 
  { $Is(#_module.Example6.Ex6a(a#62#0#0), Tclass._module.Example6()) } 
  $Is(#_module.Example6.Ex6a(a#62#0#0), Tclass._module.Example6())
     <==> $Is(a#62#0#0, Tclass._module.uint32()));

// Constructor $IsAlloc
axiom (forall a#63#0#0: int, $h: Heap :: 
  { $IsAlloc(#_module.Example6.Ex6a(a#63#0#0), Tclass._module.Example6(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Example6.Ex6a(a#63#0#0), Tclass._module.Example6(), $h)
       <==> $IsAlloc(a#63#0#0, Tclass._module.uint32(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Example6.u(d), Tclass._module.uint32(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.Example6.Ex6a_q(d)
       && $IsAlloc(d, Tclass._module.Example6(), $h)
     ==> $IsAlloc(_module.Example6.u(d), Tclass._module.uint32(), $h));

// Constructor literal
axiom (forall a#64#0#0: int :: 
  { #_module.Example6.Ex6a(LitInt(a#64#0#0)) } 
  #_module.Example6.Ex6a(LitInt(a#64#0#0))
     == Lit(#_module.Example6.Ex6a(a#64#0#0)));

function _module.Example6.u(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#65#0#0: int :: 
  { #_module.Example6.Ex6a(a#65#0#0) } 
  _module.Example6.u(#_module.Example6.Ex6a(a#65#0#0)) == a#65#0#0);

// Constructor function declaration
function #_module.Example6.Ex6b(bool) : DatatypeType;

const unique ##_module.Example6.Ex6b: DtCtorId;

// Constructor identifier
axiom (forall a#66#0#0: bool :: 
  { #_module.Example6.Ex6b(a#66#0#0) } 
  DatatypeCtorId(#_module.Example6.Ex6b(a#66#0#0)) == ##_module.Example6.Ex6b);

function _module.Example6.Ex6b_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Example6.Ex6b_q(d) } 
  _module.Example6.Ex6b_q(d) <==> DatatypeCtorId(d) == ##_module.Example6.Ex6b);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Example6.Ex6b_q(d) } 
  _module.Example6.Ex6b_q(d)
     ==> (exists a#67#0#0: bool :: d == #_module.Example6.Ex6b(a#67#0#0)));

// Constructor $Is
axiom (forall a#68#0#0: bool :: 
  { $Is(#_module.Example6.Ex6b(a#68#0#0), Tclass._module.Example6()) } 
  $Is(#_module.Example6.Ex6b(a#68#0#0), Tclass._module.Example6())
     <==> $Is(a#68#0#0, TBool));

// Constructor $IsAlloc
axiom (forall a#69#0#0: bool, $h: Heap :: 
  { $IsAlloc(#_module.Example6.Ex6b(a#69#0#0), Tclass._module.Example6(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Example6.Ex6b(a#69#0#0), Tclass._module.Example6(), $h)
       <==> $IsAlloc(a#69#0#0, TBool, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Example6.b(d), TBool, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Example6.Ex6b_q(d)
       && $IsAlloc(d, Tclass._module.Example6(), $h)
     ==> $IsAlloc(_module.Example6.b(d), TBool, $h));

// Constructor literal
axiom (forall a#70#0#0: bool :: 
  { #_module.Example6.Ex6b(Lit(a#70#0#0)) } 
  #_module.Example6.Ex6b(Lit(a#70#0#0)) == Lit(#_module.Example6.Ex6b(a#70#0#0)));

function _module.Example6.b(DatatypeType) : bool;

// Constructor injectivity
axiom (forall a#71#0#0: bool :: 
  { #_module.Example6.Ex6b(a#71#0#0) } 
  _module.Example6.b(#_module.Example6.Ex6b(a#71#0#0)) == a#71#0#0);

// Constructor function declaration
function #_module.Example6.Ex6c(int, Seq Box) : DatatypeType;

const unique ##_module.Example6.Ex6c: DtCtorId;

// Constructor identifier
axiom (forall a#72#0#0: int, a#72#1#0: Seq Box :: 
  { #_module.Example6.Ex6c(a#72#0#0, a#72#1#0) } 
  DatatypeCtorId(#_module.Example6.Ex6c(a#72#0#0, a#72#1#0))
     == ##_module.Example6.Ex6c);

function _module.Example6.Ex6c_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Example6.Ex6c_q(d) } 
  _module.Example6.Ex6c_q(d) <==> DatatypeCtorId(d) == ##_module.Example6.Ex6c);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Example6.Ex6c_q(d) } 
  _module.Example6.Ex6c_q(d)
     ==> (exists a#73#0#0: int, a#73#1#0: Seq Box :: 
      d == #_module.Example6.Ex6c(a#73#0#0, a#73#1#0)));

// Constructor $Is
axiom (forall a#74#0#0: int, a#74#1#0: Seq Box :: 
  { $Is(#_module.Example6.Ex6c(a#74#0#0, a#74#1#0), Tclass._module.Example6()) } 
  $Is(#_module.Example6.Ex6c(a#74#0#0, a#74#1#0), Tclass._module.Example6())
     <==> $Is(a#74#0#0, Tclass._module.uint32()) && $Is(a#74#1#0, TSeq(TBool)));

// Constructor $IsAlloc
axiom (forall a#75#0#0: int, a#75#1#0: Seq Box, $h: Heap :: 
  { $IsAlloc(#_module.Example6.Ex6c(a#75#0#0, a#75#1#0), Tclass._module.Example6(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Example6.Ex6c(a#75#0#0, a#75#1#0), Tclass._module.Example6(), $h)
       <==> $IsAlloc(a#75#0#0, Tclass._module.uint32(), $h)
         && $IsAlloc(a#75#1#0, TSeq(TBool), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Example6.u(d), Tclass._module.uint32(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.Example6.Ex6c_q(d)
       && $IsAlloc(d, Tclass._module.Example6(), $h)
     ==> $IsAlloc(_module.Example6.u(d), Tclass._module.uint32(), $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Example6.s(d), TSeq(TBool), $h) } 
  $IsGoodHeap($h)
       && 
      _module.Example6.Ex6c_q(d)
       && $IsAlloc(d, Tclass._module.Example6(), $h)
     ==> $IsAlloc(_module.Example6.s(d), TSeq(TBool), $h));

// Constructor literal
axiom (forall a#76#0#0: int, a#76#1#0: Seq Box :: 
  { #_module.Example6.Ex6c(LitInt(a#76#0#0), Lit(a#76#1#0)) } 
  #_module.Example6.Ex6c(LitInt(a#76#0#0), Lit(a#76#1#0))
     == Lit(#_module.Example6.Ex6c(a#76#0#0, a#76#1#0)));

// Constructor injectivity
axiom (forall a#77#0#0: int, a#77#1#0: Seq Box :: 
  { #_module.Example6.Ex6c(a#77#0#0, a#77#1#0) } 
  _module.Example6.u(#_module.Example6.Ex6c(a#77#0#0, a#77#1#0)) == a#77#0#0);

function _module.Example6.s(DatatypeType) : Seq Box;

// Constructor injectivity
axiom (forall a#78#0#0: int, a#78#1#0: Seq Box :: 
  { #_module.Example6.Ex6c(a#78#0#0, a#78#1#0) } 
  _module.Example6.s(#_module.Example6.Ex6c(a#78#0#0, a#78#1#0)) == a#78#1#0);

// Inductive seq element rank
axiom (forall a#79#0#0: int, a#79#1#0: Seq Box, i: int :: 
  { Seq#Index(a#79#1#0, i), #_module.Example6.Ex6c(a#79#0#0, a#79#1#0) } 
  0 <= i && i < Seq#Length(a#79#1#0)
     ==> DtRank($Unbox(Seq#Index(a#79#1#0, i)): DatatypeType)
       < DtRank(#_module.Example6.Ex6c(a#79#0#0, a#79#1#0)));

// Inductive seq rank
axiom (forall a#80#0#0: int, a#80#1#0: Seq Box :: 
  { #_module.Example6.Ex6c(a#80#0#0, a#80#1#0) } 
  Seq#Rank(a#80#1#0) < DtRank(#_module.Example6.Ex6c(a#80#0#0, a#80#1#0)));

// Depth-one case-split function
function $IsA#_module.Example6(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.Example6(d) } 
  $IsA#_module.Example6(d)
     ==> _module.Example6.Ex6a_q(d)
       || _module.Example6.Ex6b_q(d)
       || _module.Example6.Ex6c_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.Example6.Ex6c_q(d), $Is(d, Tclass._module.Example6()) } 
    { _module.Example6.Ex6b_q(d), $Is(d, Tclass._module.Example6()) } 
    { _module.Example6.Ex6a_q(d), $Is(d, Tclass._module.Example6()) } 
  $Is(d, Tclass._module.Example6())
     ==> _module.Example6.Ex6a_q(d)
       || _module.Example6.Ex6b_q(d)
       || _module.Example6.Ex6c_q(d));

// Datatype extensional equality declaration
function _module.Example6#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.Example6.Ex6a
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Example6#Equal(a, b), _module.Example6.Ex6a_q(a) } 
    { _module.Example6#Equal(a, b), _module.Example6.Ex6a_q(b) } 
  _module.Example6.Ex6a_q(a) && _module.Example6.Ex6a_q(b)
     ==> (_module.Example6#Equal(a, b)
       <==> _module.Example6.u(a) == _module.Example6.u(b)));

// Datatype extensional equality definition: #_module.Example6.Ex6b
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Example6#Equal(a, b), _module.Example6.Ex6b_q(a) } 
    { _module.Example6#Equal(a, b), _module.Example6.Ex6b_q(b) } 
  _module.Example6.Ex6b_q(a) && _module.Example6.Ex6b_q(b)
     ==> (_module.Example6#Equal(a, b)
       <==> _module.Example6.b(a) == _module.Example6.b(b)));

// Datatype extensional equality definition: #_module.Example6.Ex6c
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Example6#Equal(a, b), _module.Example6.Ex6c_q(a) } 
    { _module.Example6#Equal(a, b), _module.Example6.Ex6c_q(b) } 
  _module.Example6.Ex6c_q(a) && _module.Example6.Ex6c_q(b)
     ==> (_module.Example6#Equal(a, b)
       <==> _module.Example6.u(a) == _module.Example6.u(b)
         && Seq#Equal(_module.Example6.s(a), _module.Example6.s(b))));

// Datatype extensionality axiom: _module.Example6
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Example6#Equal(a, b) } 
  _module.Example6#Equal(a, b) <==> a == b);

const unique class._module.Example6: ClassName;

procedure CheckWellformed$$_module.Ex1Sub(d#0: DatatypeType where $Is(d#0, Tclass._module.Example1()));
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Ex1Sub(d#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var newtype$check#0: int;
  var newtype$check#1: int;


    // AddWellformednessCheck for subset type Ex1Sub
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(16,5): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume _module.Example1.Example1_q(d#0);
        newtype$check#0 := LitInt(0);
        assert LitInt(0) <= newtype$check#0 && newtype$check#0 < 4294967296;
        assume _module.Example1.u(d#0) == LitInt(0);
    }
    else
    {
        newtype$check#1 := LitInt(0);
        assert LitInt(0) <= newtype$check#1 && newtype$check#1 < 4294967296;
        assume _module.Example1.Example1_q(Lit(#_module.Example1.Example1(LitInt(0), Lit(true))));
        assert LitInt(_module.Example1.u(Lit(#_module.Example1.Example1(LitInt(0), Lit(true)))))
           == LitInt(0);
    }
}



function Tclass._module.Ex1Sub() : Ty;

const unique Tagclass._module.Ex1Sub: TyTag;

// Tclass._module.Ex1Sub Tag
axiom Tag(Tclass._module.Ex1Sub()) == Tagclass._module.Ex1Sub
   && TagFamily(Tclass._module.Ex1Sub()) == tytagFamily$Ex1Sub;

// Box/unbox axiom for Tclass._module.Ex1Sub
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Ex1Sub()) } 
  $IsBox(bx, Tclass._module.Ex1Sub())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Ex1Sub()));

// _module.Ex1Sub: subset type $Is
axiom (forall d#0: DatatypeType :: 
  { $Is(d#0, Tclass._module.Ex1Sub()) } 
  $Is(d#0, Tclass._module.Ex1Sub())
     <==> $Is(d#0, Tclass._module.Example1()) && _module.Example1.u(d#0) == LitInt(0));

// _module.Ex1Sub: subset type $IsAlloc
axiom (forall d#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(d#0, Tclass._module.Ex1Sub(), $h) } 
  $IsAlloc(d#0, Tclass._module.Ex1Sub(), $h)
     <==> $IsAlloc(d#0, Tclass._module.Example1(), $h));

procedure CheckWellformed$$_module.Ex2Sub(d#0: DatatypeType where $Is(d#0, Tclass._module.Example2()));
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Ex2Sub(d#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var newtype$check#0: int;
  var newtype$check#1: int;


    // AddWellformednessCheck for subset type Ex2Sub
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(17,5): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume _module.Example2.Ex2a_q(d#0);
        assert _module.Example2.Ex2a_q(d#0);
        newtype$check#0 := LitInt(0);
        assert LitInt(0) <= newtype$check#0 && newtype$check#0 < 4294967296;
        assume _module.Example2.u(d#0) == LitInt(0);
    }
    else
    {
        newtype$check#1 := LitInt(0);
        assert LitInt(0) <= newtype$check#1 && newtype$check#1 < 4294967296;
        assume true;
        assert {:subsumption 0} _module.Example2.Ex2a_q(Lit(#_module.Example2.Ex2a(LitInt(0))));
        assert {:subsumption 0} LitInt(_module.Example2.u(Lit(#_module.Example2.Ex2a(LitInt(0))))) == LitInt(0);
    }
}



function Tclass._module.Ex2Sub() : Ty;

const unique Tagclass._module.Ex2Sub: TyTag;

// Tclass._module.Ex2Sub Tag
axiom Tag(Tclass._module.Ex2Sub()) == Tagclass._module.Ex2Sub
   && TagFamily(Tclass._module.Ex2Sub()) == tytagFamily$Ex2Sub;

// Box/unbox axiom for Tclass._module.Ex2Sub
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Ex2Sub()) } 
  $IsBox(bx, Tclass._module.Ex2Sub())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Ex2Sub()));

// _module.Ex2Sub: subset type $Is
axiom (forall d#0: DatatypeType :: 
  { $Is(d#0, Tclass._module.Ex2Sub()) } 
  $Is(d#0, Tclass._module.Ex2Sub())
     <==> $Is(d#0, Tclass._module.Example2())
       && 
      _module.Example2.Ex2a_q(d#0)
       && _module.Example2.u(d#0) == LitInt(0));

// _module.Ex2Sub: subset type $IsAlloc
axiom (forall d#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(d#0, Tclass._module.Ex2Sub(), $h) } 
  $IsAlloc(d#0, Tclass._module.Ex2Sub(), $h)
     <==> $IsAlloc(d#0, Tclass._module.Example2(), $h));

procedure CheckWellformed$$_module.Ex3Sub(d#0: DatatypeType where $Is(d#0, Tclass._module.Example3()));
  free requires 7 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Ex3Sub(d#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var newtype$check#0: int;


    // AddWellformednessCheck for subset type Ex3Sub
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(18,5): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume _module.Example3.Example3_q(d#0);
        assume _module.Example1.Example1_q(_module.Example3.e(d#0));
        assume _module.Example1.b(_module.Example3.e(d#0));
    }
    else
    {
        newtype$check#0 := LitInt(42);
        assert LitInt(0) <= newtype$check#0 && newtype$check#0 < 4294967296;
        assume _module.Example3.Example3_q(Lit(#_module.Example3.Example3(Lit(#_module.Example1.Example1(LitInt(42), Lit(true))))))
           && _module.Example1.Example1_q(Lit(_module.Example3.e(Lit(#_module.Example3.Example3(Lit(#_module.Example1.Example1(LitInt(42), Lit(true))))))));
        assert _module.Example1.b(Lit(_module.Example3.e(Lit(#_module.Example3.Example3(Lit(#_module.Example1.Example1(LitInt(42), Lit(true))))))));
    }
}



function Tclass._module.Ex3Sub() : Ty;

const unique Tagclass._module.Ex3Sub: TyTag;

// Tclass._module.Ex3Sub Tag
axiom Tag(Tclass._module.Ex3Sub()) == Tagclass._module.Ex3Sub
   && TagFamily(Tclass._module.Ex3Sub()) == tytagFamily$Ex3Sub;

// Box/unbox axiom for Tclass._module.Ex3Sub
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Ex3Sub()) } 
  $IsBox(bx, Tclass._module.Ex3Sub())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Ex3Sub()));

// _module.Ex3Sub: subset type $Is
axiom (forall d#0: DatatypeType :: 
  { $Is(d#0, Tclass._module.Ex3Sub()) } 
  $Is(d#0, Tclass._module.Ex3Sub())
     <==> $Is(d#0, Tclass._module.Example3())
       && _module.Example1.b(_module.Example3.e(d#0)));

// _module.Ex3Sub: subset type $IsAlloc
axiom (forall d#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(d#0, Tclass._module.Ex3Sub(), $h) } 
  $IsAlloc(d#0, Tclass._module.Ex3Sub(), $h)
     <==> $IsAlloc(d#0, Tclass._module.Example3(), $h));

// Constructor function declaration
function #_module.DtPointer.DtPointer(Seq Box) : DatatypeType;

const unique ##_module.DtPointer.DtPointer: DtCtorId;

// Constructor identifier
axiom (forall a#0#0#0: Seq Box :: 
  { #_module.DtPointer.DtPointer(a#0#0#0) } 
  DatatypeCtorId(#_module.DtPointer.DtPointer(a#0#0#0))
     == ##_module.DtPointer.DtPointer);

function _module.DtPointer.DtPointer_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.DtPointer.DtPointer_q(d) } 
  _module.DtPointer.DtPointer_q(d)
     <==> DatatypeCtorId(d) == ##_module.DtPointer.DtPointer);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.DtPointer.DtPointer_q(d) } 
  _module.DtPointer.DtPointer_q(d)
     ==> (exists a#1#0#0: Seq Box :: d == #_module.DtPointer.DtPointer(a#1#0#0)));

function Tclass._module.DtPointer() : Ty;

const unique Tagclass._module.DtPointer: TyTag;

// Tclass._module.DtPointer Tag
axiom Tag(Tclass._module.DtPointer()) == Tagclass._module.DtPointer
   && TagFamily(Tclass._module.DtPointer()) == tytagFamily$DtPointer;

// Box/unbox axiom for Tclass._module.DtPointer
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.DtPointer()) } 
  $IsBox(bx, Tclass._module.DtPointer())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.DtPointer()));

// Constructor $Is
axiom (forall a#2#0#0: Seq Box :: 
  { $Is(#_module.DtPointer.DtPointer(a#2#0#0), Tclass._module.DtPointer()) } 
  $Is(#_module.DtPointer.DtPointer(a#2#0#0), Tclass._module.DtPointer())
     <==> $Is(a#2#0#0, TSeq(Tclass._module.uint32())));

// Constructor $IsAlloc
axiom (forall a#3#0#0: Seq Box, $h: Heap :: 
  { $IsAlloc(#_module.DtPointer.DtPointer(a#3#0#0), Tclass._module.DtPointer(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.DtPointer.DtPointer(a#3#0#0), Tclass._module.DtPointer(), $h)
       <==> $IsAlloc(a#3#0#0, TSeq(Tclass._module.uint32()), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.DtPointer.s(d), TSeq(Tclass._module.uint32()), $h) } 
  $IsGoodHeap($h)
       && 
      _module.DtPointer.DtPointer_q(d)
       && $IsAlloc(d, Tclass._module.DtPointer(), $h)
     ==> $IsAlloc(_module.DtPointer.s(d), TSeq(Tclass._module.uint32()), $h));

// Constructor literal
axiom (forall a#4#0#0: Seq Box :: 
  { #_module.DtPointer.DtPointer(Lit(a#4#0#0)) } 
  #_module.DtPointer.DtPointer(Lit(a#4#0#0))
     == Lit(#_module.DtPointer.DtPointer(a#4#0#0)));

function _module.DtPointer.s(DatatypeType) : Seq Box;

// Constructor injectivity
axiom (forall a#5#0#0: Seq Box :: 
  { #_module.DtPointer.DtPointer(a#5#0#0) } 
  _module.DtPointer.s(#_module.DtPointer.DtPointer(a#5#0#0)) == a#5#0#0);

// Inductive seq element rank
axiom (forall a#6#0#0: Seq Box, i: int :: 
  { Seq#Index(a#6#0#0, i), #_module.DtPointer.DtPointer(a#6#0#0) } 
  0 <= i && i < Seq#Length(a#6#0#0)
     ==> DtRank($Unbox(Seq#Index(a#6#0#0, i)): DatatypeType)
       < DtRank(#_module.DtPointer.DtPointer(a#6#0#0)));

// Inductive seq rank
axiom (forall a#7#0#0: Seq Box :: 
  { #_module.DtPointer.DtPointer(a#7#0#0) } 
  Seq#Rank(a#7#0#0) < DtRank(#_module.DtPointer.DtPointer(a#7#0#0)));

// Depth-one case-split function
function $IsA#_module.DtPointer(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.DtPointer(d) } 
  $IsA#_module.DtPointer(d) ==> _module.DtPointer.DtPointer_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.DtPointer.DtPointer_q(d), $Is(d, Tclass._module.DtPointer()) } 
  $Is(d, Tclass._module.DtPointer()) ==> _module.DtPointer.DtPointer_q(d));

// Datatype extensional equality declaration
function _module.DtPointer#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.DtPointer.DtPointer
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.DtPointer#Equal(a, b) } 
  true
     ==> (_module.DtPointer#Equal(a, b)
       <==> Seq#Equal(_module.DtPointer.s(a), _module.DtPointer.s(b))));

// Datatype extensionality axiom: _module.DtPointer
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.DtPointer#Equal(a, b) } 
  _module.DtPointer#Equal(a, b) <==> a == b);

const unique class._module.DtPointer: ClassName;

// Constructor function declaration
function #_module.DtPointerHolder.DtPointerHolder(DatatypeType) : DatatypeType;

const unique ##_module.DtPointerHolder.DtPointerHolder: DtCtorId;

// Constructor identifier
axiom (forall a#8#0#0: DatatypeType :: 
  { #_module.DtPointerHolder.DtPointerHolder(a#8#0#0) } 
  DatatypeCtorId(#_module.DtPointerHolder.DtPointerHolder(a#8#0#0))
     == ##_module.DtPointerHolder.DtPointerHolder);

function _module.DtPointerHolder.DtPointerHolder_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.DtPointerHolder.DtPointerHolder_q(d) } 
  _module.DtPointerHolder.DtPointerHolder_q(d)
     <==> DatatypeCtorId(d) == ##_module.DtPointerHolder.DtPointerHolder);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.DtPointerHolder.DtPointerHolder_q(d) } 
  _module.DtPointerHolder.DtPointerHolder_q(d)
     ==> (exists a#9#0#0: DatatypeType :: 
      d == #_module.DtPointerHolder.DtPointerHolder(a#9#0#0)));

function Tclass._module.DtPointerHolder() : Ty;

const unique Tagclass._module.DtPointerHolder: TyTag;

// Tclass._module.DtPointerHolder Tag
axiom Tag(Tclass._module.DtPointerHolder()) == Tagclass._module.DtPointerHolder
   && TagFamily(Tclass._module.DtPointerHolder()) == tytagFamily$DtPointerHolder;

// Box/unbox axiom for Tclass._module.DtPointerHolder
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.DtPointerHolder()) } 
  $IsBox(bx, Tclass._module.DtPointerHolder())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.DtPointerHolder()));

// Constructor $Is
axiom (forall a#10#0#0: DatatypeType :: 
  { $Is(#_module.DtPointerHolder.DtPointerHolder(a#10#0#0), 
      Tclass._module.DtPointerHolder()) } 
  $Is(#_module.DtPointerHolder.DtPointerHolder(a#10#0#0), 
      Tclass._module.DtPointerHolder())
     <==> $Is(a#10#0#0, Tclass._module.DtPointer()));

// Constructor $IsAlloc
axiom (forall a#11#0#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#_module.DtPointerHolder.DtPointerHolder(a#11#0#0), 
      Tclass._module.DtPointerHolder(), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.DtPointerHolder.DtPointerHolder(a#11#0#0), 
        Tclass._module.DtPointerHolder(), 
        $h)
       <==> $IsAlloc(a#11#0#0, Tclass._module.DtPointer(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.DtPointerHolder.e(d), Tclass._module.DtPointer(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.DtPointerHolder.DtPointerHolder_q(d)
       && $IsAlloc(d, Tclass._module.DtPointerHolder(), $h)
     ==> $IsAlloc(_module.DtPointerHolder.e(d), Tclass._module.DtPointer(), $h));

// Constructor literal
axiom (forall a#12#0#0: DatatypeType :: 
  { #_module.DtPointerHolder.DtPointerHolder(Lit(a#12#0#0)) } 
  #_module.DtPointerHolder.DtPointerHolder(Lit(a#12#0#0))
     == Lit(#_module.DtPointerHolder.DtPointerHolder(a#12#0#0)));

function _module.DtPointerHolder.e(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#13#0#0: DatatypeType :: 
  { #_module.DtPointerHolder.DtPointerHolder(a#13#0#0) } 
  _module.DtPointerHolder.e(#_module.DtPointerHolder.DtPointerHolder(a#13#0#0))
     == a#13#0#0);

// Inductive rank
axiom (forall a#14#0#0: DatatypeType :: 
  { #_module.DtPointerHolder.DtPointerHolder(a#14#0#0) } 
  DtRank(a#14#0#0) < DtRank(#_module.DtPointerHolder.DtPointerHolder(a#14#0#0)));

// Constructor function declaration
function #_module.DtPointerHolder.Other(bool) : DatatypeType;

const unique ##_module.DtPointerHolder.Other: DtCtorId;

// Constructor identifier
axiom (forall a#15#0#0: bool :: 
  { #_module.DtPointerHolder.Other(a#15#0#0) } 
  DatatypeCtorId(#_module.DtPointerHolder.Other(a#15#0#0))
     == ##_module.DtPointerHolder.Other);

function _module.DtPointerHolder.Other_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.DtPointerHolder.Other_q(d) } 
  _module.DtPointerHolder.Other_q(d)
     <==> DatatypeCtorId(d) == ##_module.DtPointerHolder.Other);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.DtPointerHolder.Other_q(d) } 
  _module.DtPointerHolder.Other_q(d)
     ==> (exists a#16#0#0: bool :: d == #_module.DtPointerHolder.Other(a#16#0#0)));

// Constructor $Is
axiom (forall a#17#0#0: bool :: 
  { $Is(#_module.DtPointerHolder.Other(a#17#0#0), Tclass._module.DtPointerHolder()) } 
  $Is(#_module.DtPointerHolder.Other(a#17#0#0), Tclass._module.DtPointerHolder())
     <==> $Is(a#17#0#0, TBool));

// Constructor $IsAlloc
axiom (forall a#18#0#0: bool, $h: Heap :: 
  { $IsAlloc(#_module.DtPointerHolder.Other(a#18#0#0), Tclass._module.DtPointerHolder(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.DtPointerHolder.Other(a#18#0#0), Tclass._module.DtPointerHolder(), $h)
       <==> $IsAlloc(a#18#0#0, TBool, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.DtPointerHolder.f(d), TBool, $h) } 
  $IsGoodHeap($h)
       && 
      _module.DtPointerHolder.Other_q(d)
       && $IsAlloc(d, Tclass._module.DtPointerHolder(), $h)
     ==> $IsAlloc(_module.DtPointerHolder.f(d), TBool, $h));

// Constructor literal
axiom (forall a#19#0#0: bool :: 
  { #_module.DtPointerHolder.Other(Lit(a#19#0#0)) } 
  #_module.DtPointerHolder.Other(Lit(a#19#0#0))
     == Lit(#_module.DtPointerHolder.Other(a#19#0#0)));

function _module.DtPointerHolder.f(DatatypeType) : bool;

// Constructor injectivity
axiom (forall a#20#0#0: bool :: 
  { #_module.DtPointerHolder.Other(a#20#0#0) } 
  _module.DtPointerHolder.f(#_module.DtPointerHolder.Other(a#20#0#0)) == a#20#0#0);

// Depth-one case-split function
function $IsA#_module.DtPointerHolder(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.DtPointerHolder(d) } 
  $IsA#_module.DtPointerHolder(d)
     ==> _module.DtPointerHolder.DtPointerHolder_q(d)
       || _module.DtPointerHolder.Other_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.DtPointerHolder.Other_q(d), $Is(d, Tclass._module.DtPointerHolder()) } 
    { _module.DtPointerHolder.DtPointerHolder_q(d), $Is(d, Tclass._module.DtPointerHolder()) } 
  $Is(d, Tclass._module.DtPointerHolder())
     ==> _module.DtPointerHolder.DtPointerHolder_q(d)
       || _module.DtPointerHolder.Other_q(d));

// Datatype extensional equality declaration
function _module.DtPointerHolder#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.DtPointerHolder.DtPointerHolder
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.DtPointerHolder#Equal(a, b), _module.DtPointerHolder.DtPointerHolder_q(a) } 
    { _module.DtPointerHolder#Equal(a, b), _module.DtPointerHolder.DtPointerHolder_q(b) } 
  _module.DtPointerHolder.DtPointerHolder_q(a)
       && _module.DtPointerHolder.DtPointerHolder_q(b)
     ==> (_module.DtPointerHolder#Equal(a, b)
       <==> _module.DtPointer#Equal(_module.DtPointerHolder.e(a), _module.DtPointerHolder.e(b))));

// Datatype extensional equality definition: #_module.DtPointerHolder.Other
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.DtPointerHolder#Equal(a, b), _module.DtPointerHolder.Other_q(a) } 
    { _module.DtPointerHolder#Equal(a, b), _module.DtPointerHolder.Other_q(b) } 
  _module.DtPointerHolder.Other_q(a) && _module.DtPointerHolder.Other_q(b)
     ==> (_module.DtPointerHolder#Equal(a, b)
       <==> _module.DtPointerHolder.f(a) == _module.DtPointerHolder.f(b)));

// Datatype extensionality axiom: _module.DtPointerHolder
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.DtPointerHolder#Equal(a, b) } 
  _module.DtPointerHolder#Equal(a, b) <==> a == b);

const unique class._module.DtPointerHolder: ClassName;

// Constructor function declaration
function #_module.Option.None() : DatatypeType;

const unique ##_module.Option.None: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#_module.Option.None()) == ##_module.Option.None;

function _module.Option.None_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Option.None_q(d) } 
  _module.Option.None_q(d) <==> DatatypeCtorId(d) == ##_module.Option.None);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Option.None_q(d) } 
  _module.Option.None_q(d) ==> d == #_module.Option.None());

function Tclass._module.Option(Ty) : Ty;

const unique Tagclass._module.Option: TyTag;

// Tclass._module.Option Tag
axiom (forall _module.Option$V: Ty :: 
  { Tclass._module.Option(_module.Option$V) } 
  Tag(Tclass._module.Option(_module.Option$V)) == Tagclass._module.Option
     && TagFamily(Tclass._module.Option(_module.Option$V)) == tytagFamily$Option);

// Tclass._module.Option injectivity 0
axiom (forall _module.Option$V: Ty :: 
  { Tclass._module.Option(_module.Option$V) } 
  Tclass._module.Option_0(Tclass._module.Option(_module.Option$V))
     == _module.Option$V);

function Tclass._module.Option_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.Option
axiom (forall _module.Option$V: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.Option(_module.Option$V)) } 
  $IsBox(bx, Tclass._module.Option(_module.Option$V))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Option(_module.Option$V)));

// Constructor $Is
axiom (forall _module.Option$V: Ty :: 
  { $Is(#_module.Option.None(), Tclass._module.Option(_module.Option$V)) } 
  $Is(#_module.Option.None(), Tclass._module.Option(_module.Option$V)));

// Constructor $IsAlloc
axiom (forall _module.Option$V: Ty, $h: Heap :: 
  { $IsAlloc(#_module.Option.None(), Tclass._module.Option(_module.Option$V), $h) } 
  $IsGoodHeap($h)
     ==> $IsAlloc(#_module.Option.None(), Tclass._module.Option(_module.Option$V), $h));

// Constructor literal
axiom #_module.Option.None() == Lit(#_module.Option.None());

// Constructor function declaration
function #_module.Option.Some(Box) : DatatypeType;

const unique ##_module.Option.Some: DtCtorId;

// Constructor identifier
axiom (forall a#26#0#0: Box :: 
  { #_module.Option.Some(a#26#0#0) } 
  DatatypeCtorId(#_module.Option.Some(a#26#0#0)) == ##_module.Option.Some);

function _module.Option.Some_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Option.Some_q(d) } 
  _module.Option.Some_q(d) <==> DatatypeCtorId(d) == ##_module.Option.Some);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Option.Some_q(d) } 
  _module.Option.Some_q(d)
     ==> (exists a#27#0#0: Box :: d == #_module.Option.Some(a#27#0#0)));

// Constructor $Is
axiom (forall _module.Option$V: Ty, a#28#0#0: Box :: 
  { $Is(#_module.Option.Some(a#28#0#0), Tclass._module.Option(_module.Option$V)) } 
  $Is(#_module.Option.Some(a#28#0#0), Tclass._module.Option(_module.Option$V))
     <==> $IsBox(a#28#0#0, _module.Option$V));

// Constructor $IsAlloc
axiom (forall _module.Option$V: Ty, a#29#0#0: Box, $h: Heap :: 
  { $IsAlloc(#_module.Option.Some(a#29#0#0), Tclass._module.Option(_module.Option$V), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Option.Some(a#29#0#0), Tclass._module.Option(_module.Option$V), $h)
       <==> $IsAllocBox(a#29#0#0, _module.Option$V, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _module.Option$V: Ty, $h: Heap :: 
  { $IsAllocBox(_module.Option.value(d), _module.Option$V, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Option.Some_q(d)
       && $IsAlloc(d, Tclass._module.Option(_module.Option$V), $h)
     ==> $IsAllocBox(_module.Option.value(d), _module.Option$V, $h));

// Constructor literal
axiom (forall a#30#0#0: Box :: 
  { #_module.Option.Some(Lit(a#30#0#0)) } 
  #_module.Option.Some(Lit(a#30#0#0)) == Lit(#_module.Option.Some(a#30#0#0)));

function _module.Option.value(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#31#0#0: Box :: 
  { #_module.Option.Some(a#31#0#0) } 
  _module.Option.value(#_module.Option.Some(a#31#0#0)) == a#31#0#0);

// Inductive rank
axiom (forall a#32#0#0: Box :: 
  { #_module.Option.Some(a#32#0#0) } 
  BoxRank(a#32#0#0) < DtRank(#_module.Option.Some(a#32#0#0)));

// Depth-one case-split function
function $IsA#_module.Option(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.Option(d) } 
  $IsA#_module.Option(d) ==> _module.Option.None_q(d) || _module.Option.Some_q(d));

// Questionmark data type disjunctivity
axiom (forall _module.Option$V: Ty, d: DatatypeType :: 
  { _module.Option.Some_q(d), $Is(d, Tclass._module.Option(_module.Option$V)) } 
    { _module.Option.None_q(d), $Is(d, Tclass._module.Option(_module.Option$V)) } 
  $Is(d, Tclass._module.Option(_module.Option$V))
     ==> _module.Option.None_q(d) || _module.Option.Some_q(d));

// Datatype extensional equality declaration
function _module.Option#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.Option.None
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Option#Equal(a, b), _module.Option.None_q(a) } 
    { _module.Option#Equal(a, b), _module.Option.None_q(b) } 
  _module.Option.None_q(a) && _module.Option.None_q(b)
     ==> (_module.Option#Equal(a, b) <==> true));

// Datatype extensional equality definition: #_module.Option.Some
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Option#Equal(a, b), _module.Option.Some_q(a) } 
    { _module.Option#Equal(a, b), _module.Option.Some_q(b) } 
  _module.Option.Some_q(a) && _module.Option.Some_q(b)
     ==> (_module.Option#Equal(a, b)
       <==> _module.Option.value(a) == _module.Option.value(b)));

// Datatype extensionality axiom: _module.Option
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Option#Equal(a, b) } 
  _module.Option#Equal(a, b) <==> a == b);

const unique class._module.Option: ClassName;

// Constructor function declaration
function #_module.Err.Fail(bool) : DatatypeType;

const unique ##_module.Err.Fail: DtCtorId;

// Constructor identifier
axiom (forall a#33#0#0: bool :: 
  { #_module.Err.Fail(a#33#0#0) } 
  DatatypeCtorId(#_module.Err.Fail(a#33#0#0)) == ##_module.Err.Fail);

function _module.Err.Fail_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Err.Fail_q(d) } 
  _module.Err.Fail_q(d) <==> DatatypeCtorId(d) == ##_module.Err.Fail);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Err.Fail_q(d) } 
  _module.Err.Fail_q(d)
     ==> (exists a#34#0#0: bool :: d == #_module.Err.Fail(a#34#0#0)));

function Tclass._module.Err(Ty) : Ty;

const unique Tagclass._module.Err: TyTag;

// Tclass._module.Err Tag
axiom (forall _module.Err$V: Ty :: 
  { Tclass._module.Err(_module.Err$V) } 
  Tag(Tclass._module.Err(_module.Err$V)) == Tagclass._module.Err
     && TagFamily(Tclass._module.Err(_module.Err$V)) == tytagFamily$Err);

// Tclass._module.Err injectivity 0
axiom (forall _module.Err$V: Ty :: 
  { Tclass._module.Err(_module.Err$V) } 
  Tclass._module.Err_0(Tclass._module.Err(_module.Err$V)) == _module.Err$V);

function Tclass._module.Err_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.Err
axiom (forall _module.Err$V: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.Err(_module.Err$V)) } 
  $IsBox(bx, Tclass._module.Err(_module.Err$V))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Err(_module.Err$V)));

// Constructor $Is
axiom (forall _module.Err$V: Ty, a#35#0#0: bool :: 
  { $Is(#_module.Err.Fail(a#35#0#0), Tclass._module.Err(_module.Err$V)) } 
  $Is(#_module.Err.Fail(a#35#0#0), Tclass._module.Err(_module.Err$V))
     <==> $Is(a#35#0#0, TBool));

// Constructor $IsAlloc
axiom (forall _module.Err$V: Ty, a#36#0#0: bool, $h: Heap :: 
  { $IsAlloc(#_module.Err.Fail(a#36#0#0), Tclass._module.Err(_module.Err$V), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Err.Fail(a#36#0#0), Tclass._module.Err(_module.Err$V), $h)
       <==> $IsAlloc(a#36#0#0, TBool, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Err.err(d), TBool, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Err.Fail_q(d)
       && (exists _module.Err$V: Ty :: 
        { $IsAlloc(d, Tclass._module.Err(_module.Err$V), $h) } 
        $IsAlloc(d, Tclass._module.Err(_module.Err$V), $h))
     ==> $IsAlloc(_module.Err.err(d), TBool, $h));

// Constructor literal
axiom (forall a#37#0#0: bool :: 
  { #_module.Err.Fail(Lit(a#37#0#0)) } 
  #_module.Err.Fail(Lit(a#37#0#0)) == Lit(#_module.Err.Fail(a#37#0#0)));

function _module.Err.err(DatatypeType) : bool;

// Constructor injectivity
axiom (forall a#38#0#0: bool :: 
  { #_module.Err.Fail(a#38#0#0) } 
  _module.Err.err(#_module.Err.Fail(a#38#0#0)) == a#38#0#0);

// Constructor function declaration
function #_module.Err.Ok(Box) : DatatypeType;

const unique ##_module.Err.Ok: DtCtorId;

// Constructor identifier
axiom (forall a#39#0#0: Box :: 
  { #_module.Err.Ok(a#39#0#0) } 
  DatatypeCtorId(#_module.Err.Ok(a#39#0#0)) == ##_module.Err.Ok);

function _module.Err.Ok_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Err.Ok_q(d) } 
  _module.Err.Ok_q(d) <==> DatatypeCtorId(d) == ##_module.Err.Ok);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Err.Ok_q(d) } 
  _module.Err.Ok_q(d) ==> (exists a#40#0#0: Box :: d == #_module.Err.Ok(a#40#0#0)));

// Constructor $Is
axiom (forall _module.Err$V: Ty, a#41#0#0: Box :: 
  { $Is(#_module.Err.Ok(a#41#0#0), Tclass._module.Err(_module.Err$V)) } 
  $Is(#_module.Err.Ok(a#41#0#0), Tclass._module.Err(_module.Err$V))
     <==> $IsBox(a#41#0#0, _module.Err$V));

// Constructor $IsAlloc
axiom (forall _module.Err$V: Ty, a#42#0#0: Box, $h: Heap :: 
  { $IsAlloc(#_module.Err.Ok(a#42#0#0), Tclass._module.Err(_module.Err$V), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Err.Ok(a#42#0#0), Tclass._module.Err(_module.Err$V), $h)
       <==> $IsAllocBox(a#42#0#0, _module.Err$V, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _module.Err$V: Ty, $h: Heap :: 
  { $IsAllocBox(_module.Err.value(d), _module.Err$V, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Err.Ok_q(d)
       && $IsAlloc(d, Tclass._module.Err(_module.Err$V), $h)
     ==> $IsAllocBox(_module.Err.value(d), _module.Err$V, $h));

// Constructor literal
axiom (forall a#43#0#0: Box :: 
  { #_module.Err.Ok(Lit(a#43#0#0)) } 
  #_module.Err.Ok(Lit(a#43#0#0)) == Lit(#_module.Err.Ok(a#43#0#0)));

function _module.Err.value(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#44#0#0: Box :: 
  { #_module.Err.Ok(a#44#0#0) } 
  _module.Err.value(#_module.Err.Ok(a#44#0#0)) == a#44#0#0);

// Inductive rank
axiom (forall a#45#0#0: Box :: 
  { #_module.Err.Ok(a#45#0#0) } 
  BoxRank(a#45#0#0) < DtRank(#_module.Err.Ok(a#45#0#0)));

// Depth-one case-split function
function $IsA#_module.Err(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.Err(d) } 
  $IsA#_module.Err(d) ==> _module.Err.Fail_q(d) || _module.Err.Ok_q(d));

// Questionmark data type disjunctivity
axiom (forall _module.Err$V: Ty, d: DatatypeType :: 
  { _module.Err.Ok_q(d), $Is(d, Tclass._module.Err(_module.Err$V)) } 
    { _module.Err.Fail_q(d), $Is(d, Tclass._module.Err(_module.Err$V)) } 
  $Is(d, Tclass._module.Err(_module.Err$V))
     ==> _module.Err.Fail_q(d) || _module.Err.Ok_q(d));

// Datatype extensional equality declaration
function _module.Err#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.Err.Fail
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Err#Equal(a, b), _module.Err.Fail_q(a) } 
    { _module.Err#Equal(a, b), _module.Err.Fail_q(b) } 
  _module.Err.Fail_q(a) && _module.Err.Fail_q(b)
     ==> (_module.Err#Equal(a, b) <==> _module.Err.err(a) == _module.Err.err(b)));

// Datatype extensional equality definition: #_module.Err.Ok
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Err#Equal(a, b), _module.Err.Ok_q(a) } 
    { _module.Err#Equal(a, b), _module.Err.Ok_q(b) } 
  _module.Err.Ok_q(a) && _module.Err.Ok_q(b)
     ==> (_module.Err#Equal(a, b) <==> _module.Err.value(a) == _module.Err.value(b)));

// Datatype extensionality axiom: _module.Err
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Err#Equal(a, b) } 
  _module.Err#Equal(a, b) <==> a == b);

const unique class._module.Err: ClassName;

// Constructor function declaration
function #_module.Dup.Dup1(bool, int) : DatatypeType;

const unique ##_module.Dup.Dup1: DtCtorId;

// Constructor identifier
axiom (forall a#46#0#0: bool, a#46#1#0: int :: 
  { #_module.Dup.Dup1(a#46#0#0, a#46#1#0) } 
  DatatypeCtorId(#_module.Dup.Dup1(a#46#0#0, a#46#1#0)) == ##_module.Dup.Dup1);

function _module.Dup.Dup1_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Dup.Dup1_q(d) } 
  _module.Dup.Dup1_q(d) <==> DatatypeCtorId(d) == ##_module.Dup.Dup1);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Dup.Dup1_q(d) } 
  _module.Dup.Dup1_q(d)
     ==> (exists a#47#0#0: bool, a#47#1#0: int :: 
      d == #_module.Dup.Dup1(a#47#0#0, a#47#1#0)));

function Tclass._module.Dup() : Ty;

const unique Tagclass._module.Dup: TyTag;

// Tclass._module.Dup Tag
axiom Tag(Tclass._module.Dup()) == Tagclass._module.Dup
   && TagFamily(Tclass._module.Dup()) == tytagFamily$Dup;

// Box/unbox axiom for Tclass._module.Dup
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Dup()) } 
  $IsBox(bx, Tclass._module.Dup())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Dup()));

// Constructor $Is
axiom (forall a#48#0#0: bool, a#48#1#0: int :: 
  { $Is(#_module.Dup.Dup1(a#48#0#0, a#48#1#0), Tclass._module.Dup()) } 
  $Is(#_module.Dup.Dup1(a#48#0#0, a#48#1#0), Tclass._module.Dup())
     <==> $Is(a#48#0#0, TBool) && $Is(a#48#1#0, Tclass._module.uint32()));

// Constructor $IsAlloc
axiom (forall a#49#0#0: bool, a#49#1#0: int, $h: Heap :: 
  { $IsAlloc(#_module.Dup.Dup1(a#49#0#0, a#49#1#0), Tclass._module.Dup(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Dup.Dup1(a#49#0#0, a#49#1#0), Tclass._module.Dup(), $h)
       <==> $IsAlloc(a#49#0#0, TBool, $h) && $IsAlloc(a#49#1#0, Tclass._module.uint32(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Dup.b(d), TBool, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Dup.Dup1_q(d)
       && $IsAlloc(d, Tclass._module.Dup(), $h)
     ==> $IsAlloc(_module.Dup.b(d), TBool, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Dup.x(d), Tclass._module.uint32(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.Dup.Dup1_q(d)
       && $IsAlloc(d, Tclass._module.Dup(), $h)
     ==> $IsAlloc(_module.Dup.x(d), Tclass._module.uint32(), $h));

// Constructor literal
axiom (forall a#50#0#0: bool, a#50#1#0: int :: 
  { #_module.Dup.Dup1(Lit(a#50#0#0), LitInt(a#50#1#0)) } 
  #_module.Dup.Dup1(Lit(a#50#0#0), LitInt(a#50#1#0))
     == Lit(#_module.Dup.Dup1(a#50#0#0, a#50#1#0)));

function _module.Dup.b(DatatypeType) : bool;

// Constructor injectivity
axiom (forall a#51#0#0: bool, a#51#1#0: int :: 
  { #_module.Dup.Dup1(a#51#0#0, a#51#1#0) } 
  _module.Dup.b(#_module.Dup.Dup1(a#51#0#0, a#51#1#0)) == a#51#0#0);

function _module.Dup.x(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#52#0#0: bool, a#52#1#0: int :: 
  { #_module.Dup.Dup1(a#52#0#0, a#52#1#0) } 
  _module.Dup.x(#_module.Dup.Dup1(a#52#0#0, a#52#1#0)) == a#52#1#0);

// Constructor function declaration
function #_module.Dup.Dup2(int) : DatatypeType;

const unique ##_module.Dup.Dup2: DtCtorId;

// Constructor identifier
axiom (forall a#53#0#0: int :: 
  { #_module.Dup.Dup2(a#53#0#0) } 
  DatatypeCtorId(#_module.Dup.Dup2(a#53#0#0)) == ##_module.Dup.Dup2);

function _module.Dup.Dup2_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Dup.Dup2_q(d) } 
  _module.Dup.Dup2_q(d) <==> DatatypeCtorId(d) == ##_module.Dup.Dup2);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Dup.Dup2_q(d) } 
  _module.Dup.Dup2_q(d)
     ==> (exists a#54#0#0: int :: d == #_module.Dup.Dup2(a#54#0#0)));

// Constructor $Is
axiom (forall a#55#0#0: int :: 
  { $Is(#_module.Dup.Dup2(a#55#0#0), Tclass._module.Dup()) } 
  $Is(#_module.Dup.Dup2(a#55#0#0), Tclass._module.Dup())
     <==> $Is(a#55#0#0, Tclass._module.uint32()));

// Constructor $IsAlloc
axiom (forall a#56#0#0: int, $h: Heap :: 
  { $IsAlloc(#_module.Dup.Dup2(a#56#0#0), Tclass._module.Dup(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Dup.Dup2(a#56#0#0), Tclass._module.Dup(), $h)
       <==> $IsAlloc(a#56#0#0, Tclass._module.uint32(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Dup.x(d), Tclass._module.uint32(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.Dup.Dup2_q(d)
       && $IsAlloc(d, Tclass._module.Dup(), $h)
     ==> $IsAlloc(_module.Dup.x(d), Tclass._module.uint32(), $h));

// Constructor literal
axiom (forall a#57#0#0: int :: 
  { #_module.Dup.Dup2(LitInt(a#57#0#0)) } 
  #_module.Dup.Dup2(LitInt(a#57#0#0)) == Lit(#_module.Dup.Dup2(a#57#0#0)));

// Constructor injectivity
axiom (forall a#58#0#0: int :: 
  { #_module.Dup.Dup2(a#58#0#0) } 
  _module.Dup.x(#_module.Dup.Dup2(a#58#0#0)) == a#58#0#0);

// Depth-one case-split function
function $IsA#_module.Dup(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.Dup(d) } 
  $IsA#_module.Dup(d) ==> _module.Dup.Dup1_q(d) || _module.Dup.Dup2_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.Dup.Dup2_q(d), $Is(d, Tclass._module.Dup()) } 
    { _module.Dup.Dup1_q(d), $Is(d, Tclass._module.Dup()) } 
  $Is(d, Tclass._module.Dup()) ==> _module.Dup.Dup1_q(d) || _module.Dup.Dup2_q(d));

// Datatype extensional equality declaration
function _module.Dup#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.Dup.Dup1
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Dup#Equal(a, b), _module.Dup.Dup1_q(a) } 
    { _module.Dup#Equal(a, b), _module.Dup.Dup1_q(b) } 
  _module.Dup.Dup1_q(a) && _module.Dup.Dup1_q(b)
     ==> (_module.Dup#Equal(a, b)
       <==> _module.Dup.b(a) == _module.Dup.b(b) && _module.Dup.x(a) == _module.Dup.x(b)));

// Datatype extensional equality definition: #_module.Dup.Dup2
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Dup#Equal(a, b), _module.Dup.Dup2_q(a) } 
    { _module.Dup#Equal(a, b), _module.Dup.Dup2_q(b) } 
  _module.Dup.Dup2_q(a) && _module.Dup.Dup2_q(b)
     ==> (_module.Dup#Equal(a, b) <==> _module.Dup.x(a) == _module.Dup.x(b)));

// Datatype extensionality axiom: _module.Dup
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Dup#Equal(a, b) } 
  _module.Dup#Equal(a, b) <==> a == b);

const unique class._module.Dup: ClassName;

// Constructor function declaration
function #_module.IntList.Nil() : DatatypeType;

const unique ##_module.IntList.Nil: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#_module.IntList.Nil()) == ##_module.IntList.Nil;

function _module.IntList.Nil_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.IntList.Nil_q(d) } 
  _module.IntList.Nil_q(d) <==> DatatypeCtorId(d) == ##_module.IntList.Nil);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.IntList.Nil_q(d) } 
  _module.IntList.Nil_q(d) ==> d == #_module.IntList.Nil());

function Tclass._module.IntList() : Ty;

const unique Tagclass._module.IntList: TyTag;

// Tclass._module.IntList Tag
axiom Tag(Tclass._module.IntList()) == Tagclass._module.IntList
   && TagFamily(Tclass._module.IntList()) == tytagFamily$IntList;

// Box/unbox axiom for Tclass._module.IntList
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.IntList()) } 
  $IsBox(bx, Tclass._module.IntList())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.IntList()));

// Constructor $Is
axiom $Is(#_module.IntList.Nil(), Tclass._module.IntList());

// Constructor $IsAlloc
axiom (forall $h: Heap :: 
  { $IsAlloc(#_module.IntList.Nil(), Tclass._module.IntList(), $h) } 
  $IsGoodHeap($h)
     ==> $IsAlloc(#_module.IntList.Nil(), Tclass._module.IntList(), $h));

// Constructor literal
axiom #_module.IntList.Nil() == Lit(#_module.IntList.Nil());

// Constructor function declaration
function #_module.IntList.Cons(int, DatatypeType) : DatatypeType;

const unique ##_module.IntList.Cons: DtCtorId;

// Constructor identifier
axiom (forall a#64#0#0: int, a#64#1#0: DatatypeType :: 
  { #_module.IntList.Cons(a#64#0#0, a#64#1#0) } 
  DatatypeCtorId(#_module.IntList.Cons(a#64#0#0, a#64#1#0))
     == ##_module.IntList.Cons);

function _module.IntList.Cons_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.IntList.Cons_q(d) } 
  _module.IntList.Cons_q(d) <==> DatatypeCtorId(d) == ##_module.IntList.Cons);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.IntList.Cons_q(d) } 
  _module.IntList.Cons_q(d)
     ==> (exists a#65#0#0: int, a#65#1#0: DatatypeType :: 
      d == #_module.IntList.Cons(a#65#0#0, a#65#1#0)));

// Constructor $Is
axiom (forall a#66#0#0: int, a#66#1#0: DatatypeType :: 
  { $Is(#_module.IntList.Cons(a#66#0#0, a#66#1#0), Tclass._module.IntList()) } 
  $Is(#_module.IntList.Cons(a#66#0#0, a#66#1#0), Tclass._module.IntList())
     <==> $Is(a#66#0#0, Tclass._module.uint32())
       && $Is(a#66#1#0, Tclass._module.IntList()));

// Constructor $IsAlloc
axiom (forall a#67#0#0: int, a#67#1#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#_module.IntList.Cons(a#67#0#0, a#67#1#0), Tclass._module.IntList(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.IntList.Cons(a#67#0#0, a#67#1#0), Tclass._module.IntList(), $h)
       <==> $IsAlloc(a#67#0#0, Tclass._module.uint32(), $h)
         && $IsAlloc(a#67#1#0, Tclass._module.IntList(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.IntList.hd(d), Tclass._module.uint32(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.IntList.Cons_q(d)
       && $IsAlloc(d, Tclass._module.IntList(), $h)
     ==> $IsAlloc(_module.IntList.hd(d), Tclass._module.uint32(), $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.IntList.tl(d), Tclass._module.IntList(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.IntList.Cons_q(d)
       && $IsAlloc(d, Tclass._module.IntList(), $h)
     ==> $IsAlloc(_module.IntList.tl(d), Tclass._module.IntList(), $h));

// Constructor literal
axiom (forall a#68#0#0: int, a#68#1#0: DatatypeType :: 
  { #_module.IntList.Cons(LitInt(a#68#0#0), Lit(a#68#1#0)) } 
  #_module.IntList.Cons(LitInt(a#68#0#0), Lit(a#68#1#0))
     == Lit(#_module.IntList.Cons(a#68#0#0, a#68#1#0)));

function _module.IntList.hd(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#69#0#0: int, a#69#1#0: DatatypeType :: 
  { #_module.IntList.Cons(a#69#0#0, a#69#1#0) } 
  _module.IntList.hd(#_module.IntList.Cons(a#69#0#0, a#69#1#0)) == a#69#0#0);

function _module.IntList.tl(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#70#0#0: int, a#70#1#0: DatatypeType :: 
  { #_module.IntList.Cons(a#70#0#0, a#70#1#0) } 
  _module.IntList.tl(#_module.IntList.Cons(a#70#0#0, a#70#1#0)) == a#70#1#0);

// Inductive rank
axiom (forall a#71#0#0: int, a#71#1#0: DatatypeType :: 
  { #_module.IntList.Cons(a#71#0#0, a#71#1#0) } 
  DtRank(a#71#1#0) < DtRank(#_module.IntList.Cons(a#71#0#0, a#71#1#0)));

// Depth-one case-split function
function $IsA#_module.IntList(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.IntList(d) } 
  $IsA#_module.IntList(d)
     ==> _module.IntList.Nil_q(d) || _module.IntList.Cons_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.IntList.Cons_q(d), $Is(d, Tclass._module.IntList()) } 
    { _module.IntList.Nil_q(d), $Is(d, Tclass._module.IntList()) } 
  $Is(d, Tclass._module.IntList())
     ==> _module.IntList.Nil_q(d) || _module.IntList.Cons_q(d));

// Datatype extensional equality declaration
function _module.IntList#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.IntList.Nil
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.IntList#Equal(a, b), _module.IntList.Nil_q(a) } 
    { _module.IntList#Equal(a, b), _module.IntList.Nil_q(b) } 
  _module.IntList.Nil_q(a) && _module.IntList.Nil_q(b)
     ==> (_module.IntList#Equal(a, b) <==> true));

// Datatype extensional equality definition: #_module.IntList.Cons
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.IntList#Equal(a, b), _module.IntList.Cons_q(a) } 
    { _module.IntList#Equal(a, b), _module.IntList.Cons_q(b) } 
  _module.IntList.Cons_q(a) && _module.IntList.Cons_q(b)
     ==> (_module.IntList#Equal(a, b)
       <==> _module.IntList.hd(a) == _module.IntList.hd(b)
         && _module.IntList#Equal(_module.IntList.tl(a), _module.IntList.tl(b))));

// Datatype extensionality axiom: _module.IntList
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.IntList#Equal(a, b) } 
  _module.IntList#Equal(a, b) <==> a == b);

const unique class._module.IntList: ClassName;

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

procedure CheckWellformed$$_module.__default.Matcher(e#0: DatatypeType
       where $Is(e#0, Tclass._module.Example1())
         && $IsAlloc(e#0, Tclass._module.Example1(), $Heap)
         && $IsA#_module.Example1(e#0));
  free requires 12 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Matcher(e#0: DatatypeType
       where $Is(e#0, Tclass._module.Example1())
         && $IsAlloc(e#0, Tclass._module.Example1(), $Heap)
         && $IsA#_module.Example1(e#0));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.Matcher(e#0: DatatypeType
       where $Is(e#0, Tclass._module.Example1())
         && $IsAlloc(e#0, Tclass._module.Example1(), $Heap)
         && $IsA#_module.Example1(e#0))
   returns ($_reverifyPost: bool);
  free requires 12 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure CheckWellformed$$_module.__default.TupleMatch(e1#0: DatatypeType
       where $Is(e1#0, Tclass._module.Example2())
         && $IsAlloc(e1#0, Tclass._module.Example2(), $Heap)
         && $IsA#_module.Example2(e1#0), 
    e2#0: DatatypeType
       where $Is(e2#0, Tclass._module.Example2())
         && $IsAlloc(e2#0, Tclass._module.Example2(), $Heap)
         && $IsA#_module.Example2(e2#0));
  free requires 13 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.TupleMatch(e1#0: DatatypeType
       where $Is(e1#0, Tclass._module.Example2())
         && $IsAlloc(e1#0, Tclass._module.Example2(), $Heap)
         && $IsA#_module.Example2(e1#0), 
    e2#0: DatatypeType
       where $Is(e2#0, Tclass._module.Example2())
         && $IsAlloc(e2#0, Tclass._module.Example2(), $Heap)
         && $IsA#_module.Example2(e2#0));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.TupleMatch(e1#0: DatatypeType
       where $Is(e1#0, Tclass._module.Example2())
         && $IsAlloc(e1#0, Tclass._module.Example2(), $Heap)
         && $IsA#_module.Example2(e1#0), 
    e2#0: DatatypeType
       where $Is(e2#0, Tclass._module.Example2())
         && $IsAlloc(e2#0, Tclass._module.Example2(), $Heap)
         && $IsA#_module.Example2(e2#0))
   returns ($_reverifyPost: bool);
  free requires 13 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure CheckWellformed$$_module.__default.Callee(e#0: DatatypeType
       where $Is(e#0, Tclass._module.Example2())
         && $IsAlloc(e#0, Tclass._module.Example2(), $Heap)
         && $IsA#_module.Example2(e#0));
  free requires 14 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Callee(e#0: DatatypeType
       where $Is(e#0, Tclass._module.Example2())
         && $IsAlloc(e#0, Tclass._module.Example2(), $Heap)
         && $IsA#_module.Example2(e#0));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.Callee(e#0: DatatypeType
       where $Is(e#0, Tclass._module.Example2())
         && $IsAlloc(e#0, Tclass._module.Example2(), $Heap)
         && $IsA#_module.Example2(e#0))
   returns ($_reverifyPost: bool);
  free requires 14 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure CheckWellformed$$_module.__default.DtUpdate(e#0: DatatypeType
       where $Is(e#0, Tclass._module.Example1())
         && $IsAlloc(e#0, Tclass._module.Example1(), $Heap)
         && $IsA#_module.Example1(e#0));
  free requires 15 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.DtUpdate(e#0: DatatypeType
       where $Is(e#0, Tclass._module.Example1())
         && $IsAlloc(e#0, Tclass._module.Example1(), $Heap)
         && $IsA#_module.Example1(e#0));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.DtUpdate(e#0: DatatypeType
       where $Is(e#0, Tclass._module.Example1())
         && $IsAlloc(e#0, Tclass._module.Example1(), $Heap)
         && $IsA#_module.Example1(e#0))
   returns ($_reverifyPost: bool);
  free requires 15 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.DtUpdate(e#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var x#0: DatatypeType
     where $Is(x#0, Tclass._module.Example1())
       && $IsAlloc(x#0, Tclass._module.Example1(), $Heap);
  var dt_update_tmp#0#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var dt_update#u#0#Z#0: int;
  var let#1#0#0: int;
  var newtype$check#0: int;

    // AddMethodImpl: DtUpdate, Impl$$_module.__default.DtUpdate
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(46,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(47,9)
    assume true;
    havoc dt_update_tmp#0#Z#0;
    assume $Is(dt_update_tmp#0#Z#0, Tclass._module.Example1());
    assume let#0#0#0 == e#0;
    assume true;
    // CheckWellformedWithResult: any expression
    assume $Is(let#0#0#0, Tclass._module.Example1());
    assume dt_update_tmp#0#Z#0 == let#0#0#0;
    havoc dt_update#u#0#Z#0;
    assume LitInt(0) <= dt_update#u#0#Z#0 && dt_update#u#0#Z#0 < 4294967296;
    newtype$check#0 := LitInt(0);
    assert LitInt(0) <= newtype$check#0 && newtype$check#0 < 4294967296;
    assume let#1#0#0 == LitInt(0);
    assume true;
    // CheckWellformedWithResult: any expression
    assume $Is(let#1#0#0, Tclass._module.uint32());
    assume dt_update#u#0#Z#0 == let#1#0#0;
    assume _module.Example1.Example1_q(dt_update_tmp#0#Z#0);
    assume (var dt_update_tmp#0#0 := e#0; _module.Example1.Example1_q(dt_update_tmp#0#0));
    x#0 := (var dt_update_tmp#0#0 := e#0; 
      (var dt_update#u#0#0 := LitInt(0); 
        #_module.Example1.Example1(dt_update#u#0#0, _module.Example1.b(dt_update_tmp#0#0))));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(47,21)"} true;
}



procedure CheckWellformed$$_module.__default.TestDestructor();
  free requires 27 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.TestDestructor();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.TestDestructor() returns ($_reverifyPost: bool);
  free requires 27 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.TestDestructor() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var e1#0: DatatypeType
     where $Is(e1#0, Tclass._module.Example1())
       && $IsAlloc(e1#0, Tclass._module.Example1(), $Heap);
  var newtype$check#0: int;
  var x#0: int where LitInt(0) <= x#0 && x#0 < 4294967296;
  var newtype$check#1: int;

    // AddMethodImpl: TestDestructor, Impl$$_module.__default.TestDestructor
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(50,24): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(51,10)
    assume true;
    newtype$check#0 := LitInt(22);
    assert LitInt(0) <= newtype$check#0 && newtype$check#0 < 4294967296;
    assume true;
    e1#0 := Lit(#_module.Example1.Example1(LitInt(22), Lit(false)));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(51,31)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(52,9)
    assume true;
    assume _module.Example1.Example1_q(e1#0);
    assume _module.Example1.Example1_q(e1#0);
    x#0 := _module.Example1.u(e1#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(52,15)"} true;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(53,3)
    newtype$check#1 := LitInt(22);
    assert LitInt(0) <= newtype$check#1 && newtype$check#1 < 4294967296;
    assume true;
    if (x#0 == LitInt(22))
    {
        // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(54,5)
        assume true;
    }
    else
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(56,5)
        assume true;
        assert false;
        // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(57,5)
        assume true;
    }
}



procedure CheckWellformed$$_module.__default.TestGenericDefault();
  free requires 24 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.TestGenericDefault();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.TestGenericDefault() returns ($_reverifyPost: bool);
  free requires 24 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure CheckWellformed$$_module.__default.matcher(e#0: DatatypeType
       where $Is(e#0, Tclass._module.Err(Tclass._module.uint32()))
         && $IsAlloc(e#0, Tclass._module.Err(Tclass._module.uint32()), $Heap)
         && $IsA#_module.Err(e#0));
  free requires 17 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.matcher(e#0: DatatypeType
       where $Is(e#0, Tclass._module.Err(Tclass._module.uint32()))
         && $IsAlloc(e#0, Tclass._module.Err(Tclass._module.uint32()), $Heap)
         && $IsA#_module.Err(e#0));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.matcher(e#0: DatatypeType
       where $Is(e#0, Tclass._module.Err(Tclass._module.uint32()))
         && $IsAlloc(e#0, Tclass._module.Err(Tclass._module.uint32()), $Heap)
         && $IsA#_module.Err(e#0))
   returns ($_reverifyPost: bool);
  free requires 17 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure CheckWellformed$$_module.__default.GenericTest();
  free requires 25 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.GenericTest();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.GenericTest() returns ($_reverifyPost: bool);
  free requires 25 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.GenericTest() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var v#0: DatatypeType
     where $Is(v#0, Tclass._module.Option(Tclass._module.uint32()))
       && $IsAlloc(v#0, Tclass._module.Option(Tclass._module.uint32()), $Heap);
  var newtype$check#0: int;
  var e##0: DatatypeType;
  var newtype$check#1: int;
  var e##1: DatatypeType;

    // AddMethodImpl: GenericTest, Impl$$_module.__default.GenericTest
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(77,21): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(78,24)
    assume true;
    newtype$check#0 := LitInt(32);
    assert LitInt(0) <= newtype$check#0 && newtype$check#0 < 4294967296;
    assume true;
    v#0 := Lit(#_module.Option.Some($Box(LitInt(32))));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(78,34)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(79,10)
    // TrCallStmt: Before ProcessCallStmt
    newtype$check#1 := LitInt(42);
    assert LitInt(0) <= newtype$check#1 && newtype$check#1 < 4294967296;
    assume true;
    // ProcessCallStmt: CheckSubrange
    e##0 := Lit(#_module.Err.Ok($Box(LitInt(42))));
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.matcher(e##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(79,17)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(80,10)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    e##1 := Lit(#_module.Err.Fail(Lit(true)));
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.matcher(e##1);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(80,21)"} true;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(81,3)
    assume true;
    if (_module.Option.Some_q(v#0))
    {
        // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(81,16)
        assume true;
        assert _module.Option.Some_q(v#0);
        assume true;
        assume true;
    }
    else
    {
    }
}



procedure CheckWellformed$$_module.__default.Comparison(x0#0: DatatypeType
       where $Is(x0#0, Tclass._module.Example1())
         && $IsAlloc(x0#0, Tclass._module.Example1(), $Heap)
         && $IsA#_module.Example1(x0#0), 
    x1#0: DatatypeType
       where $Is(x1#0, Tclass._module.Example1())
         && $IsAlloc(x1#0, Tclass._module.Example1(), $Heap)
         && $IsA#_module.Example1(x1#0), 
    y0#0: DatatypeType
       where $Is(y0#0, Tclass._module.Example4())
         && $IsAlloc(y0#0, Tclass._module.Example4(), $Heap)
         && $IsA#_module.Example4(y0#0), 
    y1#0: DatatypeType
       where $Is(y1#0, Tclass._module.Example4())
         && $IsAlloc(y1#0, Tclass._module.Example4(), $Heap)
         && $IsA#_module.Example4(y1#0));
  free requires 19 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Comparison(x0#0: DatatypeType
       where $Is(x0#0, Tclass._module.Example1())
         && $IsAlloc(x0#0, Tclass._module.Example1(), $Heap)
         && $IsA#_module.Example1(x0#0), 
    x1#0: DatatypeType
       where $Is(x1#0, Tclass._module.Example1())
         && $IsAlloc(x1#0, Tclass._module.Example1(), $Heap)
         && $IsA#_module.Example1(x1#0), 
    y0#0: DatatypeType
       where $Is(y0#0, Tclass._module.Example4())
         && $IsAlloc(y0#0, Tclass._module.Example4(), $Heap)
         && $IsA#_module.Example4(y0#0), 
    y1#0: DatatypeType
       where $Is(y1#0, Tclass._module.Example4())
         && $IsAlloc(y1#0, Tclass._module.Example4(), $Heap)
         && $IsA#_module.Example4(y1#0));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.Comparison(x0#0: DatatypeType
       where $Is(x0#0, Tclass._module.Example1())
         && $IsAlloc(x0#0, Tclass._module.Example1(), $Heap)
         && $IsA#_module.Example1(x0#0), 
    x1#0: DatatypeType
       where $Is(x1#0, Tclass._module.Example1())
         && $IsAlloc(x1#0, Tclass._module.Example1(), $Heap)
         && $IsA#_module.Example1(x1#0), 
    y0#0: DatatypeType
       where $Is(y0#0, Tclass._module.Example4())
         && $IsAlloc(y0#0, Tclass._module.Example4(), $Heap)
         && $IsA#_module.Example4(y0#0), 
    y1#0: DatatypeType
       where $Is(y1#0, Tclass._module.Example4())
         && $IsAlloc(y1#0, Tclass._module.Example4(), $Heap)
         && $IsA#_module.Example4(y1#0))
   returns ($_reverifyPost: bool);
  free requires 19 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure CheckWellformed$$_module.__default.DupTest(d#0: DatatypeType
       where $Is(d#0, Tclass._module.Dup())
         && $IsAlloc(d#0, Tclass._module.Dup(), $Heap)
         && $IsA#_module.Dup(d#0));
  free requires 20 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.DupTest(d#0: DatatypeType
       where $Is(d#0, Tclass._module.Dup())
         && $IsAlloc(d#0, Tclass._module.Dup(), $Heap)
         && $IsA#_module.Dup(d#0));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.DupTest(d#0: DatatypeType
       where $Is(d#0, Tclass._module.Dup())
         && $IsAlloc(d#0, Tclass._module.Dup(), $Heap)
         && $IsA#_module.Dup(d#0))
   returns ($_reverifyPost: bool);
  free requires 20 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure CheckWellformed$$_module.__default.DupTestTest();
  free requires 26 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.DupTestTest();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.DupTestTest() returns ($_reverifyPost: bool);
  free requires 26 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.DupTestTest() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var d##0: DatatypeType;
  var newtype$check#0: int;
  var d##1: DatatypeType;
  var newtype$check#1: int;

    // AddMethodImpl: DupTestTest, Impl$$_module.__default.DupTestTest
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(110,0): initial state"} true;
    $_reverifyPost := false;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(111,10)
    // TrCallStmt: Before ProcessCallStmt
    newtype$check#0 := LitInt(42);
    assert LitInt(0) <= newtype$check#0 && newtype$check#0 < 4294967296;
    assume true;
    // ProcessCallStmt: CheckSubrange
    d##0 := Lit(#_module.Dup.Dup1(Lit(false), LitInt(42)));
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.DupTest(d##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(111,26)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(112,10)
    // TrCallStmt: Before ProcessCallStmt
    newtype$check#1 := LitInt(330);
    assert LitInt(0) <= newtype$check#1 && newtype$check#1 < 4294967296;
    assume true;
    // ProcessCallStmt: CheckSubrange
    d##1 := Lit(#_module.Dup.Dup2(LitInt(330)));
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.DupTest(d##1);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(112,20)"} true;
}



procedure CheckWellformed$$_module.__default.IntListLen(l#0: DatatypeType
       where $Is(l#0, Tclass._module.IntList())
         && $IsAlloc(l#0, Tclass._module.IntList(), $Heap)
         && $IsA#_module.IntList(l#0))
   returns (len#0: int where LitInt(0) <= len#0 && len#0 < 4294967296);
  free requires 21 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.IntListLen(l#0: DatatypeType
       where $Is(l#0, Tclass._module.IntList())
         && $IsAlloc(l#0, Tclass._module.IntList(), $Heap)
         && $IsA#_module.IntList(l#0))
   returns (len#0: int where LitInt(0) <= len#0 && len#0 < 4294967296);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.IntListLen(l#0: DatatypeType
       where $Is(l#0, Tclass._module.IntList())
         && $IsAlloc(l#0, Tclass._module.IntList(), $Heap)
         && $IsA#_module.IntList(l#0))
   returns (len#0: int where LitInt(0) <= len#0 && len#0 < 4294967296, $_reverifyPost: bool);
  free requires 21 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.IntListLen(l#0: DatatypeType) returns (len#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0_0: int;
  var _mcc#1#0_0: DatatypeType;
  var tl#0_0: DatatypeType;
  var let#0_0#0#0: DatatypeType;
  var hd#0_0: int;
  var let#0_1#0#0: int;
  var len_rest#0_0: int where LitInt(0) <= len_rest#0_0 && len_rest#0_0 < 4294967296;
  var $rhs##0_0: int where LitInt(0) <= $rhs##0_0 && $rhs##0_0 < 4294967296;
  var l##0_0: DatatypeType;
  var newtype$check#0_0: int;
  var newtype$check#0_0_0: int;
  var newtype$check#0_0_1: int;
  var newtype$check#1_0: int;

    // AddMethodImpl: IntListLen, Impl$$_module.__default.IntListLen
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(120,0): initial state"} true;
    $_reverifyPost := false;
    assume true;
    havoc _mcc#0#0_0, _mcc#1#0_0;
    if (l#0 == #_module.IntList.Nil())
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(122,21)
        assume true;
        newtype$check#1_0 := LitInt(0);
        assert LitInt(0) <= newtype$check#1_0 && newtype$check#1_0 < 4294967296;
        assume true;
        len#0 := LitInt(0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(122,24)"} true;
    }
    else if (l#0 == #_module.IntList.Cons(_mcc#0#0_0, _mcc#1#0_0))
    {
        assume LitInt(0) <= _mcc#0#0_0 && _mcc#0#0_0 < 4294967296;
        assume $Is(_mcc#1#0_0, Tclass._module.IntList())
           && $IsAlloc(_mcc#1#0_0, Tclass._module.IntList(), $Heap);
        havoc tl#0_0;
        assume $Is(tl#0_0, Tclass._module.IntList())
           && $IsAlloc(tl#0_0, Tclass._module.IntList(), $Heap);
        assume let#0_0#0#0 == _mcc#1#0_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_0#0#0, Tclass._module.IntList());
        assume tl#0_0 == let#0_0#0#0;
        havoc hd#0_0;
        assume LitInt(0) <= hd#0_0 && hd#0_0 < 4294967296;
        assume let#0_1#0#0 == _mcc#0#0_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_1#0#0, Tclass._module.uint32());
        assume hd#0_0 == let#0_1#0#0;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(124,33)
        assume true;
        // TrCallStmt: Adding lhs with type uint32
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        l##0_0 := tl#0_0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assert DtRank(l##0_0) < DtRank(l#0);
        // ProcessCallStmt: Make the call
        call $rhs##0_0 := Call$$_module.__default.IntListLen(l##0_0);
        // TrCallStmt: After ProcessCallStmt
        len_rest#0_0 := $rhs##0_0;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(124,36)"} true;
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(125,7)
        newtype$check#0_0 := LitInt(4294967295);
        assert LitInt(0) <= newtype$check#0_0 && newtype$check#0_0 < 4294967296;
        assume true;
        if (len_rest#0_0 < 4294967295)
        {
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(126,13)
            assume true;
            newtype$check#0_0_0 := LitInt(1);
            assert LitInt(0) <= newtype$check#0_0_0 && newtype$check#0_0_0 < 4294967296;
            newtype$check#0_0_1 := len_rest#0_0 + 1;
            assert LitInt(0) <= newtype$check#0_0_1 && newtype$check#0_0_1 < 4294967296;
            assume true;
            len#0 := len_rest#0_0 + 1;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(126,27)"} true;
        }
        else
        {
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(128,13)
            assume true;
            assume true;
            len#0 := len_rest#0_0;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(128,23)"} true;
        }
    }
    else
    {
        assume false;
    }
}



procedure CheckWellformed$$_module.__default._default_Main();
  free requires 28 == $FunctionContextHeight;
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
  free requires 28 == $FunctionContextHeight;
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
  var e1#0: DatatypeType
     where $Is(e1#0, Tclass._module.Example1())
       && $IsAlloc(e1#0, Tclass._module.Example1(), $Heap);
  var newtype$check#0: int;
  var e2#0: DatatypeType
     where $Is(e2#0, Tclass._module.Example2())
       && $IsAlloc(e2#0, Tclass._module.Example2(), $Heap);
  var newtype$check#1: int;
  var e##0: DatatypeType;
  var e##1: DatatypeType;
  var x0##0: DatatypeType;
  var newtype$check#2: int;
  var x1##0: DatatypeType;
  var newtype$check#3: int;
  var y0##0: DatatypeType;
  var y1##0: DatatypeType;
  var x0##1: DatatypeType;
  var newtype$check#4: int;
  var x1##1: DatatypeType;
  var newtype$check#5: int;
  var y0##1: DatatypeType;
  var y1##1: DatatypeType;
  var x0##2: DatatypeType;
  var newtype$check#6: int;
  var x1##2: DatatypeType;
  var newtype$check#7: int;
  var y0##2: DatatypeType;
  var y1##2: DatatypeType;
  var len#0: int where LitInt(0) <= len#0 && len#0 < 4294967296;
  var $rhs##0: int where LitInt(0) <= $rhs##0 && $rhs##0 < 4294967296;
  var l##0: DatatypeType;
  var newtype$check#8: int;
  var newtype$check#9: int;
  var newtype$check#10: int;

    // AddMethodImpl: Main, Impl$$_module.__default._default_Main
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(133,14): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(134,10)
    assume true;
    newtype$check#0 := LitInt(22);
    assert LitInt(0) <= newtype$check#0 && newtype$check#0 < 4294967296;
    assume true;
    e1#0 := Lit(#_module.Example1.Example1(LitInt(22), Lit(false)));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(134,31)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(135,10)
    assume true;
    newtype$check#1 := LitInt(42);
    assert LitInt(0) <= newtype$check#1 && newtype$check#1 < 4294967296;
    assume true;
    e2#0 := Lit(#_module.Example2.Ex2a(LitInt(42)));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(135,20)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(136,9)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    e##0 := e2#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.Callee(e##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(136,12)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(137,6)
    assume true;
    assume true;
    e2#0 := Lit(#_module.Example2.Ex2b(Lit(true)));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(137,18)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(138,9)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    e##1 := e2#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.Callee(e##1);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(138,12)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(139,17)
    // TrCallStmt: Before ProcessCallStmt
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.TestDestructor();
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(139,18)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(140,14)
    // TrCallStmt: Before ProcessCallStmt
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.GenericTest();
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(140,15)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(141,13)
    // TrCallStmt: Before ProcessCallStmt
    newtype$check#2 := LitInt(42);
    assert LitInt(0) <= newtype$check#2 && newtype$check#2 < 4294967296;
    assume true;
    // ProcessCallStmt: CheckSubrange
    x0##0 := Lit(#_module.Example1.Example1(LitInt(42), Lit(true)));
    newtype$check#3 := LitInt(42);
    assert LitInt(0) <= newtype$check#3 && newtype$check#3 < 4294967296;
    assume true;
    // ProcessCallStmt: CheckSubrange
    x1##0 := Lit(#_module.Example1.Example1(LitInt(42), Lit(true)));
    assume true;
    // ProcessCallStmt: CheckSubrange
    y0##0 := Lit(#_module.Example4.Ex4b());
    assume true;
    // ProcessCallStmt: CheckSubrange
    y1##0 := Lit(#_module.Example4.Ex4b());
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.Comparison(x0##0, x1##0, y0##0, y1##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(141,64)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(142,13)
    // TrCallStmt: Before ProcessCallStmt
    newtype$check#4 := LitInt(42);
    assert LitInt(0) <= newtype$check#4 && newtype$check#4 < 4294967296;
    assume true;
    // ProcessCallStmt: CheckSubrange
    x0##1 := Lit(#_module.Example1.Example1(LitInt(42), Lit(false)));
    newtype$check#5 := LitInt(42);
    assert LitInt(0) <= newtype$check#5 && newtype$check#5 < 4294967296;
    assume true;
    // ProcessCallStmt: CheckSubrange
    x1##1 := Lit(#_module.Example1.Example1(LitInt(42), Lit(true)));
    assume true;
    // ProcessCallStmt: CheckSubrange
    y0##1 := Lit(#_module.Example4.Ex4a());
    assume true;
    // ProcessCallStmt: CheckSubrange
    y1##1 := Lit(#_module.Example4.Ex4a());
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.Comparison(x0##1, x1##1, y0##1, y1##1);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(142,65)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(143,13)
    // TrCallStmt: Before ProcessCallStmt
    newtype$check#6 := LitInt(2);
    assert LitInt(0) <= newtype$check#6 && newtype$check#6 < 4294967296;
    assume true;
    // ProcessCallStmt: CheckSubrange
    x0##2 := Lit(#_module.Example1.Example1(LitInt(2), Lit(false)));
    newtype$check#7 := LitInt(42);
    assert LitInt(0) <= newtype$check#7 && newtype$check#7 < 4294967296;
    assume true;
    // ProcessCallStmt: CheckSubrange
    x1##2 := Lit(#_module.Example1.Example1(LitInt(42), Lit(false)));
    assume true;
    // ProcessCallStmt: CheckSubrange
    y0##2 := Lit(#_module.Example4.Ex4a());
    assume true;
    // ProcessCallStmt: CheckSubrange
    y1##2 := Lit(#_module.Example4.Ex4b());
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.Comparison(x0##2, x1##2, y0##2, y1##2);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(143,66)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(144,14)
    // TrCallStmt: Before ProcessCallStmt
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.DupTestTest();
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(144,15)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(146,24)
    assume true;
    // TrCallStmt: Adding lhs with type uint32
    // TrCallStmt: Before ProcessCallStmt
    newtype$check#8 := LitInt(15);
    assert LitInt(0) <= newtype$check#8 && newtype$check#8 < 4294967296;
    newtype$check#9 := LitInt(18);
    assert LitInt(0) <= newtype$check#9 && newtype$check#9 < 4294967296;
    newtype$check#10 := LitInt(330);
    assert LitInt(0) <= newtype$check#10 && newtype$check#10 < 4294967296;
    assume true;
    // ProcessCallStmt: CheckSubrange
    l##0 := Lit(#_module.IntList.Cons(LitInt(15), 
        Lit(#_module.IntList.Cons(LitInt(18), Lit(#_module.IntList.Cons(LitInt(330), Lit(#_module.IntList.Nil())))))));
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0 := Call$$_module.__default.IntListLen(l##0);
    // TrCallStmt: After ProcessCallStmt
    len#0 := $rhs##0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(146,59)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/c++/datatypes.dfy(147,3)
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

const unique tytagFamily$_tuple#2: TyTagFamily;

const unique tytagFamily$_tuple#0: TyTagFamily;

const unique tytagFamily$uint32: TyTagFamily;

const unique tytagFamily$Op: TyTagFamily;

const unique tytagFamily$Example1: TyTagFamily;

const unique tytagFamily$Example2: TyTagFamily;

const unique tytagFamily$Example3: TyTagFamily;

const unique tytagFamily$Example4: TyTagFamily;

const unique tytagFamily$Example5: TyTagFamily;

const unique tytagFamily$Example6: TyTagFamily;

const unique tytagFamily$Ex1Sub: TyTagFamily;

const unique tytagFamily$Ex2Sub: TyTagFamily;

const unique tytagFamily$Ex3Sub: TyTagFamily;

const unique tytagFamily$DtPointer: TyTagFamily;

const unique tytagFamily$DtPointerHolder: TyTagFamily;

const unique tytagFamily$Option: TyTagFamily;

const unique tytagFamily$Err: TyTagFamily;

const unique tytagFamily$Dup: TyTagFamily;

const unique tytagFamily$IntList: TyTagFamily;

const unique tytagFamily$_default: TyTagFamily;