// Dafny 3.0.0.30204
// Command Line Options: -compile:0 -noVerify /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy -print:./SeparationLogicList.bpl

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

const unique class._module.Node?: ClassName;

function Tclass._module.Node?(Ty) : Ty;

const unique Tagclass._module.Node?: TyTag;

// Tclass._module.Node? Tag
axiom (forall _module.Node$T: Ty :: 
  { Tclass._module.Node?(_module.Node$T) } 
  Tag(Tclass._module.Node?(_module.Node$T)) == Tagclass._module.Node?
     && TagFamily(Tclass._module.Node?(_module.Node$T)) == tytagFamily$Node);

// Tclass._module.Node? injectivity 0
axiom (forall _module.Node$T: Ty :: 
  { Tclass._module.Node?(_module.Node$T) } 
  Tclass._module.Node?_0(Tclass._module.Node?(_module.Node$T)) == _module.Node$T);

function Tclass._module.Node?_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.Node?
axiom (forall _module.Node$T: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.Node?(_module.Node$T)) } 
  $IsBox(bx, Tclass._module.Node?(_module.Node$T))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.Node?(_module.Node$T)));

// Node: Class $Is
axiom (forall _module.Node$T: Ty, $o: ref :: 
  { $Is($o, Tclass._module.Node?(_module.Node$T)) } 
  $Is($o, Tclass._module.Node?(_module.Node$T))
     <==> $o == null || dtype($o) == Tclass._module.Node?(_module.Node$T));

// Node: Class $IsAlloc
axiom (forall _module.Node$T: Ty, $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.Node?(_module.Node$T), $h) } 
  $IsAlloc($o, Tclass._module.Node?(_module.Node$T), $h)
     <==> $o == null || read($h, $o, alloc));

axiom FDim(_module.Node.data) == 0
   && FieldOfDecl(class._module.Node?, field$data) == _module.Node.data
   && !$IsGhostField(_module.Node.data);

const _module.Node.data: Field Box;

// Node.data: Type axiom
axiom (forall _module.Node$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.Node.data), Tclass._module.Node?(_module.Node$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Node?(_module.Node$T)
     ==> $IsBox(read($h, $o, _module.Node.data), _module.Node$T));

// Node.data: Allocation axiom
axiom (forall _module.Node$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.Node.data), Tclass._module.Node?(_module.Node$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Node?(_module.Node$T)
       && read($h, $o, alloc)
     ==> $IsAllocBox(read($h, $o, _module.Node.data), _module.Node$T, $h));

axiom FDim(_module.Node.next) == 0
   && FieldOfDecl(class._module.Node?, field$next) == _module.Node.next
   && !$IsGhostField(_module.Node.next);

const _module.Node.next: Field ref;

// Node.next: Type axiom
axiom (forall _module.Node$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.Node.next), Tclass._module.Node?(_module.Node$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Node?(_module.Node$T)
     ==> $Is(read($h, $o, _module.Node.next), Tclass._module.Node?(_module.Node$T)));

// Node.next: Allocation axiom
axiom (forall _module.Node$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.Node.next), Tclass._module.Node?(_module.Node$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Node?(_module.Node$T)
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Node.next), Tclass._module.Node?(_module.Node$T), $h));

// function declaration for _module.Node.ListSegment
function _module.Node.ListSegment(_module.Node$T: Ty, 
    $ly: LayerType, 
    $heap: Heap, 
    q#0: Seq Box, 
    from#0: ref, 
    to#0: ref, 
    S#0: Set Box)
   : bool;

function _module.Node.ListSegment#canCall(_module.Node$T: Ty, 
    $heap: Heap, 
    q#0: Seq Box, 
    from#0: ref, 
    to#0: ref, 
    S#0: Set Box)
   : bool;

// layer synonym axiom
axiom (forall _module.Node$T: Ty, 
    $ly: LayerType, 
    $Heap: Heap, 
    q#0: Seq Box, 
    from#0: ref, 
    to#0: ref, 
    S#0: Set Box :: 
  { _module.Node.ListSegment(_module.Node$T, $LS($ly), $Heap, q#0, from#0, to#0, S#0) } 
  _module.Node.ListSegment(_module.Node$T, $LS($ly), $Heap, q#0, from#0, to#0, S#0)
     == _module.Node.ListSegment(_module.Node$T, $ly, $Heap, q#0, from#0, to#0, S#0));

// fuel synonym axiom
axiom (forall _module.Node$T: Ty, 
    $ly: LayerType, 
    $Heap: Heap, 
    q#0: Seq Box, 
    from#0: ref, 
    to#0: ref, 
    S#0: Set Box :: 
  { _module.Node.ListSegment(_module.Node$T, AsFuelBottom($ly), $Heap, q#0, from#0, to#0, S#0) } 
  _module.Node.ListSegment(_module.Node$T, $ly, $Heap, q#0, from#0, to#0, S#0)
     == _module.Node.ListSegment(_module.Node$T, $LZ, $Heap, q#0, from#0, to#0, S#0));

function Tclass._module.Node(Ty) : Ty;

const unique Tagclass._module.Node: TyTag;

// Tclass._module.Node Tag
axiom (forall _module.Node$T: Ty :: 
  { Tclass._module.Node(_module.Node$T) } 
  Tag(Tclass._module.Node(_module.Node$T)) == Tagclass._module.Node
     && TagFamily(Tclass._module.Node(_module.Node$T)) == tytagFamily$Node);

// Tclass._module.Node injectivity 0
axiom (forall _module.Node$T: Ty :: 
  { Tclass._module.Node(_module.Node$T) } 
  Tclass._module.Node_0(Tclass._module.Node(_module.Node$T)) == _module.Node$T);

function Tclass._module.Node_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.Node
axiom (forall _module.Node$T: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.Node(_module.Node$T)) } 
  $IsBox(bx, Tclass._module.Node(_module.Node$T))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.Node(_module.Node$T)));

// frame axiom for _module.Node.ListSegment
axiom (forall _module.Node$T: Ty, 
    $ly: LayerType, 
    $h0: Heap, 
    $h1: Heap, 
    q#0: Seq Box, 
    from#0: ref, 
    to#0: ref, 
    S#0: Set Box :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.Node.ListSegment(_module.Node$T, $ly, $h1, q#0, from#0, to#0, S#0) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && (_module.Node.ListSegment#canCall(_module.Node$T, $h0, q#0, from#0, to#0, S#0)
         || (
          $Is(q#0, TSeq(_module.Node$T))
           && $Is(from#0, Tclass._module.Node?(_module.Node$T))
           && $Is(to#0, Tclass._module.Node?(_module.Node$T))
           && $Is(S#0, TSet(Tclass._module.Node(_module.Node$T)))))
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && S#0[$Box($o)] ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.Node.ListSegment(_module.Node$T, $ly, $h0, q#0, from#0, to#0, S#0)
       == _module.Node.ListSegment(_module.Node$T, $ly, $h1, q#0, from#0, to#0, S#0));

// consequence axiom for _module.Node.ListSegment
axiom 1 <= $FunctionContextHeight
   ==> (forall _module.Node$T: Ty, 
      $ly: LayerType, 
      $Heap: Heap, 
      q#0: Seq Box, 
      from#0: ref, 
      to#0: ref, 
      S#0: Set Box :: 
    { _module.Node.ListSegment(_module.Node$T, $ly, $Heap, q#0, from#0, to#0, S#0) } 
    _module.Node.ListSegment#canCall(_module.Node$T, $Heap, q#0, from#0, to#0, S#0)
         || (1 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(q#0, TSeq(_module.Node$T))
           && $Is(from#0, Tclass._module.Node?(_module.Node$T))
           && $Is(to#0, Tclass._module.Node?(_module.Node$T))
           && $Is(S#0, TSet(Tclass._module.Node(_module.Node$T))))
       ==> true);

function _module.Node.ListSegment#requires(Ty, LayerType, Heap, Seq Box, ref, ref, Set Box) : bool;

// #requires axiom for _module.Node.ListSegment
axiom (forall _module.Node$T: Ty, 
    $ly: LayerType, 
    $Heap: Heap, 
    q#0: Seq Box, 
    from#0: ref, 
    to#0: ref, 
    S#0: Set Box :: 
  { _module.Node.ListSegment#requires(_module.Node$T, $ly, $Heap, q#0, from#0, to#0, S#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && $Is(q#0, TSeq(_module.Node$T))
       && $Is(from#0, Tclass._module.Node?(_module.Node$T))
       && $Is(to#0, Tclass._module.Node?(_module.Node$T))
       && $Is(S#0, TSet(Tclass._module.Node(_module.Node$T)))
     ==> _module.Node.ListSegment#requires(_module.Node$T, $ly, $Heap, q#0, from#0, to#0, S#0)
       == true);

// definition axiom for _module.Node.ListSegment (revealed)
axiom 1 <= $FunctionContextHeight
   ==> (forall _module.Node$T: Ty, 
      $ly: LayerType, 
      $Heap: Heap, 
      q#0: Seq Box, 
      from#0: ref, 
      to#0: ref, 
      S#0: Set Box :: 
    { _module.Node.ListSegment(_module.Node$T, $LS($ly), $Heap, q#0, from#0, to#0, S#0), $IsGoodHeap($Heap) } 
    _module.Node.ListSegment#canCall(_module.Node$T, $Heap, q#0, from#0, to#0, S#0)
         || (1 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(q#0, TSeq(_module.Node$T))
           && $Is(from#0, Tclass._module.Node?(_module.Node$T))
           && $Is(to#0, Tclass._module.Node?(_module.Node$T))
           && $Is(S#0, TSet(Tclass._module.Node(_module.Node$T))))
       ==> (!Seq#Equal(q#0, Seq#Empty(): Seq Box)
           ==> 
          from#0 != null
           ==> 
          S#0[$Box(from#0)]
           ==> 
          read($Heap, from#0, _module.Node.data) == Seq#Index(q#0, LitInt(0))
           ==> _module.Node.ListSegment#canCall(_module.Node$T, 
            $Heap, 
            Seq#Drop(q#0, LitInt(1)), 
            read($Heap, from#0, _module.Node.next), 
            to#0, 
            Set#Difference(S#0, Set#UnionOne(Set#Empty(): Set Box, $Box(from#0)))))
         && _module.Node.ListSegment(_module.Node$T, $LS($ly), $Heap, q#0, from#0, to#0, S#0)
           == (if Seq#Equal(q#0, Seq#Empty(): Seq Box)
             then from#0 == to#0
             else from#0 != null
               && S#0[$Box(from#0)]
               && read($Heap, from#0, _module.Node.data) == Seq#Index(q#0, LitInt(0))
               && _module.Node.ListSegment(_module.Node$T, 
                $ly, 
                $Heap, 
                Seq#Drop(q#0, LitInt(1)), 
                read($Heap, from#0, _module.Node.next), 
                to#0, 
                Set#Difference(S#0, Set#UnionOne(Set#Empty(): Set Box, $Box(from#0))))));

procedure CheckWellformed$$_module.Node.ListSegment(_module.Node$T: Ty, 
    q#0: Seq Box where $Is(q#0, TSeq(_module.Node$T)), 
    from#0: ref where $Is(from#0, Tclass._module.Node?(_module.Node$T)), 
    to#0: ref where $Is(to#0, Tclass._module.Node?(_module.Node$T)), 
    S#0: Set Box where $Is(S#0, TSet(Tclass._module.Node(_module.Node$T))));
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Node.ListSegment(_module.Node$T: Ty, q#0: Seq Box, from#0: ref, to#0: ref, S#0: Set Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##q#0: Seq Box;
  var ##from#0: ref;
  var ##to#0: ref;
  var ##S#0: Set Box;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;
  var b$reqreads#2: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;

    // AddWellformednessCheck for function ListSegment
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(15,19): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> S#0[$Box($o)]);
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> S#0[$Box($o)]);
        if (Seq#Equal(q#0, Seq#Empty(): Seq Box))
        {
            assume _module.Node.ListSegment(_module.Node$T, $LS($LZ), $Heap, q#0, from#0, to#0, S#0)
               == 
              (from#0
               == to#0);
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.Node.ListSegment(_module.Node$T, $LS($LZ), $Heap, q#0, from#0, to#0, S#0), 
              TBool);
        }
        else
        {
            if (from#0 != null)
            {
            }

            if (from#0 != null && S#0[$Box(from#0)])
            {
                assert from#0 != null;
                b$reqreads#0 := $_Frame[from#0, _module.Node.data];
                assert 0 <= LitInt(0) && LitInt(0) < Seq#Length(q#0);
            }

            if (from#0 != null
               && S#0[$Box(from#0)]
               && read($Heap, from#0, _module.Node.data) == Seq#Index(q#0, LitInt(0)))
            {
                assert 0 <= LitInt(1) && LitInt(1) <= Seq#Length(q#0);
                assert from#0 != null;
                b$reqreads#1 := $_Frame[from#0, _module.Node.next];
                ##q#0 := Seq#Drop(q#0, LitInt(1));
                // assume allocatedness for argument to function
                assume $IsAlloc(##q#0, TSeq(_module.Node$T), $Heap);
                ##from#0 := read($Heap, from#0, _module.Node.next);
                // assume allocatedness for argument to function
                assume $IsAlloc(##from#0, Tclass._module.Node?(_module.Node$T), $Heap);
                ##to#0 := to#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##to#0, Tclass._module.Node?(_module.Node$T), $Heap);
                assert $Is(Set#Difference(S#0, Set#UnionOne(Set#Empty(): Set Box, $Box(from#0))), 
                  TSet(Tclass._module.Node(_module.Node$T)));
                ##S#0 := Set#Difference(S#0, Set#UnionOne(Set#Empty(): Set Box, $Box(from#0)));
                // assume allocatedness for argument to function
                assume $IsAlloc(##S#0, TSet(Tclass._module.Node(_module.Node$T)), $Heap);
                b$reqreads#2 := (forall<alpha> $o: ref, $f: Field alpha :: 
                  $o != null && read($Heap, $o, alloc) && ##S#0[$Box($o)] ==> $_Frame[$o, $f]);
                assert (Set#Subset(##S#0, S#0) && !Set#Subset(S#0, ##S#0))
                   || (Set#Equal(##S#0, S#0)
                     && (Seq#Rank(##q#0) < Seq#Rank(q#0)
                       || (Seq#Rank(##q#0) == Seq#Rank(q#0)
                         && ((##from#0 == null && from#0 != null)
                           || ((##from#0 != null <==> from#0 != null)
                             && ((##to#0 == null && to#0 != null)
                               || ((##to#0 != null <==> to#0 != null)
                                 && 
                                Set#Subset(##S#0, S#0)
                                 && !Set#Subset(S#0, ##S#0))))))));
                assume _module.Node.ListSegment#canCall(_module.Node$T, 
                  $Heap, 
                  Seq#Drop(q#0, LitInt(1)), 
                  read($Heap, from#0, _module.Node.next), 
                  to#0, 
                  Set#Difference(S#0, Set#UnionOne(Set#Empty(): Set Box, $Box(from#0))));
            }

            assume _module.Node.ListSegment(_module.Node$T, $LS($LZ), $Heap, q#0, from#0, to#0, S#0)
               == (
                from#0 != null
                 && S#0[$Box(from#0)]
                 && read($Heap, from#0, _module.Node.data) == Seq#Index(q#0, LitInt(0))
                 && _module.Node.ListSegment(_module.Node$T, 
                  $LS($LZ), 
                  $Heap, 
                  Seq#Drop(q#0, LitInt(1)), 
                  read($Heap, from#0, _module.Node.next), 
                  to#0, 
                  Set#Difference(S#0, Set#UnionOne(Set#Empty(): Set Box, $Box(from#0)))));
            assume from#0 != null
               ==> 
              S#0[$Box(from#0)]
               ==> 
              read($Heap, from#0, _module.Node.data) == Seq#Index(q#0, LitInt(0))
               ==> _module.Node.ListSegment#canCall(_module.Node$T, 
                $Heap, 
                Seq#Drop(q#0, LitInt(1)), 
                read($Heap, from#0, _module.Node.next), 
                to#0, 
                Set#Difference(S#0, Set#UnionOne(Set#Empty(): Set Box, $Box(from#0))));
            // CheckWellformedWithResult: any expression
            assume $Is(_module.Node.ListSegment(_module.Node$T, $LS($LZ), $Heap, q#0, from#0, to#0, S#0), 
              TBool);
        }

        assert b$reqreads#0;
        assert b$reqreads#1;
        assert b$reqreads#2;
    }
}



procedure CheckWellformed$$_module.Node.Create(_module.Node$T: Ty, 
    x#0: Box
       where $IsBox(x#0, _module.Node$T) && $IsAllocBox(x#0, _module.Node$T, $Heap))
   returns (l#0: ref
       where $Is(l#0, Tclass._module.Node(_module.Node$T))
         && $IsAlloc(l#0, Tclass._module.Node(_module.Node$T), $Heap), 
    S#0: Set Box
       where $Is(S#0, TSet(Tclass._module.Node(_module.Node$T)))
         && $IsAlloc(S#0, TSet(Tclass._module.Node(_module.Node$T)), $Heap));
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Node.Create(_module.Node$T: Ty, 
    x#0: Box
       where $IsBox(x#0, _module.Node$T) && $IsAllocBox(x#0, _module.Node$T, $Heap))
   returns (l#0: ref
       where $Is(l#0, Tclass._module.Node(_module.Node$T))
         && $IsAlloc(l#0, Tclass._module.Node(_module.Node$T), $Heap), 
    S#0: Set Box
       where $Is(S#0, TSet(Tclass._module.Node(_module.Node$T)))
         && $IsAlloc(S#0, TSet(Tclass._module.Node(_module.Node$T)), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Node.ListSegment#canCall(_module.Node$T, $Heap, Seq#Build(Seq#Empty(): Seq Box, x#0), l#0, null, S#0);
  free ensures _module.Node.ListSegment#canCall(_module.Node$T, $Heap, Seq#Build(Seq#Empty(): Seq Box, x#0), l#0, null, S#0)
     && 
    _module.Node.ListSegment(_module.Node$T, 
      $LS($LZ), 
      $Heap, 
      Seq#Build(Seq#Empty(): Seq Box, x#0), 
      l#0, 
      null, 
      S#0)
     && (if Seq#Equal(Seq#Build(Seq#Empty(): Seq Box, x#0), Seq#Empty(): Seq Box)
       then l#0 == null
       else l#0 != null
         && S#0[$Box(l#0)]
         && read($Heap, l#0, _module.Node.data)
           == Seq#Index(Seq#Build(Seq#Empty(): Seq Box, x#0), LitInt(0))
         && _module.Node.ListSegment(_module.Node$T, 
          $LS($LZ), 
          $Heap, 
          Seq#Drop(Seq#Build(Seq#Empty(): Seq Box, x#0), LitInt(1)), 
          read($Heap, l#0, _module.Node.next), 
          null, 
          Set#Difference(S#0, Set#UnionOne(Set#Empty(): Set Box, $Box(l#0)))));
  ensures (forall $o: ref :: 
    { S#0[$Box($o)] } 
    S#0[$Box($o)] ==> $o != null && !read(old($Heap), $o, alloc));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Node.Create(_module.Node$T: Ty, 
    x#0: Box
       where $IsBox(x#0, _module.Node$T) && $IsAllocBox(x#0, _module.Node$T, $Heap))
   returns (defass#l#0: bool, 
    l#0: ref
       where defass#l#0
         ==> $Is(l#0, Tclass._module.Node(_module.Node$T))
           && $IsAlloc(l#0, Tclass._module.Node(_module.Node$T), $Heap), 
    S#0: Set Box
       where $Is(S#0, TSet(Tclass._module.Node(_module.Node$T)))
         && $IsAlloc(S#0, TSet(Tclass._module.Node(_module.Node$T)), $Heap), 
    $_reverifyPost: bool);
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Node.ListSegment#canCall(_module.Node$T, $Heap, Seq#Build(Seq#Empty(): Seq Box, x#0), l#0, null, S#0);
  ensures _module.Node.ListSegment#canCall(_module.Node$T, $Heap, Seq#Build(Seq#Empty(): Seq Box, x#0), l#0, null, S#0)
     ==> _module.Node.ListSegment(_module.Node$T, 
        $LS($LZ), 
        $Heap, 
        Seq#Build(Seq#Empty(): Seq Box, x#0), 
        l#0, 
        null, 
        S#0)
       || (Seq#Equal(Seq#Build(Seq#Empty(): Seq Box, x#0), Seq#Empty(): Seq Box)
         ==> l#0 == null);
  ensures _module.Node.ListSegment#canCall(_module.Node$T, $Heap, Seq#Build(Seq#Empty(): Seq Box, x#0), l#0, null, S#0)
     ==> _module.Node.ListSegment(_module.Node$T, 
        $LS($LZ), 
        $Heap, 
        Seq#Build(Seq#Empty(): Seq Box, x#0), 
        l#0, 
        null, 
        S#0)
       || (!Seq#Equal(Seq#Build(Seq#Empty(): Seq Box, x#0), Seq#Empty(): Seq Box)
         ==> l#0 != null);
  ensures _module.Node.ListSegment#canCall(_module.Node$T, $Heap, Seq#Build(Seq#Empty(): Seq Box, x#0), l#0, null, S#0)
     ==> _module.Node.ListSegment(_module.Node$T, 
        $LS($LZ), 
        $Heap, 
        Seq#Build(Seq#Empty(): Seq Box, x#0), 
        l#0, 
        null, 
        S#0)
       || (!Seq#Equal(Seq#Build(Seq#Empty(): Seq Box, x#0), Seq#Empty(): Seq Box)
         ==> S#0[$Box(l#0)]);
  ensures _module.Node.ListSegment#canCall(_module.Node$T, $Heap, Seq#Build(Seq#Empty(): Seq Box, x#0), l#0, null, S#0)
     ==> _module.Node.ListSegment(_module.Node$T, 
        $LS($LZ), 
        $Heap, 
        Seq#Build(Seq#Empty(): Seq Box, x#0), 
        l#0, 
        null, 
        S#0)
       || (!Seq#Equal(Seq#Build(Seq#Empty(): Seq Box, x#0), Seq#Empty(): Seq Box)
         ==> read($Heap, l#0, _module.Node.data)
           == Seq#Index(Seq#Build(Seq#Empty(): Seq Box, x#0), LitInt(0)));
  ensures _module.Node.ListSegment#canCall(_module.Node$T, $Heap, Seq#Build(Seq#Empty(): Seq Box, x#0), l#0, null, S#0)
     ==> _module.Node.ListSegment(_module.Node$T, 
        $LS($LZ), 
        $Heap, 
        Seq#Build(Seq#Empty(): Seq Box, x#0), 
        l#0, 
        null, 
        S#0)
       || (!Seq#Equal(Seq#Build(Seq#Empty(): Seq Box, x#0), Seq#Empty(): Seq Box)
         ==> _module.Node.ListSegment(_module.Node$T, 
          $LS($LS($LZ)), 
          $Heap, 
          Seq#Drop(Seq#Build(Seq#Empty(): Seq Box, x#0), LitInt(1)), 
          read($Heap, l#0, _module.Node.next), 
          null, 
          Set#Difference(S#0, Set#UnionOne(Set#Empty(): Set Box, $Box(l#0)))));
  ensures (forall $o: ref :: 
    { S#0[$Box($o)] } 
    S#0[$Box($o)] ==> $o != null && !read(old($Heap), $o, alloc));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Node.Create(_module.Node$T: Ty, x#0: Box)
   returns (defass#l#0: bool, l#0: ref, S#0: Set Box, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $nw: ref;
  var $rhs#0_0: Box where $IsBox($rhs#0_0, _module.Node$T);
  var $rhs#0_1: ref where $Is($rhs#0_1, Tclass._module.Node?(_module.Node$T));
  var $rhs##0: ref
     where $Is($rhs##0, Tclass._module.Node(_module.Node$T))
       && $IsAlloc($rhs##0, Tclass._module.Node(_module.Node$T), $Heap);
  var $rhs##1: Set Box
     where $Is($rhs##1, TSet(Tclass._module.Node(_module.Node$T)))
       && $IsAlloc($rhs##1, TSet(Tclass._module.Node(_module.Node$T)), $Heap);
  var x##0: Box;
  var tail##0: ref;
  var q##0: Seq Box;
  var S##0: Set Box;

    // AddMethodImpl: Create, Impl$$_module.Node.Create
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(25,2): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(28,5)
    if (*)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(29,9)
        assume true;
        havoc $nw;
        assume $nw != null && dtype($nw) == Tclass._module.Node?(_module.Node$T);
        assume !read($Heap, $nw, alloc);
        $Heap := update($Heap, $nw, alloc, true);
        assume $IsGoodHeap($Heap);
        assume $IsHeapAnchor($Heap);
        l#0 := $nw;
        defass#l#0 := true;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(29,22)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(30,14)
        assert defass#l#0;
        assert l#0 != null;
        assume true;
        assert $_Frame[l#0, _module.Node.data];
        assume true;
        $rhs#0_0 := x#0;
        $Heap := update($Heap, l#0, _module.Node.data, $rhs#0_0);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(30,17)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(31,14)
        assert defass#l#0;
        assert l#0 != null;
        assume true;
        assert $_Frame[l#0, _module.Node.next];
        assume true;
        $rhs#0_1 := null;
        $Heap := update($Heap, l#0, _module.Node.next, $rhs#0_1);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(31,20)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(32,9)
        assume true;
        assert defass#l#0;
        assume true;
        S#0 := Set#UnionOne(Set#Empty(): Set Box, $Box(l#0));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(32,14)"} true;
    }
    else
    {
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(34,19)
        assume true;
        assume true;
        // TrCallStmt: Adding lhs with type Node<T>
        // TrCallStmt: Adding lhs with type set<Node<T>>
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        x##0 := x#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        tail##0 := null;
        assume true;
        // ProcessCallStmt: CheckSubrange
        q##0 := Lit(Seq#Empty(): Seq Box);
        assume true;
        // ProcessCallStmt: CheckSubrange
        S##0 := Lit(Set#Empty(): Set Box);
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call $rhs##0, $rhs##1 := Call$$_module.Node.Cons(_module.Node$T, x##0, tail##0, q##0, S##0);
        // TrCallStmt: After ProcessCallStmt
        l#0 := $rhs##0;
        defass#l#0 := true;
        S#0 := $rhs##1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(34,35)"} true;
    }

    assert defass#l#0;
}



procedure CheckWellformed$$_module.Node.Cons(_module.Node$T: Ty, 
    x#0: Box
       where $IsBox(x#0, _module.Node$T) && $IsAllocBox(x#0, _module.Node$T, $Heap), 
    tail#0: ref
       where $Is(tail#0, Tclass._module.Node?(_module.Node$T))
         && $IsAlloc(tail#0, Tclass._module.Node?(_module.Node$T), $Heap), 
    q#0: Seq Box
       where $Is(q#0, TSeq(_module.Node$T)) && $IsAlloc(q#0, TSeq(_module.Node$T), $Heap), 
    S#0: Set Box
       where $Is(S#0, TSet(Tclass._module.Node(_module.Node$T)))
         && $IsAlloc(S#0, TSet(Tclass._module.Node(_module.Node$T)), $Heap))
   returns (l#0: ref
       where $Is(l#0, Tclass._module.Node(_module.Node$T))
         && $IsAlloc(l#0, Tclass._module.Node(_module.Node$T), $Heap), 
    U#0: Set Box
       where $Is(U#0, TSet(Tclass._module.Node(_module.Node$T)))
         && $IsAlloc(U#0, TSet(Tclass._module.Node(_module.Node$T)), $Heap));
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Node.Cons(_module.Node$T: Ty, 
    x#0: Box
       where $IsBox(x#0, _module.Node$T) && $IsAllocBox(x#0, _module.Node$T, $Heap), 
    tail#0: ref
       where $Is(tail#0, Tclass._module.Node?(_module.Node$T))
         && $IsAlloc(tail#0, Tclass._module.Node?(_module.Node$T), $Heap), 
    q#0: Seq Box
       where $Is(q#0, TSeq(_module.Node$T)) && $IsAlloc(q#0, TSeq(_module.Node$T), $Heap), 
    S#0: Set Box
       where $Is(S#0, TSet(Tclass._module.Node(_module.Node$T)))
         && $IsAlloc(S#0, TSet(Tclass._module.Node(_module.Node$T)), $Heap))
   returns (l#0: ref
       where $Is(l#0, Tclass._module.Node(_module.Node$T))
         && $IsAlloc(l#0, Tclass._module.Node(_module.Node$T), $Heap), 
    U#0: Set Box
       where $Is(U#0, TSet(Tclass._module.Node(_module.Node$T)))
         && $IsAlloc(U#0, TSet(Tclass._module.Node(_module.Node$T)), $Heap));
  // user-defined preconditions
  requires _module.Node.ListSegment#canCall(_module.Node$T, $Heap, q#0, tail#0, null, S#0)
     ==> _module.Node.ListSegment(_module.Node$T, $LS($LZ), $Heap, q#0, tail#0, null, S#0)
       || (Seq#Equal(q#0, Seq#Empty(): Seq Box) ==> tail#0 == null);
  requires _module.Node.ListSegment#canCall(_module.Node$T, $Heap, q#0, tail#0, null, S#0)
     ==> _module.Node.ListSegment(_module.Node$T, $LS($LZ), $Heap, q#0, tail#0, null, S#0)
       || (!Seq#Equal(q#0, Seq#Empty(): Seq Box) ==> tail#0 != null);
  requires _module.Node.ListSegment#canCall(_module.Node$T, $Heap, q#0, tail#0, null, S#0)
     ==> _module.Node.ListSegment(_module.Node$T, $LS($LZ), $Heap, q#0, tail#0, null, S#0)
       || (!Seq#Equal(q#0, Seq#Empty(): Seq Box) ==> S#0[$Box(tail#0)]);
  requires _module.Node.ListSegment#canCall(_module.Node$T, $Heap, q#0, tail#0, null, S#0)
     ==> _module.Node.ListSegment(_module.Node$T, $LS($LZ), $Heap, q#0, tail#0, null, S#0)
       || (!Seq#Equal(q#0, Seq#Empty(): Seq Box)
         ==> read($Heap, tail#0, _module.Node.data) == Seq#Index(q#0, LitInt(0)));
  requires _module.Node.ListSegment#canCall(_module.Node$T, $Heap, q#0, tail#0, null, S#0)
     ==> _module.Node.ListSegment(_module.Node$T, $LS($LZ), $Heap, q#0, tail#0, null, S#0)
       || (!Seq#Equal(q#0, Seq#Empty(): Seq Box)
         ==> _module.Node.ListSegment(_module.Node$T, 
          $LS($LS($LZ)), 
          $Heap, 
          Seq#Drop(q#0, LitInt(1)), 
          read($Heap, tail#0, _module.Node.next), 
          null, 
          Set#Difference(S#0, Set#UnionOne(Set#Empty(): Set Box, $Box(tail#0)))));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Node.ListSegment#canCall(_module.Node$T, 
    $Heap, 
    Seq#Append(Seq#Build(Seq#Empty(): Seq Box, x#0), q#0), 
    l#0, 
    null, 
    U#0);
  free ensures _module.Node.ListSegment#canCall(_module.Node$T, 
      $Heap, 
      Seq#Append(Seq#Build(Seq#Empty(): Seq Box, x#0), q#0), 
      l#0, 
      null, 
      U#0)
     && 
    _module.Node.ListSegment(_module.Node$T, 
      $LS($LZ), 
      $Heap, 
      Seq#Append(Seq#Build(Seq#Empty(): Seq Box, x#0), q#0), 
      l#0, 
      null, 
      U#0)
     && (if Seq#Equal(Seq#Append(Seq#Build(Seq#Empty(): Seq Box, x#0), q#0), Seq#Empty(): Seq Box)
       then l#0 == null
       else l#0 != null
         && U#0[$Box(l#0)]
         && read($Heap, l#0, _module.Node.data)
           == Seq#Index(Seq#Append(Seq#Build(Seq#Empty(): Seq Box, x#0), q#0), LitInt(0))
         && _module.Node.ListSegment(_module.Node$T, 
          $LS($LZ), 
          $Heap, 
          Seq#Drop(Seq#Append(Seq#Build(Seq#Empty(): Seq Box, x#0), q#0), LitInt(1)), 
          read($Heap, l#0, _module.Node.next), 
          null, 
          Set#Difference(U#0, Set#UnionOne(Set#Empty(): Set Box, $Box(l#0)))));
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    U#0[$Box($o)] && !S#0[$Box($o)] ==> $o != null && !read(old($Heap), $o, alloc));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Node.Cons(_module.Node$T: Ty, 
    x#0: Box
       where $IsBox(x#0, _module.Node$T) && $IsAllocBox(x#0, _module.Node$T, $Heap), 
    tail#0: ref
       where $Is(tail#0, Tclass._module.Node?(_module.Node$T))
         && $IsAlloc(tail#0, Tclass._module.Node?(_module.Node$T), $Heap), 
    q#0: Seq Box
       where $Is(q#0, TSeq(_module.Node$T)) && $IsAlloc(q#0, TSeq(_module.Node$T), $Heap), 
    S#0: Set Box
       where $Is(S#0, TSet(Tclass._module.Node(_module.Node$T)))
         && $IsAlloc(S#0, TSet(Tclass._module.Node(_module.Node$T)), $Heap))
   returns (defass#l#0: bool, 
    l#0: ref
       where defass#l#0
         ==> $Is(l#0, Tclass._module.Node(_module.Node$T))
           && $IsAlloc(l#0, Tclass._module.Node(_module.Node$T), $Heap), 
    U#0: Set Box
       where $Is(U#0, TSet(Tclass._module.Node(_module.Node$T)))
         && $IsAlloc(U#0, TSet(Tclass._module.Node(_module.Node$T)), $Heap), 
    $_reverifyPost: bool);
  free requires 2 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.Node.ListSegment#canCall(_module.Node$T, $Heap, q#0, tail#0, null, S#0)
     && 
    _module.Node.ListSegment(_module.Node$T, $LS($LZ), $Heap, q#0, tail#0, null, S#0)
     && (if Seq#Equal(q#0, Seq#Empty(): Seq Box)
       then tail#0 == null
       else tail#0 != null
         && S#0[$Box(tail#0)]
         && read($Heap, tail#0, _module.Node.data) == Seq#Index(q#0, LitInt(0))
         && _module.Node.ListSegment(_module.Node$T, 
          $LS($LZ), 
          $Heap, 
          Seq#Drop(q#0, LitInt(1)), 
          read($Heap, tail#0, _module.Node.next), 
          null, 
          Set#Difference(S#0, Set#UnionOne(Set#Empty(): Set Box, $Box(tail#0)))));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Node.ListSegment#canCall(_module.Node$T, 
    $Heap, 
    Seq#Append(Seq#Build(Seq#Empty(): Seq Box, x#0), q#0), 
    l#0, 
    null, 
    U#0);
  ensures _module.Node.ListSegment#canCall(_module.Node$T, 
      $Heap, 
      Seq#Append(Seq#Build(Seq#Empty(): Seq Box, x#0), q#0), 
      l#0, 
      null, 
      U#0)
     ==> _module.Node.ListSegment(_module.Node$T, 
        $LS($LZ), 
        $Heap, 
        Seq#Append(Seq#Build(Seq#Empty(): Seq Box, x#0), q#0), 
        l#0, 
        null, 
        U#0)
       || (Seq#Equal(Seq#Append(Seq#Build(Seq#Empty(): Seq Box, x#0), q#0), Seq#Empty(): Seq Box)
         ==> l#0 == null);
  ensures _module.Node.ListSegment#canCall(_module.Node$T, 
      $Heap, 
      Seq#Append(Seq#Build(Seq#Empty(): Seq Box, x#0), q#0), 
      l#0, 
      null, 
      U#0)
     ==> _module.Node.ListSegment(_module.Node$T, 
        $LS($LZ), 
        $Heap, 
        Seq#Append(Seq#Build(Seq#Empty(): Seq Box, x#0), q#0), 
        l#0, 
        null, 
        U#0)
       || (!Seq#Equal(Seq#Append(Seq#Build(Seq#Empty(): Seq Box, x#0), q#0), Seq#Empty(): Seq Box)
         ==> l#0 != null);
  ensures _module.Node.ListSegment#canCall(_module.Node$T, 
      $Heap, 
      Seq#Append(Seq#Build(Seq#Empty(): Seq Box, x#0), q#0), 
      l#0, 
      null, 
      U#0)
     ==> _module.Node.ListSegment(_module.Node$T, 
        $LS($LZ), 
        $Heap, 
        Seq#Append(Seq#Build(Seq#Empty(): Seq Box, x#0), q#0), 
        l#0, 
        null, 
        U#0)
       || (!Seq#Equal(Seq#Append(Seq#Build(Seq#Empty(): Seq Box, x#0), q#0), Seq#Empty(): Seq Box)
         ==> U#0[$Box(l#0)]);
  ensures _module.Node.ListSegment#canCall(_module.Node$T, 
      $Heap, 
      Seq#Append(Seq#Build(Seq#Empty(): Seq Box, x#0), q#0), 
      l#0, 
      null, 
      U#0)
     ==> _module.Node.ListSegment(_module.Node$T, 
        $LS($LZ), 
        $Heap, 
        Seq#Append(Seq#Build(Seq#Empty(): Seq Box, x#0), q#0), 
        l#0, 
        null, 
        U#0)
       || (!Seq#Equal(Seq#Append(Seq#Build(Seq#Empty(): Seq Box, x#0), q#0), Seq#Empty(): Seq Box)
         ==> read($Heap, l#0, _module.Node.data)
           == Seq#Index(Seq#Append(Seq#Build(Seq#Empty(): Seq Box, x#0), q#0), LitInt(0)));
  ensures _module.Node.ListSegment#canCall(_module.Node$T, 
      $Heap, 
      Seq#Append(Seq#Build(Seq#Empty(): Seq Box, x#0), q#0), 
      l#0, 
      null, 
      U#0)
     ==> _module.Node.ListSegment(_module.Node$T, 
        $LS($LZ), 
        $Heap, 
        Seq#Append(Seq#Build(Seq#Empty(): Seq Box, x#0), q#0), 
        l#0, 
        null, 
        U#0)
       || (!Seq#Equal(Seq#Append(Seq#Build(Seq#Empty(): Seq Box, x#0), q#0), Seq#Empty(): Seq Box)
         ==> _module.Node.ListSegment(_module.Node$T, 
          $LS($LS($LZ)), 
          $Heap, 
          Seq#Drop(Seq#Append(Seq#Build(Seq#Empty(): Seq Box, x#0), q#0), LitInt(1)), 
          read($Heap, l#0, _module.Node.next), 
          null, 
          Set#Difference(U#0, Set#UnionOne(Set#Empty(): Set Box, $Box(l#0)))));
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    U#0[$Box($o)] && !S#0[$Box($o)] ==> $o != null && !read(old($Heap), $o, alloc));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Node.Cons(_module.Node$T: Ty, x#0: Box, tail#0: ref, q#0: Seq Box, S#0: Set Box)
   returns (defass#l#0: bool, l#0: ref, U#0: Set Box, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $nw: ref;
  var $rhs#0: Box where $IsBox($rhs#0, _module.Node$T);
  var $rhs#1: ref where $Is($rhs#1, Tclass._module.Node?(_module.Node$T));

    // AddMethodImpl: Cons, Impl$$_module.Node.Cons
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(41,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(42,7)
    assume true;
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._module.Node?(_module.Node$T);
    assume !read($Heap, $nw, alloc);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    l#0 := $nw;
    defass#l#0 := true;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(42,20)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(43,12)
    assert defass#l#0;
    assert l#0 != null;
    assume true;
    assert $_Frame[l#0, _module.Node.data];
    assume true;
    $rhs#0 := x#0;
    $Heap := update($Heap, l#0, _module.Node.data, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(43,15)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(44,12)
    assert defass#l#0;
    assert l#0 != null;
    assume true;
    assert $_Frame[l#0, _module.Node.next];
    assume true;
    $rhs#1 := tail#0;
    $Heap := update($Heap, l#0, _module.Node.next, $rhs#1);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(44,18)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(45,7)
    assume true;
    assert defass#l#0;
    assume true;
    U#0 := Set#Union(S#0, Set#UnionOne(Set#Empty(): Set Box, $Box(l#0)));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(45,16)"} true;
    assert defass#l#0;
}



// _module.Node: subset type $Is
axiom (forall _module.Node$T: Ty, c#0: ref :: 
  { $Is(c#0, Tclass._module.Node(_module.Node$T)) } 
  $Is(c#0, Tclass._module.Node(_module.Node$T))
     <==> $Is(c#0, Tclass._module.Node?(_module.Node$T)) && c#0 != null);

// _module.Node: subset type $IsAlloc
axiom (forall _module.Node$T: Ty, c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.Node(_module.Node$T), $h) } 
  $IsAlloc(c#0, Tclass._module.Node(_module.Node$T), $h)
     <==> $IsAlloc(c#0, Tclass._module.Node?(_module.Node$T), $h));

const unique class._module.ListNode?: ClassName;

function Tclass._module.ListNode?(Ty) : Ty;

const unique Tagclass._module.ListNode?: TyTag;

// Tclass._module.ListNode? Tag
axiom (forall _module.ListNode$T: Ty :: 
  { Tclass._module.ListNode?(_module.ListNode$T) } 
  Tag(Tclass._module.ListNode?(_module.ListNode$T)) == Tagclass._module.ListNode?
     && TagFamily(Tclass._module.ListNode?(_module.ListNode$T)) == tytagFamily$ListNode);

// Tclass._module.ListNode? injectivity 0
axiom (forall _module.ListNode$T: Ty :: 
  { Tclass._module.ListNode?(_module.ListNode$T) } 
  Tclass._module.ListNode?_0(Tclass._module.ListNode?(_module.ListNode$T))
     == _module.ListNode$T);

function Tclass._module.ListNode?_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.ListNode?
axiom (forall _module.ListNode$T: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.ListNode?(_module.ListNode$T)) } 
  $IsBox(bx, Tclass._module.ListNode?(_module.ListNode$T))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.ListNode?(_module.ListNode$T)));

// ListNode: Class $Is
axiom (forall _module.ListNode$T: Ty, $o: ref :: 
  { $Is($o, Tclass._module.ListNode?(_module.ListNode$T)) } 
  $Is($o, Tclass._module.ListNode?(_module.ListNode$T))
     <==> $o == null || dtype($o) == Tclass._module.ListNode?(_module.ListNode$T));

// ListNode: Class $IsAlloc
axiom (forall _module.ListNode$T: Ty, $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.ListNode?(_module.ListNode$T), $h) } 
  $IsAlloc($o, Tclass._module.ListNode?(_module.ListNode$T), $h)
     <==> $o == null || read($h, $o, alloc));

axiom FDim(_module.ListNode.Contents) == 0
   && FieldOfDecl(class._module.ListNode?, field$Contents)
     == _module.ListNode.Contents
   && $IsGhostField(_module.ListNode.Contents);

const _module.ListNode.Contents: Field (Seq Box);

// ListNode.Contents: Type axiom
axiom (forall _module.ListNode$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.ListNode.Contents), Tclass._module.ListNode?(_module.ListNode$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.ListNode?(_module.ListNode$T)
     ==> $Is(read($h, $o, _module.ListNode.Contents), TSeq(_module.ListNode$T)));

// ListNode.Contents: Allocation axiom
axiom (forall _module.ListNode$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.ListNode.Contents), Tclass._module.ListNode?(_module.ListNode$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.ListNode?(_module.ListNode$T)
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.ListNode.Contents), TSeq(_module.ListNode$T), $h));

axiom FDim(_module.ListNode.Repr) == 0
   && FieldOfDecl(class._module.ListNode?, field$Repr) == _module.ListNode.Repr
   && $IsGhostField(_module.ListNode.Repr);

const _module.ListNode.Repr: Field (Set Box);

function Tclass._module.ListNode(Ty) : Ty;

const unique Tagclass._module.ListNode: TyTag;

// Tclass._module.ListNode Tag
axiom (forall _module.ListNode$T: Ty :: 
  { Tclass._module.ListNode(_module.ListNode$T) } 
  Tag(Tclass._module.ListNode(_module.ListNode$T)) == Tagclass._module.ListNode
     && TagFamily(Tclass._module.ListNode(_module.ListNode$T)) == tytagFamily$ListNode);

// Tclass._module.ListNode injectivity 0
axiom (forall _module.ListNode$T: Ty :: 
  { Tclass._module.ListNode(_module.ListNode$T) } 
  Tclass._module.ListNode_0(Tclass._module.ListNode(_module.ListNode$T))
     == _module.ListNode$T);

function Tclass._module.ListNode_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.ListNode
axiom (forall _module.ListNode$T: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.ListNode(_module.ListNode$T)) } 
  $IsBox(bx, Tclass._module.ListNode(_module.ListNode$T))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.ListNode(_module.ListNode$T)));

// ListNode.Repr: Type axiom
axiom (forall _module.ListNode$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.ListNode.Repr), Tclass._module.ListNode?(_module.ListNode$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.ListNode?(_module.ListNode$T)
     ==> $Is(read($h, $o, _module.ListNode.Repr), 
      TSet(Tclass._module.ListNode(_module.ListNode$T))));

// ListNode.Repr: Allocation axiom
axiom (forall _module.ListNode$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.ListNode.Repr), Tclass._module.ListNode?(_module.ListNode$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.ListNode?(_module.ListNode$T)
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.ListNode.Repr), 
      TSet(Tclass._module.ListNode(_module.ListNode$T)), 
      $h));

axiom FDim(_module.ListNode.data) == 0
   && FieldOfDecl(class._module.ListNode?, field$data) == _module.ListNode.data
   && !$IsGhostField(_module.ListNode.data);

const _module.ListNode.data: Field Box;

// ListNode.data: Type axiom
axiom (forall _module.ListNode$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.ListNode.data), Tclass._module.ListNode?(_module.ListNode$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.ListNode?(_module.ListNode$T)
     ==> $IsBox(read($h, $o, _module.ListNode.data), _module.ListNode$T));

// ListNode.data: Allocation axiom
axiom (forall _module.ListNode$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.ListNode.data), Tclass._module.ListNode?(_module.ListNode$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.ListNode?(_module.ListNode$T)
       && read($h, $o, alloc)
     ==> $IsAllocBox(read($h, $o, _module.ListNode.data), _module.ListNode$T, $h));

axiom FDim(_module.ListNode.next) == 0
   && FieldOfDecl(class._module.ListNode?, field$next) == _module.ListNode.next
   && !$IsGhostField(_module.ListNode.next);

const _module.ListNode.next: Field ref;

// ListNode.next: Type axiom
axiom (forall _module.ListNode$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.ListNode.next), Tclass._module.ListNode?(_module.ListNode$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.ListNode?(_module.ListNode$T)
     ==> $Is(read($h, $o, _module.ListNode.next), 
      Tclass._module.ListNode?(_module.ListNode$T)));

// ListNode.next: Allocation axiom
axiom (forall _module.ListNode$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.ListNode.next), Tclass._module.ListNode?(_module.ListNode$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.ListNode?(_module.ListNode$T)
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.ListNode.next), 
      Tclass._module.ListNode?(_module.ListNode$T), 
      $h));

// function declaration for _module.ListNode.IsList
function _module.ListNode.IsList(_module.ListNode$T: Ty, $ly: LayerType, $heap: Heap, l#0: ref) : bool;

function _module.ListNode.IsList#canCall(_module.ListNode$T: Ty, $heap: Heap, l#0: ref) : bool;

// layer synonym axiom
axiom (forall _module.ListNode$T: Ty, $ly: LayerType, $Heap: Heap, l#0: ref :: 
  { _module.ListNode.IsList(_module.ListNode$T, $LS($ly), $Heap, l#0) } 
  _module.ListNode.IsList(_module.ListNode$T, $LS($ly), $Heap, l#0)
     == _module.ListNode.IsList(_module.ListNode$T, $ly, $Heap, l#0));

// fuel synonym axiom
axiom (forall _module.ListNode$T: Ty, $ly: LayerType, $Heap: Heap, l#0: ref :: 
  { _module.ListNode.IsList(_module.ListNode$T, AsFuelBottom($ly), $Heap, l#0) } 
  _module.ListNode.IsList(_module.ListNode$T, $ly, $Heap, l#0)
     == _module.ListNode.IsList(_module.ListNode$T, $LZ, $Heap, l#0));

// frame axiom for _module.ListNode.IsList
axiom (forall _module.ListNode$T: Ty, $ly: LayerType, $h0: Heap, $h1: Heap, l#0: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.ListNode.IsList(_module.ListNode$T, $ly, $h1, l#0) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && (_module.ListNode.IsList#canCall(_module.ListNode$T, $h0, l#0)
         || $Is(l#0, Tclass._module.ListNode?(_module.ListNode$T)))
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && ($o == l#0
             || (if l#0 != null
               then read($h0, l#0, _module.ListNode.Repr)
               else Set#Empty(): Set Box)[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.ListNode.IsList(_module.ListNode$T, $ly, $h0, l#0)
       == _module.ListNode.IsList(_module.ListNode$T, $ly, $h1, l#0));

// consequence axiom for _module.ListNode.IsList
axiom 5 <= $FunctionContextHeight
   ==> (forall _module.ListNode$T: Ty, $ly: LayerType, $Heap: Heap, l#0: ref :: 
    { _module.ListNode.IsList(_module.ListNode$T, $ly, $Heap, l#0) } 
    _module.ListNode.IsList#canCall(_module.ListNode$T, $Heap, l#0)
         || (5 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(l#0, Tclass._module.ListNode?(_module.ListNode$T)))
       ==> true);

function _module.ListNode.IsList#requires(Ty, LayerType, Heap, ref) : bool;

// #requires axiom for _module.ListNode.IsList
axiom (forall _module.ListNode$T: Ty, $ly: LayerType, $Heap: Heap, l#0: ref :: 
  { _module.ListNode.IsList#requires(_module.ListNode$T, $ly, $Heap, l#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap) && $Is(l#0, Tclass._module.ListNode?(_module.ListNode$T))
     ==> _module.ListNode.IsList#requires(_module.ListNode$T, $ly, $Heap, l#0) == true);

// definition axiom for _module.ListNode.IsList (revealed)
axiom 5 <= $FunctionContextHeight
   ==> (forall _module.ListNode$T: Ty, $ly: LayerType, $Heap: Heap, l#0: ref :: 
    { _module.ListNode.IsList(_module.ListNode$T, $LS($ly), $Heap, l#0), $IsGoodHeap($Heap) } 
    _module.ListNode.IsList#canCall(_module.ListNode$T, $Heap, l#0)
         || (5 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(l#0, Tclass._module.ListNode?(_module.ListNode$T)))
       ==> (l#0 != null
           ==> 
          read($Heap, l#0, _module.ListNode.next) != null
           ==> 
          Set#Subset(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(l#0)), 
              $Box(read($Heap, l#0, _module.ListNode.next))), 
            read($Heap, l#0, _module.ListNode.Repr))
           ==> 
          Seq#Equal(read($Heap, l#0, _module.ListNode.Contents), 
            Seq#Append(Seq#Build(Seq#Empty(): Seq Box, read($Heap, l#0, _module.ListNode.data)), 
              read($Heap, read($Heap, l#0, _module.ListNode.next), _module.ListNode.Contents)))
           ==> 
          Set#Subset(read($Heap, read($Heap, l#0, _module.ListNode.next), _module.ListNode.Repr), 
            Set#Difference(read($Heap, l#0, _module.ListNode.Repr), 
              Set#UnionOne(Set#Empty(): Set Box, $Box(l#0))))
           ==> _module.ListNode.IsList#canCall(_module.ListNode$T, $Heap, read($Heap, l#0, _module.ListNode.next)))
         && _module.ListNode.IsList(_module.ListNode$T, $LS($ly), $Heap, l#0)
           == (if l#0 == null
             then true
             else (if read($Heap, l#0, _module.ListNode.next) == null
               then read($Heap, l#0, _module.ListNode.Repr)[$Box(l#0)]
                 && Seq#Equal(read($Heap, l#0, _module.ListNode.Contents), 
                  Seq#Build(Seq#Empty(): Seq Box, read($Heap, l#0, _module.ListNode.data)))
               else Set#Subset(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(l#0)), 
                    $Box(read($Heap, l#0, _module.ListNode.next))), 
                  read($Heap, l#0, _module.ListNode.Repr))
                 && Seq#Equal(read($Heap, l#0, _module.ListNode.Contents), 
                  Seq#Append(Seq#Build(Seq#Empty(): Seq Box, read($Heap, l#0, _module.ListNode.data)), 
                    read($Heap, read($Heap, l#0, _module.ListNode.next), _module.ListNode.Contents)))
                 && Set#Subset(read($Heap, read($Heap, l#0, _module.ListNode.next), _module.ListNode.Repr), 
                  Set#Difference(read($Heap, l#0, _module.ListNode.Repr), 
                    Set#UnionOne(Set#Empty(): Set Box, $Box(l#0))))
                 && _module.ListNode.IsList(_module.ListNode$T, $ly, $Heap, read($Heap, l#0, _module.ListNode.next)))));

procedure CheckWellformed$$_module.ListNode.IsList(_module.ListNode$T: Ty, 
    l#0: ref where $Is(l#0, Tclass._module.ListNode?(_module.ListNode$T)));
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.ListNode.IsList(_module.ListNode$T: Ty, l#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;
  var ##l#0: ref;
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
  var b$reqreads#12: bool;
  var b$reqreads#13: bool;
  var b$reqreads#14: bool;
  var b$reqreads#15: bool;

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
    b$reqreads#12 := true;
    b$reqreads#13 := true;
    b$reqreads#14 := true;
    b$reqreads#15 := true;

    // AddWellformednessCheck for function IsList
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(58,19): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> $o == l#0
           || (if l#0 != null
             then read($Heap, l#0, _module.ListNode.Repr)
             else Set#Empty(): Set Box)[$Box($o)]);
    if (l#0 != null)
    {
        assert l#0 != null;
        b$reqreads#0 := $_Frame[l#0, _module.ListNode.Repr];
    }
    else
    {
    }

    assert b$reqreads#0;
    if (l#0 != null)
    {
        assert l#0 != null;
    }
    else
    {
    }

    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc)
             ==> $o == l#0
               || (if l#0 != null
                 then read($Heap, l#0, _module.ListNode.Repr)
                 else Set#Empty(): Set Box)[$Box($o)]);
        if (l#0 == null)
        {
            assume _module.ListNode.IsList(_module.ListNode$T, $LS($LZ), $Heap, l#0) == Lit(true);
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.ListNode.IsList(_module.ListNode$T, $LS($LZ), $Heap, l#0), TBool);
        }
        else
        {
            assert l#0 != null;
            b$reqreads#1 := $_Frame[l#0, _module.ListNode.next];
            if (read($Heap, l#0, _module.ListNode.next) == null)
            {
                assert l#0 != null;
                b$reqreads#2 := $_Frame[l#0, _module.ListNode.Repr];
                if (read($Heap, l#0, _module.ListNode.Repr)[$Box(l#0)])
                {
                    assert l#0 != null;
                    b$reqreads#3 := $_Frame[l#0, _module.ListNode.Contents];
                    assert l#0 != null;
                    b$reqreads#4 := $_Frame[l#0, _module.ListNode.data];
                }

                assume _module.ListNode.IsList(_module.ListNode$T, $LS($LZ), $Heap, l#0)
                   == (read($Heap, l#0, _module.ListNode.Repr)[$Box(l#0)]
                     && Seq#Equal(read($Heap, l#0, _module.ListNode.Contents), 
                      Seq#Build(Seq#Empty(): Seq Box, read($Heap, l#0, _module.ListNode.data))));
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(_module.ListNode.IsList(_module.ListNode$T, $LS($LZ), $Heap, l#0), TBool);
            }
            else
            {
                assert l#0 != null;
                b$reqreads#5 := $_Frame[l#0, _module.ListNode.next];
                assert l#0 != null;
                b$reqreads#6 := $_Frame[l#0, _module.ListNode.Repr];
                if (Set#Subset(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(l#0)), 
                    $Box(read($Heap, l#0, _module.ListNode.next))), 
                  read($Heap, l#0, _module.ListNode.Repr)))
                {
                    assert l#0 != null;
                    b$reqreads#7 := $_Frame[l#0, _module.ListNode.Contents];
                    assert l#0 != null;
                    b$reqreads#8 := $_Frame[l#0, _module.ListNode.data];
                    assert l#0 != null;
                    b$reqreads#9 := $_Frame[l#0, _module.ListNode.next];
                    assert read($Heap, l#0, _module.ListNode.next) != null;
                    b$reqreads#10 := $_Frame[read($Heap, l#0, _module.ListNode.next), _module.ListNode.Contents];
                }

                if (Set#Subset(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(l#0)), 
                      $Box(read($Heap, l#0, _module.ListNode.next))), 
                    read($Heap, l#0, _module.ListNode.Repr))
                   && Seq#Equal(read($Heap, l#0, _module.ListNode.Contents), 
                    Seq#Append(Seq#Build(Seq#Empty(): Seq Box, read($Heap, l#0, _module.ListNode.data)), 
                      read($Heap, read($Heap, l#0, _module.ListNode.next), _module.ListNode.Contents))))
                {
                    assert l#0 != null;
                    b$reqreads#11 := $_Frame[l#0, _module.ListNode.next];
                    assert read($Heap, l#0, _module.ListNode.next) != null;
                    b$reqreads#12 := $_Frame[read($Heap, l#0, _module.ListNode.next), _module.ListNode.Repr];
                    assert l#0 != null;
                    b$reqreads#13 := $_Frame[l#0, _module.ListNode.Repr];
                }

                if (Set#Subset(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(l#0)), 
                      $Box(read($Heap, l#0, _module.ListNode.next))), 
                    read($Heap, l#0, _module.ListNode.Repr))
                   && Seq#Equal(read($Heap, l#0, _module.ListNode.Contents), 
                    Seq#Append(Seq#Build(Seq#Empty(): Seq Box, read($Heap, l#0, _module.ListNode.data)), 
                      read($Heap, read($Heap, l#0, _module.ListNode.next), _module.ListNode.Contents)))
                   && Set#Subset(read($Heap, read($Heap, l#0, _module.ListNode.next), _module.ListNode.Repr), 
                    Set#Difference(read($Heap, l#0, _module.ListNode.Repr), 
                      Set#UnionOne(Set#Empty(): Set Box, $Box(l#0)))))
                {
                    assert l#0 != null;
                    b$reqreads#14 := $_Frame[l#0, _module.ListNode.next];
                    ##l#0 := read($Heap, l#0, _module.ListNode.next);
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##l#0, Tclass._module.ListNode?(_module.ListNode$T), $Heap);
                    b$reqreads#15 := (forall<alpha> $o: ref, $f: Field alpha :: 
                      $o != null
                           && read($Heap, $o, alloc)
                           && ($o == ##l#0
                             || (if ##l#0 != null
                               then read($Heap, ##l#0, _module.ListNode.Repr)
                               else Set#Empty(): Set Box)[$Box($o)])
                         ==> $_Frame[$o, $f]);
                    assert (Set#Subset(Set#Union((if ##l#0 != null
                               then read($Heap, ##l#0, _module.ListNode.Repr)
                               else Set#Empty(): Set Box), 
                            Set#UnionOne(Set#Empty(): Set Box, $Box(##l#0))), 
                          Set#Union((if l#0 != null
                               then read($Heap, l#0, _module.ListNode.Repr)
                               else Set#Empty(): Set Box), 
                            Set#UnionOne(Set#Empty(): Set Box, $Box(l#0))))
                         && !Set#Subset(Set#Union((if l#0 != null
                               then read($Heap, l#0, _module.ListNode.Repr)
                               else Set#Empty(): Set Box), 
                            Set#UnionOne(Set#Empty(): Set Box, $Box(l#0))), 
                          Set#Union((if ##l#0 != null
                               then read($Heap, ##l#0, _module.ListNode.Repr)
                               else Set#Empty(): Set Box), 
                            Set#UnionOne(Set#Empty(): Set Box, $Box(##l#0)))))
                       || (Set#Equal(Set#Union((if ##l#0 != null
                               then read($Heap, ##l#0, _module.ListNode.Repr)
                               else Set#Empty(): Set Box), 
                            Set#UnionOne(Set#Empty(): Set Box, $Box(##l#0))), 
                          Set#Union((if l#0 != null
                               then read($Heap, l#0, _module.ListNode.Repr)
                               else Set#Empty(): Set Box), 
                            Set#UnionOne(Set#Empty(): Set Box, $Box(l#0))))
                         && 
                        ##l#0 == null
                         && l#0 != null);
                    assume _module.ListNode.IsList#canCall(_module.ListNode$T, $Heap, read($Heap, l#0, _module.ListNode.next));
                }

                assume _module.ListNode.IsList(_module.ListNode$T, $LS($LZ), $Heap, l#0)
                   == (
                    Set#Subset(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(l#0)), 
                        $Box(read($Heap, l#0, _module.ListNode.next))), 
                      read($Heap, l#0, _module.ListNode.Repr))
                     && Seq#Equal(read($Heap, l#0, _module.ListNode.Contents), 
                      Seq#Append(Seq#Build(Seq#Empty(): Seq Box, read($Heap, l#0, _module.ListNode.data)), 
                        read($Heap, read($Heap, l#0, _module.ListNode.next), _module.ListNode.Contents)))
                     && Set#Subset(read($Heap, read($Heap, l#0, _module.ListNode.next), _module.ListNode.Repr), 
                      Set#Difference(read($Heap, l#0, _module.ListNode.Repr), 
                        Set#UnionOne(Set#Empty(): Set Box, $Box(l#0))))
                     && _module.ListNode.IsList(_module.ListNode$T, $LS($LZ), $Heap, read($Heap, l#0, _module.ListNode.next)));
                assume Set#Subset(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(l#0)), 
                      $Box(read($Heap, l#0, _module.ListNode.next))), 
                    read($Heap, l#0, _module.ListNode.Repr))
                   ==> 
                  Seq#Equal(read($Heap, l#0, _module.ListNode.Contents), 
                    Seq#Append(Seq#Build(Seq#Empty(): Seq Box, read($Heap, l#0, _module.ListNode.data)), 
                      read($Heap, read($Heap, l#0, _module.ListNode.next), _module.ListNode.Contents)))
                   ==> 
                  Set#Subset(read($Heap, read($Heap, l#0, _module.ListNode.next), _module.ListNode.Repr), 
                    Set#Difference(read($Heap, l#0, _module.ListNode.Repr), 
                      Set#UnionOne(Set#Empty(): Set Box, $Box(l#0))))
                   ==> _module.ListNode.IsList#canCall(_module.ListNode$T, $Heap, read($Heap, l#0, _module.ListNode.next));
                // CheckWellformedWithResult: any expression
                assume $Is(_module.ListNode.IsList(_module.ListNode$T, $LS($LZ), $Heap, l#0), TBool);
            }
        }

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
        assert b$reqreads#12;
        assert b$reqreads#13;
        assert b$reqreads#14;
        assert b$reqreads#15;
    }
}



procedure CheckWellformed$$_module.ListNode.Create(_module.ListNode$T: Ty, 
    x#0: Box
       where $IsBox(x#0, _module.ListNode$T) && $IsAllocBox(x#0, _module.ListNode$T, $Heap))
   returns (l#0: ref
       where $Is(l#0, Tclass._module.ListNode(_module.ListNode$T))
         && $IsAlloc(l#0, Tclass._module.ListNode(_module.ListNode$T), $Heap));
  free requires 7 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.ListNode.Create(_module.ListNode$T: Ty, x#0: Box) returns (l#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##l#0: ref;

    // AddMethodImpl: Create, CheckWellformed$$_module.ListNode.Create
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(69,16): initial state"} true;
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
    assume $HeapSucc(old($Heap), $Heap);
    havoc l#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(70,43): post-state"} true;
    ##l#0 := l#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##l#0, Tclass._module.ListNode?(_module.ListNode$T), $Heap);
    assume _module.ListNode.IsList#canCall(_module.ListNode$T, $Heap, l#0);
    assume _module.ListNode.IsList(_module.ListNode$T, $LS($LZ), $Heap, l#0);
    assert l#0 != null;
    assume Seq#Equal(read($Heap, l#0, _module.ListNode.Contents), 
      Seq#Build(Seq#Empty(): Seq Box, x#0));
    assert l#0 != null;
    assume (forall $o: ref :: 
      { read(old($Heap), $o, alloc) } 
      $o == l#0 || read($Heap, l#0, _module.ListNode.Repr)[$Box($o)]
         ==> $o != null && !read(old($Heap), $o, alloc));
}



procedure Call$$_module.ListNode.Create(_module.ListNode$T: Ty, 
    x#0: Box
       where $IsBox(x#0, _module.ListNode$T) && $IsAllocBox(x#0, _module.ListNode$T, $Heap))
   returns (l#0: ref
       where $Is(l#0, Tclass._module.ListNode(_module.ListNode$T))
         && $IsAlloc(l#0, Tclass._module.ListNode(_module.ListNode$T), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.ListNode.IsList#canCall(_module.ListNode$T, $Heap, l#0);
  free ensures _module.ListNode.IsList#canCall(_module.ListNode$T, $Heap, l#0)
     && 
    _module.ListNode.IsList(_module.ListNode$T, $LS($LZ), $Heap, l#0)
     && (if l#0 == null
       then true
       else (if read($Heap, l#0, _module.ListNode.next) == null
         then read($Heap, l#0, _module.ListNode.Repr)[$Box(l#0)]
           && Seq#Equal(read($Heap, l#0, _module.ListNode.Contents), 
            Seq#Build(Seq#Empty(): Seq Box, read($Heap, l#0, _module.ListNode.data)))
         else Set#Subset(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(l#0)), 
              $Box(read($Heap, l#0, _module.ListNode.next))), 
            read($Heap, l#0, _module.ListNode.Repr))
           && Seq#Equal(read($Heap, l#0, _module.ListNode.Contents), 
            Seq#Append(Seq#Build(Seq#Empty(): Seq Box, read($Heap, l#0, _module.ListNode.data)), 
              read($Heap, read($Heap, l#0, _module.ListNode.next), _module.ListNode.Contents)))
           && Set#Subset(read($Heap, read($Heap, l#0, _module.ListNode.next), _module.ListNode.Repr), 
            Set#Difference(read($Heap, l#0, _module.ListNode.Repr), 
              Set#UnionOne(Set#Empty(): Set Box, $Box(l#0))))
           && _module.ListNode.IsList(_module.ListNode$T, $LS($LZ), $Heap, read($Heap, l#0, _module.ListNode.next))));
  ensures Seq#Equal(read($Heap, l#0, _module.ListNode.Contents), 
    Seq#Build(Seq#Empty(): Seq Box, x#0));
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    $o == l#0 || read($Heap, l#0, _module.ListNode.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.ListNode.Create(_module.ListNode$T: Ty, 
    x#0: Box
       where $IsBox(x#0, _module.ListNode$T) && $IsAllocBox(x#0, _module.ListNode$T, $Heap))
   returns (defass#l#0: bool, 
    l#0: ref
       where defass#l#0
         ==> $Is(l#0, Tclass._module.ListNode(_module.ListNode$T))
           && $IsAlloc(l#0, Tclass._module.ListNode(_module.ListNode$T), $Heap), 
    $_reverifyPost: bool);
  free requires 7 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.ListNode.IsList#canCall(_module.ListNode$T, $Heap, l#0);
  ensures _module.ListNode.IsList#canCall(_module.ListNode$T, $Heap, l#0)
     ==> _module.ListNode.IsList(_module.ListNode$T, $LS($LZ), $Heap, l#0)
       || (l#0 == null ==> Lit(true));
  ensures _module.ListNode.IsList#canCall(_module.ListNode$T, $Heap, l#0)
     ==> _module.ListNode.IsList(_module.ListNode$T, $LS($LZ), $Heap, l#0)
       || (l#0 != null
         ==> 
        read($Heap, l#0, _module.ListNode.next) == null
         ==> read($Heap, l#0, _module.ListNode.Repr)[$Box(l#0)]);
  ensures _module.ListNode.IsList#canCall(_module.ListNode$T, $Heap, l#0)
     ==> _module.ListNode.IsList(_module.ListNode$T, $LS($LZ), $Heap, l#0)
       || (l#0 != null
         ==> 
        read($Heap, l#0, _module.ListNode.next) == null
         ==> Seq#Equal(read($Heap, l#0, _module.ListNode.Contents), 
          Seq#Build(Seq#Empty(): Seq Box, read($Heap, l#0, _module.ListNode.data))));
  ensures _module.ListNode.IsList#canCall(_module.ListNode$T, $Heap, l#0)
     ==> _module.ListNode.IsList(_module.ListNode$T, $LS($LZ), $Heap, l#0)
       || (l#0 != null
         ==> 
        read($Heap, l#0, _module.ListNode.next) != null
         ==> Set#Subset(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(l#0)), 
            $Box(read($Heap, l#0, _module.ListNode.next))), 
          read($Heap, l#0, _module.ListNode.Repr)));
  ensures _module.ListNode.IsList#canCall(_module.ListNode$T, $Heap, l#0)
     ==> _module.ListNode.IsList(_module.ListNode$T, $LS($LZ), $Heap, l#0)
       || (l#0 != null
         ==> 
        read($Heap, l#0, _module.ListNode.next) != null
         ==> Seq#Equal(read($Heap, l#0, _module.ListNode.Contents), 
          Seq#Append(Seq#Build(Seq#Empty(): Seq Box, read($Heap, l#0, _module.ListNode.data)), 
            read($Heap, read($Heap, l#0, _module.ListNode.next), _module.ListNode.Contents))));
  ensures _module.ListNode.IsList#canCall(_module.ListNode$T, $Heap, l#0)
     ==> _module.ListNode.IsList(_module.ListNode$T, $LS($LZ), $Heap, l#0)
       || (l#0 != null
         ==> 
        read($Heap, l#0, _module.ListNode.next) != null
         ==> Set#Subset(read($Heap, read($Heap, l#0, _module.ListNode.next), _module.ListNode.Repr), 
          Set#Difference(read($Heap, l#0, _module.ListNode.Repr), 
            Set#UnionOne(Set#Empty(): Set Box, $Box(l#0)))));
  ensures _module.ListNode.IsList#canCall(_module.ListNode$T, $Heap, l#0)
     ==> _module.ListNode.IsList(_module.ListNode$T, $LS($LZ), $Heap, l#0)
       || (l#0 != null
         ==> 
        read($Heap, l#0, _module.ListNode.next) != null
         ==> _module.ListNode.IsList(_module.ListNode$T, 
          $LS($LS($LZ)), 
          $Heap, 
          read($Heap, l#0, _module.ListNode.next)));
  ensures Seq#Equal(read($Heap, l#0, _module.ListNode.Contents), 
    Seq#Build(Seq#Empty(): Seq Box, x#0));
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    $o == l#0 || read($Heap, l#0, _module.ListNode.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.ListNode.Create(_module.ListNode$T: Ty, x#0: Box)
   returns (defass#l#0: bool, l#0: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $nw: ref;
  var $rhs#0_0: Box where $IsBox($rhs#0_0, _module.ListNode$T);
  var $rhs#0_1: ref where $Is($rhs#0_1, Tclass._module.ListNode?(_module.ListNode$T));
  var $rhs#0_2: Set Box
     where $Is($rhs#0_2, TSet(Tclass._module.ListNode(_module.ListNode$T)));
  var $rhs#0_3: Seq Box where $Is($rhs#0_3, TSeq(_module.ListNode$T));
  var $rhs##0: ref
     where $Is($rhs##0, Tclass._module.ListNode(_module.ListNode$T))
       && $IsAlloc($rhs##0, Tclass._module.ListNode(_module.ListNode$T), $Heap);
  var x##0: Box;
  var tail##0: ref;

    // AddMethodImpl: Create, Impl$$_module.ListNode.Create
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(71,2): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(74,5)
    if (*)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(75,9)
        assume true;
        havoc $nw;
        assume $nw != null && dtype($nw) == Tclass._module.ListNode?(_module.ListNode$T);
        assume !read($Heap, $nw, alloc);
        $Heap := update($Heap, $nw, alloc, true);
        assume $IsGoodHeap($Heap);
        assume $IsHeapAnchor($Heap);
        l#0 := $nw;
        defass#l#0 := true;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(75,26)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(76,14)
        assert defass#l#0;
        assert l#0 != null;
        assume true;
        assert $_Frame[l#0, _module.ListNode.data];
        assume true;
        $rhs#0_0 := x#0;
        $Heap := update($Heap, l#0, _module.ListNode.data, $rhs#0_0);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(76,17)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(77,14)
        assert defass#l#0;
        assert l#0 != null;
        assume true;
        assert $_Frame[l#0, _module.ListNode.next];
        assume true;
        $rhs#0_1 := null;
        $Heap := update($Heap, l#0, _module.ListNode.next, $rhs#0_1);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(77,20)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(78,14)
        assert defass#l#0;
        assert l#0 != null;
        assume true;
        assert $_Frame[l#0, _module.ListNode.Repr];
        assert defass#l#0;
        assume true;
        $rhs#0_2 := Set#UnionOne(Set#Empty(): Set Box, $Box(l#0));
        $Heap := update($Heap, l#0, _module.ListNode.Repr, $rhs#0_2);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(78,19)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(79,18)
        assert defass#l#0;
        assert l#0 != null;
        assume true;
        assert $_Frame[l#0, _module.ListNode.Contents];
        assume true;
        $rhs#0_3 := Seq#Build(Seq#Empty(): Seq Box, x#0);
        $Heap := update($Heap, l#0, _module.ListNode.Contents, $rhs#0_3);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(79,23)"} true;
    }
    else
    {
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(81,16)
        assume true;
        // TrCallStmt: Adding lhs with type ListNode<T>
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        x##0 := x#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        tail##0 := null;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call $rhs##0 := Call$$_module.ListNode.Cons(_module.ListNode$T, x##0, tail##0);
        // TrCallStmt: After ProcessCallStmt
        l#0 := $rhs##0;
        defass#l#0 := true;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(81,24)"} true;
    }

    assert defass#l#0;
}



procedure CheckWellformed$$_module.ListNode.Cons(_module.ListNode$T: Ty, 
    x#0: Box
       where $IsBox(x#0, _module.ListNode$T) && $IsAllocBox(x#0, _module.ListNode$T, $Heap), 
    tail#0: ref
       where $Is(tail#0, Tclass._module.ListNode?(_module.ListNode$T))
         && $IsAlloc(tail#0, Tclass._module.ListNode?(_module.ListNode$T), $Heap))
   returns (l#0: ref
       where $Is(l#0, Tclass._module.ListNode(_module.ListNode$T))
         && $IsAlloc(l#0, Tclass._module.ListNode(_module.ListNode$T), $Heap));
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.ListNode.Cons(_module.ListNode$T: Ty, x#0: Box, tail#0: ref) returns (l#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##l#0: ref;
  var ##l#1: ref;

    // AddMethodImpl: Cons, CheckWellformed$$_module.ListNode.Cons
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(85,16): initial state"} true;
    ##l#0 := tail#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##l#0, Tclass._module.ListNode?(_module.ListNode$T), $Heap);
    assume _module.ListNode.IsList#canCall(_module.ListNode$T, $Heap, tail#0);
    assume _module.ListNode.IsList(_module.ListNode$T, $LS($LZ), $Heap, tail#0);
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
    assume $HeapSucc(old($Heap), $Heap);
    havoc l#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(87,18): post-state"} true;
    ##l#1 := l#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##l#1, Tclass._module.ListNode?(_module.ListNode$T), $Heap);
    assume _module.ListNode.IsList#canCall(_module.ListNode$T, $Heap, l#0);
    assume _module.ListNode.IsList(_module.ListNode$T, $LS($LZ), $Heap, l#0);
    if (*)
    {
        assume tail#0 == null;
        assert l#0 != null;
        assume Seq#Equal(read($Heap, l#0, _module.ListNode.Contents), 
          Seq#Build(Seq#Empty(): Seq Box, x#0));
        assert l#0 != null;
        assume (forall $o: ref :: 
          { read(old($Heap), $o, alloc) } 
          $o == l#0 || read($Heap, l#0, _module.ListNode.Repr)[$Box($o)]
             ==> $o != null && !read(old($Heap), $o, alloc));
    }
    else
    {
        assume tail#0 == null
           ==> Seq#Equal(read($Heap, l#0, _module.ListNode.Contents), 
              Seq#Build(Seq#Empty(): Seq Box, x#0))
             && (forall $o: ref :: 
              { read(old($Heap), $o, alloc) } 
              $o == l#0 || read($Heap, l#0, _module.ListNode.Repr)[$Box($o)]
                 ==> $o != null && !read(old($Heap), $o, alloc));
    }

    if (*)
    {
        assume tail#0 != null;
        assert l#0 != null;
        assert tail#0 != null;
        assume Seq#Equal(read($Heap, l#0, _module.ListNode.Contents), 
          Seq#Append(Seq#Build(Seq#Empty(): Seq Box, x#0), 
            read($Heap, tail#0, _module.ListNode.Contents)));
        assert l#0 != null;
        assert tail#0 != null;
        assume (forall $o: ref :: 
          { read(old($Heap), $o, alloc) } 
          ($o == l#0 || read($Heap, l#0, _module.ListNode.Repr)[$Box($o)])
               && !read($Heap, tail#0, _module.ListNode.Repr)[$Box($o)]
             ==> $o != null && !read(old($Heap), $o, alloc));
    }
    else
    {
        assume tail#0 != null
           ==> Seq#Equal(read($Heap, l#0, _module.ListNode.Contents), 
              Seq#Append(Seq#Build(Seq#Empty(): Seq Box, x#0), 
                read($Heap, tail#0, _module.ListNode.Contents)))
             && (forall $o: ref :: 
              { read(old($Heap), $o, alloc) } 
              ($o == l#0 || read($Heap, l#0, _module.ListNode.Repr)[$Box($o)])
                   && !read($Heap, tail#0, _module.ListNode.Repr)[$Box($o)]
                 ==> $o != null && !read(old($Heap), $o, alloc));
    }
}



procedure Call$$_module.ListNode.Cons(_module.ListNode$T: Ty, 
    x#0: Box
       where $IsBox(x#0, _module.ListNode$T) && $IsAllocBox(x#0, _module.ListNode$T, $Heap), 
    tail#0: ref
       where $Is(tail#0, Tclass._module.ListNode?(_module.ListNode$T))
         && $IsAlloc(tail#0, Tclass._module.ListNode?(_module.ListNode$T), $Heap))
   returns (l#0: ref
       where $Is(l#0, Tclass._module.ListNode(_module.ListNode$T))
         && $IsAlloc(l#0, Tclass._module.ListNode(_module.ListNode$T), $Heap));
  // user-defined preconditions
  requires _module.ListNode.IsList#canCall(_module.ListNode$T, $Heap, tail#0)
     ==> _module.ListNode.IsList(_module.ListNode$T, $LS($LZ), $Heap, tail#0)
       || (tail#0 == null ==> Lit(true));
  requires _module.ListNode.IsList#canCall(_module.ListNode$T, $Heap, tail#0)
     ==> _module.ListNode.IsList(_module.ListNode$T, $LS($LZ), $Heap, tail#0)
       || (tail#0 != null
         ==> 
        read($Heap, tail#0, _module.ListNode.next) == null
         ==> read($Heap, tail#0, _module.ListNode.Repr)[$Box(tail#0)]);
  requires _module.ListNode.IsList#canCall(_module.ListNode$T, $Heap, tail#0)
     ==> _module.ListNode.IsList(_module.ListNode$T, $LS($LZ), $Heap, tail#0)
       || (tail#0 != null
         ==> 
        read($Heap, tail#0, _module.ListNode.next) == null
         ==> Seq#Equal(read($Heap, tail#0, _module.ListNode.Contents), 
          Seq#Build(Seq#Empty(): Seq Box, read($Heap, tail#0, _module.ListNode.data))));
  requires _module.ListNode.IsList#canCall(_module.ListNode$T, $Heap, tail#0)
     ==> _module.ListNode.IsList(_module.ListNode$T, $LS($LZ), $Heap, tail#0)
       || (tail#0 != null
         ==> 
        read($Heap, tail#0, _module.ListNode.next) != null
         ==> Set#Subset(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(tail#0)), 
            $Box(read($Heap, tail#0, _module.ListNode.next))), 
          read($Heap, tail#0, _module.ListNode.Repr)));
  requires _module.ListNode.IsList#canCall(_module.ListNode$T, $Heap, tail#0)
     ==> _module.ListNode.IsList(_module.ListNode$T, $LS($LZ), $Heap, tail#0)
       || (tail#0 != null
         ==> 
        read($Heap, tail#0, _module.ListNode.next) != null
         ==> Seq#Equal(read($Heap, tail#0, _module.ListNode.Contents), 
          Seq#Append(Seq#Build(Seq#Empty(): Seq Box, read($Heap, tail#0, _module.ListNode.data)), 
            read($Heap, read($Heap, tail#0, _module.ListNode.next), _module.ListNode.Contents))));
  requires _module.ListNode.IsList#canCall(_module.ListNode$T, $Heap, tail#0)
     ==> _module.ListNode.IsList(_module.ListNode$T, $LS($LZ), $Heap, tail#0)
       || (tail#0 != null
         ==> 
        read($Heap, tail#0, _module.ListNode.next) != null
         ==> Set#Subset(read($Heap, read($Heap, tail#0, _module.ListNode.next), _module.ListNode.Repr), 
          Set#Difference(read($Heap, tail#0, _module.ListNode.Repr), 
            Set#UnionOne(Set#Empty(): Set Box, $Box(tail#0)))));
  requires _module.ListNode.IsList#canCall(_module.ListNode$T, $Heap, tail#0)
     ==> _module.ListNode.IsList(_module.ListNode$T, $LS($LZ), $Heap, tail#0)
       || (tail#0 != null
         ==> 
        read($Heap, tail#0, _module.ListNode.next) != null
         ==> _module.ListNode.IsList(_module.ListNode$T, 
          $LS($LS($LZ)), 
          $Heap, 
          read($Heap, tail#0, _module.ListNode.next)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.ListNode.IsList#canCall(_module.ListNode$T, $Heap, l#0);
  free ensures _module.ListNode.IsList#canCall(_module.ListNode$T, $Heap, l#0)
     && 
    _module.ListNode.IsList(_module.ListNode$T, $LS($LZ), $Heap, l#0)
     && (if l#0 == null
       then true
       else (if read($Heap, l#0, _module.ListNode.next) == null
         then read($Heap, l#0, _module.ListNode.Repr)[$Box(l#0)]
           && Seq#Equal(read($Heap, l#0, _module.ListNode.Contents), 
            Seq#Build(Seq#Empty(): Seq Box, read($Heap, l#0, _module.ListNode.data)))
         else Set#Subset(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(l#0)), 
              $Box(read($Heap, l#0, _module.ListNode.next))), 
            read($Heap, l#0, _module.ListNode.Repr))
           && Seq#Equal(read($Heap, l#0, _module.ListNode.Contents), 
            Seq#Append(Seq#Build(Seq#Empty(): Seq Box, read($Heap, l#0, _module.ListNode.data)), 
              read($Heap, read($Heap, l#0, _module.ListNode.next), _module.ListNode.Contents)))
           && Set#Subset(read($Heap, read($Heap, l#0, _module.ListNode.next), _module.ListNode.Repr), 
            Set#Difference(read($Heap, l#0, _module.ListNode.Repr), 
              Set#UnionOne(Set#Empty(): Set Box, $Box(l#0))))
           && _module.ListNode.IsList(_module.ListNode$T, $LS($LZ), $Heap, read($Heap, l#0, _module.ListNode.next))));
  free ensures true;
  ensures tail#0 == null
     ==> Seq#Equal(read($Heap, l#0, _module.ListNode.Contents), 
      Seq#Build(Seq#Empty(): Seq Box, x#0));
  ensures tail#0 == null
     ==> (forall $o: ref :: 
      { read(old($Heap), $o, alloc) } 
      $o == l#0 || read($Heap, l#0, _module.ListNode.Repr)[$Box($o)]
         ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures tail#0 != null
     ==> Seq#Equal(read($Heap, l#0, _module.ListNode.Contents), 
      Seq#Append(Seq#Build(Seq#Empty(): Seq Box, x#0), 
        read($Heap, tail#0, _module.ListNode.Contents)));
  ensures tail#0 != null
     ==> (forall $o: ref :: 
      { read(old($Heap), $o, alloc) } 
      ($o == l#0 || read($Heap, l#0, _module.ListNode.Repr)[$Box($o)])
           && !read($Heap, tail#0, _module.ListNode.Repr)[$Box($o)]
         ==> $o != null && !read(old($Heap), $o, alloc));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.ListNode.Cons(_module.ListNode$T: Ty, 
    x#0: Box
       where $IsBox(x#0, _module.ListNode$T) && $IsAllocBox(x#0, _module.ListNode$T, $Heap), 
    tail#0: ref
       where $Is(tail#0, Tclass._module.ListNode?(_module.ListNode$T))
         && $IsAlloc(tail#0, Tclass._module.ListNode?(_module.ListNode$T), $Heap))
   returns (defass#l#0: bool, 
    l#0: ref
       where defass#l#0
         ==> $Is(l#0, Tclass._module.ListNode(_module.ListNode$T))
           && $IsAlloc(l#0, Tclass._module.ListNode(_module.ListNode$T), $Heap), 
    $_reverifyPost: bool);
  free requires 6 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.ListNode.IsList#canCall(_module.ListNode$T, $Heap, tail#0)
     && 
    _module.ListNode.IsList(_module.ListNode$T, $LS($LZ), $Heap, tail#0)
     && (if tail#0 == null
       then true
       else (if read($Heap, tail#0, _module.ListNode.next) == null
         then read($Heap, tail#0, _module.ListNode.Repr)[$Box(tail#0)]
           && Seq#Equal(read($Heap, tail#0, _module.ListNode.Contents), 
            Seq#Build(Seq#Empty(): Seq Box, read($Heap, tail#0, _module.ListNode.data)))
         else Set#Subset(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(tail#0)), 
              $Box(read($Heap, tail#0, _module.ListNode.next))), 
            read($Heap, tail#0, _module.ListNode.Repr))
           && Seq#Equal(read($Heap, tail#0, _module.ListNode.Contents), 
            Seq#Append(Seq#Build(Seq#Empty(): Seq Box, read($Heap, tail#0, _module.ListNode.data)), 
              read($Heap, read($Heap, tail#0, _module.ListNode.next), _module.ListNode.Contents)))
           && Set#Subset(read($Heap, read($Heap, tail#0, _module.ListNode.next), _module.ListNode.Repr), 
            Set#Difference(read($Heap, tail#0, _module.ListNode.Repr), 
              Set#UnionOne(Set#Empty(): Set Box, $Box(tail#0))))
           && _module.ListNode.IsList(_module.ListNode$T, $LS($LZ), $Heap, read($Heap, tail#0, _module.ListNode.next))));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.ListNode.IsList#canCall(_module.ListNode$T, $Heap, l#0);
  ensures _module.ListNode.IsList#canCall(_module.ListNode$T, $Heap, l#0)
     ==> _module.ListNode.IsList(_module.ListNode$T, $LS($LZ), $Heap, l#0)
       || (l#0 == null ==> Lit(true));
  ensures _module.ListNode.IsList#canCall(_module.ListNode$T, $Heap, l#0)
     ==> _module.ListNode.IsList(_module.ListNode$T, $LS($LZ), $Heap, l#0)
       || (l#0 != null
         ==> 
        read($Heap, l#0, _module.ListNode.next) == null
         ==> read($Heap, l#0, _module.ListNode.Repr)[$Box(l#0)]);
  ensures _module.ListNode.IsList#canCall(_module.ListNode$T, $Heap, l#0)
     ==> _module.ListNode.IsList(_module.ListNode$T, $LS($LZ), $Heap, l#0)
       || (l#0 != null
         ==> 
        read($Heap, l#0, _module.ListNode.next) == null
         ==> Seq#Equal(read($Heap, l#0, _module.ListNode.Contents), 
          Seq#Build(Seq#Empty(): Seq Box, read($Heap, l#0, _module.ListNode.data))));
  ensures _module.ListNode.IsList#canCall(_module.ListNode$T, $Heap, l#0)
     ==> _module.ListNode.IsList(_module.ListNode$T, $LS($LZ), $Heap, l#0)
       || (l#0 != null
         ==> 
        read($Heap, l#0, _module.ListNode.next) != null
         ==> Set#Subset(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(l#0)), 
            $Box(read($Heap, l#0, _module.ListNode.next))), 
          read($Heap, l#0, _module.ListNode.Repr)));
  ensures _module.ListNode.IsList#canCall(_module.ListNode$T, $Heap, l#0)
     ==> _module.ListNode.IsList(_module.ListNode$T, $LS($LZ), $Heap, l#0)
       || (l#0 != null
         ==> 
        read($Heap, l#0, _module.ListNode.next) != null
         ==> Seq#Equal(read($Heap, l#0, _module.ListNode.Contents), 
          Seq#Append(Seq#Build(Seq#Empty(): Seq Box, read($Heap, l#0, _module.ListNode.data)), 
            read($Heap, read($Heap, l#0, _module.ListNode.next), _module.ListNode.Contents))));
  ensures _module.ListNode.IsList#canCall(_module.ListNode$T, $Heap, l#0)
     ==> _module.ListNode.IsList(_module.ListNode$T, $LS($LZ), $Heap, l#0)
       || (l#0 != null
         ==> 
        read($Heap, l#0, _module.ListNode.next) != null
         ==> Set#Subset(read($Heap, read($Heap, l#0, _module.ListNode.next), _module.ListNode.Repr), 
          Set#Difference(read($Heap, l#0, _module.ListNode.Repr), 
            Set#UnionOne(Set#Empty(): Set Box, $Box(l#0)))));
  ensures _module.ListNode.IsList#canCall(_module.ListNode$T, $Heap, l#0)
     ==> _module.ListNode.IsList(_module.ListNode$T, $LS($LZ), $Heap, l#0)
       || (l#0 != null
         ==> 
        read($Heap, l#0, _module.ListNode.next) != null
         ==> _module.ListNode.IsList(_module.ListNode$T, 
          $LS($LS($LZ)), 
          $Heap, 
          read($Heap, l#0, _module.ListNode.next)));
  free ensures true;
  ensures tail#0 == null
     ==> Seq#Equal(read($Heap, l#0, _module.ListNode.Contents), 
      Seq#Build(Seq#Empty(): Seq Box, x#0));
  ensures tail#0 == null
     ==> (forall $o: ref :: 
      { read(old($Heap), $o, alloc) } 
      $o == l#0 || read($Heap, l#0, _module.ListNode.Repr)[$Box($o)]
         ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures tail#0 != null
     ==> Seq#Equal(read($Heap, l#0, _module.ListNode.Contents), 
      Seq#Append(Seq#Build(Seq#Empty(): Seq Box, x#0), 
        read($Heap, tail#0, _module.ListNode.Contents)));
  ensures tail#0 != null
     ==> (forall $o: ref :: 
      { read(old($Heap), $o, alloc) } 
      ($o == l#0 || read($Heap, l#0, _module.ListNode.Repr)[$Box($o)])
           && !read($Heap, tail#0, _module.ListNode.Repr)[$Box($o)]
         ==> $o != null && !read(old($Heap), $o, alloc));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.ListNode.Cons(_module.ListNode$T: Ty, x#0: Box, tail#0: ref)
   returns (defass#l#0: bool, l#0: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $nw: ref;
  var $rhs#0: Box where $IsBox($rhs#0, _module.ListNode$T);
  var $rhs#1: ref where $Is($rhs#1, Tclass._module.ListNode?(_module.ListNode$T));
  var $rhs#0_0: Set Box
     where $Is($rhs#0_0, TSet(Tclass._module.ListNode(_module.ListNode$T)));
  var $rhs#0_1: Seq Box where $Is($rhs#0_1, TSeq(_module.ListNode$T));
  var $rhs#2: Set Box
     where $Is($rhs#2, TSet(Tclass._module.ListNode(_module.ListNode$T)));
  var $rhs#3: Seq Box where $Is($rhs#3, TSeq(_module.ListNode$T));

    // AddMethodImpl: Cons, Impl$$_module.ListNode.Cons
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(90,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(91,7)
    assume true;
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._module.ListNode?(_module.ListNode$T);
    assume !read($Heap, $nw, alloc);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    l#0 := $nw;
    defass#l#0 := true;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(91,24)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(92,12)
    assert defass#l#0;
    assert l#0 != null;
    assume true;
    assert $_Frame[l#0, _module.ListNode.data];
    assume true;
    $rhs#0 := x#0;
    $Heap := update($Heap, l#0, _module.ListNode.data, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(92,15)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(93,12)
    assert defass#l#0;
    assert l#0 != null;
    assume true;
    assert $_Frame[l#0, _module.ListNode.next];
    assume true;
    $rhs#1 := tail#0;
    $Heap := update($Heap, l#0, _module.ListNode.next, $rhs#1);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(93,18)"} true;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(94,5)
    assume true;
    if (tail#0 != null)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(95,14)
        assert defass#l#0;
        assert l#0 != null;
        assume true;
        assert $_Frame[l#0, _module.ListNode.Repr];
        assert tail#0 != null;
        assert defass#l#0;
        assume true;
        $rhs#0_0 := Set#Union(read($Heap, tail#0, _module.ListNode.Repr), 
          Set#UnionOne(Set#Empty(): Set Box, $Box(l#0)));
        $Heap := update($Heap, l#0, _module.ListNode.Repr, $rhs#0_0);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(95,31)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(96,18)
        assert defass#l#0;
        assert l#0 != null;
        assume true;
        assert $_Frame[l#0, _module.ListNode.Contents];
        assert tail#0 != null;
        assume true;
        $rhs#0_1 := Seq#Append(Seq#Build(Seq#Empty(): Seq Box, x#0), 
          read($Heap, tail#0, _module.ListNode.Contents));
        $Heap := update($Heap, l#0, _module.ListNode.Contents, $rhs#0_1);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(96,39)"} true;
    }
    else
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(98,14)
        assert defass#l#0;
        assert l#0 != null;
        assume true;
        assert $_Frame[l#0, _module.ListNode.Repr];
        assert defass#l#0;
        assume true;
        $rhs#2 := Set#UnionOne(Set#Empty(): Set Box, $Box(l#0));
        $Heap := update($Heap, l#0, _module.ListNode.Repr, $rhs#2);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(98,19)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(99,18)
        assert defass#l#0;
        assert l#0 != null;
        assume true;
        assert $_Frame[l#0, _module.ListNode.Contents];
        assume true;
        $rhs#3 := Seq#Build(Seq#Empty(): Seq Box, x#0);
        $Heap := update($Heap, l#0, _module.ListNode.Contents, $rhs#3);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(99,23)"} true;
    }

    assert defass#l#0;
}



// _module.ListNode: subset type $Is
axiom (forall _module.ListNode$T: Ty, c#0: ref :: 
  { $Is(c#0, Tclass._module.ListNode(_module.ListNode$T)) } 
  $Is(c#0, Tclass._module.ListNode(_module.ListNode$T))
     <==> $Is(c#0, Tclass._module.ListNode?(_module.ListNode$T)) && c#0 != null);

// _module.ListNode: subset type $IsAlloc
axiom (forall _module.ListNode$T: Ty, c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.ListNode(_module.ListNode$T), $h) } 
  $IsAlloc(c#0, Tclass._module.ListNode(_module.ListNode$T), $h)
     <==> $IsAlloc(c#0, Tclass._module.ListNode?(_module.ListNode$T), $h));

const unique class._module.List?: ClassName;

function Tclass._module.List?(Ty) : Ty;

const unique Tagclass._module.List?: TyTag;

// Tclass._module.List? Tag
axiom (forall _module.List$T: Ty :: 
  { Tclass._module.List?(_module.List$T) } 
  Tag(Tclass._module.List?(_module.List$T)) == Tagclass._module.List?
     && TagFamily(Tclass._module.List?(_module.List$T)) == tytagFamily$List);

// Tclass._module.List? injectivity 0
axiom (forall _module.List$T: Ty :: 
  { Tclass._module.List?(_module.List$T) } 
  Tclass._module.List?_0(Tclass._module.List?(_module.List$T)) == _module.List$T);

function Tclass._module.List?_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.List?
axiom (forall _module.List$T: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.List?(_module.List$T)) } 
  $IsBox(bx, Tclass._module.List?(_module.List$T))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.List?(_module.List$T)));

// List: Class $Is
axiom (forall _module.List$T: Ty, $o: ref :: 
  { $Is($o, Tclass._module.List?(_module.List$T)) } 
  $Is($o, Tclass._module.List?(_module.List$T))
     <==> $o == null || dtype($o) == Tclass._module.List?(_module.List$T));

// List: Class $IsAlloc
axiom (forall _module.List$T: Ty, $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.List?(_module.List$T), $h) } 
  $IsAlloc($o, Tclass._module.List?(_module.List$T), $h)
     <==> $o == null || read($h, $o, alloc));

axiom FDim(_module.List.Contents) == 0
   && FieldOfDecl(class._module.List?, field$Contents) == _module.List.Contents
   && $IsGhostField(_module.List.Contents);

const _module.List.Contents: Field (Seq Box);

// List.Contents: Type axiom
axiom (forall _module.List$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.List.Contents), Tclass._module.List?(_module.List$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.List?(_module.List$T)
     ==> $Is(read($h, $o, _module.List.Contents), TSeq(_module.List$T)));

// List.Contents: Allocation axiom
axiom (forall _module.List$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.List.Contents), Tclass._module.List?(_module.List$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.List?(_module.List$T)
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.List.Contents), TSeq(_module.List$T), $h));

axiom FDim(_module.List.Repr) == 0
   && FieldOfDecl(class._module.List?, field$Repr) == _module.List.Repr
   && $IsGhostField(_module.List.Repr);

const _module.List.Repr: Field (Set Box);

// List.Repr: Type axiom
axiom (forall _module.List$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.List.Repr), Tclass._module.List?(_module.List$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.List?(_module.List$T)
     ==> $Is(read($h, $o, _module.List.Repr), TSet(Tclass._System.object())));

// List.Repr: Allocation axiom
axiom (forall _module.List$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.List.Repr), Tclass._module.List?(_module.List$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.List?(_module.List$T)
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.List.Repr), TSet(Tclass._System.object()), $h));

axiom FDim(_module.List.head) == 0
   && FieldOfDecl(class._module.List?, field$head) == _module.List.head
   && !$IsGhostField(_module.List.head);

const _module.List.head: Field ref;

function Tclass._module.LLNode(Ty) : Ty;

const unique Tagclass._module.LLNode: TyTag;

// Tclass._module.LLNode Tag
axiom (forall _module.LLNode$T: Ty :: 
  { Tclass._module.LLNode(_module.LLNode$T) } 
  Tag(Tclass._module.LLNode(_module.LLNode$T)) == Tagclass._module.LLNode
     && TagFamily(Tclass._module.LLNode(_module.LLNode$T)) == tytagFamily$LLNode);

// Tclass._module.LLNode injectivity 0
axiom (forall _module.LLNode$T: Ty :: 
  { Tclass._module.LLNode(_module.LLNode$T) } 
  Tclass._module.LLNode_0(Tclass._module.LLNode(_module.LLNode$T))
     == _module.LLNode$T);

function Tclass._module.LLNode_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.LLNode
axiom (forall _module.LLNode$T: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.LLNode(_module.LLNode$T)) } 
  $IsBox(bx, Tclass._module.LLNode(_module.LLNode$T))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.LLNode(_module.LLNode$T)));

// List.head: Type axiom
axiom (forall _module.List$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.List.head), Tclass._module.List?(_module.List$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.List?(_module.List$T)
     ==> $Is(read($h, $o, _module.List.head), Tclass._module.LLNode(_module.List$T)));

// List.head: Allocation axiom
axiom (forall _module.List$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.List.head), Tclass._module.List?(_module.List$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.List?(_module.List$T)
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.List.head), Tclass._module.LLNode(_module.List$T), $h));

// function declaration for _module.List.IsList
function _module.List.IsList(_module.List$T: Ty, $heap: Heap, this: ref) : bool;

function _module.List.IsList#canCall(_module.List$T: Ty, $heap: Heap, this: ref) : bool;

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
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.List(_module.List$T)));

// frame axiom for _module.List.IsList
axiom (forall _module.List$T: Ty, $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.List.IsList(_module.List$T, $h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.List(_module.List$T))
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && ($o == this || read($h0, this, _module.List.Repr)[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.List.IsList(_module.List$T, $h0, this)
       == _module.List.IsList(_module.List$T, $h1, this));

// consequence axiom for _module.List.IsList
axiom 9 <= $FunctionContextHeight
   ==> (forall _module.List$T: Ty, $Heap: Heap, this: ref :: 
    { _module.List.IsList(_module.List$T, $Heap, this) } 
    _module.List.IsList#canCall(_module.List$T, $Heap, this)
         || (9 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.List(_module.List$T))
           && $IsAlloc(this, Tclass._module.List(_module.List$T), $Heap))
       ==> true);

function _module.List.IsList#requires(Ty, Heap, ref) : bool;

// #requires axiom for _module.List.IsList
axiom (forall _module.List$T: Ty, $Heap: Heap, this: ref :: 
  { _module.List.IsList#requires(_module.List$T, $Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.List(_module.List$T))
       && $IsAlloc(this, Tclass._module.List(_module.List$T), $Heap)
     ==> _module.List.IsList#requires(_module.List$T, $Heap, this) == true);

axiom FDim(_module.LLNode.Repr) == 0
   && FieldOfDecl(class._module.LLNode?, field$Repr) == _module.LLNode.Repr
   && $IsGhostField(_module.LLNode.Repr);

axiom FDim(_module.LLNode.TailContents) == 0
   && FieldOfDecl(class._module.LLNode?, field$TailContents)
     == _module.LLNode.TailContents
   && $IsGhostField(_module.LLNode.TailContents);

// definition axiom for _module.List.IsList (revealed)
axiom 9 <= $FunctionContextHeight
   ==> (forall _module.List$T: Ty, $Heap: Heap, this: ref :: 
    { _module.List.IsList(_module.List$T, $Heap, this), $IsGoodHeap($Heap) } 
    _module.List.IsList#canCall(_module.List$T, $Heap, this)
         || (9 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.List(_module.List$T))
           && $IsAlloc(this, Tclass._module.List(_module.List$T), $Heap))
       ==> (read($Heap, this, _module.List.Repr)[$Box(this)]
           ==> 
          read($Heap, this, _module.List.Repr)[$Box(read($Heap, this, _module.List.head))]
           ==> 
          Set#Subset(read($Heap, read($Heap, this, _module.List.head), _module.LLNode.Repr), 
            read($Heap, this, _module.List.Repr))
           ==> 
          !read($Heap, read($Heap, this, _module.List.head), _module.LLNode.Repr)[$Box(this)]
           ==> _module.LLNode.IsWellFormed#canCall(_module.List$T, $Heap, read($Heap, this, _module.List.head)))
         && _module.List.IsList(_module.List$T, $Heap, this)
           == (
            read($Heap, this, _module.List.Repr)[$Box(this)]
             && read($Heap, this, _module.List.Repr)[$Box(read($Heap, this, _module.List.head))]
             && Set#Subset(read($Heap, read($Heap, this, _module.List.head), _module.LLNode.Repr), 
              read($Heap, this, _module.List.Repr))
             && !read($Heap, read($Heap, this, _module.List.head), _module.LLNode.Repr)[$Box(this)]
             && _module.LLNode.IsWellFormed(_module.List$T, $LS($LZ), $Heap, read($Heap, this, _module.List.head))
             && Seq#Equal(read($Heap, this, _module.List.Contents), 
              read($Heap, read($Heap, this, _module.List.head), _module.LLNode.TailContents))));

procedure CheckWellformed$$_module.List.IsList(_module.List$T: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.List(_module.List$T))
         && $IsAlloc(this, Tclass._module.List(_module.List$T), $Heap));
  free requires 9 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.List.IsList(_module.List$T: Ty, this: ref)
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
  var b$reqreads#12: bool;
  var b$reqreads#13: bool;

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
    b$reqreads#12 := true;
    b$reqreads#13 := true;

    // AddWellformednessCheck for function IsList
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(114,12): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> $o == this || read($Heap, this, _module.List.Repr)[$Box($o)]);
    b$reqreads#0 := $_Frame[this, _module.List.Repr];
    assert b$reqreads#0;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc)
             ==> $o == this || read($Heap, this, _module.List.Repr)[$Box($o)]);
        b$reqreads#1 := $_Frame[this, _module.List.Repr];
        if (read($Heap, this, _module.List.Repr)[$Box(this)])
        {
            b$reqreads#2 := $_Frame[this, _module.List.head];
            b$reqreads#3 := $_Frame[this, _module.List.Repr];
        }

        if (read($Heap, this, _module.List.Repr)[$Box(this)]
           && read($Heap, this, _module.List.Repr)[$Box(read($Heap, this, _module.List.head))])
        {
            b$reqreads#4 := $_Frame[this, _module.List.head];
            assert read($Heap, this, _module.List.head) != null;
            b$reqreads#5 := $_Frame[read($Heap, this, _module.List.head), _module.LLNode.Repr];
            b$reqreads#6 := $_Frame[this, _module.List.Repr];
        }

        if (read($Heap, this, _module.List.Repr)[$Box(this)]
           && read($Heap, this, _module.List.Repr)[$Box(read($Heap, this, _module.List.head))]
           && Set#Subset(read($Heap, read($Heap, this, _module.List.head), _module.LLNode.Repr), 
            read($Heap, this, _module.List.Repr)))
        {
            b$reqreads#7 := $_Frame[this, _module.List.head];
            assert read($Heap, this, _module.List.head) != null;
            b$reqreads#8 := $_Frame[read($Heap, this, _module.List.head), _module.LLNode.Repr];
        }

        if (read($Heap, this, _module.List.Repr)[$Box(this)]
           && read($Heap, this, _module.List.Repr)[$Box(read($Heap, this, _module.List.head))]
           && Set#Subset(read($Heap, read($Heap, this, _module.List.head), _module.LLNode.Repr), 
            read($Heap, this, _module.List.Repr))
           && !read($Heap, read($Heap, this, _module.List.head), _module.LLNode.Repr)[$Box(this)])
        {
            b$reqreads#9 := $_Frame[this, _module.List.head];
            assert read($Heap, this, _module.List.head) != null;
            b$reqreads#10 := (forall<alpha> $o: ref, $f: Field alpha :: 
              $o != null
                   && read($Heap, $o, alloc)
                   && ($o == read($Heap, this, _module.List.head)
                     || read($Heap, read($Heap, this, _module.List.head), _module.LLNode.Repr)[$Box($o)])
                 ==> $_Frame[$o, $f]);
            assume _module.LLNode.IsWellFormed#canCall(_module.List$T, $Heap, read($Heap, this, _module.List.head));
        }

        if (read($Heap, this, _module.List.Repr)[$Box(this)]
           && read($Heap, this, _module.List.Repr)[$Box(read($Heap, this, _module.List.head))]
           && Set#Subset(read($Heap, read($Heap, this, _module.List.head), _module.LLNode.Repr), 
            read($Heap, this, _module.List.Repr))
           && !read($Heap, read($Heap, this, _module.List.head), _module.LLNode.Repr)[$Box(this)]
           && _module.LLNode.IsWellFormed(_module.List$T, $LS($LZ), $Heap, read($Heap, this, _module.List.head)))
        {
            b$reqreads#11 := $_Frame[this, _module.List.Contents];
            b$reqreads#12 := $_Frame[this, _module.List.head];
            assert read($Heap, this, _module.List.head) != null;
            b$reqreads#13 := $_Frame[read($Heap, this, _module.List.head), _module.LLNode.TailContents];
        }

        assume _module.List.IsList(_module.List$T, $Heap, this)
           == (
            read($Heap, this, _module.List.Repr)[$Box(this)]
             && read($Heap, this, _module.List.Repr)[$Box(read($Heap, this, _module.List.head))]
             && Set#Subset(read($Heap, read($Heap, this, _module.List.head), _module.LLNode.Repr), 
              read($Heap, this, _module.List.Repr))
             && !read($Heap, read($Heap, this, _module.List.head), _module.LLNode.Repr)[$Box(this)]
             && _module.LLNode.IsWellFormed(_module.List$T, $LS($LZ), $Heap, read($Heap, this, _module.List.head))
             && Seq#Equal(read($Heap, this, _module.List.Contents), 
              read($Heap, read($Heap, this, _module.List.head), _module.LLNode.TailContents)));
        assume read($Heap, this, _module.List.Repr)[$Box(this)]
           ==> 
          read($Heap, this, _module.List.Repr)[$Box(read($Heap, this, _module.List.head))]
           ==> 
          Set#Subset(read($Heap, read($Heap, this, _module.List.head), _module.LLNode.Repr), 
            read($Heap, this, _module.List.Repr))
           ==> 
          !read($Heap, read($Heap, this, _module.List.head), _module.LLNode.Repr)[$Box(this)]
           ==> _module.LLNode.IsWellFormed#canCall(_module.List$T, $Heap, read($Heap, this, _module.List.head));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.List.IsList(_module.List$T, $Heap, this), TBool);
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
        assert b$reqreads#12;
        assert b$reqreads#13;
    }
}



procedure CheckWellformed$$_module.List.Init(_module.List$T: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.List(_module.List$T))
         && $IsAlloc(this, Tclass._module.List(_module.List$T), $Heap));
  free requires 11 == $FunctionContextHeight;
  modifies $Heap, $Tick;



axiom FDim(_module.LLNode.next) == 0
   && FieldOfDecl(class._module.LLNode?, field$next) == _module.LLNode.next
   && !$IsGhostField(_module.LLNode.next);

axiom FDim(_module.LLNode.data) == 0
   && FieldOfDecl(class._module.LLNode?, field$data) == _module.LLNode.data
   && !$IsGhostField(_module.LLNode.data);

procedure Call$$_module.List.Init(_module.List$T: Ty)
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass._module.List(_module.List$T))
         && $IsAlloc(this, Tclass._module.List(_module.List$T), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.List.IsList#canCall(_module.List$T, $Heap, this);
  free ensures _module.List.IsList#canCall(_module.List$T, $Heap, this)
     && 
    _module.List.IsList(_module.List$T, $Heap, this)
     && 
    read($Heap, this, _module.List.Repr)[$Box(this)]
     && read($Heap, this, _module.List.Repr)[$Box(read($Heap, this, _module.List.head))]
     && Set#Subset(read($Heap, read($Heap, this, _module.List.head), _module.LLNode.Repr), 
      read($Heap, this, _module.List.Repr))
     && !read($Heap, read($Heap, this, _module.List.head), _module.LLNode.Repr)[$Box(this)]
     && _module.LLNode.IsWellFormed(_module.List$T, $LS($LZ), $Heap, read($Heap, this, _module.List.head))
     && Seq#Equal(read($Heap, this, _module.List.Contents), 
      read($Heap, read($Heap, this, _module.List.head), _module.LLNode.TailContents));
  ensures Seq#Equal(read($Heap, this, _module.List.Contents), Seq#Empty(): Seq Box);
  ensures (forall $o: ref :: 
    { read($Heap, this, _module.List.Repr)[$Box($o)] } 
    read($Heap, this, _module.List.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  // constructor allocates the object
  ensures !read(old($Heap), this, alloc);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.List.Init(_module.List$T: Ty)
   returns (this: ref where this != null && $Is(this, Tclass._module.List(_module.List$T)), 
    $_reverifyPost: bool);
  free requires 11 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.List.IsList#canCall(_module.List$T, $Heap, this);
  ensures _module.List.IsList#canCall(_module.List$T, $Heap, this)
     ==> _module.List.IsList(_module.List$T, $Heap, this)
       || read($Heap, this, _module.List.Repr)[$Box(this)];
  ensures _module.List.IsList#canCall(_module.List$T, $Heap, this)
     ==> _module.List.IsList(_module.List$T, $Heap, this)
       || read($Heap, this, _module.List.Repr)[$Box(read($Heap, this, _module.List.head))];
  ensures _module.List.IsList#canCall(_module.List$T, $Heap, this)
     ==> _module.List.IsList(_module.List$T, $Heap, this)
       || Set#Subset(read($Heap, read($Heap, this, _module.List.head), _module.LLNode.Repr), 
        read($Heap, this, _module.List.Repr));
  ensures _module.List.IsList#canCall(_module.List$T, $Heap, this)
     ==> _module.List.IsList(_module.List$T, $Heap, this)
       || !read($Heap, read($Heap, this, _module.List.head), _module.LLNode.Repr)[$Box(this)];
  ensures _module.List.IsList#canCall(_module.List$T, $Heap, this)
     ==> _module.List.IsList(_module.List$T, $Heap, this)
       || (_module.LLNode.IsWellFormed#canCall(_module.List$T, $Heap, read($Heap, this, _module.List.head))
         ==> _module.LLNode.IsWellFormed(_module.List$T, $LS($LZ), $Heap, read($Heap, this, _module.List.head))
           || read($Heap, read($Heap, this, _module.List.head), _module.LLNode.Repr)[$Box(read($Heap, this, _module.List.head))]);
  ensures _module.List.IsList#canCall(_module.List$T, $Heap, this)
     ==> _module.List.IsList(_module.List$T, $Heap, this)
       || (_module.LLNode.IsWellFormed#canCall(_module.List$T, $Heap, read($Heap, this, _module.List.head))
         ==> _module.LLNode.IsWellFormed(_module.List$T, $LS($LZ), $Heap, read($Heap, this, _module.List.head))
           || (read($Heap, read($Heap, this, _module.List.head), _module.LLNode.next) == null
             ==> Seq#Equal(read($Heap, read($Heap, this, _module.List.head), _module.LLNode.TailContents), 
              Seq#Empty(): Seq Box)));
  ensures _module.List.IsList#canCall(_module.List$T, $Heap, this)
     ==> _module.List.IsList(_module.List$T, $Heap, this)
       || (_module.LLNode.IsWellFormed#canCall(_module.List$T, $Heap, read($Heap, this, _module.List.head))
         ==> _module.LLNode.IsWellFormed(_module.List$T, $LS($LZ), $Heap, read($Heap, this, _module.List.head))
           || (read($Heap, read($Heap, this, _module.List.head), _module.LLNode.next) != null
             ==> read($Heap, read($Heap, this, _module.List.head), _module.LLNode.Repr)[$Box(read($Heap, read($Heap, this, _module.List.head), _module.LLNode.next))]));
  ensures _module.List.IsList#canCall(_module.List$T, $Heap, this)
     ==> _module.List.IsList(_module.List$T, $Heap, this)
       || (_module.LLNode.IsWellFormed#canCall(_module.List$T, $Heap, read($Heap, this, _module.List.head))
         ==> _module.LLNode.IsWellFormed(_module.List$T, $LS($LZ), $Heap, read($Heap, this, _module.List.head))
           || (read($Heap, read($Heap, this, _module.List.head), _module.LLNode.next) != null
             ==> Set#Subset(read($Heap, 
                read($Heap, read($Heap, this, _module.List.head), _module.LLNode.next), 
                _module.LLNode.Repr), 
              read($Heap, read($Heap, this, _module.List.head), _module.LLNode.Repr))));
  ensures _module.List.IsList#canCall(_module.List$T, $Heap, this)
     ==> _module.List.IsList(_module.List$T, $Heap, this)
       || (_module.LLNode.IsWellFormed#canCall(_module.List$T, $Heap, read($Heap, this, _module.List.head))
         ==> _module.LLNode.IsWellFormed(_module.List$T, $LS($LZ), $Heap, read($Heap, this, _module.List.head))
           || (read($Heap, read($Heap, this, _module.List.head), _module.LLNode.next) != null
             ==> !read($Heap, 
              read($Heap, read($Heap, this, _module.List.head), _module.LLNode.next), 
              _module.LLNode.Repr)[$Box(read($Heap, this, _module.List.head))]));
  ensures _module.List.IsList#canCall(_module.List$T, $Heap, this)
     ==> _module.List.IsList(_module.List$T, $Heap, this)
       || (_module.LLNode.IsWellFormed#canCall(_module.List$T, $Heap, read($Heap, this, _module.List.head))
         ==> _module.LLNode.IsWellFormed(_module.List$T, $LS($LZ), $Heap, read($Heap, this, _module.List.head))
           || (read($Heap, read($Heap, this, _module.List.head), _module.LLNode.next) != null
             ==> _module.LLNode.IsWellFormed(_module.List$T, 
              $LS($LS($LZ)), 
              $Heap, 
              read($Heap, read($Heap, this, _module.List.head), _module.LLNode.next))));
  ensures _module.List.IsList#canCall(_module.List$T, $Heap, this)
     ==> _module.List.IsList(_module.List$T, $Heap, this)
       || (_module.LLNode.IsWellFormed#canCall(_module.List$T, $Heap, read($Heap, this, _module.List.head))
         ==> _module.LLNode.IsWellFormed(_module.List$T, $LS($LZ), $Heap, read($Heap, this, _module.List.head))
           || (read($Heap, read($Heap, this, _module.List.head), _module.LLNode.next) != null
             ==> Seq#Equal(read($Heap, read($Heap, this, _module.List.head), _module.LLNode.TailContents), 
              Seq#Append(Seq#Build(Seq#Empty(): Seq Box, 
                  read($Heap, 
                    read($Heap, read($Heap, this, _module.List.head), _module.LLNode.next), 
                    _module.LLNode.data)), 
                read($Heap, 
                  read($Heap, read($Heap, this, _module.List.head), _module.LLNode.next), 
                  _module.LLNode.TailContents)))));
  ensures _module.List.IsList#canCall(_module.List$T, $Heap, this)
     ==> _module.List.IsList(_module.List$T, $Heap, this)
       || Seq#Equal(read($Heap, this, _module.List.Contents), 
        read($Heap, read($Heap, this, _module.List.head), _module.LLNode.TailContents));
  ensures Seq#Equal(read($Heap, this, _module.List.Contents), Seq#Empty(): Seq Box);
  ensures (forall $o: ref :: 
    { read($Heap, this, _module.List.Repr)[$Box($o)] } 
    read($Heap, this, _module.List.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



function Tclass._module.LLNode?(Ty) : Ty;

const unique Tagclass._module.LLNode?: TyTag;

// Tclass._module.LLNode? Tag
axiom (forall _module.LLNode$T: Ty :: 
  { Tclass._module.LLNode?(_module.LLNode$T) } 
  Tag(Tclass._module.LLNode?(_module.LLNode$T)) == Tagclass._module.LLNode?
     && TagFamily(Tclass._module.LLNode?(_module.LLNode$T)) == tytagFamily$LLNode);

// Tclass._module.LLNode? injectivity 0
axiom (forall _module.LLNode$T: Ty :: 
  { Tclass._module.LLNode?(_module.LLNode$T) } 
  Tclass._module.LLNode?_0(Tclass._module.LLNode?(_module.LLNode$T))
     == _module.LLNode$T);

function Tclass._module.LLNode?_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.LLNode?
axiom (forall _module.LLNode$T: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.LLNode?(_module.LLNode$T)) } 
  $IsBox(bx, Tclass._module.LLNode?(_module.LLNode$T))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.LLNode?(_module.LLNode$T)));

implementation Impl$$_module.List.Init(_module.List$T: Ty) returns (this: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var this.Contents: Seq Box;
  var this.Repr: Set Box;
  var this.head: ref;
  var defass#this.head: bool;
  var h#0: ref
     where $Is(h#0, Tclass._module.LLNode(_module.List$T))
       && $IsAlloc(h#0, Tclass._module.LLNode(_module.List$T), $Heap);
  var $nw: ref;
  var $rhs#0: ref where $Is($rhs#0, Tclass._module.LLNode?(_module.List$T));
  var $rhs#1: Seq Box where $Is($rhs#1, TSeq(_module.List$T));
  var $rhs#2: Set Box where $Is($rhs#2, TSet(Tclass._System.object()));

    // AddMethodImpl: Init, Impl$$_module.List.Init
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(124,2): initial state"} true;
    $_reverifyPost := false;
    // ----- divided block before new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(124,3)
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(125,22)
    assume true;
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._module.LLNode?(_module.List$T);
    assume !read($Heap, $nw, alloc);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    h#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(125,37)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(126,12)
    assert h#0 != null;
    assume true;
    assert $_Frame[h#0, _module.LLNode.next];
    assume true;
    $rhs#0 := null;
    $Heap := update($Heap, h#0, _module.LLNode.next, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(126,18)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(127,20)
    assert h#0 != null;
    assume true;
    assert $_Frame[h#0, _module.LLNode.TailContents];
    assume true;
    $rhs#1 := Lit(Seq#Empty(): Seq Box);
    $Heap := update($Heap, h#0, _module.LLNode.TailContents, $rhs#1);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(127,24)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(128,12)
    assert h#0 != null;
    assume true;
    assert $_Frame[h#0, _module.LLNode.Repr];
    assume true;
    assert $Is(Set#UnionOne(Set#Empty(): Set Box, $Box(h#0)), TSet(Tclass._System.object()));
    $rhs#2 := Set#UnionOne(Set#Empty(): Set Box, $Box(h#0));
    $Heap := update($Heap, h#0, _module.LLNode.Repr, $rhs#2);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(128,17)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(130,10)
    assume true;
    assume true;
    this.head := h#0;
    defass#this.head := true;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(130,13)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(131,14)
    assume true;
    assume true;
    this.Contents := Lit(Seq#Empty(): Seq Box);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(131,18)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(132,10)
    assume true;
    assert h#0 != null;
    assume true;
    this.Repr := Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(this)), 
      read($Heap, h#0, _module.LLNode.Repr));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(132,27)"} true;
    // ----- new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(124,3)
    assert defass#this.head;
    assume !read($Heap, this, alloc);
    assume read($Heap, this, _module.List.Contents) == this.Contents;
    assume read($Heap, this, _module.List.Repr) == this.Repr;
    assume read($Heap, this, _module.List.head) == this.head;
    $Heap := update($Heap, this, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    // ----- divided block after new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(124,3)
}



procedure CheckWellformed$$_module.List.Cons(_module.List$T: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.List(_module.List$T))
         && $IsAlloc(this, Tclass._module.List(_module.List$T), $Heap), 
    x#0: Box
       where $IsBox(x#0, _module.List$T) && $IsAllocBox(x#0, _module.List$T, $Heap));
  free requires 12 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.List.Cons(_module.List$T: Ty, this: ref, x#0: Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Cons, CheckWellformed$$_module.List.Cons
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.List.Repr)[$Box($o)]);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(135,9): initial state"} true;
    assume _module.List.IsList#canCall(_module.List$T, $Heap, this);
    assume _module.List.IsList(_module.List$T, $Heap, this);
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc)
         ==> $Heap[$o] == old($Heap)[$o]
           || read(old($Heap), this, _module.List.Repr)[$Box($o)]);
    assume $HeapSucc(old($Heap), $Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(138,56): post-state"} true;
    assume _module.List.IsList#canCall(_module.List$T, $Heap, this);
    assume _module.List.IsList(_module.List$T, $Heap, this);
    assert $IsAlloc(this, Tclass._module.List(_module.List$T), old($Heap));
    assume Seq#Equal(read($Heap, this, _module.List.Contents), 
      Seq#Append(Seq#Build(Seq#Empty(): Seq Box, x#0), 
        read(old($Heap), this, _module.List.Contents)));
    assert $IsAlloc(this, Tclass._module.List(_module.List$T), old($Heap));
    assume (forall $o: ref :: 
      { read(old($Heap), $o, alloc) } 
      read($Heap, this, _module.List.Repr)[$Box($o)]
           && !read(old($Heap), this, _module.List.Repr)[$Box($o)]
         ==> $o != null && !read(old($Heap), $o, alloc));
}



procedure Call$$_module.List.Cons(_module.List$T: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.List(_module.List$T))
         && $IsAlloc(this, Tclass._module.List(_module.List$T), $Heap), 
    x#0: Box
       where $IsBox(x#0, _module.List$T) && $IsAllocBox(x#0, _module.List$T, $Heap));
  // user-defined preconditions
  requires _module.List.IsList#canCall(_module.List$T, $Heap, this)
     ==> _module.List.IsList(_module.List$T, $Heap, this)
       || read($Heap, this, _module.List.Repr)[$Box(this)];
  requires _module.List.IsList#canCall(_module.List$T, $Heap, this)
     ==> _module.List.IsList(_module.List$T, $Heap, this)
       || read($Heap, this, _module.List.Repr)[$Box(read($Heap, this, _module.List.head))];
  requires _module.List.IsList#canCall(_module.List$T, $Heap, this)
     ==> _module.List.IsList(_module.List$T, $Heap, this)
       || Set#Subset(read($Heap, read($Heap, this, _module.List.head), _module.LLNode.Repr), 
        read($Heap, this, _module.List.Repr));
  requires _module.List.IsList#canCall(_module.List$T, $Heap, this)
     ==> _module.List.IsList(_module.List$T, $Heap, this)
       || !read($Heap, read($Heap, this, _module.List.head), _module.LLNode.Repr)[$Box(this)];
  requires _module.List.IsList#canCall(_module.List$T, $Heap, this)
     ==> _module.List.IsList(_module.List$T, $Heap, this)
       || (_module.LLNode.IsWellFormed#canCall(_module.List$T, $Heap, read($Heap, this, _module.List.head))
         ==> _module.LLNode.IsWellFormed(_module.List$T, $LS($LZ), $Heap, read($Heap, this, _module.List.head))
           || read($Heap, read($Heap, this, _module.List.head), _module.LLNode.Repr)[$Box(read($Heap, this, _module.List.head))]);
  requires _module.List.IsList#canCall(_module.List$T, $Heap, this)
     ==> _module.List.IsList(_module.List$T, $Heap, this)
       || (_module.LLNode.IsWellFormed#canCall(_module.List$T, $Heap, read($Heap, this, _module.List.head))
         ==> _module.LLNode.IsWellFormed(_module.List$T, $LS($LZ), $Heap, read($Heap, this, _module.List.head))
           || (read($Heap, read($Heap, this, _module.List.head), _module.LLNode.next) == null
             ==> Seq#Equal(read($Heap, read($Heap, this, _module.List.head), _module.LLNode.TailContents), 
              Seq#Empty(): Seq Box)));
  requires _module.List.IsList#canCall(_module.List$T, $Heap, this)
     ==> _module.List.IsList(_module.List$T, $Heap, this)
       || (_module.LLNode.IsWellFormed#canCall(_module.List$T, $Heap, read($Heap, this, _module.List.head))
         ==> _module.LLNode.IsWellFormed(_module.List$T, $LS($LZ), $Heap, read($Heap, this, _module.List.head))
           || (read($Heap, read($Heap, this, _module.List.head), _module.LLNode.next) != null
             ==> read($Heap, read($Heap, this, _module.List.head), _module.LLNode.Repr)[$Box(read($Heap, read($Heap, this, _module.List.head), _module.LLNode.next))]));
  requires _module.List.IsList#canCall(_module.List$T, $Heap, this)
     ==> _module.List.IsList(_module.List$T, $Heap, this)
       || (_module.LLNode.IsWellFormed#canCall(_module.List$T, $Heap, read($Heap, this, _module.List.head))
         ==> _module.LLNode.IsWellFormed(_module.List$T, $LS($LZ), $Heap, read($Heap, this, _module.List.head))
           || (read($Heap, read($Heap, this, _module.List.head), _module.LLNode.next) != null
             ==> Set#Subset(read($Heap, 
                read($Heap, read($Heap, this, _module.List.head), _module.LLNode.next), 
                _module.LLNode.Repr), 
              read($Heap, read($Heap, this, _module.List.head), _module.LLNode.Repr))));
  requires _module.List.IsList#canCall(_module.List$T, $Heap, this)
     ==> _module.List.IsList(_module.List$T, $Heap, this)
       || (_module.LLNode.IsWellFormed#canCall(_module.List$T, $Heap, read($Heap, this, _module.List.head))
         ==> _module.LLNode.IsWellFormed(_module.List$T, $LS($LZ), $Heap, read($Heap, this, _module.List.head))
           || (read($Heap, read($Heap, this, _module.List.head), _module.LLNode.next) != null
             ==> !read($Heap, 
              read($Heap, read($Heap, this, _module.List.head), _module.LLNode.next), 
              _module.LLNode.Repr)[$Box(read($Heap, this, _module.List.head))]));
  requires _module.List.IsList#canCall(_module.List$T, $Heap, this)
     ==> _module.List.IsList(_module.List$T, $Heap, this)
       || (_module.LLNode.IsWellFormed#canCall(_module.List$T, $Heap, read($Heap, this, _module.List.head))
         ==> _module.LLNode.IsWellFormed(_module.List$T, $LS($LZ), $Heap, read($Heap, this, _module.List.head))
           || (read($Heap, read($Heap, this, _module.List.head), _module.LLNode.next) != null
             ==> _module.LLNode.IsWellFormed(_module.List$T, 
              $LS($LS($LZ)), 
              $Heap, 
              read($Heap, read($Heap, this, _module.List.head), _module.LLNode.next))));
  requires _module.List.IsList#canCall(_module.List$T, $Heap, this)
     ==> _module.List.IsList(_module.List$T, $Heap, this)
       || (_module.LLNode.IsWellFormed#canCall(_module.List$T, $Heap, read($Heap, this, _module.List.head))
         ==> _module.LLNode.IsWellFormed(_module.List$T, $LS($LZ), $Heap, read($Heap, this, _module.List.head))
           || (read($Heap, read($Heap, this, _module.List.head), _module.LLNode.next) != null
             ==> Seq#Equal(read($Heap, read($Heap, this, _module.List.head), _module.LLNode.TailContents), 
              Seq#Append(Seq#Build(Seq#Empty(): Seq Box, 
                  read($Heap, 
                    read($Heap, read($Heap, this, _module.List.head), _module.LLNode.next), 
                    _module.LLNode.data)), 
                read($Heap, 
                  read($Heap, read($Heap, this, _module.List.head), _module.LLNode.next), 
                  _module.LLNode.TailContents)))));
  requires _module.List.IsList#canCall(_module.List$T, $Heap, this)
     ==> _module.List.IsList(_module.List$T, $Heap, this)
       || Seq#Equal(read($Heap, this, _module.List.Contents), 
        read($Heap, read($Heap, this, _module.List.head), _module.LLNode.TailContents));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.List.IsList#canCall(_module.List$T, $Heap, this);
  free ensures _module.List.IsList#canCall(_module.List$T, $Heap, this)
     && 
    _module.List.IsList(_module.List$T, $Heap, this)
     && 
    read($Heap, this, _module.List.Repr)[$Box(this)]
     && read($Heap, this, _module.List.Repr)[$Box(read($Heap, this, _module.List.head))]
     && Set#Subset(read($Heap, read($Heap, this, _module.List.head), _module.LLNode.Repr), 
      read($Heap, this, _module.List.Repr))
     && !read($Heap, read($Heap, this, _module.List.head), _module.LLNode.Repr)[$Box(this)]
     && _module.LLNode.IsWellFormed(_module.List$T, $LS($LZ), $Heap, read($Heap, this, _module.List.head))
     && Seq#Equal(read($Heap, this, _module.List.Contents), 
      read($Heap, read($Heap, this, _module.List.head), _module.LLNode.TailContents));
  ensures Seq#Equal(read($Heap, this, _module.List.Contents), 
    Seq#Append(Seq#Build(Seq#Empty(): Seq Box, x#0), 
      read(old($Heap), this, _module.List.Contents)));
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    read($Heap, this, _module.List.Repr)[$Box($o)]
         && !read(old($Heap), this, _module.List.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || read(old($Heap), this, _module.List.Repr)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.List.Cons(_module.List$T: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.List(_module.List$T))
         && $IsAlloc(this, Tclass._module.List(_module.List$T), $Heap), 
    x#0: Box
       where $IsBox(x#0, _module.List$T) && $IsAllocBox(x#0, _module.List$T, $Heap))
   returns ($_reverifyPost: bool);
  free requires 12 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.List.IsList#canCall(_module.List$T, $Heap, this)
     && 
    _module.List.IsList(_module.List$T, $Heap, this)
     && 
    read($Heap, this, _module.List.Repr)[$Box(this)]
     && read($Heap, this, _module.List.Repr)[$Box(read($Heap, this, _module.List.head))]
     && Set#Subset(read($Heap, read($Heap, this, _module.List.head), _module.LLNode.Repr), 
      read($Heap, this, _module.List.Repr))
     && !read($Heap, read($Heap, this, _module.List.head), _module.LLNode.Repr)[$Box(this)]
     && _module.LLNode.IsWellFormed(_module.List$T, $LS($LZ), $Heap, read($Heap, this, _module.List.head))
     && Seq#Equal(read($Heap, this, _module.List.Contents), 
      read($Heap, read($Heap, this, _module.List.head), _module.LLNode.TailContents));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.List.IsList#canCall(_module.List$T, $Heap, this);
  ensures _module.List.IsList#canCall(_module.List$T, $Heap, this)
     ==> _module.List.IsList(_module.List$T, $Heap, this)
       || read($Heap, this, _module.List.Repr)[$Box(this)];
  ensures _module.List.IsList#canCall(_module.List$T, $Heap, this)
     ==> _module.List.IsList(_module.List$T, $Heap, this)
       || read($Heap, this, _module.List.Repr)[$Box(read($Heap, this, _module.List.head))];
  ensures _module.List.IsList#canCall(_module.List$T, $Heap, this)
     ==> _module.List.IsList(_module.List$T, $Heap, this)
       || Set#Subset(read($Heap, read($Heap, this, _module.List.head), _module.LLNode.Repr), 
        read($Heap, this, _module.List.Repr));
  ensures _module.List.IsList#canCall(_module.List$T, $Heap, this)
     ==> _module.List.IsList(_module.List$T, $Heap, this)
       || !read($Heap, read($Heap, this, _module.List.head), _module.LLNode.Repr)[$Box(this)];
  ensures _module.List.IsList#canCall(_module.List$T, $Heap, this)
     ==> _module.List.IsList(_module.List$T, $Heap, this)
       || (_module.LLNode.IsWellFormed#canCall(_module.List$T, $Heap, read($Heap, this, _module.List.head))
         ==> _module.LLNode.IsWellFormed(_module.List$T, $LS($LZ), $Heap, read($Heap, this, _module.List.head))
           || read($Heap, read($Heap, this, _module.List.head), _module.LLNode.Repr)[$Box(read($Heap, this, _module.List.head))]);
  ensures _module.List.IsList#canCall(_module.List$T, $Heap, this)
     ==> _module.List.IsList(_module.List$T, $Heap, this)
       || (_module.LLNode.IsWellFormed#canCall(_module.List$T, $Heap, read($Heap, this, _module.List.head))
         ==> _module.LLNode.IsWellFormed(_module.List$T, $LS($LZ), $Heap, read($Heap, this, _module.List.head))
           || (read($Heap, read($Heap, this, _module.List.head), _module.LLNode.next) == null
             ==> Seq#Equal(read($Heap, read($Heap, this, _module.List.head), _module.LLNode.TailContents), 
              Seq#Empty(): Seq Box)));
  ensures _module.List.IsList#canCall(_module.List$T, $Heap, this)
     ==> _module.List.IsList(_module.List$T, $Heap, this)
       || (_module.LLNode.IsWellFormed#canCall(_module.List$T, $Heap, read($Heap, this, _module.List.head))
         ==> _module.LLNode.IsWellFormed(_module.List$T, $LS($LZ), $Heap, read($Heap, this, _module.List.head))
           || (read($Heap, read($Heap, this, _module.List.head), _module.LLNode.next) != null
             ==> read($Heap, read($Heap, this, _module.List.head), _module.LLNode.Repr)[$Box(read($Heap, read($Heap, this, _module.List.head), _module.LLNode.next))]));
  ensures _module.List.IsList#canCall(_module.List$T, $Heap, this)
     ==> _module.List.IsList(_module.List$T, $Heap, this)
       || (_module.LLNode.IsWellFormed#canCall(_module.List$T, $Heap, read($Heap, this, _module.List.head))
         ==> _module.LLNode.IsWellFormed(_module.List$T, $LS($LZ), $Heap, read($Heap, this, _module.List.head))
           || (read($Heap, read($Heap, this, _module.List.head), _module.LLNode.next) != null
             ==> Set#Subset(read($Heap, 
                read($Heap, read($Heap, this, _module.List.head), _module.LLNode.next), 
                _module.LLNode.Repr), 
              read($Heap, read($Heap, this, _module.List.head), _module.LLNode.Repr))));
  ensures _module.List.IsList#canCall(_module.List$T, $Heap, this)
     ==> _module.List.IsList(_module.List$T, $Heap, this)
       || (_module.LLNode.IsWellFormed#canCall(_module.List$T, $Heap, read($Heap, this, _module.List.head))
         ==> _module.LLNode.IsWellFormed(_module.List$T, $LS($LZ), $Heap, read($Heap, this, _module.List.head))
           || (read($Heap, read($Heap, this, _module.List.head), _module.LLNode.next) != null
             ==> !read($Heap, 
              read($Heap, read($Heap, this, _module.List.head), _module.LLNode.next), 
              _module.LLNode.Repr)[$Box(read($Heap, this, _module.List.head))]));
  ensures _module.List.IsList#canCall(_module.List$T, $Heap, this)
     ==> _module.List.IsList(_module.List$T, $Heap, this)
       || (_module.LLNode.IsWellFormed#canCall(_module.List$T, $Heap, read($Heap, this, _module.List.head))
         ==> _module.LLNode.IsWellFormed(_module.List$T, $LS($LZ), $Heap, read($Heap, this, _module.List.head))
           || (read($Heap, read($Heap, this, _module.List.head), _module.LLNode.next) != null
             ==> _module.LLNode.IsWellFormed(_module.List$T, 
              $LS($LS($LZ)), 
              $Heap, 
              read($Heap, read($Heap, this, _module.List.head), _module.LLNode.next))));
  ensures _module.List.IsList#canCall(_module.List$T, $Heap, this)
     ==> _module.List.IsList(_module.List$T, $Heap, this)
       || (_module.LLNode.IsWellFormed#canCall(_module.List$T, $Heap, read($Heap, this, _module.List.head))
         ==> _module.LLNode.IsWellFormed(_module.List$T, $LS($LZ), $Heap, read($Heap, this, _module.List.head))
           || (read($Heap, read($Heap, this, _module.List.head), _module.LLNode.next) != null
             ==> Seq#Equal(read($Heap, read($Heap, this, _module.List.head), _module.LLNode.TailContents), 
              Seq#Append(Seq#Build(Seq#Empty(): Seq Box, 
                  read($Heap, 
                    read($Heap, read($Heap, this, _module.List.head), _module.LLNode.next), 
                    _module.LLNode.data)), 
                read($Heap, 
                  read($Heap, read($Heap, this, _module.List.head), _module.LLNode.next), 
                  _module.LLNode.TailContents)))));
  ensures _module.List.IsList#canCall(_module.List$T, $Heap, this)
     ==> _module.List.IsList(_module.List$T, $Heap, this)
       || Seq#Equal(read($Heap, this, _module.List.Contents), 
        read($Heap, read($Heap, this, _module.List.head), _module.LLNode.TailContents));
  ensures Seq#Equal(read($Heap, this, _module.List.Contents), 
    Seq#Append(Seq#Build(Seq#Empty(): Seq Box, x#0), 
      read(old($Heap), this, _module.List.Contents)));
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    read($Heap, this, _module.List.Repr)[$Box($o)]
         && !read(old($Heap), this, _module.List.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || read(old($Heap), this, _module.List.Repr)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.List.Cons(_module.List$T: Ty, this: ref, x#0: Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: Box where $IsBox($rhs#0, _module.List$T);
  var h#0: ref
     where $Is(h#0, Tclass._module.LLNode(_module.List$T))
       && $IsAlloc(h#0, Tclass._module.LLNode(_module.List$T), $Heap);
  var $nw: ref;
  var $rhs#1: ref where $Is($rhs#1, Tclass._module.LLNode?(_module.List$T));
  var $rhs#2: Seq Box where $Is($rhs#2, TSeq(_module.List$T));
  var $rhs#3: Set Box where $Is($rhs#3, TSet(Tclass._System.object()));
  var $rhs#4: ref where $Is($rhs#4, Tclass._module.LLNode(_module.List$T));
  var $rhs#5: Seq Box where $Is($rhs#5, TSeq(_module.List$T));
  var $rhs#6: Set Box where $Is($rhs#6, TSet(Tclass._System.object()));

    // AddMethodImpl: Cons, Impl$$_module.List.Cons
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.List.Repr)[$Box($o)]);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(139,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(140,15)
    assert read($Heap, this, _module.List.head) != null;
    assume true;
    assert $_Frame[read($Heap, this, _module.List.head), _module.LLNode.data];
    assume true;
    $rhs#0 := x#0;
    $Heap := update($Heap, read($Heap, this, _module.List.head), _module.LLNode.data, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(140,18)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(141,5)
    assert {:subsumption 0} read($Heap, this, _module.List.head) != null;
    assume _module.LLNode.IsWellFormed#canCall(_module.List$T, $Heap, read($Heap, this, _module.List.head));
    assume _module.LLNode.IsWellFormed#canCall(_module.List$T, $Heap, read($Heap, this, _module.List.head));
    assert {:subsumption 0} _module.LLNode.IsWellFormed#canCall(_module.List$T, $Heap, read($Heap, this, _module.List.head))
       ==> _module.LLNode.IsWellFormed(_module.List$T, $LS($LZ), $Heap, read($Heap, this, _module.List.head))
         || read($Heap, read($Heap, this, _module.List.head), _module.LLNode.Repr)[$Box(read($Heap, this, _module.List.head))];
    assert {:subsumption 0} _module.LLNode.IsWellFormed#canCall(_module.List$T, $Heap, read($Heap, this, _module.List.head))
       ==> _module.LLNode.IsWellFormed(_module.List$T, $LS($LZ), $Heap, read($Heap, this, _module.List.head))
         || (read($Heap, read($Heap, this, _module.List.head), _module.LLNode.next) == null
           ==> Seq#Equal(read($Heap, read($Heap, this, _module.List.head), _module.LLNode.TailContents), 
            Seq#Empty(): Seq Box));
    assert {:subsumption 0} _module.LLNode.IsWellFormed#canCall(_module.List$T, $Heap, read($Heap, this, _module.List.head))
       ==> _module.LLNode.IsWellFormed(_module.List$T, $LS($LZ), $Heap, read($Heap, this, _module.List.head))
         || (read($Heap, read($Heap, this, _module.List.head), _module.LLNode.next) != null
           ==> read($Heap, read($Heap, this, _module.List.head), _module.LLNode.Repr)[$Box(read($Heap, read($Heap, this, _module.List.head), _module.LLNode.next))]);
    assert {:subsumption 0} _module.LLNode.IsWellFormed#canCall(_module.List$T, $Heap, read($Heap, this, _module.List.head))
       ==> _module.LLNode.IsWellFormed(_module.List$T, $LS($LZ), $Heap, read($Heap, this, _module.List.head))
         || (read($Heap, read($Heap, this, _module.List.head), _module.LLNode.next) != null
           ==> Set#Subset(read($Heap, 
              read($Heap, read($Heap, this, _module.List.head), _module.LLNode.next), 
              _module.LLNode.Repr), 
            read($Heap, read($Heap, this, _module.List.head), _module.LLNode.Repr)));
    assert {:subsumption 0} _module.LLNode.IsWellFormed#canCall(_module.List$T, $Heap, read($Heap, this, _module.List.head))
       ==> _module.LLNode.IsWellFormed(_module.List$T, $LS($LZ), $Heap, read($Heap, this, _module.List.head))
         || (read($Heap, read($Heap, this, _module.List.head), _module.LLNode.next) != null
           ==> !read($Heap, 
            read($Heap, read($Heap, this, _module.List.head), _module.LLNode.next), 
            _module.LLNode.Repr)[$Box(read($Heap, this, _module.List.head))]);
    assert {:subsumption 0} _module.LLNode.IsWellFormed#canCall(_module.List$T, $Heap, read($Heap, this, _module.List.head))
       ==> _module.LLNode.IsWellFormed(_module.List$T, $LS($LZ), $Heap, read($Heap, this, _module.List.head))
         || (read($Heap, read($Heap, this, _module.List.head), _module.LLNode.next) != null
           ==> _module.LLNode.IsWellFormed(_module.List$T, 
            $LS($LS($LZ)), 
            $Heap, 
            read($Heap, read($Heap, this, _module.List.head), _module.LLNode.next)));
    assert {:subsumption 0} _module.LLNode.IsWellFormed#canCall(_module.List$T, $Heap, read($Heap, this, _module.List.head))
       ==> _module.LLNode.IsWellFormed(_module.List$T, $LS($LZ), $Heap, read($Heap, this, _module.List.head))
         || (read($Heap, read($Heap, this, _module.List.head), _module.LLNode.next) != null
           ==> Seq#Equal(read($Heap, read($Heap, this, _module.List.head), _module.LLNode.TailContents), 
            Seq#Append(Seq#Build(Seq#Empty(): Seq Box, 
                read($Heap, 
                  read($Heap, read($Heap, this, _module.List.head), _module.LLNode.next), 
                  _module.LLNode.data)), 
              read($Heap, 
                read($Heap, read($Heap, this, _module.List.head), _module.LLNode.next), 
                _module.LLNode.TailContents))));
    assume _module.LLNode.IsWellFormed(_module.List$T, $LS($LZ), $Heap, read($Heap, this, _module.List.head));
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(143,22)
    assume true;
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._module.LLNode?(_module.List$T);
    assume !read($Heap, $nw, alloc);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    h#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(143,37)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(144,12)
    assert h#0 != null;
    assume true;
    assert $_Frame[h#0, _module.LLNode.next];
    assume true;
    $rhs#1 := read($Heap, this, _module.List.head);
    $Heap := update($Heap, h#0, _module.LLNode.next, $rhs#1);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(144,18)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(145,20)
    assert h#0 != null;
    assume true;
    assert $_Frame[h#0, _module.LLNode.TailContents];
    assert read($Heap, this, _module.List.head) != null;
    assume true;
    $rhs#2 := Seq#Append(Seq#Build(Seq#Empty(): Seq Box, x#0), 
      read($Heap, read($Heap, this, _module.List.head), _module.LLNode.TailContents));
    $Heap := update($Heap, h#0, _module.LLNode.TailContents, $rhs#2);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(145,45)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(146,12)
    assert h#0 != null;
    assume true;
    assert $_Frame[h#0, _module.LLNode.Repr];
    assert read($Heap, this, _module.List.head) != null;
    assume true;
    $rhs#3 := Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(h#0)), 
      read($Heap, read($Heap, this, _module.List.head), _module.LLNode.Repr));
    $Heap := update($Heap, h#0, _module.LLNode.Repr, $rhs#3);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(146,29)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(148,10)
    assume true;
    assert $_Frame[this, _module.List.head];
    assume true;
    $rhs#4 := h#0;
    $Heap := update($Heap, this, _module.List.head, $rhs#4);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(148,13)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(149,14)
    assume true;
    assert $_Frame[this, _module.List.Contents];
    assume true;
    $rhs#5 := Seq#Append(Seq#Build(Seq#Empty(): Seq Box, x#0), read($Heap, this, _module.List.Contents));
    $Heap := update($Heap, this, _module.List.Contents, $rhs#5);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(149,30)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(150,10)
    assume true;
    assert $_Frame[this, _module.List.Repr];
    assume true;
    $rhs#6 := Set#Union(read($Heap, this, _module.List.Repr), 
      Set#UnionOne(Set#Empty(): Set Box, $Box(h#0)));
    $Heap := update($Heap, this, _module.List.Repr, $rhs#6);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(150,22)"} true;
}



// _module.List: subset type $Is
axiom (forall _module.List$T: Ty, c#0: ref :: 
  { $Is(c#0, Tclass._module.List(_module.List$T)) } 
  $Is(c#0, Tclass._module.List(_module.List$T))
     <==> $Is(c#0, Tclass._module.List?(_module.List$T)) && c#0 != null);

// _module.List: subset type $IsAlloc
axiom (forall _module.List$T: Ty, c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.List(_module.List$T), $h) } 
  $IsAlloc(c#0, Tclass._module.List(_module.List$T), $h)
     <==> $IsAlloc(c#0, Tclass._module.List?(_module.List$T), $h));

const unique class._module.LLNode?: ClassName;

// LLNode: Class $Is
axiom (forall _module.LLNode$T: Ty, $o: ref :: 
  { $Is($o, Tclass._module.LLNode?(_module.LLNode$T)) } 
  $Is($o, Tclass._module.LLNode?(_module.LLNode$T))
     <==> $o == null || dtype($o) == Tclass._module.LLNode?(_module.LLNode$T));

// LLNode: Class $IsAlloc
axiom (forall _module.LLNode$T: Ty, $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.LLNode?(_module.LLNode$T), $h) } 
  $IsAlloc($o, Tclass._module.LLNode?(_module.LLNode$T), $h)
     <==> $o == null || read($h, $o, alloc));

const _module.LLNode.data: Field Box;

// LLNode.data: Type axiom
axiom (forall _module.LLNode$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.LLNode.data), Tclass._module.LLNode?(_module.LLNode$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.LLNode?(_module.LLNode$T)
     ==> $IsBox(read($h, $o, _module.LLNode.data), _module.LLNode$T));

// LLNode.data: Allocation axiom
axiom (forall _module.LLNode$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.LLNode.data), Tclass._module.LLNode?(_module.LLNode$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.LLNode?(_module.LLNode$T)
       && read($h, $o, alloc)
     ==> $IsAllocBox(read($h, $o, _module.LLNode.data), _module.LLNode$T, $h));

const _module.LLNode.next: Field ref;

// LLNode.next: Type axiom
axiom (forall _module.LLNode$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.LLNode.next), Tclass._module.LLNode?(_module.LLNode$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.LLNode?(_module.LLNode$T)
     ==> $Is(read($h, $o, _module.LLNode.next), Tclass._module.LLNode?(_module.LLNode$T)));

// LLNode.next: Allocation axiom
axiom (forall _module.LLNode$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.LLNode.next), Tclass._module.LLNode?(_module.LLNode$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.LLNode?(_module.LLNode$T)
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.LLNode.next), Tclass._module.LLNode?(_module.LLNode$T), $h));

const _module.LLNode.TailContents: Field (Seq Box);

// LLNode.TailContents: Type axiom
axiom (forall _module.LLNode$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.LLNode.TailContents), Tclass._module.LLNode?(_module.LLNode$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.LLNode?(_module.LLNode$T)
     ==> $Is(read($h, $o, _module.LLNode.TailContents), TSeq(_module.LLNode$T)));

// LLNode.TailContents: Allocation axiom
axiom (forall _module.LLNode$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.LLNode.TailContents), Tclass._module.LLNode?(_module.LLNode$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.LLNode?(_module.LLNode$T)
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.LLNode.TailContents), TSeq(_module.LLNode$T), $h));

const _module.LLNode.Repr: Field (Set Box);

// LLNode.Repr: Type axiom
axiom (forall _module.LLNode$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.LLNode.Repr), Tclass._module.LLNode?(_module.LLNode$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.LLNode?(_module.LLNode$T)
     ==> $Is(read($h, $o, _module.LLNode.Repr), TSet(Tclass._System.object())));

// LLNode.Repr: Allocation axiom
axiom (forall _module.LLNode$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.LLNode.Repr), Tclass._module.LLNode?(_module.LLNode$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.LLNode?(_module.LLNode$T)
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.LLNode.Repr), TSet(Tclass._System.object()), $h));

// function declaration for _module.LLNode.IsWellFormed
function _module.LLNode.IsWellFormed(_module.LLNode$T: Ty, $ly: LayerType, $heap: Heap, this: ref) : bool;

function _module.LLNode.IsWellFormed#canCall(_module.LLNode$T: Ty, $heap: Heap, this: ref) : bool;

// layer synonym axiom
axiom (forall _module.LLNode$T: Ty, $ly: LayerType, $Heap: Heap, this: ref :: 
  { _module.LLNode.IsWellFormed(_module.LLNode$T, $LS($ly), $Heap, this) } 
  _module.LLNode.IsWellFormed(_module.LLNode$T, $LS($ly), $Heap, this)
     == _module.LLNode.IsWellFormed(_module.LLNode$T, $ly, $Heap, this));

// fuel synonym axiom
axiom (forall _module.LLNode$T: Ty, $ly: LayerType, $Heap: Heap, this: ref :: 
  { _module.LLNode.IsWellFormed(_module.LLNode$T, AsFuelBottom($ly), $Heap, this) } 
  _module.LLNode.IsWellFormed(_module.LLNode$T, $ly, $Heap, this)
     == _module.LLNode.IsWellFormed(_module.LLNode$T, $LZ, $Heap, this));

// frame axiom for _module.LLNode.IsWellFormed
axiom (forall _module.LLNode$T: Ty, $ly: LayerType, $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.LLNode.IsWellFormed(_module.LLNode$T, $ly, $h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.LLNode(_module.LLNode$T))
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && ($o == this || read($h0, this, _module.LLNode.Repr)[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.LLNode.IsWellFormed(_module.LLNode$T, $ly, $h0, this)
       == _module.LLNode.IsWellFormed(_module.LLNode$T, $ly, $h1, this));

// consequence axiom for _module.LLNode.IsWellFormed
axiom 8 <= $FunctionContextHeight
   ==> (forall _module.LLNode$T: Ty, $ly: LayerType, $Heap: Heap, this: ref :: 
    { _module.LLNode.IsWellFormed(_module.LLNode$T, $ly, $Heap, this) } 
    _module.LLNode.IsWellFormed#canCall(_module.LLNode$T, $Heap, this)
         || (8 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.LLNode(_module.LLNode$T))
           && $IsAlloc(this, Tclass._module.LLNode(_module.LLNode$T), $Heap))
       ==> true);

function _module.LLNode.IsWellFormed#requires(Ty, LayerType, Heap, ref) : bool;

// #requires axiom for _module.LLNode.IsWellFormed
axiom (forall _module.LLNode$T: Ty, $ly: LayerType, $Heap: Heap, this: ref :: 
  { _module.LLNode.IsWellFormed#requires(_module.LLNode$T, $ly, $Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.LLNode(_module.LLNode$T))
       && $IsAlloc(this, Tclass._module.LLNode(_module.LLNode$T), $Heap)
     ==> _module.LLNode.IsWellFormed#requires(_module.LLNode$T, $ly, $Heap, this) == true);

// definition axiom for _module.LLNode.IsWellFormed (revealed)
axiom 8 <= $FunctionContextHeight
   ==> (forall _module.LLNode$T: Ty, $ly: LayerType, $Heap: Heap, this: ref :: 
    { _module.LLNode.IsWellFormed(_module.LLNode$T, $LS($ly), $Heap, this), $IsGoodHeap($Heap) } 
    _module.LLNode.IsWellFormed#canCall(_module.LLNode$T, $Heap, this)
         || (8 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.LLNode(_module.LLNode$T))
           && $IsAlloc(this, Tclass._module.LLNode(_module.LLNode$T), $Heap))
       ==> (read($Heap, this, _module.LLNode.Repr)[$Box(this)]
           ==> 
          (read($Heap, this, _module.LLNode.next) == null
           ==> Seq#Equal(read($Heap, this, _module.LLNode.TailContents), Seq#Empty(): Seq Box))
           ==> 
          read($Heap, this, _module.LLNode.next) != null
           ==> 
          read($Heap, this, _module.LLNode.Repr)[$Box(read($Heap, this, _module.LLNode.next))]
           ==> 
          Set#Subset(read($Heap, read($Heap, this, _module.LLNode.next), _module.LLNode.Repr), 
            read($Heap, this, _module.LLNode.Repr))
           ==> 
          !read($Heap, read($Heap, this, _module.LLNode.next), _module.LLNode.Repr)[$Box(this)]
           ==> _module.LLNode.IsWellFormed#canCall(_module.LLNode$T, $Heap, read($Heap, this, _module.LLNode.next)))
         && _module.LLNode.IsWellFormed(_module.LLNode$T, $LS($ly), $Heap, this)
           == (
            read($Heap, this, _module.LLNode.Repr)[$Box(this)]
             && (read($Heap, this, _module.LLNode.next) == null
               ==> Seq#Equal(read($Heap, this, _module.LLNode.TailContents), Seq#Empty(): Seq Box))
             && (read($Heap, this, _module.LLNode.next) != null
               ==> read($Heap, this, _module.LLNode.Repr)[$Box(read($Heap, this, _module.LLNode.next))]
                 && Set#Subset(read($Heap, read($Heap, this, _module.LLNode.next), _module.LLNode.Repr), 
                  read($Heap, this, _module.LLNode.Repr))
                 && !read($Heap, read($Heap, this, _module.LLNode.next), _module.LLNode.Repr)[$Box(this)]
                 && _module.LLNode.IsWellFormed(_module.LLNode$T, $ly, $Heap, read($Heap, this, _module.LLNode.next))
                 && Seq#Equal(read($Heap, this, _module.LLNode.TailContents), 
                  Seq#Append(Seq#Build(Seq#Empty(): Seq Box, 
                      read($Heap, read($Heap, this, _module.LLNode.next), _module.LLNode.data)), 
                    read($Heap, read($Heap, this, _module.LLNode.next), _module.LLNode.TailContents))))));

procedure CheckWellformed$$_module.LLNode.IsWellFormed(_module.LLNode$T: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.LLNode(_module.LLNode$T))
         && $IsAlloc(this, Tclass._module.LLNode(_module.LLNode$T), $Heap));
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.LLNode.IsWellFormed(_module.LLNode$T: Ty, this: ref)
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
  var b$reqreads#12: bool;
  var b$reqreads#13: bool;
  var b$reqreads#14: bool;
  var b$reqreads#15: bool;
  var b$reqreads#16: bool;
  var b$reqreads#17: bool;
  var b$reqreads#18: bool;

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
    b$reqreads#12 := true;
    b$reqreads#13 := true;
    b$reqreads#14 := true;
    b$reqreads#15 := true;
    b$reqreads#16 := true;
    b$reqreads#17 := true;
    b$reqreads#18 := true;

    // AddWellformednessCheck for function IsWellFormed
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SeparationLogicList.dfy(161,12): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> $o == this || read($Heap, this, _module.LLNode.Repr)[$Box($o)]);
    b$reqreads#0 := $_Frame[this, _module.LLNode.Repr];
    assert b$reqreads#0;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc)
             ==> $o == this || read($Heap, this, _module.LLNode.Repr)[$Box($o)]);
        b$reqreads#1 := $_Frame[this, _module.LLNode.Repr];
        if (read($Heap, this, _module.LLNode.Repr)[$Box(this)])
        {
            b$reqreads#2 := $_Frame[this, _module.LLNode.next];
            if (read($Heap, this, _module.LLNode.next) == null)
            {
                b$reqreads#3 := $_Frame[this, _module.LLNode.TailContents];
            }
        }

        if (read($Heap, this, _module.LLNode.Repr)[$Box(this)]
           && (read($Heap, this, _module.LLNode.next) == null
             ==> Seq#Equal(read($Heap, this, _module.LLNode.TailContents), Seq#Empty(): Seq Box)))
        {
            b$reqreads#4 := $_Frame[this, _module.LLNode.next];
            if (read($Heap, this, _module.LLNode.next) != null)
            {
                b$reqreads#5 := $_Frame[this, _module.LLNode.next];
                b$reqreads#6 := $_Frame[this, _module.LLNode.Repr];
                if (read($Heap, this, _module.LLNode.Repr)[$Box(read($Heap, this, _module.LLNode.next))])
                {
                    b$reqreads#7 := $_Frame[this, _module.LLNode.next];
                    assert read($Heap, this, _module.LLNode.next) != null;
                    b$reqreads#8 := $_Frame[read($Heap, this, _module.LLNode.next), _module.LLNode.Repr];
                    b$reqreads#9 := $_Frame[this, _module.LLNode.Repr];
                }

                if (read($Heap, this, _module.LLNode.Repr)[$Box(read($Heap, this, _module.LLNode.next))]
                   && Set#Subset(read($Heap, read($Heap, this, _module.LLNode.next), _module.LLNode.Repr), 
                    read($Heap, this, _module.LLNode.Repr)))
                {
                    b$reqreads#10 := $_Frame[this, _module.LLNode.next];
                    assert read($Heap, this, _module.LLNode.next) != null;
                    b$reqreads#11 := $_Frame[read($Heap, this, _module.LLNode.next), _module.LLNode.Repr];
                }

                if (read($Heap, this, _module.LLNode.Repr)[$Box(read($Heap, this, _module.LLNode.next))]
                   && Set#Subset(read($Heap, read($Heap, this, _module.LLNode.next), _module.LLNode.Repr), 
                    read($Heap, this, _module.LLNode.Repr))
                   && !read($Heap, read($Heap, this, _module.LLNode.next), _module.LLNode.Repr)[$Box(this)])
                {
                    b$reqreads#12 := $_Frame[this, _module.LLNode.next];
                    assert read($Heap, this, _module.LLNode.next) != null;
                    b$reqreads#13 := (forall<alpha> $o: ref, $f: Field alpha :: 
                      $o != null
                           && read($Heap, $o, alloc)
                           && ($o == read($Heap, this, _module.LLNode.next)
                             || read($Heap, read($Heap, this, _module.LLNode.next), _module.LLNode.Repr)[$Box($o)])
                         ==> $_Frame[$o, $f]);
                    assert Set#Subset(Set#Union(read($Heap, read($Heap, this, _module.LLNode.next), _module.LLNode.Repr), 
                          Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.LLNode.next)))), 
                        Set#Union(read($Heap, this, _module.LLNode.Repr), 
                          Set#UnionOne(Set#Empty(): Set Box, $Box(this))))
                       && !Set#Subset(Set#Union(read($Heap, this, _module.LLNode.Repr), 
                          Set#UnionOne(Set#Empty(): Set Box, $Box(this))), 
                        Set#Union(read($Heap, read($Heap, this, _module.LLNode.next), _module.LLNode.Repr), 
                          Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.LLNode.next)))));
                    assume _module.LLNode.IsWellFormed#canCall(_module.LLNode$T, $Heap, read($Heap, this, _module.LLNode.next));
                }

                if (read($Heap, this, _module.LLNode.Repr)[$Box(read($Heap, this, _module.LLNode.next))]
                   && Set#Subset(read($Heap, read($Heap, this, _module.LLNode.next), _module.LLNode.Repr), 
                    read($Heap, this, _module.LLNode.Repr))
                   && !read($Heap, read($Heap, this, _module.LLNode.next), _module.LLNode.Repr)[$Box(this)]
                   && _module.LLNode.IsWellFormed(_module.LLNode$T, $LS($LZ), $Heap, read($Heap, this, _module.LLNode.next)))
                {
                    b$reqreads#14 := $_Frame[this, _module.LLNode.TailContents];
                    b$reqreads#15 := $_Frame[this, _module.LLNode.next];
                    assert read($Heap, this, _module.LLNode.next) != null;
                    b$reqreads#16 := $_Frame[read($Heap, this, _module.LLNode.next), _module.LLNode.data];
                    b$reqreads#17 := $_Frame[this, _module.LLNode.next];
                    assert read($Heap, this, _module.LLNode.next) != null;
                    b$reqreads#18 := $_Frame[read($Heap, this, _module.LLNode.next), _module.LLNode.TailContents];
                }
            }
        }

        assume _module.LLNode.IsWellFormed(_module.LLNode$T, $LS($LZ), $Heap, this)
           == (
            read($Heap, this, _module.LLNode.Repr)[$Box(this)]
             && (read($Heap, this, _module.LLNode.next) == null
               ==> Seq#Equal(read($Heap, this, _module.LLNode.TailContents), Seq#Empty(): Seq Box))
             && (read($Heap, this, _module.LLNode.next) != null
               ==> read($Heap, this, _module.LLNode.Repr)[$Box(read($Heap, this, _module.LLNode.next))]
                 && Set#Subset(read($Heap, read($Heap, this, _module.LLNode.next), _module.LLNode.Repr), 
                  read($Heap, this, _module.LLNode.Repr))
                 && !read($Heap, read($Heap, this, _module.LLNode.next), _module.LLNode.Repr)[$Box(this)]
                 && _module.LLNode.IsWellFormed(_module.LLNode$T, $LS($LZ), $Heap, read($Heap, this, _module.LLNode.next))
                 && Seq#Equal(read($Heap, this, _module.LLNode.TailContents), 
                  Seq#Append(Seq#Build(Seq#Empty(): Seq Box, 
                      read($Heap, read($Heap, this, _module.LLNode.next), _module.LLNode.data)), 
                    read($Heap, read($Heap, this, _module.LLNode.next), _module.LLNode.TailContents)))));
        assume read($Heap, this, _module.LLNode.Repr)[$Box(this)]
           ==> 
          (read($Heap, this, _module.LLNode.next) == null
           ==> Seq#Equal(read($Heap, this, _module.LLNode.TailContents), Seq#Empty(): Seq Box))
           ==> 
          read($Heap, this, _module.LLNode.next) != null
           ==> 
          read($Heap, this, _module.LLNode.Repr)[$Box(read($Heap, this, _module.LLNode.next))]
           ==> 
          Set#Subset(read($Heap, read($Heap, this, _module.LLNode.next), _module.LLNode.Repr), 
            read($Heap, this, _module.LLNode.Repr))
           ==> 
          !read($Heap, read($Heap, this, _module.LLNode.next), _module.LLNode.Repr)[$Box(this)]
           ==> _module.LLNode.IsWellFormed#canCall(_module.LLNode$T, $Heap, read($Heap, this, _module.LLNode.next));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.LLNode.IsWellFormed(_module.LLNode$T, $LS($LZ), $Heap, this), TBool);
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
        assert b$reqreads#12;
        assert b$reqreads#13;
        assert b$reqreads#14;
        assert b$reqreads#15;
        assert b$reqreads#16;
        assert b$reqreads#17;
        assert b$reqreads#18;
    }
}



// _module.LLNode: subset type $Is
axiom (forall _module.LLNode$T: Ty, c#0: ref :: 
  { $Is(c#0, Tclass._module.LLNode(_module.LLNode$T)) } 
  $Is(c#0, Tclass._module.LLNode(_module.LLNode$T))
     <==> $Is(c#0, Tclass._module.LLNode?(_module.LLNode$T)) && c#0 != null);

// _module.LLNode: subset type $IsAlloc
axiom (forall _module.LLNode$T: Ty, c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.LLNode(_module.LLNode$T), $h) } 
  $IsAlloc(c#0, Tclass._module.LLNode(_module.LLNode$T), $h)
     <==> $IsAlloc(c#0, Tclass._module.LLNode?(_module.LLNode$T), $h));

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

const unique tytagFamily$nat: TyTagFamily;

const unique tytagFamily$object: TyTagFamily;

const unique tytagFamily$array: TyTagFamily;

const unique tytagFamily$_#Func1: TyTagFamily;

const unique tytagFamily$_#PartialFunc1: TyTagFamily;

const unique tytagFamily$_#TotalFunc1: TyTagFamily;

const unique tytagFamily$_#Func0: TyTagFamily;

const unique tytagFamily$_#PartialFunc0: TyTagFamily;

const unique tytagFamily$_#TotalFunc0: TyTagFamily;

const unique tytagFamily$_#Func4: TyTagFamily;

const unique tytagFamily$_#PartialFunc4: TyTagFamily;

const unique tytagFamily$_#TotalFunc4: TyTagFamily;

const unique tytagFamily$_tuple#2: TyTagFamily;

const unique tytagFamily$_tuple#0: TyTagFamily;

const unique tytagFamily$Node: TyTagFamily;

const unique tytagFamily$ListNode: TyTagFamily;

const unique tytagFamily$List: TyTagFamily;

const unique tytagFamily$LLNode: TyTagFamily;

const unique tytagFamily$_default: TyTagFamily;

const unique field$data: NameFamily;

const unique field$next: NameFamily;

const unique field$Contents: NameFamily;

const unique field$Repr: NameFamily;

const unique field$head: NameFamily;

const unique field$TailContents: NameFamily;