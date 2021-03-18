// Dafny 3.0.0.30204
// Command Line Options: -compile:0 -noVerify /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy -print:./Constant.bpl

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

const unique class._module.Calendar?: ClassName;

function Tclass._module.Calendar?() : Ty;

const unique Tagclass._module.Calendar?: TyTag;

// Tclass._module.Calendar? Tag
axiom Tag(Tclass._module.Calendar?()) == Tagclass._module.Calendar?
   && TagFamily(Tclass._module.Calendar?()) == tytagFamily$Calendar;

// Box/unbox axiom for Tclass._module.Calendar?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Calendar?()) } 
  $IsBox(bx, Tclass._module.Calendar?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Calendar?()));

// Calendar: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.Calendar?()) } 
  $Is($o, Tclass._module.Calendar?())
     <==> $o == null || dtype($o) == Tclass._module.Calendar?());

// Calendar: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.Calendar?(), $h) } 
  $IsAlloc($o, Tclass._module.Calendar?(), $h)
     <==> $o == null || read($h, $o, alloc));

function {:inline} _module.Calendar.months() : int
{
  LitInt(12)
}

procedure CheckWellformed$$_module.Calendar.months();
  free requires 33 == $FunctionContextHeight;
  modifies $Heap;



// Calendar.months: Type axiom
axiom 33 < $FunctionContextHeight ==> $Is(_module.Calendar.months(), TInt);

// Calendar.months: Allocation axiom
axiom 33 < $FunctionContextHeight
   ==> (forall $h: Heap :: 
    { $IsAlloc(_module.Calendar.months(), TInt, $h) } 
    $IsGoodHeap($h) ==> $IsAlloc(_module.Calendar.months(), TInt, $h));

function {:inline} _module.Calendar.weeks() : int
{
  LitInt(52)
}

procedure CheckWellformed$$_module.Calendar.weeks();
  free requires 32 == $FunctionContextHeight;
  modifies $Heap;



// Calendar.weeks: Type axiom
axiom 32 < $FunctionContextHeight ==> $Is(_module.Calendar.weeks(), TInt);

// Calendar.weeks: Allocation axiom
axiom 32 < $FunctionContextHeight
   ==> (forall $h: Heap :: 
    { $IsAlloc(_module.Calendar.weeks(), TInt, $h) } 
    $IsGoodHeap($h) ==> $IsAlloc(_module.Calendar.weeks(), TInt, $h));

function Tclass._module.Calendar() : Ty;

const unique Tagclass._module.Calendar: TyTag;

// Tclass._module.Calendar Tag
axiom Tag(Tclass._module.Calendar()) == Tagclass._module.Calendar
   && TagFamily(Tclass._module.Calendar()) == tytagFamily$Calendar;

// Box/unbox axiom for Tclass._module.Calendar
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Calendar()) } 
  $IsBox(bx, Tclass._module.Calendar())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Calendar()));

// _module.Calendar: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.Calendar()) } 
  $Is(c#0, Tclass._module.Calendar())
     <==> $Is(c#0, Tclass._module.Calendar?()) && c#0 != null);

// _module.Calendar: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.Calendar(), $h) } 
  $IsAlloc(c#0, Tclass._module.Calendar(), $h)
     <==> $IsAlloc(c#0, Tclass._module.Calendar?(), $h));

const unique class._module.C?: ClassName;

function Tclass._module.C?() : Ty;

const unique Tagclass._module.C?: TyTag;

// Tclass._module.C? Tag
axiom Tag(Tclass._module.C?()) == Tagclass._module.C?
   && TagFamily(Tclass._module.C?()) == tytagFamily$C;

// Box/unbox axiom for Tclass._module.C?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.C?()) } 
  $IsBox(bx, Tclass._module.C?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.C?()));

// C: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.C?()) } 
  $Is($o, Tclass._module.C?()) <==> $o == null || dtype($o) == Tclass._module.C?());

// C: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.C?(), $h) } 
  $IsAlloc($o, Tclass._module.C?(), $h) <==> $o == null || read($h, $o, alloc));

function {:inline} _module.C.y() : int
{
  LitInt(5)
}

function {:inline} _module.C.x() : int
{
  _module.C.y() + 1
}

procedure CheckWellformed$$_module.C.x();
  free requires 2 == $FunctionContextHeight;
  modifies $Heap;



// C.x: Type axiom
axiom 2 < $FunctionContextHeight ==> $Is(_module.C.x(), TInt);

// C.x: Allocation axiom
axiom 2 < $FunctionContextHeight
   ==> (forall $h: Heap :: 
    { $IsAlloc(_module.C.x(), TInt, $h) } 
    $IsGoodHeap($h) ==> $IsAlloc(_module.C.x(), TInt, $h));

procedure CheckWellformed$$_module.C.y();
  free requires 1 == $FunctionContextHeight;
  modifies $Heap;



// C.y: Type axiom
axiom 1 < $FunctionContextHeight ==> $Is(_module.C.y(), TInt);

// C.y: Allocation axiom
axiom 1 < $FunctionContextHeight
   ==> (forall $h: Heap :: 
    { $IsAlloc(_module.C.y(), TInt, $h) } 
    $IsGoodHeap($h) ==> $IsAlloc(_module.C.y(), TInt, $h));

axiom FDim(_module.C.z) == 0
   && FieldOfDecl(class._module.C?, field$z) == _module.C.z
   && !$IsGhostField(_module.C.z);

const _module.C.z: Field int;

// C.z: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.C.z) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.C?()
     ==> $Is(read($h, $o, _module.C.z), TInt));

// C.z: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.C.z) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.C?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.C.z), TInt, $h));

// function declaration for _module.C.G
function _module.C.G(c#0: ref) : int;

function _module.C.G#canCall(c#0: ref) : bool;

function Tclass._module.C() : Ty;

const unique Tagclass._module.C: TyTag;

// Tclass._module.C Tag
axiom Tag(Tclass._module.C()) == Tagclass._module.C
   && TagFamily(Tclass._module.C()) == tytagFamily$C;

// Box/unbox axiom for Tclass._module.C
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.C()) } 
  $IsBox(bx, Tclass._module.C())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.C()));

// consequence axiom for _module.C.G
axiom 3 <= $FunctionContextHeight
   ==> (forall c#0: ref :: 
    { _module.C.G(c#0) } 
    _module.C.G#canCall(c#0)
         || (3 != $FunctionContextHeight && $Is(c#0, Tclass._module.C()))
       ==> _module.C.G(c#0) == LitInt(16));

function _module.C.G#requires(ref) : bool;

// #requires axiom for _module.C.G
axiom (forall c#0: ref :: 
  { _module.C.G#requires(c#0) } 
  $Is(c#0, Tclass._module.C()) ==> _module.C.G#requires(c#0) == true);

// definition axiom for _module.C.G (revealed)
axiom 3 <= $FunctionContextHeight
   ==> (forall c#0: ref :: 
    { _module.C.G(c#0) } 
    _module.C.G#canCall(c#0)
         || (3 != $FunctionContextHeight && $Is(c#0, Tclass._module.C()))
       ==> _module.C.G(c#0) == _module.C.x() + _module.C.y() + _module.C.y());

// definition axiom for _module.C.G for all literals (revealed)
axiom 3 <= $FunctionContextHeight
   ==> (forall c#0: ref :: 
    {:weight 3} { _module.C.G(Lit(c#0)) } 
    _module.C.G#canCall(Lit(c#0))
         || (3 != $FunctionContextHeight && $Is(c#0, Tclass._module.C()))
       ==> _module.C.G(Lit(c#0)) == _module.C.x() + _module.C.y() + _module.C.y());

procedure CheckWellformed$$_module.C.G(c#0: ref where $Is(c#0, Tclass._module.C()));
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures _module.C.G(c#0) == LitInt(16);



implementation CheckWellformed$$_module.C.G(c#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##c#0: ref;


    // AddWellformednessCheck for function G
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(55,25): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        ##c#0 := c#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#0, Tclass._module.C(), $Heap);
        assert c#0 == c#0 || (##c#0 == null && c#0 != null);
        assume c#0 == c#0 || _module.C.G#canCall(c#0);
        assume _module.C.G(c#0) == LitInt(16);
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        assume _module.C.G(c#0) == _module.C.x() + _module.C.y() + _module.C.y();
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.C.G(c#0), TInt);
    }
}



function {:inline} _module.C.b(this: ref) : int
{
  LitInt(50)
}

function {:inline} _module.C.a(this: ref) : int
{
  _module.C.b(this) + 2
}

procedure CheckWellformed$$_module.C.a(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.C())
         && $IsAlloc(this, Tclass._module.C(), $Heap));
  free requires 5 == $FunctionContextHeight;
  modifies $Heap;



// C.a: Type axiom
axiom 5 < $FunctionContextHeight
   ==> (forall $o: ref :: { _module.C.a($o) } $Is(_module.C.a($o), TInt));

// C.a: Allocation axiom
axiom 5 < $FunctionContextHeight
   ==> (forall $h: Heap, $o: ref :: 
    { _module.C.a($o), read($h, $o, alloc) } 
    $IsGoodHeap($h) && read($h, $o, alloc) ==> $IsAlloc(_module.C.a($o), TInt, $h));

procedure CheckWellformed$$_module.C.b(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.C())
         && $IsAlloc(this, Tclass._module.C(), $Heap));
  free requires 4 == $FunctionContextHeight;
  modifies $Heap;



// C.b: Type axiom
axiom 4 < $FunctionContextHeight
   ==> (forall $o: ref :: { _module.C.b($o) } $Is(_module.C.b($o), TInt));

// C.b: Allocation axiom
axiom 4 < $FunctionContextHeight
   ==> (forall $h: Heap, $o: ref :: 
    { _module.C.b($o), read($h, $o, alloc) } 
    $IsGoodHeap($h) && read($h, $o, alloc) ==> $IsAlloc(_module.C.b($o), TInt, $h));

// function declaration for _module.C.H
function _module.C.H(this: ref, c#0: ref) : int;

function _module.C.H#canCall(this: ref, c#0: ref) : bool;

// consequence axiom for _module.C.H
axiom 6 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref, c#0: ref :: 
    { _module.C.H(this, c#0), $IsGoodHeap($Heap) } 
    _module.C.H#canCall(this, c#0)
         || (6 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.C())
           && $IsAlloc(this, Tclass._module.C(), $Heap)
           && $Is(c#0, Tclass._module.C()))
       ==> _module.C.H(this, c#0) == LitInt(50 + 52 + 50 + 6 + 5 + 5 + 5)
         && LitInt(50 + 52 + 50 + 6 + 5 + 5 + 5) == LitInt(173));

function _module.C.H#requires(ref, ref) : bool;

// #requires axiom for _module.C.H
axiom (forall $Heap: Heap, this: ref, c#0: ref :: 
  { _module.C.H#requires(this, c#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.C())
       && $IsAlloc(this, Tclass._module.C(), $Heap)
       && $Is(c#0, Tclass._module.C())
     ==> _module.C.H#requires(this, c#0) == true);

// definition axiom for _module.C.H (revealed)
axiom 6 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref, c#0: ref :: 
    { _module.C.H(this, c#0), $IsGoodHeap($Heap) } 
    _module.C.H#canCall(this, c#0)
         || (6 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.C())
           && $IsAlloc(this, Tclass._module.C(), $Heap)
           && $Is(c#0, Tclass._module.C()))
       ==> _module.C.H(this, c#0)
         == _module.C.a(this)
           + _module.C.b(this)
           + _module.C.b(c#0)
           + _module.C.x()
           + _module.C.y()
           + _module.C.y()
           + _module.C.y());

// definition axiom for _module.C.H for decreasing-related literals (revealed)
axiom 6 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref, c#0: ref :: 
    {:weight 3} { _module.C.H(this, Lit(c#0)), $IsGoodHeap($Heap) } 
    _module.C.H#canCall(this, Lit(c#0))
         || (6 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.C())
           && $IsAlloc(this, Tclass._module.C(), $Heap)
           && $Is(c#0, Tclass._module.C()))
       ==> _module.C.H(this, Lit(c#0))
         == _module.C.a(this)
           + _module.C.b(this)
           + _module.C.b(Lit(c#0))
           + _module.C.x()
           + _module.C.y()
           + _module.C.y()
           + _module.C.y());

// definition axiom for _module.C.H for all literals (revealed)
axiom 6 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref, c#0: ref :: 
    {:weight 3} { _module.C.H(Lit(this), Lit(c#0)), $IsGoodHeap($Heap) } 
    _module.C.H#canCall(Lit(this), Lit(c#0))
         || (6 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.C())
           && $IsAlloc(this, Tclass._module.C(), $Heap)
           && $Is(c#0, Tclass._module.C()))
       ==> _module.C.H(Lit(this), Lit(c#0))
         == _module.C.a(Lit(this))
           + _module.C.b(Lit(this))
           + _module.C.b(Lit(c#0))
           + _module.C.x()
           + _module.C.y()
           + _module.C.y()
           + _module.C.y());

procedure CheckWellformed$$_module.C.H(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.C())
         && $IsAlloc(this, Tclass._module.C(), $Heap), 
    c#0: ref where $Is(c#0, Tclass._module.C()));
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures _module.C.H(this, c#0) == LitInt(50 + 52 + 50 + 6 + 5 + 5 + 5);
  ensures LitInt(50 + 52 + 50 + 6 + 5 + 5 + 5) == LitInt(173);



implementation CheckWellformed$$_module.C.H(this: ref, c#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##c#0: ref;


    // AddWellformednessCheck for function H
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(63,18): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        ##c#0 := c#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#0, Tclass._module.C(), $Heap);
        assert (this == this && c#0 == c#0) || (##c#0 == null && c#0 != null);
        assume (this == this && c#0 == c#0) || _module.C.H#canCall(this, c#0);
        if (_module.C.H(this, c#0) == LitInt(50 + 52 + 50 + 6 + 5 + 5 + 5))
        {
        }

        assume _module.C.H(this, c#0) == LitInt(50 + 52 + 50 + 6 + 5 + 5 + 5)
           && LitInt(50 + 52 + 50 + 6 + 5 + 5 + 5) == LitInt(173);
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        assert c#0 != null;
        assume _module.C.H(this, c#0)
           == _module.C.a(this)
             + _module.C.b(this)
             + _module.C.b(c#0)
             + _module.C.x()
             + _module.C.y()
             + _module.C.y()
             + _module.C.y();
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.C.H(this, c#0), TInt);
    }
}



procedure CheckWellformed$$_module.C.M(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.C())
         && $IsAlloc(this, Tclass._module.C(), $Heap))
   returns (r#0: int);
  free requires 26 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.C.M(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.C())
         && $IsAlloc(this, Tclass._module.C(), $Heap))
   returns (r#0: int);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures r#0 == LitInt(11);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.C.M(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.C())
         && $IsAlloc(this, Tclass._module.C(), $Heap))
   returns (r#0: int, $_reverifyPost: bool);
  free requires 26 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures r#0 == LitInt(11);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.C.M(this: ref) returns (r#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: M, Impl$$_module.C.M
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(71,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(72,7)
    assume true;
    assume true;
    r#0 := _module.C.x() + _module.C.y();
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(72,14)"} true;
}



// _module.C: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.C()) } 
  $Is(c#0, Tclass._module.C()) <==> $Is(c#0, Tclass._module.C?()) && c#0 != null);

// _module.C: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.C(), $h) } 
  $IsAlloc(c#0, Tclass._module.C(), $h)
     <==> $IsAlloc(c#0, Tclass._module.C?(), $h));

const unique class._module.Generic?: ClassName;

function Tclass._module.Generic?(Ty) : Ty;

const unique Tagclass._module.Generic?: TyTag;

// Tclass._module.Generic? Tag
axiom (forall _module.Generic$G: Ty :: 
  { Tclass._module.Generic?(_module.Generic$G) } 
  Tag(Tclass._module.Generic?(_module.Generic$G)) == Tagclass._module.Generic?
     && TagFamily(Tclass._module.Generic?(_module.Generic$G)) == tytagFamily$Generic);

// Tclass._module.Generic? injectivity 0
axiom (forall _module.Generic$G: Ty :: 
  { Tclass._module.Generic?(_module.Generic$G) } 
  Tclass._module.Generic?_0(Tclass._module.Generic?(_module.Generic$G))
     == _module.Generic$G);

function Tclass._module.Generic?_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.Generic?
axiom (forall _module.Generic$G: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.Generic?(_module.Generic$G)) } 
  $IsBox(bx, Tclass._module.Generic?(_module.Generic$G))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.Generic?(_module.Generic$G)));

// Generic: Class $Is
axiom (forall _module.Generic$G: Ty, $o: ref :: 
  { $Is($o, Tclass._module.Generic?(_module.Generic$G)) } 
  $Is($o, Tclass._module.Generic?(_module.Generic$G))
     <==> $o == null || dtype($o) == Tclass._module.Generic?(_module.Generic$G));

// Generic: Class $IsAlloc
axiom (forall _module.Generic$G: Ty, $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.Generic?(_module.Generic$G), $h) } 
  $IsAlloc($o, Tclass._module.Generic?(_module.Generic$G), $h)
     <==> $o == null || read($h, $o, alloc));

function {:inline} _module.Generic.y(_module.Generic$G: Ty, this: ref) : int
{
  LitInt(63)
}

function Tclass._module.Generic(Ty) : Ty;

const unique Tagclass._module.Generic: TyTag;

// Tclass._module.Generic Tag
axiom (forall _module.Generic$G: Ty :: 
  { Tclass._module.Generic(_module.Generic$G) } 
  Tag(Tclass._module.Generic(_module.Generic$G)) == Tagclass._module.Generic
     && TagFamily(Tclass._module.Generic(_module.Generic$G)) == tytagFamily$Generic);

// Tclass._module.Generic injectivity 0
axiom (forall _module.Generic$G: Ty :: 
  { Tclass._module.Generic(_module.Generic$G) } 
  Tclass._module.Generic_0(Tclass._module.Generic(_module.Generic$G))
     == _module.Generic$G);

function Tclass._module.Generic_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.Generic
axiom (forall _module.Generic$G: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.Generic(_module.Generic$G)) } 
  $IsBox(bx, Tclass._module.Generic(_module.Generic$G))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.Generic(_module.Generic$G)));

procedure CheckWellformed$$_module.Generic.y(_module.Generic$G: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Generic(_module.Generic$G))
         && $IsAlloc(this, Tclass._module.Generic(_module.Generic$G), $Heap));
  free requires 27 == $FunctionContextHeight;
  modifies $Heap;



// Generic.y: Type axiom
axiom 27 < $FunctionContextHeight
   ==> (forall _module.Generic$G: Ty, $o: ref :: 
    { _module.Generic.y(_module.Generic$G, $o) } 
    $Is(_module.Generic.y(_module.Generic$G, $o), TInt));

// Generic.y: Allocation axiom
axiom 27 < $FunctionContextHeight
   ==> (forall _module.Generic$G: Ty, $h: Heap, $o: ref :: 
    { _module.Generic.y(_module.Generic$G, $o), read($h, $o, alloc) } 
    $IsGoodHeap($h) && read($h, $o, alloc)
       ==> $IsAlloc(_module.Generic.y(_module.Generic$G, $o), TInt, $h));

procedure CheckWellformed$$_module.Generic.M(_module.Generic$G: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Generic(_module.Generic$G))
         && $IsAlloc(this, Tclass._module.Generic(_module.Generic$G), $Heap))
   returns (q#0: int);
  free requires 28 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Generic.M(_module.Generic$G: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Generic(_module.Generic$G))
         && $IsAlloc(this, Tclass._module.Generic(_module.Generic$G), $Heap))
   returns (q#0: int);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures q#0 == LitInt(63);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Generic.M(_module.Generic$G: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Generic(_module.Generic$G))
         && $IsAlloc(this, Tclass._module.Generic(_module.Generic$G), $Heap))
   returns (q#0: int, $_reverifyPost: bool);
  free requires 28 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures q#0 == LitInt(63);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Generic.M(_module.Generic$G: Ty, this: ref) returns (q#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: M, Impl$$_module.Generic.M
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(80,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(81,7)
    assume true;
    assume true;
    q#0 := _module.Generic.y(_module.Generic$G, this);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(81,15)"} true;
}



// _module.Generic: subset type $Is
axiom (forall _module.Generic$G: Ty, c#0: ref :: 
  { $Is(c#0, Tclass._module.Generic(_module.Generic$G)) } 
  $Is(c#0, Tclass._module.Generic(_module.Generic$G))
     <==> $Is(c#0, Tclass._module.Generic?(_module.Generic$G)) && c#0 != null);

// _module.Generic: subset type $IsAlloc
axiom (forall _module.Generic$G: Ty, c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.Generic(_module.Generic$G), $h) } 
  $IsAlloc(c#0, Tclass._module.Generic(_module.Generic$G), $h)
     <==> $IsAlloc(c#0, Tclass._module.Generic?(_module.Generic$G), $h));

procedure CheckWellformed$$_module.Six(x#0: int);
  free requires 7 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Six(x#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;


    // AddWellformednessCheck for newtype Six
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(85,8): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume LitInt(6) <= x#0;
    }
    else
    {
        assume true;
        assert LitInt(6) <= LitInt(6);
    }
}



function Tclass._module.Six() : Ty;

const unique Tagclass._module.Six: TyTag;

// Tclass._module.Six Tag
axiom Tag(Tclass._module.Six()) == Tagclass._module.Six
   && TagFamily(Tclass._module.Six()) == tytagFamily$Six;

// Box/unbox axiom for Tclass._module.Six
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Six()) } 
  $IsBox(bx, Tclass._module.Six())
     ==> $Box($Unbox(bx): int) == bx && $Is($Unbox(bx): int, Tclass._module.Six()));

// _module.Six: newtype $Is
axiom (forall x#0: int :: 
  { $Is(x#0, Tclass._module.Six()) } 
  $Is(x#0, Tclass._module.Six()) <==> LitInt(6) <= x#0);

// _module.Six: newtype $IsAlloc
axiom (forall x#0: int, $h: Heap :: 
  { $IsAlloc(x#0, Tclass._module.Six(), $h) } 
  $IsAlloc(x#0, Tclass._module.Six(), $h));

const unique class._module.Six: ClassName;

const unique class._module.NoRHS?: ClassName;

function Tclass._module.NoRHS?() : Ty;

const unique Tagclass._module.NoRHS?: TyTag;

// Tclass._module.NoRHS? Tag
axiom Tag(Tclass._module.NoRHS?()) == Tagclass._module.NoRHS?
   && TagFamily(Tclass._module.NoRHS?()) == tytagFamily$NoRHS;

// Box/unbox axiom for Tclass._module.NoRHS?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.NoRHS?()) } 
  $IsBox(bx, Tclass._module.NoRHS?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.NoRHS?()));

// NoRHS: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.NoRHS?()) } 
  $Is($o, Tclass._module.NoRHS?())
     <==> $o == null || dtype($o) == Tclass._module.NoRHS?());

// NoRHS: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.NoRHS?(), $h) } 
  $IsAlloc($o, Tclass._module.NoRHS?(), $h) <==> $o == null || read($h, $o, alloc));

function _module.NoRHS.y(this: ref) : int;

// NoRHS.y: Type axiom
axiom 8 < $FunctionContextHeight
   ==> (forall $o: ref :: 
    { _module.NoRHS.y($o) } 
    $Is(_module.NoRHS.y($o), Tclass._module.Six()));

// NoRHS.y: Allocation axiom
axiom 8 < $FunctionContextHeight
   ==> (forall $h: Heap, $o: ref :: 
    { _module.NoRHS.y($o), read($h, $o, alloc) } 
    $IsGoodHeap($h) && read($h, $o, alloc)
       ==> $IsAlloc(_module.NoRHS.y($o), Tclass._module.Six(), $h));

function Tclass._module.NoRHS() : Ty;

const unique Tagclass._module.NoRHS: TyTag;

// Tclass._module.NoRHS Tag
axiom Tag(Tclass._module.NoRHS()) == Tagclass._module.NoRHS
   && TagFamily(Tclass._module.NoRHS()) == tytagFamily$NoRHS;

// Box/unbox axiom for Tclass._module.NoRHS
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.NoRHS()) } 
  $IsBox(bx, Tclass._module.NoRHS())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.NoRHS()));

// _module.NoRHS: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.NoRHS()) } 
  $Is(c#0, Tclass._module.NoRHS())
     <==> $Is(c#0, Tclass._module.NoRHS?()) && c#0 != null);

// _module.NoRHS: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.NoRHS(), $h) } 
  $IsAlloc(c#0, Tclass._module.NoRHS(), $h)
     <==> $IsAlloc(c#0, Tclass._module.NoRHS?(), $h));

const unique class._module.Trait?: ClassName;

function Tclass._module.Trait?() : Ty;

const unique Tagclass._module.Trait?: TyTag;

// Tclass._module.Trait? Tag
axiom Tag(Tclass._module.Trait?()) == Tagclass._module.Trait?
   && TagFamily(Tclass._module.Trait?()) == tytagFamily$Trait;

// Box/unbox axiom for Tclass._module.Trait?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Trait?()) } 
  $IsBox(bx, Tclass._module.Trait?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Trait?()));

// Trait: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.Trait?()) } 
  $Is($o, Tclass._module.Trait?())
     <==> $o == null || implements$_module.Trait(dtype($o)));

// Trait: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.Trait?(), $h) } 
  $IsAlloc($o, Tclass._module.Trait?(), $h) <==> $o == null || read($h, $o, alloc));

function implements$_module.Trait(Ty) : bool;

function _module.Trait.x0(this: ref) : int;

// Trait.x0: Type axiom
axiom 9 < $FunctionContextHeight
   ==> (forall $o: ref :: 
    { _module.Trait.x0($o) } 
    $Is(_module.Trait.x0($o), Tclass._module.Six()));

// Trait.x0: Allocation axiom
axiom 9 < $FunctionContextHeight
   ==> (forall $h: Heap, $o: ref :: 
    { _module.Trait.x0($o), read($h, $o, alloc) } 
    $IsGoodHeap($h) && read($h, $o, alloc)
       ==> $IsAlloc(_module.Trait.x0($o), Tclass._module.Six(), $h));

function {:inline} _module.Trait.x1(this: ref) : int
{
  LitInt(7)
}

function Tclass._module.Trait() : Ty;

const unique Tagclass._module.Trait: TyTag;

// Tclass._module.Trait Tag
axiom Tag(Tclass._module.Trait()) == Tagclass._module.Trait
   && TagFamily(Tclass._module.Trait()) == tytagFamily$Trait;

// Box/unbox axiom for Tclass._module.Trait
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Trait()) } 
  $IsBox(bx, Tclass._module.Trait())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Trait()));

procedure CheckWellformed$$_module.Trait.x1(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Trait())
         && $IsAlloc(this, Tclass._module.Trait(), $Heap));
  free requires 10 == $FunctionContextHeight;
  modifies $Heap;



implementation CheckWellformed$$_module.Trait.x1(this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var newtype$check#0: int;

    // AddWellformednessCheck for const field x1
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(95,8): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    newtype$check#0 := LitInt(7);
    assert LitInt(6) <= newtype$check#0;
    assume true;
}



// Trait.x1: Type axiom
axiom 10 < $FunctionContextHeight
   ==> (forall $o: ref :: 
    { _module.Trait.x1($o) } 
    $Is(_module.Trait.x1($o), Tclass._module.Six()));

// Trait.x1: Allocation axiom
axiom 10 < $FunctionContextHeight
   ==> (forall $h: Heap, $o: ref :: 
    { _module.Trait.x1($o), read($h, $o, alloc) } 
    $IsGoodHeap($h) && read($h, $o, alloc)
       ==> $IsAlloc(_module.Trait.x1($o), Tclass._module.Six(), $h));

function {:inline} _module.Trait.y() : int
{
  LitInt(7)
}

procedure CheckWellformed$$_module.Trait.y();
  free requires 11 == $FunctionContextHeight;
  modifies $Heap;



implementation CheckWellformed$$_module.Trait.y()
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var newtype$check#0: int;

    // AddWellformednessCheck for const field y
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(97,15): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    newtype$check#0 := LitInt(7);
    assert LitInt(6) <= newtype$check#0;
    assume true;
}



// Trait.y: Type axiom
axiom 11 < $FunctionContextHeight ==> $Is(_module.Trait.y(), Tclass._module.Six());

// Trait.y: Allocation axiom
axiom 11 < $FunctionContextHeight
   ==> (forall $h: Heap :: 
    { $IsAlloc(_module.Trait.y(), Tclass._module.Six(), $h) } 
    $IsGoodHeap($h) ==> $IsAlloc(_module.Trait.y(), Tclass._module.Six(), $h));

// _module.Trait: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.Trait()) } 
  $Is(c#0, Tclass._module.Trait())
     <==> $Is(c#0, Tclass._module.Trait?()) && c#0 != null);

// _module.Trait: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.Trait(), $h) } 
  $IsAlloc(c#0, Tclass._module.Trait(), $h)
     <==> $IsAlloc(c#0, Tclass._module.Trait?(), $h));

const unique class._module.Class?: ClassName;

function Tclass._module.Class?() : Ty;

const unique Tagclass._module.Class?: TyTag;

// Tclass._module.Class? Tag
axiom Tag(Tclass._module.Class?()) == Tagclass._module.Class?
   && TagFamily(Tclass._module.Class?()) == tytagFamily$Class;

// Box/unbox axiom for Tclass._module.Class?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Class?()) } 
  $IsBox(bx, Tclass._module.Class?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Class?()));

// Class: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.Class?()) } 
  $Is($o, Tclass._module.Class?())
     <==> $o == null || dtype($o) == Tclass._module.Class?());

// Class: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.Class?(), $h) } 
  $IsAlloc($o, Tclass._module.Class?(), $h) <==> $o == null || read($h, $o, alloc));

axiom implements$_module.Trait(Tclass._module.Class?());

function Tclass._module.Class() : Ty;

const unique Tagclass._module.Class: TyTag;

// Tclass._module.Class Tag
axiom Tag(Tclass._module.Class()) == Tagclass._module.Class
   && TagFamily(Tclass._module.Class()) == tytagFamily$Class;

// Box/unbox axiom for Tclass._module.Class
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Class()) } 
  $IsBox(bx, Tclass._module.Class())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Class()));

procedure CheckWellformed$$_module.Class.Test(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Class())
         && $IsAlloc(this, Tclass._module.Class(), $Heap));
  free requires 29 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Class.Test(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Class())
         && $IsAlloc(this, Tclass._module.Class(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Class.Test(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Class())
         && $IsAlloc(this, Tclass._module.Class(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 29 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Class.Test(this: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var newtype$check#0: int;
  var newtype$check#1: int;

    // AddMethodImpl: Test, Impl$$_module.Class.Test
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(101,16): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(102,5)
    newtype$check#0 := LitInt(7);
    assert LitInt(6) <= newtype$check#0;
    if (_module.Trait.x1(this) == LitInt(7))
    {
        newtype$check#1 := LitInt(7);
        assert LitInt(6) <= newtype$check#1;
    }

    assume true;
    assert {:subsumption 0} _module.Trait.x1(this) == LitInt(7);
    assert {:subsumption 0} _module.Trait.y() == LitInt(7);
    assume _module.Trait.x1(this) == LitInt(7) && _module.Trait.y() == LitInt(7);
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(103,5)
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
}



// _module.Class: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.Class()) } 
  $Is(c#0, Tclass._module.Class())
     <==> $Is(c#0, Tclass._module.Class?()) && c#0 != null);

// _module.Class: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.Class(), $h) } 
  $IsAlloc(c#0, Tclass._module.Class(), $h)
     <==> $IsAlloc(c#0, Tclass._module.Class?(), $h));

const unique class._module.InstanceInit?: ClassName;

function Tclass._module.InstanceInit?() : Ty;

const unique Tagclass._module.InstanceInit?: TyTag;

// Tclass._module.InstanceInit? Tag
axiom Tag(Tclass._module.InstanceInit?()) == Tagclass._module.InstanceInit?
   && TagFamily(Tclass._module.InstanceInit?()) == tytagFamily$InstanceInit;

// Box/unbox axiom for Tclass._module.InstanceInit?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.InstanceInit?()) } 
  $IsBox(bx, Tclass._module.InstanceInit?())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.InstanceInit?()));

// InstanceInit: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.InstanceInit?()) } 
  $Is($o, Tclass._module.InstanceInit?())
     <==> $o == null || dtype($o) == Tclass._module.InstanceInit?());

// InstanceInit: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.InstanceInit?(), $h) } 
  $IsAlloc($o, Tclass._module.InstanceInit?(), $h)
     <==> $o == null || read($h, $o, alloc));

axiom implements$_module.Trait(Tclass._module.InstanceInit?());

function _module.InstanceInit.y2(this: ref) : int;

// InstanceInit.y2: Type axiom
axiom 12 < $FunctionContextHeight
   ==> (forall $o: ref :: 
    { _module.InstanceInit.y2($o) } 
    $Is(_module.InstanceInit.y2($o), Tclass._module.Six()));

// InstanceInit.y2: Allocation axiom
axiom 12 < $FunctionContextHeight
   ==> (forall $h: Heap, $o: ref :: 
    { _module.InstanceInit.y2($o), read($h, $o, alloc) } 
    $IsGoodHeap($h) && read($h, $o, alloc)
       ==> $IsAlloc(_module.InstanceInit.y2($o), Tclass._module.Six(), $h));

function {:inline} _module.InstanceInit.y3(this: ref) : int
{
  LitInt(12)
}

function Tclass._module.InstanceInit() : Ty;

const unique Tagclass._module.InstanceInit: TyTag;

// Tclass._module.InstanceInit Tag
axiom Tag(Tclass._module.InstanceInit()) == Tagclass._module.InstanceInit
   && TagFamily(Tclass._module.InstanceInit()) == tytagFamily$InstanceInit;

// Box/unbox axiom for Tclass._module.InstanceInit
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.InstanceInit()) } 
  $IsBox(bx, Tclass._module.InstanceInit())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.InstanceInit()));

procedure CheckWellformed$$_module.InstanceInit.y3(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.InstanceInit())
         && $IsAlloc(this, Tclass._module.InstanceInit(), $Heap));
  free requires 13 == $FunctionContextHeight;
  modifies $Heap;



implementation CheckWellformed$$_module.InstanceInit.y3(this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var newtype$check#0: int;

    // AddWellformednessCheck for const field y3
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(117,8): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    newtype$check#0 := LitInt(12);
    assert LitInt(6) <= newtype$check#0;
    assume true;
}



// InstanceInit.y3: Type axiom
axiom 13 < $FunctionContextHeight
   ==> (forall $o: ref :: 
    { _module.InstanceInit.y3($o) } 
    $Is(_module.InstanceInit.y3($o), Tclass._module.Six()));

// InstanceInit.y3: Allocation axiom
axiom 13 < $FunctionContextHeight
   ==> (forall $h: Heap, $o: ref :: 
    { _module.InstanceInit.y3($o), read($h, $o, alloc) } 
    $IsGoodHeap($h) && read($h, $o, alloc)
       ==> $IsAlloc(_module.InstanceInit.y3($o), Tclass._module.Six(), $h));

function {:inline} _module.InstanceInit.N(this: ref) : int
{
  LitInt(20)
}

procedure CheckWellformed$$_module.InstanceInit.N(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.InstanceInit())
         && $IsAlloc(this, Tclass._module.InstanceInit(), $Heap));
  free requires 14 == $FunctionContextHeight;
  modifies $Heap;



// InstanceInit.N: Type axiom
axiom 14 < $FunctionContextHeight
   ==> (forall $o: ref :: 
    { _module.InstanceInit.N($o) } 
    $Is(_module.InstanceInit.N($o), TInt));

// InstanceInit.N: Allocation axiom
axiom 14 < $FunctionContextHeight
   ==> (forall $h: Heap, $o: ref :: 
    { _module.InstanceInit.N($o), read($h, $o, alloc) } 
    $IsGoodHeap($h) && read($h, $o, alloc)
       ==> $IsAlloc(_module.InstanceInit.N($o), TInt, $h));

axiom FDim(_module.InstanceInit.r) == 0
   && FieldOfDecl(class._module.InstanceInit?, field$r) == _module.InstanceInit.r
   && !$IsGhostField(_module.InstanceInit.r);

const _module.InstanceInit.r: Field real;

// InstanceInit.r: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.InstanceInit.r) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.InstanceInit?()
     ==> $Is(read($h, $o, _module.InstanceInit.r), TReal));

// InstanceInit.r: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.InstanceInit.r) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.InstanceInit?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.InstanceInit.r), TReal, $h));

procedure CheckWellformed$$_module.InstanceInit.__ctor(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.InstanceInit())
         && $IsAlloc(this, Tclass._module.InstanceInit(), $Heap), 
    u#0: int where LitInt(6) <= u#0);
  free requires 16 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.InstanceInit.__ctor(this: ref, u#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var newtype$check#0: int;

    // AddMethodImpl: _ctor, CheckWellformed$$_module.InstanceInit.__ctor
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(122,2): initial state"} true;
    newtype$check#0 := LitInt(10);
    assert LitInt(6) <= newtype$check#0;
    assume LitInt(10) <= u#0;
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
    assume $HeapSucc(old($Heap), $Heap);
}



procedure Call$$_module.InstanceInit.__ctor(u#0: int where LitInt(6) <= u#0)
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass._module.InstanceInit())
         && $IsAlloc(this, Tclass._module.InstanceInit(), $Heap));
  // user-defined preconditions
  requires LitInt(10) <= u#0;
  modifies $Heap, $Tick;
  // constructor allocates the object
  ensures !read(old($Heap), this, alloc);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.InstanceInit.__ctor(u#0: int where LitInt(6) <= u#0)
   returns (this: ref where this != null && $Is(this, Tclass._module.InstanceInit()), 
    $_reverifyPost: bool);
  free requires 16 == $FunctionContextHeight;
  // user-defined preconditions
  requires LitInt(10) <= u#0;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.InstanceInit.__ctor(u#0: int) returns (this: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var this.x0: int;
  var this.y2: int;
  var this.r: real;
  var newtype$check#1: int;
  var newtype$check#2: int;
  var arr#0: ref
     where $Is(arr#0, Tclass._System.array(TReal))
       && $IsAlloc(arr#0, Tclass._System.array(TReal), $Heap);
  var $nw: ref;
  var $rhs#0: real;
  var newtype$check#3: int;
  var newtype$check#4: int;
  var newtype$check#5: int;
  var newtype$check#6: int;
  var newtype$check#7: int;
  var newtype$check#8: int;
  var newtype$check#9: int;
  var $rhs#1: real;
  var $rhs#2: real;

    // AddMethodImpl: _ctor, Impl$$_module.InstanceInit.__ctor
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(124,2): initial state"} true;
    $_reverifyPost := false;
    // ----- divided block before new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(124,3)
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(125,8)
    assume true;
    newtype$check#1 := LitInt(80);
    assert LitInt(6) <= newtype$check#1;
    newtype$check#2 := 80 + u#0;
    assert LitInt(6) <= newtype$check#2;
    assume true;
    this.x0 := 80 + u#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(125,16)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(126,13)
    assume true;
    assert 0 <= _module.InstanceInit.N(this);
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._System.array?(TReal);
    assume !read($Heap, $nw, alloc);
    assume _System.array.Length($nw) == _module.InstanceInit.N(this);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    arr#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(126,26)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(127,12)
    assert arr#0 != null;
    assert 0 <= LitInt(8) && LitInt(8) < _System.array.Length(arr#0);
    assume true;
    assert $_Frame[arr#0, IndexField(LitInt(8))];
    assume true;
    $rhs#0 := LitReal(27e-1);
    $Heap := update($Heap, arr#0, IndexField(LitInt(8)), $Box($rhs#0));
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(127,17)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(128,7)
    assume true;
    assert arr#0 != null;
    assert 0 <= LitInt(8) && LitInt(8) < _System.array.Length(arr#0);
    assume true;
    this.r := $Unbox(read($Heap, arr#0, IndexField(LitInt(8)))): real;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(128,15)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(129,8)
    assume true;
    newtype$check#3 := LitInt(77);
    assert LitInt(6) <= newtype$check#3;
    newtype$check#4 := 77 + _module.InstanceInit.y3(this);
    assert LitInt(6) <= newtype$check#4;
    assume true;
    this.y2 := 77 + _module.InstanceInit.y3(this);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(129,17)"} true;
    // ----- new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(124,3)
    assume !read($Heap, this, alloc);
    assume _module.Trait.x0(this) == this.x0;
    assume _module.InstanceInit.y2(this) == this.y2;
    assume read($Heap, this, _module.InstanceInit.r) == this.r;
    $Heap := update($Heap, this, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    // ----- divided block after new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(124,3)
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(131,5)
    newtype$check#5 := LitInt(80);
    assert LitInt(6) <= newtype$check#5;
    newtype$check#6 := u#0 + 80;
    assert LitInt(6) <= newtype$check#6;
    if (_module.Trait.x0(this) == u#0 + 80)
    {
        newtype$check#7 := LitInt(7);
        assert LitInt(6) <= newtype$check#7;
    }

    assume true;
    assert {:subsumption 0} _module.Trait.x0(this) == u#0 + 80;
    assert {:subsumption 0} _module.Trait.x1(this) == LitInt(7);
    assume _module.Trait.x0(this) == u#0 + 80 && _module.Trait.x1(this) == LitInt(7);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(132,5)
    newtype$check#8 := LitInt(89);
    assert LitInt(6) <= newtype$check#8;
    if (_module.InstanceInit.y2(this) == LitInt(89))
    {
        newtype$check#9 := LitInt(12);
        assert LitInt(6) <= newtype$check#9;
    }

    assume true;
    assert {:subsumption 0} _module.InstanceInit.y2(this) == LitInt(89);
    assert {:subsumption 0} _module.InstanceInit.y3(this) == LitInt(12);
    assume _module.InstanceInit.y2(this) == LitInt(89)
       && _module.InstanceInit.y3(this) == LitInt(12);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(133,5)
    assert {:subsumption 0} arr#0 != null;
    assume true;
    assert _System.array.Length(arr#0) == LitInt(20);
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(134,12)
    assert arr#0 != null;
    assert 0 <= LitInt(9) && LitInt(9) < _System.array.Length(arr#0);
    assume true;
    assert $_Frame[arr#0, IndexField(LitInt(9))];
    assume true;
    $rhs#1 := LitReal(314e-2);
    $Heap := update($Heap, arr#0, IndexField(LitInt(9)), $Box($rhs#1));
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(134,18)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(135,7)
    assume true;
    assert $_Frame[this, _module.InstanceInit.r];
    assert arr#0 != null;
    assert 0 <= LitInt(8) && LitInt(8) < _System.array.Length(arr#0);
    assert arr#0 != null;
    assert 0 <= LitInt(9) && LitInt(9) < _System.array.Length(arr#0);
    assume true;
    $rhs#2 := read($Heap, this, _module.InstanceInit.r)
       + $Unbox(read($Heap, arr#0, IndexField(LitInt(8)))): real
       + $Unbox(read($Heap, arr#0, IndexField(LitInt(9)))): real;
    $Heap := update($Heap, this, _module.InstanceInit.r, $rhs#2);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(135,28)"} true;
}



// _module.InstanceInit: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.InstanceInit()) } 
  $Is(c#0, Tclass._module.InstanceInit())
     <==> $Is(c#0, Tclass._module.InstanceInit?()) && c#0 != null);

// _module.InstanceInit: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.InstanceInit(), $h) } 
  $IsAlloc(c#0, Tclass._module.InstanceInit(), $h)
     <==> $IsAlloc(c#0, Tclass._module.InstanceInit?(), $h));

const unique class._module.UninterpretedStaticsTrait?: ClassName;

function Tclass._module.UninterpretedStaticsTrait?() : Ty;

const unique Tagclass._module.UninterpretedStaticsTrait?: TyTag;

// Tclass._module.UninterpretedStaticsTrait? Tag
axiom Tag(Tclass._module.UninterpretedStaticsTrait?())
     == Tagclass._module.UninterpretedStaticsTrait?
   && TagFamily(Tclass._module.UninterpretedStaticsTrait?())
     == tytagFamily$UninterpretedStaticsTrait;

// Box/unbox axiom for Tclass._module.UninterpretedStaticsTrait?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.UninterpretedStaticsTrait?()) } 
  $IsBox(bx, Tclass._module.UninterpretedStaticsTrait?())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.UninterpretedStaticsTrait?()));

// UninterpretedStaticsTrait: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.UninterpretedStaticsTrait?()) } 
  $Is($o, Tclass._module.UninterpretedStaticsTrait?())
     <==> $o == null || implements$_module.UninterpretedStaticsTrait(dtype($o)));

// UninterpretedStaticsTrait: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.UninterpretedStaticsTrait?(), $h) } 
  $IsAlloc($o, Tclass._module.UninterpretedStaticsTrait?(), $h)
     <==> $o == null || read($h, $o, alloc));

function implements$_module.UninterpretedStaticsTrait(Ty) : bool;

function _module.UninterpretedStaticsTrait.mmtt() : int;

// UninterpretedStaticsTrait.mmtt: Type axiom
axiom 17 < $FunctionContextHeight
   ==> $Is(_module.UninterpretedStaticsTrait.mmtt(), Tclass._module.Six());

// UninterpretedStaticsTrait.mmtt: Allocation axiom
axiom 17 < $FunctionContextHeight
   ==> (forall $h: Heap :: 
    { $IsAlloc(_module.UninterpretedStaticsTrait.mmtt(), Tclass._module.Six(), $h) } 
    $IsGoodHeap($h)
       ==> $IsAlloc(_module.UninterpretedStaticsTrait.mmtt(), Tclass._module.Six(), $h));

function Tclass._module.UninterpretedStaticsTrait() : Ty;

const unique Tagclass._module.UninterpretedStaticsTrait: TyTag;

// Tclass._module.UninterpretedStaticsTrait Tag
axiom Tag(Tclass._module.UninterpretedStaticsTrait())
     == Tagclass._module.UninterpretedStaticsTrait
   && TagFamily(Tclass._module.UninterpretedStaticsTrait())
     == tytagFamily$UninterpretedStaticsTrait;

// Box/unbox axiom for Tclass._module.UninterpretedStaticsTrait
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.UninterpretedStaticsTrait()) } 
  $IsBox(bx, Tclass._module.UninterpretedStaticsTrait())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.UninterpretedStaticsTrait()));

// _module.UninterpretedStaticsTrait: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.UninterpretedStaticsTrait()) } 
  $Is(c#0, Tclass._module.UninterpretedStaticsTrait())
     <==> $Is(c#0, Tclass._module.UninterpretedStaticsTrait?()) && c#0 != null);

// _module.UninterpretedStaticsTrait: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.UninterpretedStaticsTrait(), $h) } 
  $IsAlloc(c#0, Tclass._module.UninterpretedStaticsTrait(), $h)
     <==> $IsAlloc(c#0, Tclass._module.UninterpretedStaticsTrait?(), $h));

const unique class._module.UninterpretedStaticsClass?: ClassName;

function Tclass._module.UninterpretedStaticsClass?() : Ty;

const unique Tagclass._module.UninterpretedStaticsClass?: TyTag;

// Tclass._module.UninterpretedStaticsClass? Tag
axiom Tag(Tclass._module.UninterpretedStaticsClass?())
     == Tagclass._module.UninterpretedStaticsClass?
   && TagFamily(Tclass._module.UninterpretedStaticsClass?())
     == tytagFamily$UninterpretedStaticsClass;

// Box/unbox axiom for Tclass._module.UninterpretedStaticsClass?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.UninterpretedStaticsClass?()) } 
  $IsBox(bx, Tclass._module.UninterpretedStaticsClass?())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.UninterpretedStaticsClass?()));

// UninterpretedStaticsClass: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.UninterpretedStaticsClass?()) } 
  $Is($o, Tclass._module.UninterpretedStaticsClass?())
     <==> $o == null || dtype($o) == Tclass._module.UninterpretedStaticsClass?());

// UninterpretedStaticsClass: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.UninterpretedStaticsClass?(), $h) } 
  $IsAlloc($o, Tclass._module.UninterpretedStaticsClass?(), $h)
     <==> $o == null || read($h, $o, alloc));

axiom implements$_module.UninterpretedStaticsTrait(Tclass._module.UninterpretedStaticsClass?());

function _module.UninterpretedStaticsClass.mmcc() : int;

// UninterpretedStaticsClass.mmcc: Type axiom
axiom 18 < $FunctionContextHeight
   ==> $Is(_module.UninterpretedStaticsClass.mmcc(), Tclass._module.Six());

// UninterpretedStaticsClass.mmcc: Allocation axiom
axiom 18 < $FunctionContextHeight
   ==> (forall $h: Heap :: 
    { $IsAlloc(_module.UninterpretedStaticsClass.mmcc(), Tclass._module.Six(), $h) } 
    $IsGoodHeap($h)
       ==> $IsAlloc(_module.UninterpretedStaticsClass.mmcc(), Tclass._module.Six(), $h));

function Tclass._module.UninterpretedStaticsClass() : Ty;

const unique Tagclass._module.UninterpretedStaticsClass: TyTag;

// Tclass._module.UninterpretedStaticsClass Tag
axiom Tag(Tclass._module.UninterpretedStaticsClass())
     == Tagclass._module.UninterpretedStaticsClass
   && TagFamily(Tclass._module.UninterpretedStaticsClass())
     == tytagFamily$UninterpretedStaticsClass;

// Box/unbox axiom for Tclass._module.UninterpretedStaticsClass
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.UninterpretedStaticsClass()) } 
  $IsBox(bx, Tclass._module.UninterpretedStaticsClass())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.UninterpretedStaticsClass()));

// _module.UninterpretedStaticsClass: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.UninterpretedStaticsClass()) } 
  $Is(c#0, Tclass._module.UninterpretedStaticsClass())
     <==> $Is(c#0, Tclass._module.UninterpretedStaticsClass?()) && c#0 != null);

// _module.UninterpretedStaticsClass: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.UninterpretedStaticsClass(), $h) } 
  $IsAlloc(c#0, Tclass._module.UninterpretedStaticsClass(), $h)
     <==> $IsAlloc(c#0, Tclass._module.UninterpretedStaticsClass?(), $h));

procedure CheckWellformed$$_module.byte(x#0: int);
  free requires 19 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.byte(x#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;


    // AddWellformednessCheck for subset type byte
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(153,5): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        if (LitInt(0) <= x#0)
        {
        }

        assume LitInt(0) <= x#0 && x#0 < 256;
    }
    else
    {
        assume true;
        assert {:subsumption 0} LitInt(0) <= LitInt(0);
        assert {:subsumption 0} 0 < 256;
    }
}



function Tclass._module.byte() : Ty;

const unique Tagclass._module.byte: TyTag;

// Tclass._module.byte Tag
axiom Tag(Tclass._module.byte()) == Tagclass._module.byte
   && TagFamily(Tclass._module.byte()) == tytagFamily$byte;

// Box/unbox axiom for Tclass._module.byte
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.byte()) } 
  $IsBox(bx, Tclass._module.byte())
     ==> $Box($Unbox(bx): int) == bx && $Is($Unbox(bx): int, Tclass._module.byte()));

// _module.byte: subset type $Is
axiom (forall x#0: int :: 
  { $Is(x#0, Tclass._module.byte()) } 
  $Is(x#0, Tclass._module.byte()) <==> LitInt(0) <= x#0 && x#0 < 256);

// _module.byte: subset type $IsAlloc
axiom (forall x#0: int, $h: Heap :: 
  { $IsAlloc(x#0, Tclass._module.byte(), $h) } 
  $IsAlloc(x#0, Tclass._module.byte(), $h));

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

function _module.MyClass.B(this: ref) : ref;

// MyClass.B: Type axiom
axiom 20 < $FunctionContextHeight
   ==> (forall $o: ref :: 
    { _module.MyClass.B($o) } 
    $Is(_module.MyClass.B($o), Tclass._System.array(Tclass._module.byte())));

// MyClass.B: Allocation axiom
axiom 20 < $FunctionContextHeight
   ==> (forall $h: Heap, $o: ref :: 
    { _module.MyClass.B($o), read($h, $o, alloc) } 
    $IsGoodHeap($h) && read($h, $o, alloc)
       ==> $IsAlloc(_module.MyClass.B($o), Tclass._System.array(Tclass._module.byte()), $h));

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

procedure CheckWellformed$$_module.MyClass.M(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.MyClass())
         && $IsAlloc(this, Tclass._module.MyClass(), $Heap));
  free requires 30 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.MyClass.M(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.MyClass())
         && $IsAlloc(this, Tclass._module.MyClass(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.MyClass.M(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.MyClass())
         && $IsAlloc(this, Tclass._module.MyClass(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 30 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.MyClass.M(this: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var x#0: ref
     where $Is(x#0, Tclass._System.array?(Tclass._module.byte()))
       && $IsAlloc(x#0, Tclass._System.array?(Tclass._module.byte()), $Heap);
  var y#0: ref
     where $Is(y#0, Tclass._System.array(Tclass._module.byte()))
       && $IsAlloc(y#0, Tclass._System.array(Tclass._module.byte()), $Heap);

    // AddMethodImpl: M, Impl$$_module.MyClass.M
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(159,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(160,25)
    assume true;
    assume true;
    x#0 := _module.MyClass.B(this);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(160,28)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(161,24)
    assume true;
    assume true;
    assert $Is(x#0, Tclass._System.array(Tclass._module.byte()));
    y#0 := x#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(161,27)"} true;
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

const unique class._module.MyOnePurposeClass?: ClassName;

function Tclass._module.MyOnePurposeClass?() : Ty;

const unique Tagclass._module.MyOnePurposeClass?: TyTag;

// Tclass._module.MyOnePurposeClass? Tag
axiom Tag(Tclass._module.MyOnePurposeClass?()) == Tagclass._module.MyOnePurposeClass?
   && TagFamily(Tclass._module.MyOnePurposeClass?()) == tytagFamily$MyOnePurposeClass;

// Box/unbox axiom for Tclass._module.MyOnePurposeClass?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.MyOnePurposeClass?()) } 
  $IsBox(bx, Tclass._module.MyOnePurposeClass?())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.MyOnePurposeClass?()));

// MyOnePurposeClass: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.MyOnePurposeClass?()) } 
  $Is($o, Tclass._module.MyOnePurposeClass?())
     <==> $o == null || dtype($o) == Tclass._module.MyOnePurposeClass?());

// MyOnePurposeClass: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.MyOnePurposeClass?(), $h) } 
  $IsAlloc($o, Tclass._module.MyOnePurposeClass?(), $h)
     <==> $o == null || read($h, $o, alloc));

function _module.MyOnePurposeClass.z() : int;

// MyOnePurposeClass.z: Type axiom
axiom 40 < $FunctionContextHeight ==> $Is(_module.MyOnePurposeClass.z(), TInt);

// MyOnePurposeClass.z: Allocation axiom
axiom 40 < $FunctionContextHeight
   ==> (forall $h: Heap :: 
    { $IsAlloc(_module.MyOnePurposeClass.z(), TInt, $h) } 
    $IsGoodHeap($h) ==> $IsAlloc(_module.MyOnePurposeClass.z(), TInt, $h));

function {:inline} _module.MyOnePurposeClass.w() : int
{
  LitInt(76)
}

procedure CheckWellformed$$_module.MyOnePurposeClass.w();
  free requires 41 == $FunctionContextHeight;
  modifies $Heap;



// MyOnePurposeClass.w: Type axiom
axiom 41 < $FunctionContextHeight ==> $Is(_module.MyOnePurposeClass.w(), TInt);

// MyOnePurposeClass.w: Allocation axiom
axiom 41 < $FunctionContextHeight
   ==> (forall $h: Heap :: 
    { $IsAlloc(_module.MyOnePurposeClass.w(), TInt, $h) } 
    $IsGoodHeap($h) ==> $IsAlloc(_module.MyOnePurposeClass.w(), TInt, $h));

function _module.MyOnePurposeClass.self() : ref;

// MyOnePurposeClass.self: Type axiom
axiom 42 < $FunctionContextHeight
   ==> $Is(_module.MyOnePurposeClass.self(), Tclass._module.MyOnePurposeClass?());

// MyOnePurposeClass.self: Allocation axiom
axiom 42 < $FunctionContextHeight
   ==> (forall $h: Heap :: 
    { $IsAlloc(_module.MyOnePurposeClass.self(), Tclass._module.MyOnePurposeClass?(), $h) } 
    $IsGoodHeap($h)
       ==> $IsAlloc(_module.MyOnePurposeClass.self(), Tclass._module.MyOnePurposeClass?(), $h));

function Tclass._module.MyOnePurposeClass() : Ty;

const unique Tagclass._module.MyOnePurposeClass: TyTag;

// Tclass._module.MyOnePurposeClass Tag
axiom Tag(Tclass._module.MyOnePurposeClass()) == Tagclass._module.MyOnePurposeClass
   && TagFamily(Tclass._module.MyOnePurposeClass()) == tytagFamily$MyOnePurposeClass;

// Box/unbox axiom for Tclass._module.MyOnePurposeClass
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.MyOnePurposeClass()) } 
  $IsBox(bx, Tclass._module.MyOnePurposeClass())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.MyOnePurposeClass()));

// _module.MyOnePurposeClass: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.MyOnePurposeClass()) } 
  $Is(c#0, Tclass._module.MyOnePurposeClass())
     <==> $Is(c#0, Tclass._module.MyOnePurposeClass?()) && c#0 != null);

// _module.MyOnePurposeClass: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.MyOnePurposeClass(), $h) } 
  $IsAlloc(c#0, Tclass._module.MyOnePurposeClass(), $h)
     <==> $IsAlloc(c#0, Tclass._module.MyOnePurposeClass?(), $h));

const unique class._module.MyGenericClass?: ClassName;

function Tclass._module.MyGenericClass?(Ty, Ty) : Ty;

const unique Tagclass._module.MyGenericClass?: TyTag;

// Tclass._module.MyGenericClass? Tag
axiom (forall _module.MyGenericClass$X: Ty, _module.MyGenericClass$Y: Ty :: 
  { Tclass._module.MyGenericClass?(_module.MyGenericClass$X, _module.MyGenericClass$Y) } 
  Tag(Tclass._module.MyGenericClass?(_module.MyGenericClass$X, _module.MyGenericClass$Y))
       == Tagclass._module.MyGenericClass?
     && TagFamily(Tclass._module.MyGenericClass?(_module.MyGenericClass$X, _module.MyGenericClass$Y))
       == tytagFamily$MyGenericClass);

// Tclass._module.MyGenericClass? injectivity 0
axiom (forall _module.MyGenericClass$X: Ty, _module.MyGenericClass$Y: Ty :: 
  { Tclass._module.MyGenericClass?(_module.MyGenericClass$X, _module.MyGenericClass$Y) } 
  Tclass._module.MyGenericClass?_0(Tclass._module.MyGenericClass?(_module.MyGenericClass$X, _module.MyGenericClass$Y))
     == _module.MyGenericClass$X);

function Tclass._module.MyGenericClass?_0(Ty) : Ty;

// Tclass._module.MyGenericClass? injectivity 1
axiom (forall _module.MyGenericClass$X: Ty, _module.MyGenericClass$Y: Ty :: 
  { Tclass._module.MyGenericClass?(_module.MyGenericClass$X, _module.MyGenericClass$Y) } 
  Tclass._module.MyGenericClass?_1(Tclass._module.MyGenericClass?(_module.MyGenericClass$X, _module.MyGenericClass$Y))
     == _module.MyGenericClass$Y);

function Tclass._module.MyGenericClass?_1(Ty) : Ty;

// Box/unbox axiom for Tclass._module.MyGenericClass?
axiom (forall _module.MyGenericClass$X: Ty, _module.MyGenericClass$Y: Ty, bx: Box :: 
  { $IsBox(bx, 
      Tclass._module.MyGenericClass?(_module.MyGenericClass$X, _module.MyGenericClass$Y)) } 
  $IsBox(bx, 
      Tclass._module.MyGenericClass?(_module.MyGenericClass$X, _module.MyGenericClass$Y))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, 
        Tclass._module.MyGenericClass?(_module.MyGenericClass$X, _module.MyGenericClass$Y)));

// MyGenericClass: Class $Is
axiom (forall _module.MyGenericClass$X: Ty, _module.MyGenericClass$Y: Ty, $o: ref :: 
  { $Is($o, 
      Tclass._module.MyGenericClass?(_module.MyGenericClass$X, _module.MyGenericClass$Y)) } 
  $Is($o, 
      Tclass._module.MyGenericClass?(_module.MyGenericClass$X, _module.MyGenericClass$Y))
     <==> $o == null
       || dtype($o)
         == Tclass._module.MyGenericClass?(_module.MyGenericClass$X, _module.MyGenericClass$Y));

// MyGenericClass: Class $IsAlloc
axiom (forall _module.MyGenericClass$X: Ty, _module.MyGenericClass$Y: Ty, $o: ref, $h: Heap :: 
  { $IsAlloc($o, 
      Tclass._module.MyGenericClass?(_module.MyGenericClass$X, _module.MyGenericClass$Y), 
      $h) } 
  $IsAlloc($o, 
      Tclass._module.MyGenericClass?(_module.MyGenericClass$X, _module.MyGenericClass$Y), 
      $h)
     <==> $o == null || read($h, $o, alloc));

function _module.MyGenericClass.x(_module.MyGenericClass$X: Ty, _module.MyGenericClass$Y: Ty) : Box;

// MyGenericClass.x: Type axiom
axiom 43 < $FunctionContextHeight
   ==> (forall _module.MyGenericClass$X: Ty, _module.MyGenericClass$Y: Ty :: 
    { _module.MyGenericClass.x(_module.MyGenericClass$X, _module.MyGenericClass$Y) } 
    $IsBox(_module.MyGenericClass.x(_module.MyGenericClass$X, _module.MyGenericClass$Y), 
      _module.MyGenericClass$X));

// MyGenericClass.x: Allocation axiom
axiom 43 < $FunctionContextHeight
   ==> (forall _module.MyGenericClass$X: Ty, _module.MyGenericClass$Y: Ty, $h: Heap :: 
    { $IsAllocBox(_module.MyGenericClass.x(_module.MyGenericClass$X, _module.MyGenericClass$Y), 
        _module.MyGenericClass$X, 
        $h) } 
    $IsGoodHeap($h)
       ==> $IsAllocBox(_module.MyGenericClass.x(_module.MyGenericClass$X, _module.MyGenericClass$Y), 
        _module.MyGenericClass$X, 
        $h));

function _module.MyGenericClass.y(_module.MyGenericClass$X: Ty, _module.MyGenericClass$Y: Ty) : Box;

// MyGenericClass.y: Type axiom
axiom 44 < $FunctionContextHeight
   ==> (forall _module.MyGenericClass$X: Ty, _module.MyGenericClass$Y: Ty :: 
    { _module.MyGenericClass.y(_module.MyGenericClass$X, _module.MyGenericClass$Y) } 
    $IsBox(_module.MyGenericClass.y(_module.MyGenericClass$X, _module.MyGenericClass$Y), 
      _module.MyGenericClass$Y));

// MyGenericClass.y: Allocation axiom
axiom 44 < $FunctionContextHeight
   ==> (forall _module.MyGenericClass$X: Ty, _module.MyGenericClass$Y: Ty, $h: Heap :: 
    { $IsAllocBox(_module.MyGenericClass.y(_module.MyGenericClass$X, _module.MyGenericClass$Y), 
        _module.MyGenericClass$Y, 
        $h) } 
    $IsGoodHeap($h)
       ==> $IsAllocBox(_module.MyGenericClass.y(_module.MyGenericClass$X, _module.MyGenericClass$Y), 
        _module.MyGenericClass$Y, 
        $h));

function _module.MyGenericClass.z(_module.MyGenericClass$X: Ty, _module.MyGenericClass$Y: Ty) : int;

// MyGenericClass.z: Type axiom
axiom 45 < $FunctionContextHeight
   ==> (forall _module.MyGenericClass$X: Ty, _module.MyGenericClass$Y: Ty :: 
    { _module.MyGenericClass.z(_module.MyGenericClass$X, _module.MyGenericClass$Y) } 
    $Is(_module.MyGenericClass.z(_module.MyGenericClass$X, _module.MyGenericClass$Y), 
      TInt));

// MyGenericClass.z: Allocation axiom
axiom 45 < $FunctionContextHeight
   ==> (forall _module.MyGenericClass$X: Ty, _module.MyGenericClass$Y: Ty, $h: Heap :: 
    { $IsAlloc(_module.MyGenericClass.z(_module.MyGenericClass$X, _module.MyGenericClass$Y), 
        TInt, 
        $h) } 
    $IsGoodHeap($h)
       ==> $IsAlloc(_module.MyGenericClass.z(_module.MyGenericClass$X, _module.MyGenericClass$Y), 
        TInt, 
        $h));

function {:inline} _module.MyGenericClass.w(_module.MyGenericClass$X: Ty, _module.MyGenericClass$Y: Ty) : int
{
  LitInt(76)
}

procedure CheckWellformed$$_module.MyGenericClass.w(_module.MyGenericClass$X: Ty, _module.MyGenericClass$Y: Ty);
  free requires 46 == $FunctionContextHeight;
  modifies $Heap;



// MyGenericClass.w: Type axiom
axiom 46 < $FunctionContextHeight
   ==> (forall _module.MyGenericClass$X: Ty, _module.MyGenericClass$Y: Ty :: 
    { _module.MyGenericClass.w(_module.MyGenericClass$X, _module.MyGenericClass$Y) } 
    $Is(_module.MyGenericClass.w(_module.MyGenericClass$X, _module.MyGenericClass$Y), 
      TInt));

// MyGenericClass.w: Allocation axiom
axiom 46 < $FunctionContextHeight
   ==> (forall _module.MyGenericClass$X: Ty, _module.MyGenericClass$Y: Ty, $h: Heap :: 
    { $IsAlloc(_module.MyGenericClass.w(_module.MyGenericClass$X, _module.MyGenericClass$Y), 
        TInt, 
        $h) } 
    $IsGoodHeap($h)
       ==> $IsAlloc(_module.MyGenericClass.w(_module.MyGenericClass$X, _module.MyGenericClass$Y), 
        TInt, 
        $h));

function _module.MyGenericClass.self(_module.MyGenericClass$X: Ty, _module.MyGenericClass$Y: Ty) : ref;

// MyGenericClass.self: Type axiom
axiom 47 < $FunctionContextHeight
   ==> (forall _module.MyGenericClass$X: Ty, _module.MyGenericClass$Y: Ty :: 
    { _module.MyGenericClass.self(_module.MyGenericClass$X, _module.MyGenericClass$Y) } 
    $Is(_module.MyGenericClass.self(_module.MyGenericClass$X, _module.MyGenericClass$Y), 
      Tclass._module.MyGenericClass?(_module.MyGenericClass$X, _module.MyGenericClass$Y)));

// MyGenericClass.self: Allocation axiom
axiom 47 < $FunctionContextHeight
   ==> (forall _module.MyGenericClass$X: Ty, _module.MyGenericClass$Y: Ty, $h: Heap :: 
    { $IsAlloc(_module.MyGenericClass.self(_module.MyGenericClass$X, _module.MyGenericClass$Y), 
        Tclass._module.MyGenericClass?(_module.MyGenericClass$X, _module.MyGenericClass$Y), 
        $h) } 
    $IsGoodHeap($h)
       ==> $IsAlloc(_module.MyGenericClass.self(_module.MyGenericClass$X, _module.MyGenericClass$Y), 
        Tclass._module.MyGenericClass?(_module.MyGenericClass$X, _module.MyGenericClass$Y), 
        $h));

function _module.MyGenericClass.almostSelf(_module.MyGenericClass$X: Ty, _module.MyGenericClass$Y: Ty) : ref;

// MyGenericClass.almostSelf: Type axiom
axiom 48 < $FunctionContextHeight
   ==> (forall _module.MyGenericClass$X: Ty, _module.MyGenericClass$Y: Ty :: 
    { _module.MyGenericClass.almostSelf(_module.MyGenericClass$X, _module.MyGenericClass$Y) } 
    $Is(_module.MyGenericClass.almostSelf(_module.MyGenericClass$X, _module.MyGenericClass$Y), 
      Tclass._module.MyGenericClass?(_module.MyGenericClass$Y, _module.MyGenericClass$X)));

// MyGenericClass.almostSelf: Allocation axiom
axiom 48 < $FunctionContextHeight
   ==> (forall _module.MyGenericClass$X: Ty, _module.MyGenericClass$Y: Ty, $h: Heap :: 
    { $IsAlloc(_module.MyGenericClass.almostSelf(_module.MyGenericClass$X, _module.MyGenericClass$Y), 
        Tclass._module.MyGenericClass?(_module.MyGenericClass$Y, _module.MyGenericClass$X), 
        $h) } 
    $IsGoodHeap($h)
       ==> $IsAlloc(_module.MyGenericClass.almostSelf(_module.MyGenericClass$X, _module.MyGenericClass$Y), 
        Tclass._module.MyGenericClass?(_module.MyGenericClass$Y, _module.MyGenericClass$X), 
        $h));

function _module.MyGenericClass.another(_module.MyGenericClass$X: Ty, _module.MyGenericClass$Y: Ty) : ref;

// MyGenericClass.another: Type axiom
axiom 21 < $FunctionContextHeight
   ==> (forall _module.MyGenericClass$X: Ty, _module.MyGenericClass$Y: Ty :: 
    { _module.MyGenericClass.another(_module.MyGenericClass$X, _module.MyGenericClass$Y) } 
    $Is(_module.MyGenericClass.another(_module.MyGenericClass$X, _module.MyGenericClass$Y), 
      Tclass._module.MyGenericClass?(Tclass._module.byte(), TSeq(_module.MyGenericClass$X))));

// MyGenericClass.another: Allocation axiom
axiom 21 < $FunctionContextHeight
   ==> (forall _module.MyGenericClass$X: Ty, _module.MyGenericClass$Y: Ty, $h: Heap :: 
    { $IsAlloc(_module.MyGenericClass.another(_module.MyGenericClass$X, _module.MyGenericClass$Y), 
        Tclass._module.MyGenericClass?(Tclass._module.byte(), TSeq(_module.MyGenericClass$X)), 
        $h) } 
    $IsGoodHeap($h)
       ==> $IsAlloc(_module.MyGenericClass.another(_module.MyGenericClass$X, _module.MyGenericClass$Y), 
        Tclass._module.MyGenericClass?(Tclass._module.byte(), TSeq(_module.MyGenericClass$X)), 
        $h));

function Tclass._module.MyGenericClass(Ty, Ty) : Ty;

const unique Tagclass._module.MyGenericClass: TyTag;

// Tclass._module.MyGenericClass Tag
axiom (forall _module.MyGenericClass$X: Ty, _module.MyGenericClass$Y: Ty :: 
  { Tclass._module.MyGenericClass(_module.MyGenericClass$X, _module.MyGenericClass$Y) } 
  Tag(Tclass._module.MyGenericClass(_module.MyGenericClass$X, _module.MyGenericClass$Y))
       == Tagclass._module.MyGenericClass
     && TagFamily(Tclass._module.MyGenericClass(_module.MyGenericClass$X, _module.MyGenericClass$Y))
       == tytagFamily$MyGenericClass);

// Tclass._module.MyGenericClass injectivity 0
axiom (forall _module.MyGenericClass$X: Ty, _module.MyGenericClass$Y: Ty :: 
  { Tclass._module.MyGenericClass(_module.MyGenericClass$X, _module.MyGenericClass$Y) } 
  Tclass._module.MyGenericClass_0(Tclass._module.MyGenericClass(_module.MyGenericClass$X, _module.MyGenericClass$Y))
     == _module.MyGenericClass$X);

function Tclass._module.MyGenericClass_0(Ty) : Ty;

// Tclass._module.MyGenericClass injectivity 1
axiom (forall _module.MyGenericClass$X: Ty, _module.MyGenericClass$Y: Ty :: 
  { Tclass._module.MyGenericClass(_module.MyGenericClass$X, _module.MyGenericClass$Y) } 
  Tclass._module.MyGenericClass_1(Tclass._module.MyGenericClass(_module.MyGenericClass$X, _module.MyGenericClass$Y))
     == _module.MyGenericClass$Y);

function Tclass._module.MyGenericClass_1(Ty) : Ty;

// Box/unbox axiom for Tclass._module.MyGenericClass
axiom (forall _module.MyGenericClass$X: Ty, _module.MyGenericClass$Y: Ty, bx: Box :: 
  { $IsBox(bx, 
      Tclass._module.MyGenericClass(_module.MyGenericClass$X, _module.MyGenericClass$Y)) } 
  $IsBox(bx, 
      Tclass._module.MyGenericClass(_module.MyGenericClass$X, _module.MyGenericClass$Y))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, 
        Tclass._module.MyGenericClass(_module.MyGenericClass$X, _module.MyGenericClass$Y)));

// _module.MyGenericClass: subset type $Is
axiom (forall _module.MyGenericClass$X: Ty, _module.MyGenericClass$Y: Ty, c#0: ref :: 
  { $Is(c#0, 
      Tclass._module.MyGenericClass(_module.MyGenericClass$X, _module.MyGenericClass$Y)) } 
  $Is(c#0, 
      Tclass._module.MyGenericClass(_module.MyGenericClass$X, _module.MyGenericClass$Y))
     <==> $Is(c#0, 
        Tclass._module.MyGenericClass?(_module.MyGenericClass$X, _module.MyGenericClass$Y))
       && c#0 != null);

// _module.MyGenericClass: subset type $IsAlloc
axiom (forall _module.MyGenericClass$X: Ty, _module.MyGenericClass$Y: Ty, c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, 
      Tclass._module.MyGenericClass(_module.MyGenericClass$X, _module.MyGenericClass$Y), 
      $h) } 
  $IsAlloc(c#0, 
      Tclass._module.MyGenericClass(_module.MyGenericClass$X, _module.MyGenericClass$Y), 
      $h)
     <==> $IsAlloc(c#0, 
      Tclass._module.MyGenericClass?(_module.MyGenericClass$X, _module.MyGenericClass$Y), 
      $h));

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

function {:inline} _module.__default.one() : int
{
  LitInt(1)
}

procedure CheckWellformed$$_module.__default.one();
  free requires 23 == $FunctionContextHeight;
  modifies $Heap;



// _default.one: Type axiom
axiom 23 < $FunctionContextHeight ==> $Is(_module.__default.one(), TInt);

// _default.one: Allocation axiom
axiom 23 < $FunctionContextHeight
   ==> (forall $h: Heap :: 
    { $IsAlloc(_module.__default.one(), TInt, $h) } 
    $IsGoodHeap($h) ==> $IsAlloc(_module.__default.one(), TInt, $h));

function {:inline} _module.__default.two() : int
{
  Mul(_module.__default.one(), LitInt(2))
}

procedure CheckWellformed$$_module.__default.two();
  free requires 24 == $FunctionContextHeight;
  modifies $Heap;



// _default.two: Type axiom
axiom 24 < $FunctionContextHeight ==> $Is(_module.__default.two(), TInt);

// _default.two: Allocation axiom
axiom 24 < $FunctionContextHeight
   ==> (forall $h: Heap :: 
    { $IsAlloc(_module.__default.two(), TInt, $h) } 
    $IsGoodHeap($h) ==> $IsAlloc(_module.__default.two(), TInt, $h));

function {:inline} _module.__default.three() : int
{
  _module.__default.one() + _module.__default.two()
}

procedure CheckWellformed$$_module.__default.three();
  free requires 25 == $FunctionContextHeight;
  modifies $Heap;



// _default.three: Type axiom
axiom 25 < $FunctionContextHeight ==> $Is(_module.__default.three(), TInt);

// _default.three: Allocation axiom
axiom 25 < $FunctionContextHeight
   ==> (forall $h: Heap :: 
    { $IsAlloc(_module.__default.three(), TInt, $h) } 
    $IsGoodHeap($h) ==> $IsAlloc(_module.__default.three(), TInt, $h));

function {:inline} _module.__default.Pi() : real
{
  LitReal(314e-2)
}

procedure CheckWellformed$$_module.__default.Pi();
  free requires 31 == $FunctionContextHeight;
  modifies $Heap;



// _default.Pi: Type axiom
axiom 31 < $FunctionContextHeight ==> $Is(_module.__default.Pi(), TReal);

// _default.Pi: Allocation axiom
axiom 31 < $FunctionContextHeight
   ==> (forall $h: Heap :: 
    { $IsAlloc(_module.__default.Pi(), TReal, $h) } 
    $IsGoodHeap($h) ==> $IsAlloc(_module.__default.Pi(), TReal, $h));

procedure CheckWellformed$$_module.__default._default_Main();
  free requires 38 == $FunctionContextHeight;
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
  free requires 38 == $FunctionContextHeight;
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
  var weeks#0: int;
  var c#0: ref
     where $Is(c#0, Tclass._module.C()) && $IsAlloc(c#0, Tclass._module.C(), $Heap);
  var $nw: ref;
  var tu#0: int;
  var $rhs##0: int;
  var ##c#0: ref;
  var ##c#1: ref;
  var g#0: ref
     where $Is(g#0, Tclass._module.Generic(TReal))
       && $IsAlloc(g#0, Tclass._module.Generic(TReal), $Heap);
  var putItHere#0: int;
  var go#0: int;
  var $rhs##1: int;
  var noRhs#0: ref
     where $Is(noRhs#0, Tclass._module.NoRHS())
       && $IsAlloc(noRhs#0, Tclass._module.NoRHS(), $Heap);
  var cl#0: ref
     where $Is(cl#0, Tclass._module.Class())
       && $IsAlloc(cl#0, Tclass._module.Class(), $Heap);
  var ii#0: ref
     where $Is(ii#0, Tclass._module.InstanceInit())
       && $IsAlloc(ii#0, Tclass._module.InstanceInit(), $Heap);
  var u##0: int;
  var newtype$check#0: int;

    // AddMethodImpl: Main, Impl$$_module.__default._default_Main
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(14,14): initial state"} true;
    $_reverifyPost := false;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(15,3)
    assume true;
    assume true;
    assume true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(16,3)
    assume true;
    assume true;
    assume true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(17,3)
    assume true;
    assume true;
    assume true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(18,3)
    assume true;
    assert _module.__default.three() == LitInt(3);
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(19,3)
    assume true;
    assume true;
    assume true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(20,3)
    assume true;
    assert _module.__default.Pi() == LitReal(314e-2);
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(21,13)
    assume true;
    assume true;
    weeks#0 := _module.Calendar.weeks();
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(21,29)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(22,3)
    assume true;
    assume true;
    assume true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(23,3)
    assume true;
    assume true;
    assume true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(24,3)
    assume true;
    assert weeks#0 == LitInt(52);
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(26,9)
    assume true;
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._module.C?();
    assume !read($Heap, $nw, alloc);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    c#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(26,16)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(27,16)
    assume true;
    // TrCallStmt: Adding lhs with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert c#0 != null;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0 := Call$$_module.C.M(c#0);
    // TrCallStmt: After ProcessCallStmt
    tu#0 := $rhs##0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(27,17)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(28,3)
    assume true;
    assume true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(29,3)
    ##c#0 := c#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##c#0, Tclass._module.C(), $Heap);
    assume _module.C.G#canCall(c#0);
    assume _module.C.G#canCall(c#0);
    assume true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(30,3)
    assert {:subsumption 0} c#0 != null;
    ##c#1 := c#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##c#1, Tclass._module.C(), $Heap);
    assume _module.C.H#canCall(c#0, c#0);
    assume _module.C.H#canCall(c#0, c#0);
    assume true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(31,3)
    assume true;
    assume true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(32,9)
    assume true;
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._module.Generic?(TReal);
    assume !read($Heap, $nw, alloc);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    g#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(32,28)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(33,17)
    assume true;
    assert g#0 != null;
    assume true;
    putItHere#0 := _module.Generic.y(TReal, g#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(33,22)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(34,3)
    assume true;
    assume true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(35,16)
    assume true;
    // TrCallStmt: Adding lhs with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert g#0 != null;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##1 := Call$$_module.Generic.M(TReal, g#0);
    // TrCallStmt: After ProcessCallStmt
    go#0 := $rhs##1;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(35,17)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(36,3)
    assume true;
    assume true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(38,13)
    assume true;
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._module.NoRHS?();
    assume !read($Heap, $nw, alloc);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    noRhs#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(38,24)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(39,3)
    assume true;
    assert {:subsumption 0} noRhs#0 != null;
    assume true;
    assume true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(41,10)
    assume true;
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._module.Class?();
    assume !read($Heap, $nw, alloc);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    cl#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(41,21)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(42,10)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert cl#0 != null;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.Class.Test(cl#0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(42,11)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(43,10)
    assume true;
    // ----- init call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(43,13)
    // TrCallStmt: Before ProcessCallStmt
    newtype$check#0 := LitInt(13);
    assert LitInt(6) <= newtype$check#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    u##0 := LitInt(13);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $nw := Call$$_module.InstanceInit.__ctor(u##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(43,32)"} true;
    ii#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(43,32)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(44,3)
    assert {:subsumption 0} ii#0 != null;
    assume true;
    assume true;
    assert {:subsumption 0} ii#0 != null;
    assume true;
    assume true;
    assert {:subsumption 0} ii#0 != null;
    assume true;
    assume true;
    assert {:subsumption 0} ii#0 != null;
    assume true;
    assume true;
    assert {:subsumption 0} ii#0 != null;
    assume true;
    assume true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(46,3)
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(48,37)
    // TrCallStmt: Before ProcessCallStmt
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$InitializationDependencies.__default.PrintEm();
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(48,38)"} true;
}



procedure CheckWellformed$$_module.__default.MMethod(tr#0: ref
       where $Is(tr#0, Tclass._module.Trait?())
         && $IsAlloc(tr#0, Tclass._module.Trait?(), $Heap));
  free requires 39 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.MMethod(tr#0: ref
       where $Is(tr#0, Tclass._module.Trait?())
         && $IsAlloc(tr#0, Tclass._module.Trait?(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.MMethod(tr#0: ref
       where $Is(tr#0, Tclass._module.Trait?())
         && $IsAlloc(tr#0, Tclass._module.Trait?(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 39 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.MMethod(tr#0: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var newtype$check#0: int;
  var newtype$check#1: int;
  var newtype$check#2: int;

    // AddMethodImpl: MMethod, Impl$$_module.__default.MMethod
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(107,27): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(108,3)
    newtype$check#0 := LitInt(7);
    assert LitInt(6) <= newtype$check#0;
    assume true;
    assert _module.Trait.y() == LitInt(7);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(109,3)
    newtype$check#1 := LitInt(7);
    assert LitInt(6) <= newtype$check#1;
    assume true;
    assert _module.Trait.y() == LitInt(7);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Constant.dfy(110,3)
    if (tr#0 != null)
    {
        assert {:subsumption 0} tr#0 != null;
        newtype$check#2 := LitInt(7);
        assert LitInt(6) <= newtype$check#2;
    }

    assume true;
    assert tr#0 == null || _module.Trait.x1(tr#0) == LitInt(7);
}



function _module.__default.mmgg() : int;

// _default.mmgg: Type axiom
axiom 22 < $FunctionContextHeight
   ==> $Is(_module.__default.mmgg(), Tclass._module.Six());

// _default.mmgg: Allocation axiom
axiom 22 < $FunctionContextHeight
   ==> (forall $h: Heap :: 
    { $IsAlloc(_module.__default.mmgg(), Tclass._module.Six(), $h) } 
    $IsGoodHeap($h) ==> $IsAlloc(_module.__default.mmgg(), Tclass._module.Six(), $h));

const unique class.InitializationDependencies.C?: ClassName;

function Tclass.InitializationDependencies.C?() : Ty;

const unique Tagclass.InitializationDependencies.C?: TyTag;

// Tclass.InitializationDependencies.C? Tag
axiom Tag(Tclass.InitializationDependencies.C?())
     == Tagclass.InitializationDependencies.C?
   && TagFamily(Tclass.InitializationDependencies.C?()) == tytagFamily$C;

// Box/unbox axiom for Tclass.InitializationDependencies.C?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.InitializationDependencies.C?()) } 
  $IsBox(bx, Tclass.InitializationDependencies.C?())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.InitializationDependencies.C?()));

// C: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.InitializationDependencies.C?()) } 
  $Is($o, Tclass.InitializationDependencies.C?())
     <==> $o == null || dtype($o) == Tclass.InitializationDependencies.C?());

// C: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.InitializationDependencies.C?(), $h) } 
  $IsAlloc($o, Tclass.InitializationDependencies.C?(), $h)
     <==> $o == null || read($h, $o, alloc));

function {:inline} InitializationDependencies.D.m() : int
{
  LitInt(20)
}

function {:inline} InitializationDependencies.C.b() : int
{
  InitializationDependencies.D.m()
}

function {:inline} InitializationDependencies.C.a() : int
{
  InitializationDependencies.C.b()
}

// C.a: Type axiom
axiom $Is(InitializationDependencies.C.a(), TInt);

// C.a: Allocation axiom
axiom (forall $h: Heap :: 
  { $IsAlloc(InitializationDependencies.C.a(), TInt, $h) } 
  $IsGoodHeap($h) ==> $IsAlloc(InitializationDependencies.C.a(), TInt, $h));

// C.b: Type axiom
axiom $Is(InitializationDependencies.C.b(), TInt);

// C.b: Allocation axiom
axiom (forall $h: Heap :: 
  { $IsAlloc(InitializationDependencies.C.b(), TInt, $h) } 
  $IsGoodHeap($h) ==> $IsAlloc(InitializationDependencies.C.b(), TInt, $h));

function {:inline} InitializationDependencies.C.c() : int
{
  InitializationDependencies.C.b()
}

// C.c: Type axiom
axiom $Is(InitializationDependencies.C.c(), TInt);

// C.c: Allocation axiom
axiom (forall $h: Heap :: 
  { $IsAlloc(InitializationDependencies.C.c(), TInt, $h) } 
  $IsGoodHeap($h) ==> $IsAlloc(InitializationDependencies.C.c(), TInt, $h));

function Tclass.InitializationDependencies.C() : Ty;

const unique Tagclass.InitializationDependencies.C: TyTag;

// Tclass.InitializationDependencies.C Tag
axiom Tag(Tclass.InitializationDependencies.C())
     == Tagclass.InitializationDependencies.C
   && TagFamily(Tclass.InitializationDependencies.C()) == tytagFamily$C;

// Box/unbox axiom for Tclass.InitializationDependencies.C
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.InitializationDependencies.C()) } 
  $IsBox(bx, Tclass.InitializationDependencies.C())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.InitializationDependencies.C()));

// InitializationDependencies.C: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass.InitializationDependencies.C()) } 
  $Is(c#0, Tclass.InitializationDependencies.C())
     <==> $Is(c#0, Tclass.InitializationDependencies.C?()) && c#0 != null);

// InitializationDependencies.C: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass.InitializationDependencies.C(), $h) } 
  $IsAlloc(c#0, Tclass.InitializationDependencies.C(), $h)
     <==> $IsAlloc(c#0, Tclass.InitializationDependencies.C?(), $h));

const unique class.InitializationDependencies.D?: ClassName;

function Tclass.InitializationDependencies.D?() : Ty;

const unique Tagclass.InitializationDependencies.D?: TyTag;

// Tclass.InitializationDependencies.D? Tag
axiom Tag(Tclass.InitializationDependencies.D?())
     == Tagclass.InitializationDependencies.D?
   && TagFamily(Tclass.InitializationDependencies.D?()) == tytagFamily$D;

// Box/unbox axiom for Tclass.InitializationDependencies.D?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.InitializationDependencies.D?()) } 
  $IsBox(bx, Tclass.InitializationDependencies.D?())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.InitializationDependencies.D?()));

// D: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.InitializationDependencies.D?()) } 
  $Is($o, Tclass.InitializationDependencies.D?())
     <==> $o == null || dtype($o) == Tclass.InitializationDependencies.D?());

// D: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.InitializationDependencies.D?(), $h) } 
  $IsAlloc($o, Tclass.InitializationDependencies.D?(), $h)
     <==> $o == null || read($h, $o, alloc));

// D.m: Type axiom
axiom $Is(InitializationDependencies.D.m(), TInt);

// D.m: Allocation axiom
axiom (forall $h: Heap :: 
  { $IsAlloc(InitializationDependencies.D.m(), TInt, $h) } 
  $IsGoodHeap($h) ==> $IsAlloc(InitializationDependencies.D.m(), TInt, $h));

function Tclass.InitializationDependencies.D() : Ty;

const unique Tagclass.InitializationDependencies.D: TyTag;

// Tclass.InitializationDependencies.D Tag
axiom Tag(Tclass.InitializationDependencies.D())
     == Tagclass.InitializationDependencies.D
   && TagFamily(Tclass.InitializationDependencies.D()) == tytagFamily$D;

// Box/unbox axiom for Tclass.InitializationDependencies.D
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.InitializationDependencies.D()) } 
  $IsBox(bx, Tclass.InitializationDependencies.D())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.InitializationDependencies.D()));

// InitializationDependencies.D: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass.InitializationDependencies.D()) } 
  $Is(c#0, Tclass.InitializationDependencies.D())
     <==> $Is(c#0, Tclass.InitializationDependencies.D?()) && c#0 != null);

// InitializationDependencies.D: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass.InitializationDependencies.D(), $h) } 
  $IsAlloc(c#0, Tclass.InitializationDependencies.D(), $h)
     <==> $IsAlloc(c#0, Tclass.InitializationDependencies.D?(), $h));

const unique class.InitializationDependencies.R?: ClassName;

function Tclass.InitializationDependencies.R?() : Ty;

const unique Tagclass.InitializationDependencies.R?: TyTag;

// Tclass.InitializationDependencies.R? Tag
axiom Tag(Tclass.InitializationDependencies.R?())
     == Tagclass.InitializationDependencies.R?
   && TagFamily(Tclass.InitializationDependencies.R?()) == tytagFamily$R;

// Box/unbox axiom for Tclass.InitializationDependencies.R?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.InitializationDependencies.R?()) } 
  $IsBox(bx, Tclass.InitializationDependencies.R?())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.InitializationDependencies.R?()));

// R: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.InitializationDependencies.R?()) } 
  $Is($o, Tclass.InitializationDependencies.R?())
     <==> $o == null || dtype($o) == Tclass.InitializationDependencies.R?());

// R: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.InitializationDependencies.R?(), $h) } 
  $IsAlloc($o, Tclass.InitializationDependencies.R?(), $h)
     <==> $o == null || read($h, $o, alloc));

function {:inline} InitializationDependencies.R.m(this: ref) : int
{
  LitInt(21)
}

function {:inline} InitializationDependencies.R.b(this: ref) : int
{
  InitializationDependencies.R.m(this)
}

function {:inline} InitializationDependencies.R.a(this: ref) : int
{
  InitializationDependencies.R.b(this) + InitializationDependencies.R.b(this)
}

// R.a: Type axiom
axiom (forall $o: ref :: 
  { InitializationDependencies.R.a($o) } 
  $Is(InitializationDependencies.R.a($o), TInt));

// R.a: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { InitializationDependencies.R.a($o), read($h, $o, alloc) } 
  $IsGoodHeap($h) && read($h, $o, alloc)
     ==> $IsAlloc(InitializationDependencies.R.a($o), TInt, $h));

// R.b: Type axiom
axiom (forall $o: ref :: 
  { InitializationDependencies.R.b($o) } 
  $Is(InitializationDependencies.R.b($o), TInt));

// R.b: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { InitializationDependencies.R.b($o), read($h, $o, alloc) } 
  $IsGoodHeap($h) && read($h, $o, alloc)
     ==> $IsAlloc(InitializationDependencies.R.b($o), TInt, $h));

function {:inline} InitializationDependencies.R.c(this: ref) : int
{
  InitializationDependencies.R.b(this)
}

// R.c: Type axiom
axiom (forall $o: ref :: 
  { InitializationDependencies.R.c($o) } 
  $Is(InitializationDependencies.R.c($o), TInt));

// R.c: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { InitializationDependencies.R.c($o), read($h, $o, alloc) } 
  $IsGoodHeap($h) && read($h, $o, alloc)
     ==> $IsAlloc(InitializationDependencies.R.c($o), TInt, $h));

// R.m: Type axiom
axiom (forall $o: ref :: 
  { InitializationDependencies.R.m($o) } 
  $Is(InitializationDependencies.R.m($o), TInt));

// R.m: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { InitializationDependencies.R.m($o), read($h, $o, alloc) } 
  $IsGoodHeap($h) && read($h, $o, alloc)
     ==> $IsAlloc(InitializationDependencies.R.m($o), TInt, $h));

function {:inline} InitializationDependencies.R.n(this: ref) : int
{
  InitializationDependencies.R.F(this, InitializationDependencies.R.b(this))
}

// R.n: Type axiom
axiom (forall $o: ref :: 
  { InitializationDependencies.R.n($o) } 
  $Is(InitializationDependencies.R.n($o), TInt));

// R.n: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { InitializationDependencies.R.n($o), read($h, $o, alloc) } 
  $IsGoodHeap($h) && read($h, $o, alloc)
     ==> $IsAlloc(InitializationDependencies.R.n($o), TInt, $h));

// function declaration for InitializationDependencies.R.F
function InitializationDependencies.R.F(this: ref, nn#0: int) : int;

function InitializationDependencies.R.F#canCall(this: ref, nn#0: int) : bool;

function Tclass.InitializationDependencies.R() : Ty;

const unique Tagclass.InitializationDependencies.R: TyTag;

// Tclass.InitializationDependencies.R Tag
axiom Tag(Tclass.InitializationDependencies.R())
     == Tagclass.InitializationDependencies.R
   && TagFamily(Tclass.InitializationDependencies.R()) == tytagFamily$R;

// Box/unbox axiom for Tclass.InitializationDependencies.R
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.InitializationDependencies.R()) } 
  $IsBox(bx, Tclass.InitializationDependencies.R())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.InitializationDependencies.R()));

// consequence axiom for InitializationDependencies.R.F
axiom true
   ==> (forall this: ref, nn#0: int :: 
    { InitializationDependencies.R.F(this, nn#0) } 
    InitializationDependencies.R.F#canCall(this, nn#0)
         || (this != null && $Is(this, Tclass.InitializationDependencies.R()))
       ==> true);

function InitializationDependencies.R.F#requires(ref, int) : bool;

// #requires axiom for InitializationDependencies.R.F
axiom (forall this: ref, nn#0: int :: 
  { InitializationDependencies.R.F#requires(this, nn#0) } 
  this != null && $Is(this, Tclass.InitializationDependencies.R())
     ==> InitializationDependencies.R.F#requires(this, nn#0) == true);

// definition axiom for InitializationDependencies.R.F (revealed)
axiom true
   ==> (forall this: ref, nn#0: int :: 
    { InitializationDependencies.R.F(this, nn#0) } 
    InitializationDependencies.R.F#canCall(this, nn#0)
         || (this != null && $Is(this, Tclass.InitializationDependencies.R()))
       ==> InitializationDependencies.R.F(this, nn#0)
         == Mul(LitInt(2), nn#0) + InitializationDependencies.C.b());

// definition axiom for InitializationDependencies.R.F for decreasing-related literals (revealed)
axiom true
   ==> (forall this: ref, nn#0: int :: 
    {:weight 3} { InitializationDependencies.R.F(this, LitInt(nn#0)) } 
    InitializationDependencies.R.F#canCall(this, LitInt(nn#0))
         || (this != null && $Is(this, Tclass.InitializationDependencies.R()))
       ==> InitializationDependencies.R.F(this, LitInt(nn#0))
         == Mul(LitInt(2), LitInt(nn#0)) + InitializationDependencies.C.b());

// definition axiom for InitializationDependencies.R.F for all literals (revealed)
axiom true
   ==> (forall this: ref, nn#0: int :: 
    {:weight 3} { InitializationDependencies.R.F(Lit(this), LitInt(nn#0)) } 
    InitializationDependencies.R.F#canCall(Lit(this), LitInt(nn#0))
         || (this != null && $Is(this, Tclass.InitializationDependencies.R()))
       ==> InitializationDependencies.R.F(Lit(this), LitInt(nn#0))
         == Mul(LitInt(2), LitInt(nn#0)) + InitializationDependencies.C.b());

// InitializationDependencies.R: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass.InitializationDependencies.R()) } 
  $Is(c#0, Tclass.InitializationDependencies.R())
     <==> $Is(c#0, Tclass.InitializationDependencies.R?()) && c#0 != null);

// InitializationDependencies.R: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass.InitializationDependencies.R(), $h) } 
  $IsAlloc(c#0, Tclass.InitializationDependencies.R(), $h)
     <==> $IsAlloc(c#0, Tclass.InitializationDependencies.R?(), $h));

const unique class.InitializationDependencies.__default: ClassName;

function Tclass.InitializationDependencies.__default() : Ty;

const unique Tagclass.InitializationDependencies.__default: TyTag;

// Tclass.InitializationDependencies.__default Tag
axiom Tag(Tclass.InitializationDependencies.__default())
     == Tagclass.InitializationDependencies.__default
   && TagFamily(Tclass.InitializationDependencies.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.InitializationDependencies.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.InitializationDependencies.__default()) } 
  $IsBox(bx, Tclass.InitializationDependencies.__default())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.InitializationDependencies.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.InitializationDependencies.__default()) } 
  $Is($o, Tclass.InitializationDependencies.__default())
     <==> $o == null || dtype($o) == Tclass.InitializationDependencies.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.InitializationDependencies.__default(), $h) } 
  $IsAlloc($o, Tclass.InitializationDependencies.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

procedure CheckWellformed$$InitializationDependencies.__default.PrintEm();
  free requires 11 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$InitializationDependencies.__default.PrintEm();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



const unique class.A.__default: ClassName;

function Tclass.A.__default() : Ty;

const unique Tagclass.A.__default: TyTag;

// Tclass.A.__default Tag
axiom Tag(Tclass.A.__default()) == Tagclass.A.__default
   && TagFamily(Tclass.A.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.A.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.A.__default()) } 
  $IsBox(bx, Tclass.A.__default())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.A.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.A.__default()) } 
  $Is($o, Tclass.A.__default())
     <==> $o == null || dtype($o) == Tclass.A.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.A.__default(), $h) } 
  $IsAlloc($o, Tclass.A.__default(), $h) <==> $o == null || read($h, $o, alloc));

function {:inline} A.__default.x() : int
{
  LitInt(100)
}

// _default.x: Type axiom
axiom $Is(A.__default.x(), TInt);

// _default.x: Allocation axiom
axiom (forall $h: Heap :: 
  { $IsAlloc(A.__default.x(), TInt, $h) } 
  $IsGoodHeap($h) ==> $IsAlloc(A.__default.x(), TInt, $h));

const unique class.B.__default: ClassName;

function Tclass.B.__default() : Ty;

const unique Tagclass.B.__default: TyTag;

// Tclass.B.__default Tag
axiom Tag(Tclass.B.__default()) == Tagclass.B.__default
   && TagFamily(Tclass.B.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.B.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.B.__default()) } 
  $IsBox(bx, Tclass.B.__default())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.B.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.B.__default()) } 
  $Is($o, Tclass.B.__default())
     <==> $o == null || dtype($o) == Tclass.B.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.B.__default(), $h) } 
  $IsAlloc($o, Tclass.B.__default(), $h) <==> $o == null || read($h, $o, alloc));

function {:inline} B.__default.x() : int
{
  LitInt(100)
}

// _default.x: Type axiom
axiom $Is(B.__default.x(), TInt);

// _default.x: Allocation axiom
axiom (forall $h: Heap :: 
  { $IsAlloc(B.__default.x(), TInt, $h) } 
  $IsGoodHeap($h) ==> $IsAlloc(B.__default.x(), TInt, $h));

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

const unique tytagFamily$Calendar: TyTagFamily;

const unique tytagFamily$C: TyTagFamily;

const unique tytagFamily$Generic: TyTagFamily;

const unique tytagFamily$Six: TyTagFamily;

const unique tytagFamily$NoRHS: TyTagFamily;

const unique tytagFamily$Trait: TyTagFamily;

const unique tytagFamily$Class: TyTagFamily;

const unique tytagFamily$InstanceInit: TyTagFamily;

const unique tytagFamily$UninterpretedStaticsTrait: TyTagFamily;

const unique tytagFamily$UninterpretedStaticsClass: TyTagFamily;

const unique tytagFamily$byte: TyTagFamily;

const unique tytagFamily$MyClass: TyTagFamily;

const unique tytagFamily$MyOnePurposeClass: TyTagFamily;

const unique tytagFamily$MyGenericClass: TyTagFamily;

const unique tytagFamily$_default: TyTagFamily;

const unique tytagFamily$D: TyTagFamily;

const unique tytagFamily$R: TyTagFamily;

const unique field$z: NameFamily;

const unique field$r: NameFamily;

axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.Class?()) } 
  $o != null && $Is($o, Tclass._module.Class?())
     ==> $Is($o, Tclass._module.Trait()));

axiom (forall $o: ref, $heap: Heap :: 
  { $IsAlloc($o, Tclass._module.Class?(), $heap) } 
  $o != null && $IsAlloc($o, Tclass._module.Class?(), $heap)
     ==> $IsAlloc($o, Tclass._module.Trait(), $heap));

axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.InstanceInit?()) } 
  $o != null && $Is($o, Tclass._module.InstanceInit?())
     ==> $Is($o, Tclass._module.Trait()));

axiom (forall $o: ref, $heap: Heap :: 
  { $IsAlloc($o, Tclass._module.InstanceInit?(), $heap) } 
  $o != null && $IsAlloc($o, Tclass._module.InstanceInit?(), $heap)
     ==> $IsAlloc($o, Tclass._module.Trait(), $heap));

axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.UninterpretedStaticsClass?()) } 
  $o != null && $Is($o, Tclass._module.UninterpretedStaticsClass?())
     ==> $Is($o, Tclass._module.UninterpretedStaticsTrait()));

axiom (forall $o: ref, $heap: Heap :: 
  { $IsAlloc($o, Tclass._module.UninterpretedStaticsClass?(), $heap) } 
  $o != null && $IsAlloc($o, Tclass._module.UninterpretedStaticsClass?(), $heap)
     ==> $IsAlloc($o, Tclass._module.UninterpretedStaticsTrait(), $heap));
