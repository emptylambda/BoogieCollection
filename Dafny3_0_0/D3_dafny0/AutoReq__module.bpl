// Dafny 3.0.0.30204
// Command Line Options: -compile:0 -noVerify /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/AutoReq.dfy -print:./AutoReq.bpl

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

const BaseFuel_OpaqueTest._default.foo: LayerType;

const StartFuel_OpaqueTest._default.foo: LayerType;

const StartFuelAssert_OpaqueTest._default.foo: LayerType;

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

// function declaration for _module._default.f
function _module.__default.f(x#0: int) : bool;

function _module.__default.f#canCall(x#0: int) : bool;

// consequence axiom for _module.__default.f
axiom 0 <= $FunctionContextHeight
   ==> (forall x#0: int :: 
    { _module.__default.f(x#0) } 
    _module.__default.f#canCall(x#0) || (0 != $FunctionContextHeight && x#0 > 3)
       ==> true);

function _module.__default.f#requires(int) : bool;

// #requires axiom for _module.__default.f
axiom (forall x#0: int :: 
  { _module.__default.f#requires(x#0) } 
  _module.__default.f#requires(x#0) == (x#0 > 3));

// definition axiom for _module.__default.f (revealed)
axiom 0 <= $FunctionContextHeight
   ==> (forall x#0: int :: 
    { _module.__default.f(x#0) } 
    _module.__default.f#canCall(x#0) || (0 != $FunctionContextHeight && x#0 > 3)
       ==> _module.__default.f(x#0) == (x#0 > 7));

// definition axiom for _module.__default.f for all literals (revealed)
axiom 0 <= $FunctionContextHeight
   ==> (forall x#0: int :: 
    {:weight 3} { _module.__default.f(LitInt(x#0)) } 
    _module.__default.f#canCall(LitInt(x#0))
         || (0 != $FunctionContextHeight && Lit(x#0 > 3))
       ==> _module.__default.f(LitInt(x#0)) == Lit(x#0 > 7));

procedure CheckWellformed$$_module.__default.f(x#0: int);
  free requires 0 == $FunctionContextHeight;
  modifies $Heap, $Tick;



// function declaration for _module._default.g
function _module.__default.g(y#0: int) : bool;

function _module.__default.g#canCall(y#0: int) : bool;

// consequence axiom for _module.__default.g
axiom 1 <= $FunctionContextHeight
   ==> (forall y#0: int :: 
    { _module.__default.g(y#0) } 
    _module.__default.g#canCall(y#0) || 1 != $FunctionContextHeight ==> true);

function _module.__default.g#requires(int) : bool;

// #requires axiom for _module.__default.g
axiom (forall y#0: int :: 
  { _module.__default.g#requires(y#0) } 
  _module.__default.g#requires(y#0) == true);

// definition axiom for _module.__default.g (revealed)
axiom 1 <= $FunctionContextHeight
   ==> (forall y#0: int :: 
    { _module.__default.g(y#0) } 
    _module.__default.g#canCall(y#0) || 1 != $FunctionContextHeight
       ==> _module.__default.f#canCall(y#0)
         && _module.__default.g(y#0) == _module.__default.f(y#0));

// definition axiom for _module.__default.g for all literals (revealed)
axiom 1 <= $FunctionContextHeight
   ==> (forall y#0: int :: 
    {:weight 3} { _module.__default.g(LitInt(y#0)) } 
    _module.__default.g#canCall(LitInt(y#0)) || 1 != $FunctionContextHeight
       ==> _module.__default.f#canCall(LitInt(y#0))
         && _module.__default.g(LitInt(y#0)) == Lit(_module.__default.f(LitInt(y#0))));

procedure CheckWellformed$$_module.__default.g(y#0: int);
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.g(y#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##x#0: int;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function g
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/AutoReq.dfy(11,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_OpaqueTest._default.foo)
       == StartFuel_OpaqueTest._default.foo;
    assume AsFuelBottom(StartFuelAssert_OpaqueTest._default.foo)
       == StartFuelAssert_OpaqueTest._default.foo;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        ##x#0 := y#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##x#0, TInt, $Heap);
        assert {:subsumption 0} ##x#0 > 3;
        assume ##x#0 > 3;
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.f#canCall(y#0);
        assume _module.__default.g(y#0) == _module.__default.f(y#0);
        assume _module.__default.f#canCall(y#0);
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.g(y#0), TBool);
        assert b$reqreads#0;
    }
}



// function declaration for _module._default.h
function _module.__default.h(y#0: int) : bool;

function _module.__default.h#canCall(y#0: int) : bool;

// consequence axiom for _module.__default.h
axiom 2 <= $FunctionContextHeight
   ==> (forall y#0: int :: 
    { _module.__default.h(y#0) } 
    _module.__default.h#canCall(y#0) || (2 != $FunctionContextHeight && y#0 > 3)
       ==> true);

function _module.__default.h#requires(int) : bool;

// #requires axiom for _module.__default.h
axiom (forall y#0: int :: 
  { _module.__default.h#requires(y#0) } 
  _module.__default.h#requires(y#0) == (y#0 > 3));

// definition axiom for _module.__default.h (revealed)
axiom 2 <= $FunctionContextHeight
   ==> (forall y#0: int :: 
    { _module.__default.h(y#0) } 
    _module.__default.h#canCall(y#0) || (2 != $FunctionContextHeight && y#0 > 3)
       ==> _module.__default.f#canCall(y#0)
         && _module.__default.h(y#0) == _module.__default.f(y#0));

// definition axiom for _module.__default.h for all literals (revealed)
axiom 2 <= $FunctionContextHeight
   ==> (forall y#0: int :: 
    {:weight 3} { _module.__default.h(LitInt(y#0)) } 
    _module.__default.h#canCall(LitInt(y#0))
         || (2 != $FunctionContextHeight && Lit(y#0 > 3))
       ==> _module.__default.f#canCall(LitInt(y#0))
         && _module.__default.h(LitInt(y#0)) == Lit(_module.__default.f(LitInt(y#0))));

procedure {:autoReq} CheckWellformed$$_module.__default.h(y#0: int);
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:autoReq} CheckWellformed$$_module.__default.h(y#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##x#0: int;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function h
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/AutoReq.dfy(17,20): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_OpaqueTest._default.foo)
       == StartFuel_OpaqueTest._default.foo;
    assume AsFuelBottom(StartFuelAssert_OpaqueTest._default.foo)
       == StartFuelAssert_OpaqueTest._default.foo;
    assume y#0 > 3;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        ##x#0 := y#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##x#0, TInt, $Heap);
        assert {:subsumption 0} ##x#0 > 3;
        assume ##x#0 > 3;
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.f#canCall(y#0);
        assume _module.__default.h(y#0) == _module.__default.f(y#0);
        assume _module.__default.f#canCall(y#0);
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.h(y#0), TBool);
        assert b$reqreads#0;
    }
}



// function declaration for _module._default.h_tester
function _module.__default.h__tester() : bool;

function _module.__default.h__tester#canCall() : bool;

// consequence axiom for _module.__default.h__tester
axiom 3 <= $FunctionContextHeight
   ==> 
  _module.__default.h__tester#canCall() || 3 != $FunctionContextHeight
   ==> true;

function _module.__default.h__tester#requires() : bool;

// #requires axiom for _module.__default.h__tester
axiom _module.__default.h__tester#requires() == true;

// definition axiom for _module.__default.h__tester (revealed)
axiom 3 <= $FunctionContextHeight
   ==> 
  _module.__default.h__tester#canCall() || 3 != $FunctionContextHeight
   ==> _module.__default.h#canCall(LitInt(2))
     && _module.__default.h__tester() == Lit(_module.__default.h(LitInt(2)));

// definition axiom for _module.__default.h__tester for all literals (revealed)
axiom 3 <= $FunctionContextHeight
   ==> 
  _module.__default.h__tester#canCall() || 3 != $FunctionContextHeight
   ==> _module.__default.h#canCall(LitInt(2))
     && _module.__default.h__tester() == Lit(_module.__default.h(LitInt(2)));

procedure CheckWellformed$$_module.__default.h__tester();
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.h__tester()
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##y#0: int;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function h_tester
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/AutoReq.dfy(23,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_OpaqueTest._default.foo)
       == StartFuel_OpaqueTest._default.foo;
    assume AsFuelBottom(StartFuelAssert_OpaqueTest._default.foo)
       == StartFuelAssert_OpaqueTest._default.foo;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        ##y#0 := LitInt(2);
        // assume allocatedness for argument to function
        assume $IsAlloc(##y#0, TInt, $Heap);
        assert {:subsumption 0} ##y#0 > 3;
        assume ##y#0 > 3;
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.h#canCall(LitInt(2));
        assume _module.__default.h__tester() == Lit(_module.__default.h(LitInt(2)));
        assume _module.__default.h#canCall(LitInt(2));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.h__tester(), TBool);
        assert b$reqreads#0;
    }
}



// function declaration for _module._default.i
function _module.__default.i(y#0: int, b#0: bool) : bool;

function _module.__default.i#canCall(y#0: int, b#0: bool) : bool;

// consequence axiom for _module.__default.i
axiom 4 <= $FunctionContextHeight
   ==> (forall y#0: int, b#0: bool :: 
    { _module.__default.i(y#0, b#0) } 
    _module.__default.i#canCall(y#0, b#0)
         || (4 != $FunctionContextHeight
           && (if b#0 then y#0 + 2 > 3 else Mul(LitInt(2), y#0) > 3))
       ==> true);

function _module.__default.i#requires(int, bool) : bool;

// #requires axiom for _module.__default.i
axiom (forall y#0: int, b#0: bool :: 
  { _module.__default.i#requires(y#0, b#0) } 
  _module.__default.i#requires(y#0, b#0)
     == (if b#0 then y#0 + 2 > 3 else Mul(LitInt(2), y#0) > 3));

// definition axiom for _module.__default.i (revealed)
axiom 4 <= $FunctionContextHeight
   ==> (forall y#0: int, b#0: bool :: 
    { _module.__default.i(y#0, b#0) } 
    _module.__default.i#canCall(y#0, b#0)
         || (4 != $FunctionContextHeight
           && (if b#0 then y#0 + 2 > 3 else Mul(LitInt(2), y#0) > 3))
       ==> (b#0 ==> _module.__default.f#canCall(y#0 + 2))
         && (!b#0 ==> _module.__default.f#canCall(Mul(LitInt(2), y#0)))
         && _module.__default.i(y#0, b#0)
           == (if b#0
             then _module.__default.f(y#0 + 2)
             else _module.__default.f(Mul(LitInt(2), y#0))));

// definition axiom for _module.__default.i for all literals (revealed)
axiom 4 <= $FunctionContextHeight
   ==> (forall y#0: int, b#0: bool :: 
    {:weight 3} { _module.__default.i(LitInt(y#0), Lit(b#0)) } 
    _module.__default.i#canCall(LitInt(y#0), Lit(b#0))
         || (4 != $FunctionContextHeight
           && (if b#0 then y#0 + 2 > 3 else Mul(LitInt(2), LitInt(y#0)) > 3))
       ==> (Lit(b#0) ==> _module.__default.f#canCall(LitInt(y#0 + 2)))
         && (!Lit(b#0) ==> _module.__default.f#canCall(LitInt(Mul(LitInt(2), LitInt(y#0)))))
         && _module.__default.i(LitInt(y#0), Lit(b#0))
           == (if b#0
             then _module.__default.f(LitInt(y#0 + 2))
             else _module.__default.f(LitInt(Mul(LitInt(2), LitInt(y#0))))));

procedure {:autoReq} CheckWellformed$$_module.__default.i(y#0: int, b#0: bool);
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:autoReq} CheckWellformed$$_module.__default.i(y#0: int, b#0: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##x#0: int;
  var ##x#1: int;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function i
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/AutoReq.dfy(29,20): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_OpaqueTest._default.foo)
       == StartFuel_OpaqueTest._default.foo;
    assume AsFuelBottom(StartFuelAssert_OpaqueTest._default.foo)
       == StartFuelAssert_OpaqueTest._default.foo;
    if (*)
    {
        assume b#0;
        assume y#0 + 2 > 3;
    }
    else
    {
        assume !b#0;
        assume Mul(LitInt(2), y#0) > 3;
    }

    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (b#0)
        {
            ##x#0 := y#0 + 2;
            // assume allocatedness for argument to function
            assume $IsAlloc(##x#0, TInt, $Heap);
            assert {:subsumption 0} ##x#0 > 3;
            assume ##x#0 > 3;
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.f#canCall(y#0 + 2);
            assume _module.__default.i(y#0, b#0) == _module.__default.f(y#0 + 2);
            assume _module.__default.f#canCall(y#0 + 2);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.i(y#0, b#0), TBool);
        }
        else
        {
            ##x#1 := Mul(LitInt(2), y#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##x#1, TInt, $Heap);
            assert {:subsumption 0} ##x#1 > 3;
            assume ##x#1 > 3;
            b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.f#canCall(Mul(LitInt(2), y#0));
            assume _module.__default.i(y#0, b#0) == _module.__default.f(Mul(LitInt(2), y#0));
            assume _module.__default.f#canCall(Mul(LitInt(2), y#0));
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.i(y#0, b#0), TBool);
        }

        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



procedure CheckWellformed$$_module.__default.test();
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.test();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.test() returns ($_reverifyPost: bool);
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.test() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##y#0_0: int;
  var ##b#0_0: bool;
  var ##y#1_0: int;
  var ##b#1_0: bool;
  var ##y#2_0: int;
  var ##b#2_0: bool;
  var ##y#0: int;
  var ##b#0: bool;

    // AddMethodImpl: test, Impl$$_module.__default.test
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_OpaqueTest._default.foo)
       == StartFuel_OpaqueTest._default.foo;
    assume AsFuelBottom(StartFuelAssert_OpaqueTest._default.foo)
       == StartFuelAssert_OpaqueTest._default.foo;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/AutoReq.dfy(35,0): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/AutoReq.dfy(37,3)
    if (*)
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/AutoReq.dfy(38,5)
        ##y#0_0 := LitInt(1);
        // assume allocatedness for argument to function
        assume $IsAlloc(##y#0_0, TInt, $Heap);
        ##b#0_0 := Lit(true);
        // assume allocatedness for argument to function
        assume $IsAlloc(##b#0_0, TBool, $Heap);
        assert {:subsumption 0} ##b#0_0 ==> ##y#0_0 + 2 > 3;
        assert {:subsumption 0} !##b#0_0 ==> Mul(LitInt(2), ##y#0_0) > 3;
        assume _module.__default.i#canCall(LitInt(1), Lit(true));
        assume _module.__default.i#canCall(LitInt(1), Lit(true));
        assert {:subsumption 0} _module.__default.i#canCall(LitInt(1), Lit(true))
           ==> Lit(_module.__default.i(LitInt(1), Lit(true)))
             || (Lit(true)
               ==> 
              _module.__default.f#canCall(LitInt(1 + 2))
               ==> Lit(_module.__default.f(LitInt(1 + 2))) || Lit(1 + 2 > 7));
        assert {:subsumption 0} _module.__default.i#canCall(LitInt(1), Lit(true))
           ==> Lit(_module.__default.i(LitInt(1), Lit(true)))
             || (!Lit(true)
               ==> 
              _module.__default.f#canCall(LitInt(Mul(LitInt(2), LitInt(1))))
               ==> Lit(_module.__default.f(LitInt(Mul(LitInt(2), LitInt(1)))))
                 || Lit(Mul(LitInt(2), LitInt(1)) > 7));
        assume _module.__default.i(LitInt(1), Lit(true));
    }
    else
    {
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/AutoReq.dfy(39,10)
        if (*)
        {
            // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/AutoReq.dfy(40,5)
            ##y#1_0 := LitInt(0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##y#1_0, TInt, $Heap);
            ##b#1_0 := Lit(false);
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#1_0, TBool, $Heap);
            assert {:subsumption 0} ##b#1_0 ==> ##y#1_0 + 2 > 3;
            assert {:subsumption 0} !##b#1_0 ==> Mul(LitInt(2), ##y#1_0) > 3;
            assume _module.__default.i#canCall(LitInt(0), Lit(false));
            assume _module.__default.i#canCall(LitInt(0), Lit(false));
            assert {:subsumption 0} _module.__default.i#canCall(LitInt(0), Lit(false))
               ==> Lit(_module.__default.i(LitInt(0), Lit(false)))
                 || (Lit(false)
                   ==> 
                  _module.__default.f#canCall(LitInt(0 + 2))
                   ==> Lit(_module.__default.f(LitInt(0 + 2))) || Lit(0 + 2 > 7));
            assert {:subsumption 0} _module.__default.i#canCall(LitInt(0), Lit(false))
               ==> Lit(_module.__default.i(LitInt(0), Lit(false)))
                 || (!Lit(false)
                   ==> 
                  _module.__default.f#canCall(LitInt(Mul(LitInt(2), LitInt(0))))
                   ==> Lit(_module.__default.f(LitInt(Mul(LitInt(2), LitInt(0)))))
                     || Lit(Mul(LitInt(2), LitInt(0)) > 7));
            assume _module.__default.i(LitInt(0), Lit(false));
        }
        else
        {
        }
    }

    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/AutoReq.dfy(44,3)
    if (*)
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/AutoReq.dfy(45,5)
        ##y#2_0 := LitInt(3);
        // assume allocatedness for argument to function
        assume $IsAlloc(##y#2_0, TInt, $Heap);
        ##b#2_0 := Lit(true);
        // assume allocatedness for argument to function
        assume $IsAlloc(##b#2_0, TBool, $Heap);
        assert {:subsumption 0} ##b#2_0 ==> ##y#2_0 + 2 > 3;
        assert {:subsumption 0} !##b#2_0 ==> Mul(LitInt(2), ##y#2_0) > 3;
        assume _module.__default.i#canCall(LitInt(3), Lit(true));
        assume _module.__default.i#canCall(LitInt(3), Lit(true));
        assert {:subsumption 0} _module.__default.i#canCall(LitInt(3), Lit(true))
           ==> Lit(_module.__default.i(LitInt(3), Lit(true)))
             || (Lit(true)
               ==> 
              _module.__default.f#canCall(LitInt(3 + 2))
               ==> Lit(_module.__default.f(LitInt(3 + 2))) || Lit(3 + 2 > 7));
        assert {:subsumption 0} _module.__default.i#canCall(LitInt(3), Lit(true))
           ==> Lit(_module.__default.i(LitInt(3), Lit(true)))
             || (!Lit(true)
               ==> 
              _module.__default.f#canCall(LitInt(Mul(LitInt(2), LitInt(3))))
               ==> Lit(_module.__default.f(LitInt(Mul(LitInt(2), LitInt(3)))))
                 || Lit(Mul(LitInt(2), LitInt(3)) > 7));
        assume _module.__default.i(LitInt(3), Lit(true));
    }
    else
    {
    }

    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/AutoReq.dfy(47,3)
    ##y#0 := LitInt(7);
    // assume allocatedness for argument to function
    assume $IsAlloc(##y#0, TInt, $Heap);
    ##b#0 := Lit(false);
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#0, TBool, $Heap);
    assert {:subsumption 0} ##b#0 ==> ##y#0 + 2 > 3;
    assert {:subsumption 0} !##b#0 ==> Mul(LitInt(2), ##y#0) > 3;
    assume _module.__default.i#canCall(LitInt(7), Lit(false));
    assume _module.__default.i#canCall(LitInt(7), Lit(false));
    assert {:subsumption 0} _module.__default.i#canCall(LitInt(7), Lit(false))
       ==> Lit(_module.__default.i(LitInt(7), Lit(false)))
         || (Lit(false)
           ==> 
          _module.__default.f#canCall(LitInt(7 + 2))
           ==> Lit(_module.__default.f(LitInt(7 + 2))) || Lit(7 + 2 > 7));
    assert {:subsumption 0} _module.__default.i#canCall(LitInt(7), Lit(false))
       ==> Lit(_module.__default.i(LitInt(7), Lit(false)))
         || (!Lit(false)
           ==> 
          _module.__default.f#canCall(LitInt(Mul(LitInt(2), LitInt(7))))
           ==> Lit(_module.__default.f(LitInt(Mul(LitInt(2), LitInt(7)))))
             || Lit(Mul(LitInt(2), LitInt(7)) > 7));
    assume _module.__default.i(LitInt(7), Lit(false));
}



const unique class.TwoLayersOfRequires.__default: ClassName;

function Tclass.TwoLayersOfRequires.__default() : Ty;

const unique Tagclass.TwoLayersOfRequires.__default: TyTag;

// Tclass.TwoLayersOfRequires.__default Tag
axiom Tag(Tclass.TwoLayersOfRequires.__default())
     == Tagclass.TwoLayersOfRequires.__default
   && TagFamily(Tclass.TwoLayersOfRequires.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.TwoLayersOfRequires.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.TwoLayersOfRequires.__default()) } 
  $IsBox(bx, Tclass.TwoLayersOfRequires.__default())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.TwoLayersOfRequires.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.TwoLayersOfRequires.__default()) } 
  $Is($o, Tclass.TwoLayersOfRequires.__default())
     <==> $o == null || dtype($o) == Tclass.TwoLayersOfRequires.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.TwoLayersOfRequires.__default(), $h) } 
  $IsAlloc($o, Tclass.TwoLayersOfRequires.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

// function declaration for TwoLayersOfRequires._default.f
function TwoLayersOfRequires.__default.f(x#0: int) : bool;

function TwoLayersOfRequires.__default.f#canCall(x#0: int) : bool;

// consequence axiom for TwoLayersOfRequires.__default.f
axiom true
   ==> (forall x#0: int :: 
    { TwoLayersOfRequires.__default.f(x#0) } 
    TwoLayersOfRequires.__default.f#canCall(x#0) || x#0 > 4 ==> true);

function TwoLayersOfRequires.__default.f#requires(int) : bool;

// #requires axiom for TwoLayersOfRequires.__default.f
axiom (forall x#0: int :: 
  { TwoLayersOfRequires.__default.f#requires(x#0) } 
  TwoLayersOfRequires.__default.f#requires(x#0) == (x#0 > 4));

// definition axiom for TwoLayersOfRequires.__default.f (revealed)
axiom true
   ==> (forall x#0: int :: 
    { TwoLayersOfRequires.__default.f(x#0) } 
    TwoLayersOfRequires.__default.f#canCall(x#0) || x#0 > 4
       ==> TwoLayersOfRequires.__default.f(x#0) == (x#0 > 5));

// definition axiom for TwoLayersOfRequires.__default.f for all literals (revealed)
axiom true
   ==> (forall x#0: int :: 
    {:weight 3} { TwoLayersOfRequires.__default.f(LitInt(x#0)) } 
    TwoLayersOfRequires.__default.f#canCall(LitInt(x#0)) || Lit(x#0 > 4)
       ==> TwoLayersOfRequires.__default.f(LitInt(x#0)) == Lit(x#0 > 5));

// function declaration for TwoLayersOfRequires._default.g
function TwoLayersOfRequires.__default.g(y#0: int) : bool;

function TwoLayersOfRequires.__default.g#canCall(y#0: int) : bool;

// consequence axiom for TwoLayersOfRequires.__default.g
axiom true
   ==> (forall y#0: int :: 
    { TwoLayersOfRequires.__default.g(y#0) } 
    TwoLayersOfRequires.__default.g#canCall(y#0) || (y#0 < 50 && y#0 > 4) ==> true);

function TwoLayersOfRequires.__default.g#requires(int) : bool;

// #requires axiom for TwoLayersOfRequires.__default.g
axiom (forall y#0: int :: 
  { TwoLayersOfRequires.__default.g#requires(y#0) } 
  TwoLayersOfRequires.__default.g#requires(y#0) == (y#0 < 50 && y#0 > 4));

// definition axiom for TwoLayersOfRequires.__default.g (revealed)
axiom true
   ==> (forall y#0: int :: 
    { TwoLayersOfRequires.__default.g(y#0) } 
    TwoLayersOfRequires.__default.g#canCall(y#0) || (y#0 < 50 && y#0 > 4)
       ==> TwoLayersOfRequires.__default.f#canCall(y#0)
         && TwoLayersOfRequires.__default.g(y#0) == TwoLayersOfRequires.__default.f(y#0));

// definition axiom for TwoLayersOfRequires.__default.g for all literals (revealed)
axiom true
   ==> (forall y#0: int :: 
    {:weight 3} { TwoLayersOfRequires.__default.g(LitInt(y#0)) } 
    TwoLayersOfRequires.__default.g#canCall(LitInt(y#0))
         || (Lit(y#0 < 50) && Lit(y#0 > 4))
       ==> TwoLayersOfRequires.__default.f#canCall(LitInt(y#0))
         && TwoLayersOfRequires.__default.g(LitInt(y#0))
           == Lit(TwoLayersOfRequires.__default.f(LitInt(y#0))));

// function declaration for TwoLayersOfRequires._default.h
function TwoLayersOfRequires.__default.h(z#0: int) : bool;

function TwoLayersOfRequires.__default.h#canCall(z#0: int) : bool;

// consequence axiom for TwoLayersOfRequires.__default.h
axiom true
   ==> (forall z#0: int :: 
    { TwoLayersOfRequires.__default.h(z#0) } 
    TwoLayersOfRequires.__default.h#canCall(z#0) || (z#0 < 50 && z#0 > 4) ==> true);

function TwoLayersOfRequires.__default.h#requires(int) : bool;

// #requires axiom for TwoLayersOfRequires.__default.h
axiom (forall z#0: int :: 
  { TwoLayersOfRequires.__default.h#requires(z#0) } 
  TwoLayersOfRequires.__default.h#requires(z#0) == (z#0 < 50 && z#0 > 4));

// definition axiom for TwoLayersOfRequires.__default.h (revealed)
axiom true
   ==> (forall z#0: int :: 
    { TwoLayersOfRequires.__default.h(z#0) } 
    TwoLayersOfRequires.__default.h#canCall(z#0) || (z#0 < 50 && z#0 > 4)
       ==> TwoLayersOfRequires.__default.g#canCall(z#0)
         && TwoLayersOfRequires.__default.h(z#0) == TwoLayersOfRequires.__default.g(z#0));

// definition axiom for TwoLayersOfRequires.__default.h for all literals (revealed)
axiom true
   ==> (forall z#0: int :: 
    {:weight 3} { TwoLayersOfRequires.__default.h(LitInt(z#0)) } 
    TwoLayersOfRequires.__default.h#canCall(LitInt(z#0))
         || (Lit(z#0 < 50) && Lit(z#0 > 4))
       ==> TwoLayersOfRequires.__default.g#canCall(LitInt(z#0))
         && TwoLayersOfRequires.__default.h(LitInt(z#0))
           == Lit(TwoLayersOfRequires.__default.g(LitInt(z#0))));

const unique class.QuantifierTestsSimple.__default: ClassName;

function Tclass.QuantifierTestsSimple.__default() : Ty;

const unique Tagclass.QuantifierTestsSimple.__default: TyTag;

// Tclass.QuantifierTestsSimple.__default Tag
axiom Tag(Tclass.QuantifierTestsSimple.__default())
     == Tagclass.QuantifierTestsSimple.__default
   && TagFamily(Tclass.QuantifierTestsSimple.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.QuantifierTestsSimple.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.QuantifierTestsSimple.__default()) } 
  $IsBox(bx, Tclass.QuantifierTestsSimple.__default())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.QuantifierTestsSimple.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.QuantifierTestsSimple.__default()) } 
  $Is($o, Tclass.QuantifierTestsSimple.__default())
     <==> $o == null || dtype($o) == Tclass.QuantifierTestsSimple.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.QuantifierTestsSimple.__default(), $h) } 
  $IsAlloc($o, Tclass.QuantifierTestsSimple.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

// function declaration for QuantifierTestsSimple._default.byte
function QuantifierTestsSimple.__default.byte(x#0: int) : bool;

function QuantifierTestsSimple.__default.byte#canCall(x#0: int) : bool;

// consequence axiom for QuantifierTestsSimple.__default.byte
axiom true
   ==> (forall x#0: int :: { QuantifierTestsSimple.__default.byte(x#0) } true ==> true);

function QuantifierTestsSimple.__default.byte#requires(int) : bool;

// #requires axiom for QuantifierTestsSimple.__default.byte
axiom (forall x#0: int :: 
  { QuantifierTestsSimple.__default.byte#requires(x#0) } 
  QuantifierTestsSimple.__default.byte#requires(x#0) == true);

// definition axiom for QuantifierTestsSimple.__default.byte (revealed)
axiom true
   ==> (forall x#0: int :: 
    { QuantifierTestsSimple.__default.byte(x#0) } 
    true
       ==> QuantifierTestsSimple.__default.byte(x#0) == (LitInt(0) <= x#0 && x#0 < 256));

// definition axiom for QuantifierTestsSimple.__default.byte for all literals (revealed)
axiom true
   ==> (forall x#0: int :: 
    {:weight 3} { QuantifierTestsSimple.__default.byte(LitInt(x#0)) } 
    true
       ==> QuantifierTestsSimple.__default.byte(LitInt(x#0))
         == (LitInt(0) <= LitInt(x#0) && x#0 < 256));

// function declaration for QuantifierTestsSimple._default.f_forall
function QuantifierTestsSimple.__default.f__forall(s#0: Seq Box) : bool;

function QuantifierTestsSimple.__default.f__forall#canCall(s#0: Seq Box) : bool;

// consequence axiom for QuantifierTestsSimple.__default.f__forall
axiom true
   ==> (forall s#0: Seq Box :: 
    { QuantifierTestsSimple.__default.f__forall(s#0) } 
    QuantifierTestsSimple.__default.f__forall#canCall(s#0) || $Is(s#0, TSeq(TInt))
       ==> true);

function QuantifierTestsSimple.__default.f__forall#requires(Seq Box) : bool;

// #requires axiom for QuantifierTestsSimple.__default.f__forall
axiom (forall s#0: Seq Box :: 
  { QuantifierTestsSimple.__default.f__forall#requires(s#0) } 
  $Is(s#0, TSeq(TInt))
     ==> QuantifierTestsSimple.__default.f__forall#requires(s#0) == true);

// definition axiom for QuantifierTestsSimple.__default.f__forall (revealed)
axiom true
   ==> (forall s#0: Seq Box :: 
    { QuantifierTestsSimple.__default.f__forall(s#0) } 
    QuantifierTestsSimple.__default.f__forall#canCall(s#0) || $Is(s#0, TSeq(TInt))
       ==> (forall i#4: int :: 
          { $Unbox(Seq#Index(s#0, i#4)): int } 
          LitInt(0) <= i#4
             ==> 
            i#4 < Seq#Length(s#0)
             ==> QuantifierTestsSimple.__default.byte#canCall($Unbox(Seq#Index(s#0, i#4)): int))
         && QuantifierTestsSimple.__default.f__forall(s#0)
           == (forall i#4: int :: 
            { $Unbox(Seq#Index(s#0, i#4)): int } 
            true
               ==> 
              LitInt(0) <= i#4 && i#4 < Seq#Length(s#0)
               ==> QuantifierTestsSimple.__default.byte($Unbox(Seq#Index(s#0, i#4)): int)));

// definition axiom for QuantifierTestsSimple.__default.f__forall for all literals (revealed)
axiom true
   ==> (forall s#0: Seq Box :: 
    {:weight 3} { QuantifierTestsSimple.__default.f__forall(Lit(s#0)) } 
    QuantifierTestsSimple.__default.f__forall#canCall(Lit(s#0))
         || $Is(s#0, TSeq(TInt))
       ==> (forall i#5: int :: 
          { $Unbox(Seq#Index(s#0, i#5)): int } 
          LitInt(0) <= i#5
             ==> 
            i#5 < Seq#Length(Lit(s#0))
             ==> QuantifierTestsSimple.__default.byte#canCall($Unbox(Seq#Index(Lit(s#0), i#5)): int))
         && QuantifierTestsSimple.__default.f__forall(Lit(s#0))
           == (forall i#5: int :: 
            { $Unbox(Seq#Index(s#0, i#5)): int } 
            true
               ==> 
              LitInt(0) <= i#5 && i#5 < Seq#Length(Lit(s#0))
               ==> QuantifierTestsSimple.__default.byte($Unbox(Seq#Index(Lit(s#0), i#5)): int)));

// function declaration for QuantifierTestsSimple._default.f_exists
function QuantifierTestsSimple.__default.f__exists(s#0: Seq Box) : bool;

function QuantifierTestsSimple.__default.f__exists#canCall(s#0: Seq Box) : bool;

// consequence axiom for QuantifierTestsSimple.__default.f__exists
axiom true
   ==> (forall s#0: Seq Box :: 
    { QuantifierTestsSimple.__default.f__exists(s#0) } 
    QuantifierTestsSimple.__default.f__exists#canCall(s#0) || $Is(s#0, TSeq(TInt))
       ==> true);

function QuantifierTestsSimple.__default.f__exists#requires(Seq Box) : bool;

// #requires axiom for QuantifierTestsSimple.__default.f__exists
axiom (forall s#0: Seq Box :: 
  { QuantifierTestsSimple.__default.f__exists#requires(s#0) } 
  $Is(s#0, TSeq(TInt))
     ==> QuantifierTestsSimple.__default.f__exists#requires(s#0) == true);

// definition axiom for QuantifierTestsSimple.__default.f__exists (revealed)
axiom true
   ==> (forall s#0: Seq Box :: 
    { QuantifierTestsSimple.__default.f__exists(s#0) } 
    QuantifierTestsSimple.__default.f__exists#canCall(s#0) || $Is(s#0, TSeq(TInt))
       ==> (forall i#4: int :: 
          { $Unbox(Seq#Index(s#0, i#4)): int } 
          LitInt(0) <= i#4
             ==> 
            i#4 < Seq#Length(s#0)
             ==> QuantifierTestsSimple.__default.byte#canCall($Unbox(Seq#Index(s#0, i#4)): int))
         && QuantifierTestsSimple.__default.f__exists(s#0)
           == (exists i#4: int :: 
            { $Unbox(Seq#Index(s#0, i#4)): int } 
            LitInt(0) <= i#4
               && i#4 < Seq#Length(s#0)
               && QuantifierTestsSimple.__default.byte($Unbox(Seq#Index(s#0, i#4)): int)));

// definition axiom for QuantifierTestsSimple.__default.f__exists for all literals (revealed)
axiom true
   ==> (forall s#0: Seq Box :: 
    {:weight 3} { QuantifierTestsSimple.__default.f__exists(Lit(s#0)) } 
    QuantifierTestsSimple.__default.f__exists#canCall(Lit(s#0))
         || $Is(s#0, TSeq(TInt))
       ==> (forall i#5: int :: 
          { $Unbox(Seq#Index(s#0, i#5)): int } 
          LitInt(0) <= i#5
             ==> 
            i#5 < Seq#Length(Lit(s#0))
             ==> QuantifierTestsSimple.__default.byte#canCall($Unbox(Seq#Index(Lit(s#0), i#5)): int))
         && QuantifierTestsSimple.__default.f__exists(Lit(s#0))
           == (exists i#5: int :: 
            { $Unbox(Seq#Index(s#0, i#5)): int } 
            LitInt(0) <= i#5
               && i#5 < Seq#Length(Lit(s#0))
               && QuantifierTestsSimple.__default.byte($Unbox(Seq#Index(Lit(s#0), i#5)): int)));

// function declaration for QuantifierTestsSimple._default.g_forall
function QuantifierTestsSimple.__default.g__forall(s#0: Seq Box) : bool;

function QuantifierTestsSimple.__default.g__forall#canCall(s#0: Seq Box) : bool;

// consequence axiom for QuantifierTestsSimple.__default.g__forall
axiom true
   ==> (forall s#0: Seq Box :: 
    { QuantifierTestsSimple.__default.g__forall(s#0) } 
    QuantifierTestsSimple.__default.g__forall#canCall(s#0)
         || ($Is(s#0, TSeq(TInt)) && QuantifierTestsSimple.__default.f__forall(s#0))
       ==> true);

function QuantifierTestsSimple.__default.g__forall#requires(Seq Box) : bool;

// #requires axiom for QuantifierTestsSimple.__default.g__forall
axiom (forall s#0: Seq Box :: 
  { QuantifierTestsSimple.__default.g__forall#requires(s#0) } 
  $Is(s#0, TSeq(TInt))
     ==> QuantifierTestsSimple.__default.g__forall#requires(s#0)
       == QuantifierTestsSimple.__default.f__forall(s#0));

// definition axiom for QuantifierTestsSimple.__default.g__forall (revealed)
axiom true
   ==> (forall s#0: Seq Box :: 
    { QuantifierTestsSimple.__default.g__forall(s#0) } 
    QuantifierTestsSimple.__default.g__forall#canCall(s#0)
         || ($Is(s#0, TSeq(TInt)) && QuantifierTestsSimple.__default.f__forall(s#0))
       ==> QuantifierTestsSimple.__default.g__forall(s#0) == (Seq#Length(s#0) > 2));

// definition axiom for QuantifierTestsSimple.__default.g__forall for all literals (revealed)
axiom true
   ==> (forall s#0: Seq Box :: 
    {:weight 3} { QuantifierTestsSimple.__default.g__forall(Lit(s#0)) } 
    QuantifierTestsSimple.__default.g__forall#canCall(Lit(s#0))
         || ($Is(s#0, TSeq(TInt))
           && Lit(QuantifierTestsSimple.__default.f__forall(Lit(s#0))))
       ==> QuantifierTestsSimple.__default.g__forall(Lit(s#0))
         == (Seq#Length(Lit(s#0)) > 2));

// function declaration for QuantifierTestsSimple._default.g_exists
function QuantifierTestsSimple.__default.g__exists(s#0: Seq Box) : bool;

function QuantifierTestsSimple.__default.g__exists#canCall(s#0: Seq Box) : bool;

// consequence axiom for QuantifierTestsSimple.__default.g__exists
axiom true
   ==> (forall s#0: Seq Box :: 
    { QuantifierTestsSimple.__default.g__exists(s#0) } 
    QuantifierTestsSimple.__default.g__exists#canCall(s#0)
         || ($Is(s#0, TSeq(TInt)) && QuantifierTestsSimple.__default.f__exists(s#0))
       ==> true);

function QuantifierTestsSimple.__default.g__exists#requires(Seq Box) : bool;

// #requires axiom for QuantifierTestsSimple.__default.g__exists
axiom (forall s#0: Seq Box :: 
  { QuantifierTestsSimple.__default.g__exists#requires(s#0) } 
  $Is(s#0, TSeq(TInt))
     ==> QuantifierTestsSimple.__default.g__exists#requires(s#0)
       == QuantifierTestsSimple.__default.f__exists(s#0));

// definition axiom for QuantifierTestsSimple.__default.g__exists (revealed)
axiom true
   ==> (forall s#0: Seq Box :: 
    { QuantifierTestsSimple.__default.g__exists(s#0) } 
    QuantifierTestsSimple.__default.g__exists#canCall(s#0)
         || ($Is(s#0, TSeq(TInt)) && QuantifierTestsSimple.__default.f__exists(s#0))
       ==> QuantifierTestsSimple.__default.g__exists(s#0) == (Seq#Length(s#0) > 2));

// definition axiom for QuantifierTestsSimple.__default.g__exists for all literals (revealed)
axiom true
   ==> (forall s#0: Seq Box :: 
    {:weight 3} { QuantifierTestsSimple.__default.g__exists(Lit(s#0)) } 
    QuantifierTestsSimple.__default.g__exists#canCall(Lit(s#0))
         || ($Is(s#0, TSeq(TInt))
           && Lit(QuantifierTestsSimple.__default.f__exists(Lit(s#0))))
       ==> QuantifierTestsSimple.__default.g__exists(Lit(s#0))
         == (Seq#Length(Lit(s#0)) > 2));

// function declaration for QuantifierTestsSimple._default.h
function QuantifierTestsSimple.__default.h(s#0: Seq Box) : bool;

function QuantifierTestsSimple.__default.h#canCall(s#0: Seq Box) : bool;

// consequence axiom for QuantifierTestsSimple.__default.h
axiom true
   ==> (forall s#0: Seq Box :: 
    { QuantifierTestsSimple.__default.h(s#0) } 
    QuantifierTestsSimple.__default.h#canCall(s#0)
         || ($Is(s#0, TSeq(TInt))
           && 
          QuantifierTestsSimple.__default.f__forall(s#0)
           && (QuantifierTestsSimple.__default.g__forall(s#0)
             ==> QuantifierTestsSimple.__default.f__exists(s#0)))
       ==> true);

function QuantifierTestsSimple.__default.h#requires(Seq Box) : bool;

// #requires axiom for QuantifierTestsSimple.__default.h
axiom (forall s#0: Seq Box :: 
  { QuantifierTestsSimple.__default.h#requires(s#0) } 
  $Is(s#0, TSeq(TInt))
     ==> QuantifierTestsSimple.__default.h#requires(s#0)
       == (QuantifierTestsSimple.__default.f__forall(s#0)
         && (QuantifierTestsSimple.__default.g__forall(s#0)
           ==> QuantifierTestsSimple.__default.f__exists(s#0))));

// definition axiom for QuantifierTestsSimple.__default.h (revealed)
axiom true
   ==> (forall s#0: Seq Box :: 
    { QuantifierTestsSimple.__default.h(s#0) } 
    QuantifierTestsSimple.__default.h#canCall(s#0)
         || ($Is(s#0, TSeq(TInt))
           && 
          QuantifierTestsSimple.__default.f__forall(s#0)
           && (QuantifierTestsSimple.__default.g__forall(s#0)
             ==> QuantifierTestsSimple.__default.f__exists(s#0)))
       ==> QuantifierTestsSimple.__default.g__forall#canCall(s#0)
         && (QuantifierTestsSimple.__default.g__forall(s#0)
           ==> QuantifierTestsSimple.__default.g__exists#canCall(s#0))
         && QuantifierTestsSimple.__default.h(s#0)
           == (QuantifierTestsSimple.__default.g__forall(s#0)
             && QuantifierTestsSimple.__default.g__exists(s#0)));

// definition axiom for QuantifierTestsSimple.__default.h for all literals (revealed)
axiom true
   ==> (forall s#0: Seq Box :: 
    {:weight 3} { QuantifierTestsSimple.__default.h(Lit(s#0)) } 
    QuantifierTestsSimple.__default.h#canCall(Lit(s#0))
         || ($Is(s#0, TSeq(TInt))
           && 
          Lit(QuantifierTestsSimple.__default.f__forall(Lit(s#0)))
           && Lit(QuantifierTestsSimple.__default.g__forall(Lit(s#0))
               ==> QuantifierTestsSimple.__default.f__exists(Lit(s#0))))
       ==> QuantifierTestsSimple.__default.g__forall#canCall(Lit(s#0))
         && (Lit(QuantifierTestsSimple.__default.g__forall(Lit(s#0)))
           ==> QuantifierTestsSimple.__default.g__exists#canCall(Lit(s#0)))
         && QuantifierTestsSimple.__default.h(Lit(s#0))
           == Lit(QuantifierTestsSimple.__default.g__forall(Lit(s#0))
               && QuantifierTestsSimple.__default.g__exists(Lit(s#0))));

const unique class.QuantifierTestsHard.__default: ClassName;

function Tclass.QuantifierTestsHard.__default() : Ty;

const unique Tagclass.QuantifierTestsHard.__default: TyTag;

// Tclass.QuantifierTestsHard.__default Tag
axiom Tag(Tclass.QuantifierTestsHard.__default())
     == Tagclass.QuantifierTestsHard.__default
   && TagFamily(Tclass.QuantifierTestsHard.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.QuantifierTestsHard.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.QuantifierTestsHard.__default()) } 
  $IsBox(bx, Tclass.QuantifierTestsHard.__default())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.QuantifierTestsHard.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.QuantifierTestsHard.__default()) } 
  $Is($o, Tclass.QuantifierTestsHard.__default())
     <==> $o == null || dtype($o) == Tclass.QuantifierTestsHard.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.QuantifierTestsHard.__default(), $h) } 
  $IsAlloc($o, Tclass.QuantifierTestsHard.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

// function declaration for QuantifierTestsHard._default.byte
function QuantifierTestsHard.__default.byte(x#0: int) : bool;

function QuantifierTestsHard.__default.byte#canCall(x#0: int) : bool;

// consequence axiom for QuantifierTestsHard.__default.byte
axiom true
   ==> (forall x#0: int :: 
    { QuantifierTestsHard.__default.byte(x#0) } 
    QuantifierTestsHard.__default.byte#canCall(x#0)
         || (LitInt(0) <= x#0 && x#0 < 256)
       ==> true);

function QuantifierTestsHard.__default.byte#requires(int) : bool;

// #requires axiom for QuantifierTestsHard.__default.byte
axiom (forall x#0: int :: 
  { QuantifierTestsHard.__default.byte#requires(x#0) } 
  QuantifierTestsHard.__default.byte#requires(x#0)
     == (LitInt(0) <= x#0 && x#0 < 256));

// definition axiom for QuantifierTestsHard.__default.byte (revealed)
axiom true
   ==> (forall x#0: int :: 
    { QuantifierTestsHard.__default.byte(x#0) } 
    QuantifierTestsHard.__default.byte#canCall(x#0)
         || (LitInt(0) <= x#0 && x#0 < 256)
       ==> QuantifierTestsHard.__default.byte(x#0) == Lit(true));

// definition axiom for QuantifierTestsHard.__default.byte for all literals (revealed)
axiom true
   ==> (forall x#0: int :: 
    {:weight 3} { QuantifierTestsHard.__default.byte(LitInt(x#0)) } 
    QuantifierTestsHard.__default.byte#canCall(LitInt(x#0))
         || (LitInt(0) <= LitInt(x#0) && x#0 < 256)
       ==> QuantifierTestsHard.__default.byte(LitInt(x#0)) == Lit(true));

// function declaration for QuantifierTestsHard._default.f_forall
function QuantifierTestsHard.__default.f__forall(s#0: Seq Box) : bool;

function QuantifierTestsHard.__default.f__forall#canCall(s#0: Seq Box) : bool;

// consequence axiom for QuantifierTestsHard.__default.f__forall
axiom true
   ==> (forall s#0: Seq Box :: 
    { QuantifierTestsHard.__default.f__forall(s#0) } 
    QuantifierTestsHard.__default.f__forall#canCall(s#0) || $Is(s#0, TSeq(TInt))
       ==> true);

function QuantifierTestsHard.__default.f__forall#requires(Seq Box) : bool;

// #requires axiom for QuantifierTestsHard.__default.f__forall
axiom (forall s#0: Seq Box :: 
  { QuantifierTestsHard.__default.f__forall#requires(s#0) } 
  $Is(s#0, TSeq(TInt))
     ==> QuantifierTestsHard.__default.f__forall#requires(s#0) == true);

// definition axiom for QuantifierTestsHard.__default.f__forall (revealed)
axiom true
   ==> (forall s#0: Seq Box :: 
    { QuantifierTestsHard.__default.f__forall(s#0) } 
    QuantifierTestsHard.__default.f__forall#canCall(s#0) || $Is(s#0, TSeq(TInt))
       ==> (forall i#4: int :: 
          { $Unbox(Seq#Index(s#0, i#4)): int } 
          (LitInt(0) <= i#4 && i#4 < Seq#Length(s#0)
             ==> LitInt(0) <= $Unbox(Seq#Index(s#0, i#4)): int
               && $Unbox(Seq#Index(s#0, i#4)): int < 256)
             ==> 
            LitInt(0) <= i#4
             ==> 
            i#4 < Seq#Length(s#0)
             ==> QuantifierTestsHard.__default.byte#canCall($Unbox(Seq#Index(s#0, i#4)): int))
         && QuantifierTestsHard.__default.f__forall(s#0)
           == (forall i#4: int :: 
            { $Unbox(Seq#Index(s#0, i#4)): int } 
            true
               ==> (LitInt(0) <= i#4 && i#4 < Seq#Length(s#0)
                   ==> LitInt(0) <= $Unbox(Seq#Index(s#0, i#4)): int
                     && $Unbox(Seq#Index(s#0, i#4)): int < 256)
                 && (LitInt(0) <= i#4 && i#4 < Seq#Length(s#0)
                   ==> QuantifierTestsHard.__default.byte($Unbox(Seq#Index(s#0, i#4)): int))));

// definition axiom for QuantifierTestsHard.__default.f__forall for all literals (revealed)
axiom true
   ==> (forall s#0: Seq Box :: 
    {:weight 3} { QuantifierTestsHard.__default.f__forall(Lit(s#0)) } 
    QuantifierTestsHard.__default.f__forall#canCall(Lit(s#0))
         || $Is(s#0, TSeq(TInt))
       ==> (forall i#5: int :: 
          { $Unbox(Seq#Index(s#0, i#5)): int } 
          (LitInt(0) <= i#5 && i#5 < Seq#Length(Lit(s#0))
             ==> LitInt(0) <= $Unbox(Seq#Index(Lit(s#0), i#5)): int
               && $Unbox(Seq#Index(Lit(s#0), i#5)): int < 256)
             ==> 
            LitInt(0) <= i#5
             ==> 
            i#5 < Seq#Length(Lit(s#0))
             ==> QuantifierTestsHard.__default.byte#canCall($Unbox(Seq#Index(Lit(s#0), i#5)): int))
         && QuantifierTestsHard.__default.f__forall(Lit(s#0))
           == (forall i#5: int :: 
            { $Unbox(Seq#Index(s#0, i#5)): int } 
            true
               ==> (LitInt(0) <= i#5 && i#5 < Seq#Length(Lit(s#0))
                   ==> LitInt(0) <= $Unbox(Seq#Index(Lit(s#0), i#5)): int
                     && $Unbox(Seq#Index(Lit(s#0), i#5)): int < 256)
                 && (LitInt(0) <= i#5 && i#5 < Seq#Length(Lit(s#0))
                   ==> QuantifierTestsHard.__default.byte($Unbox(Seq#Index(Lit(s#0), i#5)): int))));

// function declaration for QuantifierTestsHard._default.f_exists
function QuantifierTestsHard.__default.f__exists(s#0: Seq Box) : bool;

function QuantifierTestsHard.__default.f__exists#canCall(s#0: Seq Box) : bool;

// consequence axiom for QuantifierTestsHard.__default.f__exists
axiom true
   ==> (forall s#0: Seq Box :: 
    { QuantifierTestsHard.__default.f__exists(s#0) } 
    QuantifierTestsHard.__default.f__exists#canCall(s#0) || $Is(s#0, TSeq(TInt))
       ==> true);

function QuantifierTestsHard.__default.f__exists#requires(Seq Box) : bool;

// #requires axiom for QuantifierTestsHard.__default.f__exists
axiom (forall s#0: Seq Box :: 
  { QuantifierTestsHard.__default.f__exists#requires(s#0) } 
  $Is(s#0, TSeq(TInt))
     ==> QuantifierTestsHard.__default.f__exists#requires(s#0) == true);

// definition axiom for QuantifierTestsHard.__default.f__exists (revealed)
axiom true
   ==> (forall s#0: Seq Box :: 
    { QuantifierTestsHard.__default.f__exists(s#0) } 
    QuantifierTestsHard.__default.f__exists#canCall(s#0) || $Is(s#0, TSeq(TInt))
       ==> (forall i#4: int :: 
          { $Unbox(Seq#Index(s#0, i#4)): int } 
          (LitInt(0) <= i#4 && i#4 < Seq#Length(s#0)
             ==> LitInt(0) <= $Unbox(Seq#Index(s#0, i#4)): int
               && $Unbox(Seq#Index(s#0, i#4)): int < 256)
             ==> 
            LitInt(0) <= i#4
             ==> 
            i#4 < Seq#Length(s#0)
             ==> QuantifierTestsHard.__default.byte#canCall($Unbox(Seq#Index(s#0, i#4)): int))
         && QuantifierTestsHard.__default.f__exists(s#0)
           == (exists i#4: int :: 
            { $Unbox(Seq#Index(s#0, i#4)): int } 
            (LitInt(0) <= i#4 && i#4 < Seq#Length(s#0)
                 ==> LitInt(0) <= $Unbox(Seq#Index(s#0, i#4)): int
                   && $Unbox(Seq#Index(s#0, i#4)): int < 256)
               && 
              LitInt(0) <= i#4
               && i#4 < Seq#Length(s#0)
               && QuantifierTestsHard.__default.byte($Unbox(Seq#Index(s#0, i#4)): int)));

// definition axiom for QuantifierTestsHard.__default.f__exists for all literals (revealed)
axiom true
   ==> (forall s#0: Seq Box :: 
    {:weight 3} { QuantifierTestsHard.__default.f__exists(Lit(s#0)) } 
    QuantifierTestsHard.__default.f__exists#canCall(Lit(s#0))
         || $Is(s#0, TSeq(TInt))
       ==> (forall i#5: int :: 
          { $Unbox(Seq#Index(s#0, i#5)): int } 
          (LitInt(0) <= i#5 && i#5 < Seq#Length(Lit(s#0))
             ==> LitInt(0) <= $Unbox(Seq#Index(Lit(s#0), i#5)): int
               && $Unbox(Seq#Index(Lit(s#0), i#5)): int < 256)
             ==> 
            LitInt(0) <= i#5
             ==> 
            i#5 < Seq#Length(Lit(s#0))
             ==> QuantifierTestsHard.__default.byte#canCall($Unbox(Seq#Index(Lit(s#0), i#5)): int))
         && QuantifierTestsHard.__default.f__exists(Lit(s#0))
           == (exists i#5: int :: 
            { $Unbox(Seq#Index(s#0, i#5)): int } 
            (LitInt(0) <= i#5 && i#5 < Seq#Length(Lit(s#0))
                 ==> LitInt(0) <= $Unbox(Seq#Index(Lit(s#0), i#5)): int
                   && $Unbox(Seq#Index(Lit(s#0), i#5)): int < 256)
               && 
              LitInt(0) <= i#5
               && i#5 < Seq#Length(Lit(s#0))
               && QuantifierTestsHard.__default.byte($Unbox(Seq#Index(Lit(s#0), i#5)): int)));

// function declaration for QuantifierTestsHard._default.g_forall
function QuantifierTestsHard.__default.g__forall(s#0: Seq Box) : bool;

function QuantifierTestsHard.__default.g__forall#canCall(s#0: Seq Box) : bool;

// consequence axiom for QuantifierTestsHard.__default.g__forall
axiom true
   ==> (forall s#0: Seq Box :: 
    { QuantifierTestsHard.__default.g__forall(s#0) } 
    QuantifierTestsHard.__default.g__forall#canCall(s#0)
         || ($Is(s#0, TSeq(TInt))
           && (forall j#5: int :: 
            { $Unbox(Seq#Index(s#0, j#5)): int } 
            true
               ==> (LitInt(0) <= j#5 && j#5 < Seq#Length(s#0)
                   ==> LitInt(0) <= $Unbox(Seq#Index(s#0, j#5)): int
                     && $Unbox(Seq#Index(s#0, j#5)): int < 256)
                 && (LitInt(0) <= j#5 && j#5 < Seq#Length(s#0)
                   ==> QuantifierTestsHard.__default.byte($Unbox(Seq#Index(s#0, j#5)): int))))
       ==> true);

function QuantifierTestsHard.__default.g__forall#requires(Seq Box) : bool;

// #requires axiom for QuantifierTestsHard.__default.g__forall
axiom (forall s#0: Seq Box :: 
  { QuantifierTestsHard.__default.g__forall#requires(s#0) } 
  $Is(s#0, TSeq(TInt))
     ==> QuantifierTestsHard.__default.g__forall#requires(s#0)
       == (forall j#6: int :: 
        { $Unbox(Seq#Index(s#0, j#6)): int } 
        true
           ==> (LitInt(0) <= j#6 && j#6 < Seq#Length(s#0)
               ==> LitInt(0) <= $Unbox(Seq#Index(s#0, j#6)): int
                 && $Unbox(Seq#Index(s#0, j#6)): int < 256)
             && (LitInt(0) <= j#6 && j#6 < Seq#Length(s#0)
               ==> QuantifierTestsHard.__default.byte($Unbox(Seq#Index(s#0, j#6)): int))));

// definition axiom for QuantifierTestsHard.__default.g__forall (revealed)
axiom true
   ==> (forall s#0: Seq Box :: 
    { QuantifierTestsHard.__default.g__forall(s#0) } 
    QuantifierTestsHard.__default.g__forall#canCall(s#0)
         || ($Is(s#0, TSeq(TInt))
           && (forall j#6: int :: 
            { $Unbox(Seq#Index(s#0, j#6)): int } 
            true
               ==> (LitInt(0) <= j#6 && j#6 < Seq#Length(s#0)
                   ==> LitInt(0) <= $Unbox(Seq#Index(s#0, j#6)): int
                     && $Unbox(Seq#Index(s#0, j#6)): int < 256)
                 && (LitInt(0) <= j#6 && j#6 < Seq#Length(s#0)
                   ==> QuantifierTestsHard.__default.byte($Unbox(Seq#Index(s#0, j#6)): int))))
       ==> QuantifierTestsHard.__default.g__forall(s#0) == (Seq#Length(s#0) > 2));

// definition axiom for QuantifierTestsHard.__default.g__forall for all literals (revealed)
axiom true
   ==> (forall s#0: Seq Box :: 
    {:weight 3} { QuantifierTestsHard.__default.g__forall(Lit(s#0)) } 
    QuantifierTestsHard.__default.g__forall#canCall(Lit(s#0))
         || ($Is(s#0, TSeq(TInt))
           && (forall j#7: int :: 
            { $Unbox(Seq#Index(s#0, j#7)): int } 
            true
               ==> (LitInt(0) <= j#7 && j#7 < Seq#Length(Lit(s#0))
                   ==> LitInt(0) <= $Unbox(Seq#Index(Lit(s#0), j#7)): int
                     && $Unbox(Seq#Index(Lit(s#0), j#7)): int < 256)
                 && (LitInt(0) <= j#7 && j#7 < Seq#Length(Lit(s#0))
                   ==> QuantifierTestsHard.__default.byte($Unbox(Seq#Index(Lit(s#0), j#7)): int))))
       ==> QuantifierTestsHard.__default.g__forall(Lit(s#0)) == (Seq#Length(Lit(s#0)) > 2));

// function declaration for QuantifierTestsHard._default.h_forall
function QuantifierTestsHard.__default.h__forall(s#0: Seq Box) : bool;

function QuantifierTestsHard.__default.h__forall#canCall(s#0: Seq Box) : bool;

// consequence axiom for QuantifierTestsHard.__default.h__forall
axiom true
   ==> (forall s#0: Seq Box :: 
    { QuantifierTestsHard.__default.h__forall(s#0) } 
    QuantifierTestsHard.__default.h__forall#canCall(s#0) || $Is(s#0, TSeq(TInt))
       ==> true);

function QuantifierTestsHard.__default.h__forall#requires(Seq Box) : bool;

// #requires axiom for QuantifierTestsHard.__default.h__forall
axiom (forall s#0: Seq Box :: 
  { QuantifierTestsHard.__default.h__forall#requires(s#0) } 
  $Is(s#0, TSeq(TInt))
     ==> QuantifierTestsHard.__default.h__forall#requires(s#0) == true);

// definition axiom for QuantifierTestsHard.__default.h__forall (revealed)
axiom true
   ==> (forall s#0: Seq Box :: 
    { QuantifierTestsHard.__default.h__forall(s#0) } 
    QuantifierTestsHard.__default.h__forall#canCall(s#0) || $Is(s#0, TSeq(TInt))
       ==> QuantifierTestsHard.__default.f__forall#canCall(s#0)
         && QuantifierTestsHard.__default.h__forall(s#0)
           == QuantifierTestsHard.__default.f__forall(s#0));

// definition axiom for QuantifierTestsHard.__default.h__forall for all literals (revealed)
axiom true
   ==> (forall s#0: Seq Box :: 
    {:weight 3} { QuantifierTestsHard.__default.h__forall(Lit(s#0)) } 
    QuantifierTestsHard.__default.h__forall#canCall(Lit(s#0))
         || $Is(s#0, TSeq(TInt))
       ==> QuantifierTestsHard.__default.f__forall#canCall(Lit(s#0))
         && QuantifierTestsHard.__default.h__forall(Lit(s#0))
           == Lit(QuantifierTestsHard.__default.f__forall(Lit(s#0))));

// function declaration for QuantifierTestsHard._default.h
function QuantifierTestsHard.__default.h(s#0: Seq Box) : bool;

function QuantifierTestsHard.__default.h#canCall(s#0: Seq Box) : bool;

// consequence axiom for QuantifierTestsHard.__default.h
axiom true
   ==> (forall s#0: Seq Box :: 
    { QuantifierTestsHard.__default.h(s#0) } 
    QuantifierTestsHard.__default.h#canCall(s#0)
         || ($Is(s#0, TSeq(TInt))
           && (forall j#6: int :: 
            { $Unbox(Seq#Index(s#0, j#6)): int } 
            true
               ==> (LitInt(0) <= j#6 && j#6 < Seq#Length(s#0)
                   ==> LitInt(0) <= $Unbox(Seq#Index(s#0, j#6)): int
                     && $Unbox(Seq#Index(s#0, j#6)): int < 256)
                 && (LitInt(0) <= j#6 && j#6 < Seq#Length(s#0)
                   ==> QuantifierTestsHard.__default.byte($Unbox(Seq#Index(s#0, j#6)): int))))
       ==> true);

function QuantifierTestsHard.__default.h#requires(Seq Box) : bool;

// #requires axiom for QuantifierTestsHard.__default.h
axiom (forall s#0: Seq Box :: 
  { QuantifierTestsHard.__default.h#requires(s#0) } 
  $Is(s#0, TSeq(TInt))
     ==> QuantifierTestsHard.__default.h#requires(s#0)
       == (forall j#7: int :: 
        { $Unbox(Seq#Index(s#0, j#7)): int } 
        true
           ==> (LitInt(0) <= j#7 && j#7 < Seq#Length(s#0)
               ==> LitInt(0) <= $Unbox(Seq#Index(s#0, j#7)): int
                 && $Unbox(Seq#Index(s#0, j#7)): int < 256)
             && (LitInt(0) <= j#7 && j#7 < Seq#Length(s#0)
               ==> QuantifierTestsHard.__default.byte($Unbox(Seq#Index(s#0, j#7)): int))));

// definition axiom for QuantifierTestsHard.__default.h (revealed)
axiom true
   ==> (forall s#0: Seq Box :: 
    { QuantifierTestsHard.__default.h(s#0) } 
    QuantifierTestsHard.__default.h#canCall(s#0)
         || ($Is(s#0, TSeq(TInt))
           && (forall j#7: int :: 
            { $Unbox(Seq#Index(s#0, j#7)): int } 
            true
               ==> (LitInt(0) <= j#7 && j#7 < Seq#Length(s#0)
                   ==> LitInt(0) <= $Unbox(Seq#Index(s#0, j#7)): int
                     && $Unbox(Seq#Index(s#0, j#7)): int < 256)
                 && (LitInt(0) <= j#7 && j#7 < Seq#Length(s#0)
                   ==> QuantifierTestsHard.__default.byte($Unbox(Seq#Index(s#0, j#7)): int))))
       ==> QuantifierTestsHard.__default.g__forall#canCall(s#0)
         && QuantifierTestsHard.__default.h(s#0)
           == QuantifierTestsHard.__default.g__forall(s#0));

// definition axiom for QuantifierTestsHard.__default.h for all literals (revealed)
axiom true
   ==> (forall s#0: Seq Box :: 
    {:weight 3} { QuantifierTestsHard.__default.h(Lit(s#0)) } 
    QuantifierTestsHard.__default.h#canCall(Lit(s#0))
         || ($Is(s#0, TSeq(TInt))
           && (forall j#8: int :: 
            { $Unbox(Seq#Index(s#0, j#8)): int } 
            true
               ==> (LitInt(0) <= j#8 && j#8 < Seq#Length(Lit(s#0))
                   ==> LitInt(0) <= $Unbox(Seq#Index(Lit(s#0), j#8)): int
                     && $Unbox(Seq#Index(Lit(s#0), j#8)): int < 256)
                 && (LitInt(0) <= j#8 && j#8 < Seq#Length(Lit(s#0))
                   ==> QuantifierTestsHard.__default.byte($Unbox(Seq#Index(Lit(s#0), j#8)): int))))
       ==> QuantifierTestsHard.__default.g__forall#canCall(Lit(s#0))
         && QuantifierTestsHard.__default.h(Lit(s#0))
           == Lit(QuantifierTestsHard.__default.g__forall(Lit(s#0))));

// function declaration for QuantifierTestsHard._default.i
function QuantifierTestsHard.__default.i(s#0: Seq Box) : bool;

function QuantifierTestsHard.__default.i#canCall(s#0: Seq Box) : bool;

// consequence axiom for QuantifierTestsHard.__default.i
axiom true
   ==> (forall s#0: Seq Box :: 
    { QuantifierTestsHard.__default.i(s#0) } 
    QuantifierTestsHard.__default.i#canCall(s#0)
         || ($Is(s#0, TSeq(TInt))
           && (forall k#5: int :: 
            { $Unbox(Seq#Index(s#0, k#5)): int } 
            true
               ==> (LitInt(0) <= k#5 && k#5 < Seq#Length(s#0)
                   ==> LitInt(0) <= $Unbox(Seq#Index(s#0, k#5)): int)
                 && (LitInt(0) <= k#5 && k#5 < Seq#Length(s#0)
                   ==> $Unbox(Seq#Index(s#0, k#5)): int < 5)))
       ==> true);

function QuantifierTestsHard.__default.i#requires(Seq Box) : bool;

// #requires axiom for QuantifierTestsHard.__default.i
axiom (forall s#0: Seq Box :: 
  { QuantifierTestsHard.__default.i#requires(s#0) } 
  $Is(s#0, TSeq(TInt))
     ==> QuantifierTestsHard.__default.i#requires(s#0)
       == (forall k#6: int :: 
        { $Unbox(Seq#Index(s#0, k#6)): int } 
        true
           ==> (LitInt(0) <= k#6 && k#6 < Seq#Length(s#0)
               ==> LitInt(0) <= $Unbox(Seq#Index(s#0, k#6)): int)
             && (LitInt(0) <= k#6 && k#6 < Seq#Length(s#0)
               ==> $Unbox(Seq#Index(s#0, k#6)): int < 5)));

// definition axiom for QuantifierTestsHard.__default.i (revealed)
axiom true
   ==> (forall s#0: Seq Box :: 
    { QuantifierTestsHard.__default.i(s#0) } 
    QuantifierTestsHard.__default.i#canCall(s#0)
         || ($Is(s#0, TSeq(TInt))
           && (forall k#6: int :: 
            { $Unbox(Seq#Index(s#0, k#6)): int } 
            true
               ==> (LitInt(0) <= k#6 && k#6 < Seq#Length(s#0)
                   ==> LitInt(0) <= $Unbox(Seq#Index(s#0, k#6)): int)
                 && (LitInt(0) <= k#6 && k#6 < Seq#Length(s#0)
                   ==> $Unbox(Seq#Index(s#0, k#6)): int < 5)))
       ==> QuantifierTestsHard.__default.i(s#0) == Lit(true));

// definition axiom for QuantifierTestsHard.__default.i for all literals (revealed)
axiom true
   ==> (forall s#0: Seq Box :: 
    {:weight 3} { QuantifierTestsHard.__default.i(Lit(s#0)) } 
    QuantifierTestsHard.__default.i#canCall(Lit(s#0))
         || ($Is(s#0, TSeq(TInt))
           && (forall k#7: int :: 
            { $Unbox(Seq#Index(s#0, k#7)): int } 
            true
               ==> (LitInt(0) <= k#7 && k#7 < Seq#Length(Lit(s#0))
                   ==> LitInt(0) <= $Unbox(Seq#Index(Lit(s#0), k#7)): int)
                 && (LitInt(0) <= k#7 && k#7 < Seq#Length(Lit(s#0))
                   ==> $Unbox(Seq#Index(Lit(s#0), k#7)): int < 5)))
       ==> QuantifierTestsHard.__default.i(Lit(s#0)) == Lit(true));

// function declaration for QuantifierTestsHard._default.j
function QuantifierTestsHard.__default.j(s#0: Seq Box) : bool;

function QuantifierTestsHard.__default.j#canCall(s#0: Seq Box) : bool;

// consequence axiom for QuantifierTestsHard.__default.j
axiom true
   ==> (forall s#0: Seq Box :: 
    { QuantifierTestsHard.__default.j(s#0) } 
    QuantifierTestsHard.__default.j#canCall(s#0)
         || ($Is(s#0, TSeq(TInt))
           && (forall k#6: int :: 
            { $Unbox(Seq#Index(s#0, k#6)): int } 
            true
               ==> (LitInt(0) <= k#6 && k#6 < Seq#Length(s#0)
                   ==> LitInt(0) <= $Unbox(Seq#Index(s#0, k#6)): int)
                 && (LitInt(0) <= k#6 && k#6 < Seq#Length(s#0)
                   ==> $Unbox(Seq#Index(s#0, k#6)): int < 5)))
       ==> true);

function QuantifierTestsHard.__default.j#requires(Seq Box) : bool;

// #requires axiom for QuantifierTestsHard.__default.j
axiom (forall s#0: Seq Box :: 
  { QuantifierTestsHard.__default.j#requires(s#0) } 
  $Is(s#0, TSeq(TInt))
     ==> QuantifierTestsHard.__default.j#requires(s#0)
       == (forall k#7: int :: 
        { $Unbox(Seq#Index(s#0, k#7)): int } 
        true
           ==> (LitInt(0) <= k#7 && k#7 < Seq#Length(s#0)
               ==> LitInt(0) <= $Unbox(Seq#Index(s#0, k#7)): int)
             && (LitInt(0) <= k#7 && k#7 < Seq#Length(s#0)
               ==> $Unbox(Seq#Index(s#0, k#7)): int < 5)));

// definition axiom for QuantifierTestsHard.__default.j (revealed)
axiom true
   ==> (forall s#0: Seq Box :: 
    { QuantifierTestsHard.__default.j(s#0) } 
    QuantifierTestsHard.__default.j#canCall(s#0)
         || ($Is(s#0, TSeq(TInt))
           && (forall k#7: int :: 
            { $Unbox(Seq#Index(s#0, k#7)): int } 
            true
               ==> (LitInt(0) <= k#7 && k#7 < Seq#Length(s#0)
                   ==> LitInt(0) <= $Unbox(Seq#Index(s#0, k#7)): int)
                 && (LitInt(0) <= k#7 && k#7 < Seq#Length(s#0)
                   ==> $Unbox(Seq#Index(s#0, k#7)): int < 5)))
       ==> QuantifierTestsHard.__default.i#canCall(s#0)
         && QuantifierTestsHard.__default.j(s#0) == QuantifierTestsHard.__default.i(s#0));

// definition axiom for QuantifierTestsHard.__default.j for all literals (revealed)
axiom true
   ==> (forall s#0: Seq Box :: 
    {:weight 3} { QuantifierTestsHard.__default.j(Lit(s#0)) } 
    QuantifierTestsHard.__default.j#canCall(Lit(s#0))
         || ($Is(s#0, TSeq(TInt))
           && (forall k#8: int :: 
            { $Unbox(Seq#Index(s#0, k#8)): int } 
            true
               ==> (LitInt(0) <= k#8 && k#8 < Seq#Length(Lit(s#0))
                   ==> LitInt(0) <= $Unbox(Seq#Index(Lit(s#0), k#8)): int)
                 && (LitInt(0) <= k#8 && k#8 < Seq#Length(Lit(s#0))
                   ==> $Unbox(Seq#Index(Lit(s#0), k#8)): int < 5)))
       ==> QuantifierTestsHard.__default.i#canCall(Lit(s#0))
         && QuantifierTestsHard.__default.j(Lit(s#0))
           == Lit(QuantifierTestsHard.__default.i(Lit(s#0))));

// function declaration for QuantifierTestsHard._default.m
function QuantifierTestsHard.__default.m(x#0: int) : bool;

function QuantifierTestsHard.__default.m#canCall(x#0: int) : bool;

// consequence axiom for QuantifierTestsHard.__default.m
axiom true
   ==> (forall x#0: int :: { QuantifierTestsHard.__default.m(x#0) } true ==> true);

function QuantifierTestsHard.__default.m#requires(int) : bool;

// #requires axiom for QuantifierTestsHard.__default.m
axiom (forall x#0: int :: 
  { QuantifierTestsHard.__default.m#requires(x#0) } 
  QuantifierTestsHard.__default.m#requires(x#0) == true);

// function declaration for QuantifierTestsHard._default.n
function QuantifierTestsHard.__default.n(x#0: int) : bool;

function QuantifierTestsHard.__default.n#canCall(x#0: int) : bool;

// consequence axiom for QuantifierTestsHard.__default.n
axiom true
   ==> (forall x#0: int :: { QuantifierTestsHard.__default.n(x#0) } true ==> true);

function QuantifierTestsHard.__default.n#requires(int) : bool;

// #requires axiom for QuantifierTestsHard.__default.n
axiom (forall x#0: int :: 
  { QuantifierTestsHard.__default.n#requires(x#0) } 
  QuantifierTestsHard.__default.n#requires(x#0) == true);

// function declaration for QuantifierTestsHard._default.f1
function QuantifierTestsHard.__default.f1(x#0: int) : bool;

function QuantifierTestsHard.__default.f1#canCall(x#0: int) : bool;

// consequence axiom for QuantifierTestsHard.__default.f1
axiom true
   ==> (forall x#0: int :: 
    { QuantifierTestsHard.__default.f1(x#0) } 
    QuantifierTestsHard.__default.f1#canCall(x#0) || (x#0 > 3 && x#0 < 16) ==> true);

function QuantifierTestsHard.__default.f1#requires(int) : bool;

// #requires axiom for QuantifierTestsHard.__default.f1
axiom (forall x#0: int :: 
  { QuantifierTestsHard.__default.f1#requires(x#0) } 
  QuantifierTestsHard.__default.f1#requires(x#0) == (x#0 > 3 && x#0 < 16));

// function declaration for QuantifierTestsHard._default.variable_uniqueness_test
function QuantifierTestsHard.__default.variable__uniqueness__test(x#0: int) : bool;

function QuantifierTestsHard.__default.variable__uniqueness__test#canCall(x#0: int) : bool;

// consequence axiom for QuantifierTestsHard.__default.variable__uniqueness__test
axiom true
   ==> (forall x#0: int :: 
    { QuantifierTestsHard.__default.variable__uniqueness__test(x#0) } 
    QuantifierTestsHard.__default.variable__uniqueness__test#canCall(x#0)
         || (((forall y#12: int :: 
              { QuantifierTestsHard.__default.m(y#12) } 
              true ==> QuantifierTestsHard.__default.m(y#12))
             ==> x#0 > 3)
           && ((forall y#13: int :: 
              { QuantifierTestsHard.__default.m(y#13) } 
              true ==> QuantifierTestsHard.__default.m(y#13))
             ==> x#0 < 16))
       ==> true);

function QuantifierTestsHard.__default.variable__uniqueness__test#requires(int) : bool;

// #requires axiom for QuantifierTestsHard.__default.variable__uniqueness__test
axiom (forall x#0: int :: 
  { QuantifierTestsHard.__default.variable__uniqueness__test#requires(x#0) } 
  QuantifierTestsHard.__default.variable__uniqueness__test#requires(x#0)
     == (((forall y#14: int :: 
          { QuantifierTestsHard.__default.m(y#14) } 
          true ==> QuantifierTestsHard.__default.m(y#14))
         ==> x#0 > 3)
       && ((forall y#15: int :: 
          { QuantifierTestsHard.__default.m(y#15) } 
          true ==> QuantifierTestsHard.__default.m(y#15))
         ==> x#0 < 16)));

// definition axiom for QuantifierTestsHard.__default.variable__uniqueness__test (revealed)
axiom true
   ==> (forall x#0: int :: 
    { QuantifierTestsHard.__default.variable__uniqueness__test(x#0) } 
    QuantifierTestsHard.__default.variable__uniqueness__test#canCall(x#0)
         || (((forall y#14: int :: 
              { QuantifierTestsHard.__default.m(y#14) } 
              true ==> QuantifierTestsHard.__default.m(y#14))
             ==> x#0 > 3)
           && ((forall y#15: int :: 
              { QuantifierTestsHard.__default.m(y#15) } 
              true ==> QuantifierTestsHard.__default.m(y#15))
             ==> x#0 < 16))
       ==> (forall y#16: int :: 
          { QuantifierTestsHard.__default.m(y#16) } 
          QuantifierTestsHard.__default.m#canCall(y#16))
         && ((forall y#16: int :: 
            { QuantifierTestsHard.__default.m(y#16) } 
            true ==> QuantifierTestsHard.__default.m(y#16))
           ==> QuantifierTestsHard.__default.f1#canCall(x#0))
         && QuantifierTestsHard.__default.variable__uniqueness__test(x#0)
           == ((forall y#16: int :: 
              { QuantifierTestsHard.__default.m(y#16) } 
              true ==> QuantifierTestsHard.__default.m(y#16))
             && QuantifierTestsHard.__default.f1(x#0)));

// definition axiom for QuantifierTestsHard.__default.variable__uniqueness__test for all literals (revealed)
axiom true
   ==> (forall x#0: int :: 
    {:weight 3} { QuantifierTestsHard.__default.variable__uniqueness__test(LitInt(x#0)) } 
    QuantifierTestsHard.__default.variable__uniqueness__test#canCall(LitInt(x#0))
         || (((forall y#17: int :: 
              { QuantifierTestsHard.__default.m(y#17) } 
              true ==> QuantifierTestsHard.__default.m(y#17))
             ==> x#0 > 3)
           && ((forall y#18: int :: 
              { QuantifierTestsHard.__default.m(y#18) } 
              true ==> QuantifierTestsHard.__default.m(y#18))
             ==> x#0 < 16))
       ==> (forall y#19: int :: 
          { QuantifierTestsHard.__default.m(y#19) } 
          QuantifierTestsHard.__default.m#canCall(y#19))
         && ((forall y#19: int :: 
            { QuantifierTestsHard.__default.m(y#19) } 
            true ==> QuantifierTestsHard.__default.m(y#19))
           ==> QuantifierTestsHard.__default.f1#canCall(LitInt(x#0)))
         && QuantifierTestsHard.__default.variable__uniqueness__test(LitInt(x#0))
           == ((forall y#19: int :: 
              { QuantifierTestsHard.__default.m(y#19) } 
              true ==> QuantifierTestsHard.__default.m(y#19))
             && QuantifierTestsHard.__default.f1(LitInt(x#0))));

const unique class.CorrectReqOrdering.__default: ClassName;

function Tclass.CorrectReqOrdering.__default() : Ty;

const unique Tagclass.CorrectReqOrdering.__default: TyTag;

// Tclass.CorrectReqOrdering.__default Tag
axiom Tag(Tclass.CorrectReqOrdering.__default())
     == Tagclass.CorrectReqOrdering.__default
   && TagFamily(Tclass.CorrectReqOrdering.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.CorrectReqOrdering.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.CorrectReqOrdering.__default()) } 
  $IsBox(bx, Tclass.CorrectReqOrdering.__default())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.CorrectReqOrdering.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.CorrectReqOrdering.__default()) } 
  $Is($o, Tclass.CorrectReqOrdering.__default())
     <==> $o == null || dtype($o) == Tclass.CorrectReqOrdering.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.CorrectReqOrdering.__default(), $h) } 
  $IsAlloc($o, Tclass.CorrectReqOrdering.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

// function declaration for CorrectReqOrdering._default.f1
function CorrectReqOrdering.__default.f1(x#0: int) : bool;

function CorrectReqOrdering.__default.f1#canCall(x#0: int) : bool;

// consequence axiom for CorrectReqOrdering.__default.f1
axiom true
   ==> (forall x#0: int :: 
    { CorrectReqOrdering.__default.f1(x#0) } 
    CorrectReqOrdering.__default.f1#canCall(x#0) || x#0 > 3 ==> true);

function CorrectReqOrdering.__default.f1#requires(int) : bool;

// #requires axiom for CorrectReqOrdering.__default.f1
axiom (forall x#0: int :: 
  { CorrectReqOrdering.__default.f1#requires(x#0) } 
  CorrectReqOrdering.__default.f1#requires(x#0) == (x#0 > 3));

// function declaration for CorrectReqOrdering._default.f2
function CorrectReqOrdering.__default.f2(b#0: bool) : bool;

function CorrectReqOrdering.__default.f2#canCall(b#0: bool) : bool;

// consequence axiom for CorrectReqOrdering.__default.f2
axiom true
   ==> (forall b#0: bool :: 
    { CorrectReqOrdering.__default.f2(b#0) } 
    CorrectReqOrdering.__default.f2#canCall(b#0) || b#0 ==> true);

function CorrectReqOrdering.__default.f2#requires(bool) : bool;

// #requires axiom for CorrectReqOrdering.__default.f2
axiom (forall b#0: bool :: 
  { CorrectReqOrdering.__default.f2#requires(b#0) } 
  CorrectReqOrdering.__default.f2#requires(b#0) == b#0);

// function declaration for CorrectReqOrdering._default.f3
function CorrectReqOrdering.__default.f3(z#0: int) : bool;

function CorrectReqOrdering.__default.f3#canCall(z#0: int) : bool;

// consequence axiom for CorrectReqOrdering.__default.f3
axiom true
   ==> (forall z#0: int :: 
    { CorrectReqOrdering.__default.f3(z#0) } 
    CorrectReqOrdering.__default.f3#canCall(z#0)
         || (z#0 > 3 && CorrectReqOrdering.__default.f1(z#0))
       ==> true);

function CorrectReqOrdering.__default.f3#requires(int) : bool;

// #requires axiom for CorrectReqOrdering.__default.f3
axiom (forall z#0: int :: 
  { CorrectReqOrdering.__default.f3#requires(z#0) } 
  CorrectReqOrdering.__default.f3#requires(z#0)
     == (z#0 > 3 && CorrectReqOrdering.__default.f1(z#0)));

// definition axiom for CorrectReqOrdering.__default.f3 (revealed)
axiom true
   ==> (forall z#0: int :: 
    { CorrectReqOrdering.__default.f3(z#0) } 
    CorrectReqOrdering.__default.f3#canCall(z#0)
         || (z#0 > 3 && CorrectReqOrdering.__default.f1(z#0))
       ==> CorrectReqOrdering.__default.f1#canCall(z#0)
         && CorrectReqOrdering.__default.f2#canCall(CorrectReqOrdering.__default.f1(z#0))
         && CorrectReqOrdering.__default.f3(z#0)
           == CorrectReqOrdering.__default.f2(CorrectReqOrdering.__default.f1(z#0)));

// definition axiom for CorrectReqOrdering.__default.f3 for all literals (revealed)
axiom true
   ==> (forall z#0: int :: 
    {:weight 3} { CorrectReqOrdering.__default.f3(LitInt(z#0)) } 
    CorrectReqOrdering.__default.f3#canCall(LitInt(z#0))
         || (Lit(z#0 > 3) && CorrectReqOrdering.__default.f1(LitInt(z#0)))
       ==> CorrectReqOrdering.__default.f1#canCall(LitInt(z#0))
         && CorrectReqOrdering.__default.f2#canCall(CorrectReqOrdering.__default.f1(LitInt(z#0)))
         && CorrectReqOrdering.__default.f3(LitInt(z#0))
           == CorrectReqOrdering.__default.f2(CorrectReqOrdering.__default.f1(LitInt(z#0))));

const unique class.ShortCircuiting.__default: ClassName;

function Tclass.ShortCircuiting.__default() : Ty;

const unique Tagclass.ShortCircuiting.__default: TyTag;

// Tclass.ShortCircuiting.__default Tag
axiom Tag(Tclass.ShortCircuiting.__default()) == Tagclass.ShortCircuiting.__default
   && TagFamily(Tclass.ShortCircuiting.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.ShortCircuiting.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.ShortCircuiting.__default()) } 
  $IsBox(bx, Tclass.ShortCircuiting.__default())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.ShortCircuiting.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.ShortCircuiting.__default()) } 
  $Is($o, Tclass.ShortCircuiting.__default())
     <==> $o == null || dtype($o) == Tclass.ShortCircuiting.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.ShortCircuiting.__default(), $h) } 
  $IsAlloc($o, Tclass.ShortCircuiting.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

// function declaration for ShortCircuiting._default.f1
function ShortCircuiting.__default.f1(x#0: int) : bool;

function ShortCircuiting.__default.f1#canCall(x#0: int) : bool;

// consequence axiom for ShortCircuiting.__default.f1
axiom true
   ==> (forall x#0: int :: 
    { ShortCircuiting.__default.f1(x#0) } 
    ShortCircuiting.__default.f1#canCall(x#0) || x#0 > 3 ==> true);

function ShortCircuiting.__default.f1#requires(int) : bool;

// #requires axiom for ShortCircuiting.__default.f1
axiom (forall x#0: int :: 
  { ShortCircuiting.__default.f1#requires(x#0) } 
  ShortCircuiting.__default.f1#requires(x#0) == (x#0 > 3));

// function declaration for ShortCircuiting._default.f2
function ShortCircuiting.__default.f2(y#0: int) : bool;

function ShortCircuiting.__default.f2#canCall(y#0: int) : bool;

// consequence axiom for ShortCircuiting.__default.f2
axiom true
   ==> (forall y#0: int :: 
    { ShortCircuiting.__default.f2(y#0) } 
    ShortCircuiting.__default.f2#canCall(y#0) || y#0 < 10 ==> true);

function ShortCircuiting.__default.f2#requires(int) : bool;

// #requires axiom for ShortCircuiting.__default.f2
axiom (forall y#0: int :: 
  { ShortCircuiting.__default.f2#requires(y#0) } 
  ShortCircuiting.__default.f2#requires(y#0) == (y#0 < 10));

// function declaration for ShortCircuiting._default.test1
function ShortCircuiting.__default.test1(x'#0: int, y'#0: int) : bool;

function ShortCircuiting.__default.test1#canCall(x'#0: int, y'#0: int) : bool;

// consequence axiom for ShortCircuiting.__default.test1
axiom true
   ==> (forall x'#0: int, y'#0: int :: 
    { ShortCircuiting.__default.test1(x'#0, y'#0) } 
    ShortCircuiting.__default.test1#canCall(x'#0, y'#0)
         || (x'#0 > 3 && (ShortCircuiting.__default.f1(x'#0) ==> y'#0 < 10))
       ==> true);

function ShortCircuiting.__default.test1#requires(int, int) : bool;

// #requires axiom for ShortCircuiting.__default.test1
axiom (forall x'#0: int, y'#0: int :: 
  { ShortCircuiting.__default.test1#requires(x'#0, y'#0) } 
  ShortCircuiting.__default.test1#requires(x'#0, y'#0)
     == (x'#0 > 3 && (ShortCircuiting.__default.f1(x'#0) ==> y'#0 < 10)));

// definition axiom for ShortCircuiting.__default.test1 (revealed)
axiom true
   ==> (forall x'#0: int, y'#0: int :: 
    { ShortCircuiting.__default.test1(x'#0, y'#0) } 
    ShortCircuiting.__default.test1#canCall(x'#0, y'#0)
         || (x'#0 > 3 && (ShortCircuiting.__default.f1(x'#0) ==> y'#0 < 10))
       ==> ShortCircuiting.__default.f1#canCall(x'#0)
         && (ShortCircuiting.__default.f1(x'#0)
           ==> ShortCircuiting.__default.f2#canCall(y'#0))
         && ShortCircuiting.__default.test1(x'#0, y'#0)
           == (ShortCircuiting.__default.f1(x'#0) && ShortCircuiting.__default.f2(y'#0)));

// definition axiom for ShortCircuiting.__default.test1 for all literals (revealed)
axiom true
   ==> (forall x'#0: int, y'#0: int :: 
    {:weight 3} { ShortCircuiting.__default.test1(LitInt(x'#0), LitInt(y'#0)) } 
    ShortCircuiting.__default.test1#canCall(LitInt(x'#0), LitInt(y'#0))
         || (Lit(x'#0 > 3) && (ShortCircuiting.__default.f1(LitInt(x'#0)) ==> y'#0 < 10))
       ==> ShortCircuiting.__default.f1#canCall(LitInt(x'#0))
         && (ShortCircuiting.__default.f1(LitInt(x'#0))
           ==> ShortCircuiting.__default.f2#canCall(LitInt(y'#0)))
         && ShortCircuiting.__default.test1(LitInt(x'#0), LitInt(y'#0))
           == (ShortCircuiting.__default.f1(LitInt(x'#0))
             && ShortCircuiting.__default.f2(LitInt(y'#0))));

// function declaration for ShortCircuiting._default.test2
function ShortCircuiting.__default.test2(x'#0: int, y'#0: int) : bool;

function ShortCircuiting.__default.test2#canCall(x'#0: int, y'#0: int) : bool;

// consequence axiom for ShortCircuiting.__default.test2
axiom true
   ==> (forall x'#0: int, y'#0: int :: 
    { ShortCircuiting.__default.test2(x'#0, y'#0) } 
    ShortCircuiting.__default.test2#canCall(x'#0, y'#0)
         || (x'#0 > 3 && (ShortCircuiting.__default.f1(x'#0) ==> y'#0 < 10))
       ==> true);

function ShortCircuiting.__default.test2#requires(int, int) : bool;

// #requires axiom for ShortCircuiting.__default.test2
axiom (forall x'#0: int, y'#0: int :: 
  { ShortCircuiting.__default.test2#requires(x'#0, y'#0) } 
  ShortCircuiting.__default.test2#requires(x'#0, y'#0)
     == (x'#0 > 3 && (ShortCircuiting.__default.f1(x'#0) ==> y'#0 < 10)));

// definition axiom for ShortCircuiting.__default.test2 (revealed)
axiom true
   ==> (forall x'#0: int, y'#0: int :: 
    { ShortCircuiting.__default.test2(x'#0, y'#0) } 
    ShortCircuiting.__default.test2#canCall(x'#0, y'#0)
         || (x'#0 > 3 && (ShortCircuiting.__default.f1(x'#0) ==> y'#0 < 10))
       ==> ShortCircuiting.__default.f1#canCall(x'#0)
         && (ShortCircuiting.__default.f1(x'#0)
           ==> ShortCircuiting.__default.f2#canCall(y'#0))
         && ShortCircuiting.__default.test2(x'#0, y'#0)
           == (ShortCircuiting.__default.f1(x'#0) ==> ShortCircuiting.__default.f2(y'#0)));

// definition axiom for ShortCircuiting.__default.test2 for all literals (revealed)
axiom true
   ==> (forall x'#0: int, y'#0: int :: 
    {:weight 3} { ShortCircuiting.__default.test2(LitInt(x'#0), LitInt(y'#0)) } 
    ShortCircuiting.__default.test2#canCall(LitInt(x'#0), LitInt(y'#0))
         || (Lit(x'#0 > 3) && (ShortCircuiting.__default.f1(LitInt(x'#0)) ==> y'#0 < 10))
       ==> ShortCircuiting.__default.f1#canCall(LitInt(x'#0))
         && (ShortCircuiting.__default.f1(LitInt(x'#0))
           ==> ShortCircuiting.__default.f2#canCall(LitInt(y'#0)))
         && ShortCircuiting.__default.test2(LitInt(x'#0), LitInt(y'#0))
           == (ShortCircuiting.__default.f1(LitInt(x'#0))
             ==> ShortCircuiting.__default.f2(LitInt(y'#0))));

// function declaration for ShortCircuiting._default.test3
function ShortCircuiting.__default.test3(x'#0: int, y'#0: int) : bool;

function ShortCircuiting.__default.test3#canCall(x'#0: int, y'#0: int) : bool;

// consequence axiom for ShortCircuiting.__default.test3
axiom true
   ==> (forall x'#0: int, y'#0: int :: 
    { ShortCircuiting.__default.test3(x'#0, y'#0) } 
    ShortCircuiting.__default.test3#canCall(x'#0, y'#0)
         || (x'#0 > 3 && (!ShortCircuiting.__default.f1(x'#0) ==> y'#0 < 10))
       ==> true);

function ShortCircuiting.__default.test3#requires(int, int) : bool;

// #requires axiom for ShortCircuiting.__default.test3
axiom (forall x'#0: int, y'#0: int :: 
  { ShortCircuiting.__default.test3#requires(x'#0, y'#0) } 
  ShortCircuiting.__default.test3#requires(x'#0, y'#0)
     == (x'#0 > 3 && (!ShortCircuiting.__default.f1(x'#0) ==> y'#0 < 10)));

// definition axiom for ShortCircuiting.__default.test3 (revealed)
axiom true
   ==> (forall x'#0: int, y'#0: int :: 
    { ShortCircuiting.__default.test3(x'#0, y'#0) } 
    ShortCircuiting.__default.test3#canCall(x'#0, y'#0)
         || (x'#0 > 3 && (!ShortCircuiting.__default.f1(x'#0) ==> y'#0 < 10))
       ==> ShortCircuiting.__default.f1#canCall(x'#0)
         && (!ShortCircuiting.__default.f1(x'#0)
           ==> ShortCircuiting.__default.f2#canCall(y'#0))
         && ShortCircuiting.__default.test3(x'#0, y'#0)
           == (ShortCircuiting.__default.f1(x'#0) || ShortCircuiting.__default.f2(y'#0)));

// definition axiom for ShortCircuiting.__default.test3 for all literals (revealed)
axiom true
   ==> (forall x'#0: int, y'#0: int :: 
    {:weight 3} { ShortCircuiting.__default.test3(LitInt(x'#0), LitInt(y'#0)) } 
    ShortCircuiting.__default.test3#canCall(LitInt(x'#0), LitInt(y'#0))
         || (Lit(x'#0 > 3) && (!ShortCircuiting.__default.f1(LitInt(x'#0)) ==> y'#0 < 10))
       ==> ShortCircuiting.__default.f1#canCall(LitInt(x'#0))
         && (!ShortCircuiting.__default.f1(LitInt(x'#0))
           ==> ShortCircuiting.__default.f2#canCall(LitInt(y'#0)))
         && ShortCircuiting.__default.test3(LitInt(x'#0), LitInt(y'#0))
           == (ShortCircuiting.__default.f1(LitInt(x'#0))
             || ShortCircuiting.__default.f2(LitInt(y'#0))));

const unique class.Lets.__default: ClassName;

function Tclass.Lets.__default() : Ty;

const unique Tagclass.Lets.__default: TyTag;

// Tclass.Lets.__default Tag
axiom Tag(Tclass.Lets.__default()) == Tagclass.Lets.__default
   && TagFamily(Tclass.Lets.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.Lets.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.Lets.__default()) } 
  $IsBox(bx, Tclass.Lets.__default())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.Lets.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.Lets.__default()) } 
  $Is($o, Tclass.Lets.__default())
     <==> $o == null || dtype($o) == Tclass.Lets.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.Lets.__default(), $h) } 
  $IsAlloc($o, Tclass.Lets.__default(), $h) <==> $o == null || read($h, $o, alloc));

// function declaration for Lets._default.f1
function Lets.__default.f1(x#0: int) : bool;

function Lets.__default.f1#canCall(x#0: int) : bool;

// consequence axiom for Lets.__default.f1
axiom true
   ==> (forall x#0: int :: 
    { Lets.__default.f1(x#0) } 
    Lets.__default.f1#canCall(x#0) || x#0 > 3 ==> true);

function Lets.__default.f1#requires(int) : bool;

// #requires axiom for Lets.__default.f1
axiom (forall x#0: int :: 
  { Lets.__default.f1#requires(x#0) } 
  Lets.__default.f1#requires(x#0) == (x#0 > 3));

// function declaration for Lets._default.test1
function Lets.__default.test1(x'#0: int) : bool;

function Lets.__default.test1#canCall(x'#0: int) : bool;

// consequence axiom for Lets.__default.test1
axiom true
   ==> (forall x'#0: int :: 
    { Lets.__default.test1(x'#0) } 
    Lets.__default.test1#canCall(x'#0)
         || (var y'#6 := Mul(LitInt(3), x'#0); y'#6 > 3)
       ==> true);

function Lets.__default.test1#requires(int) : bool;

// #requires axiom for Lets.__default.test1
axiom (forall x'#0: int :: 
  { Lets.__default.test1#requires(x'#0) } 
  Lets.__default.test1#requires(x'#0)
     == (var y'#7 := Mul(LitInt(3), x'#0); y'#7 > 3));

// definition axiom for Lets.__default.test1 (revealed)
axiom true
   ==> (forall x'#0: int :: 
    { Lets.__default.test1(x'#0) } 
    Lets.__default.test1#canCall(x'#0)
         || (var y'#7 := Mul(LitInt(3), x'#0); y'#7 > 3)
       ==> (var y'#8 := Mul(LitInt(3), x'#0); Lets.__default.f1#canCall(y'#8))
         && Lets.__default.test1(x'#0)
           == (var y'#8 := Mul(LitInt(3), x'#0); Lets.__default.f1(y'#8)));

// definition axiom for Lets.__default.test1 for all literals (revealed)
axiom true
   ==> (forall x'#0: int :: 
    {:weight 3} { Lets.__default.test1(LitInt(x'#0)) } 
    Lets.__default.test1#canCall(LitInt(x'#0))
         || (var y'#9 := LitInt(Mul(LitInt(3), LitInt(x'#0))); Lit(y'#9 > 3))
       ==> (var y'#10 := LitInt(Mul(LitInt(3), LitInt(x'#0))); 
          Lets.__default.f1#canCall(y'#10))
         && Lets.__default.test1(LitInt(x'#0))
           == (var y'#10 := LitInt(Mul(LitInt(3), LitInt(x'#0))); Lets.__default.f1(y'#10)));

const unique class.M1_mM2.__default: ClassName;

function Tclass.M1_mM2.__default() : Ty;

const unique Tagclass.M1_mM2.__default: TyTag;

// Tclass.M1_mM2.__default Tag
axiom Tag(Tclass.M1_mM2.__default()) == Tagclass.M1_mM2.__default
   && TagFamily(Tclass.M1_mM2.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.M1_mM2.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.M1_mM2.__default()) } 
  $IsBox(bx, Tclass.M1_mM2.__default())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.M1_mM2.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.M1_mM2.__default()) } 
  $Is($o, Tclass.M1_mM2.__default())
     <==> $o == null || dtype($o) == Tclass.M1_mM2.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.M1_mM2.__default(), $h) } 
  $IsAlloc($o, Tclass.M1_mM2.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

// function declaration for M1.M2._default.f
function M1_mM2.__default.f(x#0: int) : bool;

function M1_mM2.__default.f#canCall(x#0: int) : bool;

// consequence axiom for M1_mM2.__default.f
axiom true
   ==> (forall x#0: int :: 
    { M1_mM2.__default.f(x#0) } 
    M1_mM2.__default.f#canCall(x#0) || x#0 > 3 ==> true);

function M1_mM2.__default.f#requires(int) : bool;

// #requires axiom for M1_mM2.__default.f
axiom (forall x#0: int :: 
  { M1_mM2.__default.f#requires(x#0) } 
  M1_mM2.__default.f#requires(x#0) == (x#0 > 3));

// definition axiom for M1_mM2.__default.f (revealed)
axiom true
   ==> (forall x#0: int :: 
    { M1_mM2.__default.f(x#0) } 
    M1_mM2.__default.f#canCall(x#0) || x#0 > 3
       ==> M1_mM2.__default.f(x#0) == (x#0 > 7));

// definition axiom for M1_mM2.__default.f for all literals (revealed)
axiom true
   ==> (forall x#0: int :: 
    {:weight 3} { M1_mM2.__default.f(LitInt(x#0)) } 
    M1_mM2.__default.f#canCall(LitInt(x#0)) || Lit(x#0 > 3)
       ==> M1_mM2.__default.f(LitInt(x#0)) == Lit(x#0 > 7));

// function declaration for M1.M2._default.h
function M1_mM2.__default.h(y#0: int) : bool;

function M1_mM2.__default.h#canCall(y#0: int) : bool;

// consequence axiom for M1_mM2.__default.h
axiom true
   ==> (forall y#0: int :: 
    { M1_mM2.__default.h(y#0) } 
    M1_mM2.__default.h#canCall(y#0) || y#0 > 3 ==> true);

function M1_mM2.__default.h#requires(int) : bool;

// #requires axiom for M1_mM2.__default.h
axiom (forall y#0: int :: 
  { M1_mM2.__default.h#requires(y#0) } 
  M1_mM2.__default.h#requires(y#0) == (y#0 > 3));

// definition axiom for M1_mM2.__default.h (revealed)
axiom true
   ==> (forall y#0: int :: 
    { M1_mM2.__default.h(y#0) } 
    M1_mM2.__default.h#canCall(y#0) || y#0 > 3
       ==> M1_mM2.__default.f#canCall(y#0)
         && M1_mM2.__default.h(y#0) == M1_mM2.__default.f(y#0));

// definition axiom for M1_mM2.__default.h for all literals (revealed)
axiom true
   ==> (forall y#0: int :: 
    {:weight 3} { M1_mM2.__default.h(LitInt(y#0)) } 
    M1_mM2.__default.h#canCall(LitInt(y#0)) || Lit(y#0 > 3)
       ==> M1_mM2.__default.f#canCall(LitInt(y#0))
         && M1_mM2.__default.h(LitInt(y#0)) == Lit(M1_mM2.__default.f(LitInt(y#0))));

const unique class.M1.__default: ClassName;

function Tclass.M1.__default() : Ty;

const unique Tagclass.M1.__default: TyTag;

// Tclass.M1.__default Tag
axiom Tag(Tclass.M1.__default()) == Tagclass.M1.__default
   && TagFamily(Tclass.M1.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.M1.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.M1.__default()) } 
  $IsBox(bx, Tclass.M1.__default())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.M1.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.M1.__default()) } 
  $Is($o, Tclass.M1.__default())
     <==> $o == null || dtype($o) == Tclass.M1.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.M1.__default(), $h) } 
  $IsAlloc($o, Tclass.M1.__default(), $h) <==> $o == null || read($h, $o, alloc));

// Constructor function declaration
function #Datatypes.TheType.TheType_builder(int) : DatatypeType;

const unique ##Datatypes.TheType.TheType_builder: DtCtorId;

// Constructor identifier
axiom (forall a#0#0#0: int :: 
  { #Datatypes.TheType.TheType_builder(a#0#0#0) } 
  DatatypeCtorId(#Datatypes.TheType.TheType_builder(a#0#0#0))
     == ##Datatypes.TheType.TheType_builder);

function Datatypes.TheType.TheType__builder_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { Datatypes.TheType.TheType__builder_q(d) } 
  Datatypes.TheType.TheType__builder_q(d)
     <==> DatatypeCtorId(d) == ##Datatypes.TheType.TheType_builder);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { Datatypes.TheType.TheType__builder_q(d) } 
  Datatypes.TheType.TheType__builder_q(d)
     ==> (exists a#1#0#0: int :: d == #Datatypes.TheType.TheType_builder(a#1#0#0)));

function Tclass.Datatypes.TheType() : Ty;

const unique Tagclass.Datatypes.TheType: TyTag;

// Tclass.Datatypes.TheType Tag
axiom Tag(Tclass.Datatypes.TheType()) == Tagclass.Datatypes.TheType
   && TagFamily(Tclass.Datatypes.TheType()) == tytagFamily$TheType;

// Box/unbox axiom for Tclass.Datatypes.TheType
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.Datatypes.TheType()) } 
  $IsBox(bx, Tclass.Datatypes.TheType())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass.Datatypes.TheType()));

// Constructor $Is
axiom (forall a#2#0#0: int :: 
  { $Is(#Datatypes.TheType.TheType_builder(a#2#0#0), Tclass.Datatypes.TheType()) } 
  $Is(#Datatypes.TheType.TheType_builder(a#2#0#0), Tclass.Datatypes.TheType())
     <==> $Is(a#2#0#0, TInt));

// Constructor $IsAlloc
axiom (forall a#3#0#0: int, $h: Heap :: 
  { $IsAlloc(#Datatypes.TheType.TheType_builder(a#3#0#0), Tclass.Datatypes.TheType(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#Datatypes.TheType.TheType_builder(a#3#0#0), Tclass.Datatypes.TheType(), $h)
       <==> $IsAlloc(a#3#0#0, TInt, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(Datatypes.TheType.x(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      Datatypes.TheType.TheType__builder_q(d)
       && $IsAlloc(d, Tclass.Datatypes.TheType(), $h)
     ==> $IsAlloc(Datatypes.TheType.x(d), TInt, $h));

// Constructor literal
axiom (forall a#4#0#0: int :: 
  { #Datatypes.TheType.TheType_builder(LitInt(a#4#0#0)) } 
  #Datatypes.TheType.TheType_builder(LitInt(a#4#0#0))
     == Lit(#Datatypes.TheType.TheType_builder(a#4#0#0)));

function Datatypes.TheType.x(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#5#0#0: int :: 
  { #Datatypes.TheType.TheType_builder(a#5#0#0) } 
  Datatypes.TheType.x(#Datatypes.TheType.TheType_builder(a#5#0#0)) == a#5#0#0);

// Constructor function declaration
function #Datatypes.TheType.TheType_copier(DatatypeType) : DatatypeType;

const unique ##Datatypes.TheType.TheType_copier: DtCtorId;

// Constructor identifier
axiom (forall a#6#0#0: DatatypeType :: 
  { #Datatypes.TheType.TheType_copier(a#6#0#0) } 
  DatatypeCtorId(#Datatypes.TheType.TheType_copier(a#6#0#0))
     == ##Datatypes.TheType.TheType_copier);

function Datatypes.TheType.TheType__copier_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { Datatypes.TheType.TheType__copier_q(d) } 
  Datatypes.TheType.TheType__copier_q(d)
     <==> DatatypeCtorId(d) == ##Datatypes.TheType.TheType_copier);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { Datatypes.TheType.TheType__copier_q(d) } 
  Datatypes.TheType.TheType__copier_q(d)
     ==> (exists a#7#0#0: DatatypeType :: 
      d == #Datatypes.TheType.TheType_copier(a#7#0#0)));

// Constructor $Is
axiom (forall a#8#0#0: DatatypeType :: 
  { $Is(#Datatypes.TheType.TheType_copier(a#8#0#0), Tclass.Datatypes.TheType()) } 
  $Is(#Datatypes.TheType.TheType_copier(a#8#0#0), Tclass.Datatypes.TheType())
     <==> $Is(a#8#0#0, Tclass.Datatypes.TheType()));

// Constructor $IsAlloc
axiom (forall a#9#0#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#Datatypes.TheType.TheType_copier(a#9#0#0), Tclass.Datatypes.TheType(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#Datatypes.TheType.TheType_copier(a#9#0#0), Tclass.Datatypes.TheType(), $h)
       <==> $IsAlloc(a#9#0#0, Tclass.Datatypes.TheType(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(Datatypes.TheType.t(d), Tclass.Datatypes.TheType(), $h) } 
  $IsGoodHeap($h)
       && 
      Datatypes.TheType.TheType__copier_q(d)
       && $IsAlloc(d, Tclass.Datatypes.TheType(), $h)
     ==> $IsAlloc(Datatypes.TheType.t(d), Tclass.Datatypes.TheType(), $h));

// Constructor literal
axiom (forall a#10#0#0: DatatypeType :: 
  { #Datatypes.TheType.TheType_copier(Lit(a#10#0#0)) } 
  #Datatypes.TheType.TheType_copier(Lit(a#10#0#0))
     == Lit(#Datatypes.TheType.TheType_copier(a#10#0#0)));

function Datatypes.TheType.t(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#11#0#0: DatatypeType :: 
  { #Datatypes.TheType.TheType_copier(a#11#0#0) } 
  Datatypes.TheType.t(#Datatypes.TheType.TheType_copier(a#11#0#0)) == a#11#0#0);

// Inductive rank
axiom (forall a#12#0#0: DatatypeType :: 
  { #Datatypes.TheType.TheType_copier(a#12#0#0) } 
  DtRank(a#12#0#0) < DtRank(#Datatypes.TheType.TheType_copier(a#12#0#0)));

// Depth-one case-split function
function $IsA#Datatypes.TheType(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#Datatypes.TheType(d) } 
  $IsA#Datatypes.TheType(d)
     ==> Datatypes.TheType.TheType__builder_q(d)
       || Datatypes.TheType.TheType__copier_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { Datatypes.TheType.TheType__copier_q(d), $Is(d, Tclass.Datatypes.TheType()) } 
    { Datatypes.TheType.TheType__builder_q(d), $Is(d, Tclass.Datatypes.TheType()) } 
  $Is(d, Tclass.Datatypes.TheType())
     ==> Datatypes.TheType.TheType__builder_q(d)
       || Datatypes.TheType.TheType__copier_q(d));

// Datatype extensional equality declaration
function Datatypes.TheType#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #Datatypes.TheType.TheType_builder
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { Datatypes.TheType#Equal(a, b), Datatypes.TheType.TheType__builder_q(a) } 
    { Datatypes.TheType#Equal(a, b), Datatypes.TheType.TheType__builder_q(b) } 
  Datatypes.TheType.TheType__builder_q(a)
       && Datatypes.TheType.TheType__builder_q(b)
     ==> (Datatypes.TheType#Equal(a, b)
       <==> Datatypes.TheType.x(a) == Datatypes.TheType.x(b)));

// Datatype extensional equality definition: #Datatypes.TheType.TheType_copier
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { Datatypes.TheType#Equal(a, b), Datatypes.TheType.TheType__copier_q(a) } 
    { Datatypes.TheType#Equal(a, b), Datatypes.TheType.TheType__copier_q(b) } 
  Datatypes.TheType.TheType__copier_q(a) && Datatypes.TheType.TheType__copier_q(b)
     ==> (Datatypes.TheType#Equal(a, b)
       <==> Datatypes.TheType#Equal(Datatypes.TheType.t(a), Datatypes.TheType.t(b))));

// Datatype extensionality axiom: Datatypes.TheType
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { Datatypes.TheType#Equal(a, b) } 
  Datatypes.TheType#Equal(a, b) <==> a == b);

const unique class.Datatypes.TheType: ClassName;

const unique class.Datatypes.__default: ClassName;

function Tclass.Datatypes.__default() : Ty;

const unique Tagclass.Datatypes.__default: TyTag;

// Tclass.Datatypes.__default Tag
axiom Tag(Tclass.Datatypes.__default()) == Tagclass.Datatypes.__default
   && TagFamily(Tclass.Datatypes.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.Datatypes.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.Datatypes.__default()) } 
  $IsBox(bx, Tclass.Datatypes.__default())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.Datatypes.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.Datatypes.__default()) } 
  $Is($o, Tclass.Datatypes.__default())
     <==> $o == null || dtype($o) == Tclass.Datatypes.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.Datatypes.__default(), $h) } 
  $IsAlloc($o, Tclass.Datatypes.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

// function declaration for Datatypes._default.f1
function Datatypes.__default.f1(t#0: DatatypeType) : bool;

function Datatypes.__default.f1#canCall(t#0: DatatypeType) : bool;

// consequence axiom for Datatypes.__default.f1
axiom true
   ==> (forall t#0: DatatypeType :: 
    { Datatypes.__default.f1(t#0) } 
    Datatypes.__default.f1#canCall(t#0)
         || ($Is(t#0, Tclass.Datatypes.TheType())
           && 
          Datatypes.TheType.TheType__builder_q(t#0)
           && Datatypes.TheType.x(t#0) > 3)
       ==> true);

function Datatypes.__default.f1#requires(DatatypeType) : bool;

// #requires axiom for Datatypes.__default.f1
axiom (forall t#0: DatatypeType :: 
  { Datatypes.__default.f1#requires(t#0) } 
  $Is(t#0, Tclass.Datatypes.TheType())
     ==> Datatypes.__default.f1#requires(t#0)
       == (Datatypes.TheType.TheType__builder_q(t#0) && Datatypes.TheType.x(t#0) > 3));

// function declaration for Datatypes._default.test
function Datatypes.__default.test(t#0: DatatypeType) : bool;

function Datatypes.__default.test#canCall(t#0: DatatypeType) : bool;

// consequence axiom for Datatypes.__default.test
axiom true
   ==> (forall t#0: DatatypeType :: 
    { Datatypes.__default.test(t#0) } 
    Datatypes.__default.test#canCall(t#0)
         || ($Is(t#0, Tclass.Datatypes.TheType())
           && 
          Datatypes.TheType.TheType__builder_q(t#0)
           && Datatypes.TheType.x(t#0) > 3)
       ==> true);

function Datatypes.__default.test#requires(DatatypeType) : bool;

// #requires axiom for Datatypes.__default.test
axiom (forall t#0: DatatypeType :: 
  { Datatypes.__default.test#requires(t#0) } 
  $Is(t#0, Tclass.Datatypes.TheType())
     ==> Datatypes.__default.test#requires(t#0)
       == (Datatypes.TheType.TheType__builder_q(t#0) && Datatypes.TheType.x(t#0) > 3));

// definition axiom for Datatypes.__default.test (revealed)
axiom true
   ==> (forall t#0: DatatypeType :: 
    { Datatypes.__default.test(t#0) } 
    Datatypes.__default.test#canCall(t#0)
         || ($Is(t#0, Tclass.Datatypes.TheType())
           && 
          Datatypes.TheType.TheType__builder_q(t#0)
           && Datatypes.TheType.x(t#0) > 3)
       ==> Datatypes.__default.f1#canCall(t#0)
         && Datatypes.__default.test(t#0) == Datatypes.__default.f1(t#0));

// definition axiom for Datatypes.__default.test for all literals (revealed)
axiom true
   ==> (forall t#0: DatatypeType :: 
    {:weight 3} { Datatypes.__default.test(Lit(t#0)) } 
    Datatypes.__default.test#canCall(Lit(t#0))
         || ($Is(t#0, Tclass.Datatypes.TheType())
           && Lit(Datatypes.TheType.TheType__builder_q(Lit(t#0))
               && Datatypes.TheType.x(Lit(t#0)) > 3))
       ==> Datatypes.__default.f1#canCall(Lit(t#0))
         && Datatypes.__default.test(Lit(t#0)) == Datatypes.__default.f1(Lit(t#0)));

// function declaration for Datatypes._default.f2
function Datatypes.__default.f2(x#0: int) : bool;

function Datatypes.__default.f2#canCall(x#0: int) : bool;

// consequence axiom for Datatypes.__default.f2
axiom true
   ==> (forall x#0: int :: 
    { Datatypes.__default.f2(x#0) } 
    Datatypes.__default.f2#canCall(x#0)
         || (forall t#5: DatatypeType :: 
          { Datatypes.TheType.x(t#5) } { Datatypes.TheType.TheType__builder_q(t#5) } 
          $Is(t#5, Tclass.Datatypes.TheType())
             ==> Datatypes.TheType.TheType__builder_q(t#5) && Datatypes.TheType.x(t#5) > x#0)
       ==> true);

function Datatypes.__default.f2#requires(int) : bool;

// #requires axiom for Datatypes.__default.f2
axiom (forall x#0: int :: 
  { Datatypes.__default.f2#requires(x#0) } 
  Datatypes.__default.f2#requires(x#0)
     == (forall t#6: DatatypeType :: 
      { Datatypes.TheType.x(t#6) } { Datatypes.TheType.TheType__builder_q(t#6) } 
      $Is(t#6, Tclass.Datatypes.TheType())
         ==> Datatypes.TheType.TheType__builder_q(t#6) && Datatypes.TheType.x(t#6) > x#0));

// definition axiom for Datatypes.__default.f2 (revealed)
axiom true
   ==> (forall x#0: int :: 
    { Datatypes.__default.f2(x#0) } 
    Datatypes.__default.f2#canCall(x#0)
         || (forall t#6: DatatypeType :: 
          { Datatypes.TheType.x(t#6) } { Datatypes.TheType.TheType__builder_q(t#6) } 
          $Is(t#6, Tclass.Datatypes.TheType())
             ==> Datatypes.TheType.TheType__builder_q(t#6) && Datatypes.TheType.x(t#6) > x#0)
       ==> Datatypes.__default.f2(x#0) == Lit(true));

// definition axiom for Datatypes.__default.f2 for all literals (revealed)
axiom true
   ==> (forall x#0: int :: 
    {:weight 3} { Datatypes.__default.f2(LitInt(x#0)) } 
    Datatypes.__default.f2#canCall(LitInt(x#0))
         || (forall t#7: DatatypeType :: 
          { Datatypes.TheType.x(t#7) } { Datatypes.TheType.TheType__builder_q(t#7) } 
          $Is(t#7, Tclass.Datatypes.TheType())
             ==> Datatypes.TheType.TheType__builder_q(t#7) && Datatypes.TheType.x(t#7) > x#0)
       ==> Datatypes.__default.f2(LitInt(x#0)) == Lit(true));

// function declaration for Datatypes._default.f3
function Datatypes.__default.f3(y#0: int) : bool;

function Datatypes.__default.f3#canCall(y#0: int) : bool;

// consequence axiom for Datatypes.__default.f3
axiom true ==> (forall y#0: int :: { Datatypes.__default.f3(y#0) } true ==> true);

function Datatypes.__default.f3#requires(int) : bool;

// #requires axiom for Datatypes.__default.f3
axiom (forall y#0: int :: 
  { Datatypes.__default.f3#requires(y#0) } 
  Datatypes.__default.f3#requires(y#0) == true);

// definition axiom for Datatypes.__default.f3 (revealed)
axiom true
   ==> (forall y#0: int :: 
    { Datatypes.__default.f3(y#0) } 
    true
       ==> Datatypes.__default.f2#canCall(y#0)
         && Datatypes.__default.f3(y#0) == Datatypes.__default.f2(y#0));

// definition axiom for Datatypes.__default.f3 for all literals (revealed)
axiom true
   ==> (forall y#0: int :: 
    {:weight 3} { Datatypes.__default.f3(LitInt(y#0)) } 
    true
       ==> Datatypes.__default.f2#canCall(LitInt(y#0))
         && Datatypes.__default.f3(LitInt(y#0)) == Lit(Datatypes.__default.f2(LitInt(y#0))));

// function declaration for Datatypes._default.test2
function Datatypes.__default.test2(z#0: int) : bool;

function Datatypes.__default.test2#canCall(z#0: int) : bool;

// consequence axiom for Datatypes.__default.test2
axiom true
   ==> (forall z#0: int :: 
    { Datatypes.__default.test2(z#0) } 
    Datatypes.__default.test2#canCall(z#0)
         || (forall t#6: DatatypeType :: 
          { Datatypes.TheType.x(t#6) } { Datatypes.TheType.TheType__builder_q(t#6) } 
          $Is(t#6, Tclass.Datatypes.TheType())
             ==> Datatypes.TheType.TheType__builder_q(t#6) && Datatypes.TheType.x(t#6) > z#0)
       ==> true);

function Datatypes.__default.test2#requires(int) : bool;

// #requires axiom for Datatypes.__default.test2
axiom (forall z#0: int :: 
  { Datatypes.__default.test2#requires(z#0) } 
  Datatypes.__default.test2#requires(z#0)
     == (forall t#7: DatatypeType :: 
      { Datatypes.TheType.x(t#7) } { Datatypes.TheType.TheType__builder_q(t#7) } 
      $Is(t#7, Tclass.Datatypes.TheType())
         ==> Datatypes.TheType.TheType__builder_q(t#7) && Datatypes.TheType.x(t#7) > z#0));

// definition axiom for Datatypes.__default.test2 (revealed)
axiom true
   ==> (forall z#0: int :: 
    { Datatypes.__default.test2(z#0) } 
    Datatypes.__default.test2#canCall(z#0)
         || (forall t#7: DatatypeType :: 
          { Datatypes.TheType.x(t#7) } { Datatypes.TheType.TheType__builder_q(t#7) } 
          $Is(t#7, Tclass.Datatypes.TheType())
             ==> Datatypes.TheType.TheType__builder_q(t#7) && Datatypes.TheType.x(t#7) > z#0)
       ==> Datatypes.__default.f2#canCall(z#0)
         && Datatypes.__default.test2(z#0) == Datatypes.__default.f2(z#0));

// definition axiom for Datatypes.__default.test2 for all literals (revealed)
axiom true
   ==> (forall z#0: int :: 
    {:weight 3} { Datatypes.__default.test2(LitInt(z#0)) } 
    Datatypes.__default.test2#canCall(LitInt(z#0))
         || (forall t#8: DatatypeType :: 
          { Datatypes.TheType.x(t#8) } { Datatypes.TheType.TheType__builder_q(t#8) } 
          $Is(t#8, Tclass.Datatypes.TheType())
             ==> Datatypes.TheType.TheType__builder_q(t#8) && Datatypes.TheType.x(t#8) > z#0)
       ==> Datatypes.__default.f2#canCall(LitInt(z#0))
         && Datatypes.__default.test2(LitInt(z#0))
           == Lit(Datatypes.__default.f2(LitInt(z#0))));

// Constructor function declaration
function #Matches.TheType.TheType_builder(int) : DatatypeType;

const unique ##Matches.TheType.TheType_builder: DtCtorId;

// Constructor identifier
axiom (forall a#0#0#0: int :: 
  { #Matches.TheType.TheType_builder(a#0#0#0) } 
  DatatypeCtorId(#Matches.TheType.TheType_builder(a#0#0#0))
     == ##Matches.TheType.TheType_builder);

function Matches.TheType.TheType__builder_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { Matches.TheType.TheType__builder_q(d) } 
  Matches.TheType.TheType__builder_q(d)
     <==> DatatypeCtorId(d) == ##Matches.TheType.TheType_builder);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { Matches.TheType.TheType__builder_q(d) } 
  Matches.TheType.TheType__builder_q(d)
     ==> (exists a#1#0#0: int :: d == #Matches.TheType.TheType_builder(a#1#0#0)));

function Tclass.Matches.TheType() : Ty;

const unique Tagclass.Matches.TheType: TyTag;

// Tclass.Matches.TheType Tag
axiom Tag(Tclass.Matches.TheType()) == Tagclass.Matches.TheType
   && TagFamily(Tclass.Matches.TheType()) == tytagFamily$TheType;

// Box/unbox axiom for Tclass.Matches.TheType
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.Matches.TheType()) } 
  $IsBox(bx, Tclass.Matches.TheType())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass.Matches.TheType()));

// Constructor $Is
axiom (forall a#2#0#0: int :: 
  { $Is(#Matches.TheType.TheType_builder(a#2#0#0), Tclass.Matches.TheType()) } 
  $Is(#Matches.TheType.TheType_builder(a#2#0#0), Tclass.Matches.TheType())
     <==> $Is(a#2#0#0, TInt));

// Constructor $IsAlloc
axiom (forall a#3#0#0: int, $h: Heap :: 
  { $IsAlloc(#Matches.TheType.TheType_builder(a#3#0#0), Tclass.Matches.TheType(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#Matches.TheType.TheType_builder(a#3#0#0), Tclass.Matches.TheType(), $h)
       <==> $IsAlloc(a#3#0#0, TInt, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(Matches.TheType.x(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      Matches.TheType.TheType__builder_q(d)
       && $IsAlloc(d, Tclass.Matches.TheType(), $h)
     ==> $IsAlloc(Matches.TheType.x(d), TInt, $h));

// Constructor literal
axiom (forall a#4#0#0: int :: 
  { #Matches.TheType.TheType_builder(LitInt(a#4#0#0)) } 
  #Matches.TheType.TheType_builder(LitInt(a#4#0#0))
     == Lit(#Matches.TheType.TheType_builder(a#4#0#0)));

function Matches.TheType.x(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#5#0#0: int :: 
  { #Matches.TheType.TheType_builder(a#5#0#0) } 
  Matches.TheType.x(#Matches.TheType.TheType_builder(a#5#0#0)) == a#5#0#0);

// Constructor function declaration
function #Matches.TheType.TheType_copier(DatatypeType) : DatatypeType;

const unique ##Matches.TheType.TheType_copier: DtCtorId;

// Constructor identifier
axiom (forall a#6#0#0: DatatypeType :: 
  { #Matches.TheType.TheType_copier(a#6#0#0) } 
  DatatypeCtorId(#Matches.TheType.TheType_copier(a#6#0#0))
     == ##Matches.TheType.TheType_copier);

function Matches.TheType.TheType__copier_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { Matches.TheType.TheType__copier_q(d) } 
  Matches.TheType.TheType__copier_q(d)
     <==> DatatypeCtorId(d) == ##Matches.TheType.TheType_copier);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { Matches.TheType.TheType__copier_q(d) } 
  Matches.TheType.TheType__copier_q(d)
     ==> (exists a#7#0#0: DatatypeType :: d == #Matches.TheType.TheType_copier(a#7#0#0)));

// Constructor $Is
axiom (forall a#8#0#0: DatatypeType :: 
  { $Is(#Matches.TheType.TheType_copier(a#8#0#0), Tclass.Matches.TheType()) } 
  $Is(#Matches.TheType.TheType_copier(a#8#0#0), Tclass.Matches.TheType())
     <==> $Is(a#8#0#0, Tclass.Matches.TheType()));

// Constructor $IsAlloc
axiom (forall a#9#0#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#Matches.TheType.TheType_copier(a#9#0#0), Tclass.Matches.TheType(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#Matches.TheType.TheType_copier(a#9#0#0), Tclass.Matches.TheType(), $h)
       <==> $IsAlloc(a#9#0#0, Tclass.Matches.TheType(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(Matches.TheType.t(d), Tclass.Matches.TheType(), $h) } 
  $IsGoodHeap($h)
       && 
      Matches.TheType.TheType__copier_q(d)
       && $IsAlloc(d, Tclass.Matches.TheType(), $h)
     ==> $IsAlloc(Matches.TheType.t(d), Tclass.Matches.TheType(), $h));

// Constructor literal
axiom (forall a#10#0#0: DatatypeType :: 
  { #Matches.TheType.TheType_copier(Lit(a#10#0#0)) } 
  #Matches.TheType.TheType_copier(Lit(a#10#0#0))
     == Lit(#Matches.TheType.TheType_copier(a#10#0#0)));

function Matches.TheType.t(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#11#0#0: DatatypeType :: 
  { #Matches.TheType.TheType_copier(a#11#0#0) } 
  Matches.TheType.t(#Matches.TheType.TheType_copier(a#11#0#0)) == a#11#0#0);

// Inductive rank
axiom (forall a#12#0#0: DatatypeType :: 
  { #Matches.TheType.TheType_copier(a#12#0#0) } 
  DtRank(a#12#0#0) < DtRank(#Matches.TheType.TheType_copier(a#12#0#0)));

// Depth-one case-split function
function $IsA#Matches.TheType(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#Matches.TheType(d) } 
  $IsA#Matches.TheType(d)
     ==> Matches.TheType.TheType__builder_q(d) || Matches.TheType.TheType__copier_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { Matches.TheType.TheType__copier_q(d), $Is(d, Tclass.Matches.TheType()) } 
    { Matches.TheType.TheType__builder_q(d), $Is(d, Tclass.Matches.TheType()) } 
  $Is(d, Tclass.Matches.TheType())
     ==> Matches.TheType.TheType__builder_q(d) || Matches.TheType.TheType__copier_q(d));

// Datatype extensional equality declaration
function Matches.TheType#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #Matches.TheType.TheType_builder
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { Matches.TheType#Equal(a, b), Matches.TheType.TheType__builder_q(a) } 
    { Matches.TheType#Equal(a, b), Matches.TheType.TheType__builder_q(b) } 
  Matches.TheType.TheType__builder_q(a) && Matches.TheType.TheType__builder_q(b)
     ==> (Matches.TheType#Equal(a, b) <==> Matches.TheType.x(a) == Matches.TheType.x(b)));

// Datatype extensional equality definition: #Matches.TheType.TheType_copier
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { Matches.TheType#Equal(a, b), Matches.TheType.TheType__copier_q(a) } 
    { Matches.TheType#Equal(a, b), Matches.TheType.TheType__copier_q(b) } 
  Matches.TheType.TheType__copier_q(a) && Matches.TheType.TheType__copier_q(b)
     ==> (Matches.TheType#Equal(a, b)
       <==> Matches.TheType#Equal(Matches.TheType.t(a), Matches.TheType.t(b))));

// Datatype extensionality axiom: Matches.TheType
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { Matches.TheType#Equal(a, b) } 
  Matches.TheType#Equal(a, b) <==> a == b);

const unique class.Matches.TheType: ClassName;

const unique class.Matches.__default: ClassName;

function Tclass.Matches.__default() : Ty;

const unique Tagclass.Matches.__default: TyTag;

// Tclass.Matches.__default Tag
axiom Tag(Tclass.Matches.__default()) == Tagclass.Matches.__default
   && TagFamily(Tclass.Matches.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.Matches.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.Matches.__default()) } 
  $IsBox(bx, Tclass.Matches.__default())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.Matches.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.Matches.__default()) } 
  $Is($o, Tclass.Matches.__default())
     <==> $o == null || dtype($o) == Tclass.Matches.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.Matches.__default(), $h) } 
  $IsAlloc($o, Tclass.Matches.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

// function declaration for Matches._default.f1
function Matches.__default.f1(x#0: int) : bool;

function Matches.__default.f1#canCall(x#0: int) : bool;

// consequence axiom for Matches.__default.f1
axiom true
   ==> (forall x#0: int :: 
    { Matches.__default.f1(x#0) } 
    Matches.__default.f1#canCall(x#0) || x#0 > 3 ==> true);

function Matches.__default.f1#requires(int) : bool;

// #requires axiom for Matches.__default.f1
axiom (forall x#0: int :: 
  { Matches.__default.f1#requires(x#0) } 
  Matches.__default.f1#requires(x#0) == (x#0 > 3));

// function declaration for Matches._default.basic_test
function Matches.__default.basic__test(t#0: DatatypeType) : bool;

function Matches.__default.basic__test#canCall(t#0: DatatypeType) : bool;

// consequence axiom for Matches.__default.basic__test
axiom true
   ==> (forall t#0: DatatypeType :: 
    { Matches.__default.basic__test(t#0) } 
    Matches.__default.basic__test#canCall(t#0)
         || ($Is(t#0, Tclass.Matches.TheType())
           && (if Matches.TheType.TheType__builder_q(t#0)
             then (var x#8 := Matches.TheType.x(t#0); x#8 > 3)
             else true))
       ==> true);

function Matches.__default.basic__test#requires(DatatypeType) : bool;

// #requires axiom for Matches.__default.basic__test
axiom (forall t#0: DatatypeType :: 
  { Matches.__default.basic__test#requires(t#0) } 
  $Is(t#0, Tclass.Matches.TheType())
     ==> Matches.__default.basic__test#requires(t#0)
       == (if Matches.TheType.TheType__builder_q(t#0)
         then (var x#9 := Matches.TheType.x(t#0); x#9 > 3)
         else true));

// definition axiom for Matches.__default.basic__test (revealed)
axiom true
   ==> (forall t#0: DatatypeType :: 
    { Matches.__default.basic__test(t#0) } 
    Matches.__default.basic__test#canCall(t#0)
         || ($Is(t#0, Tclass.Matches.TheType())
           && (if Matches.TheType.TheType__builder_q(t#0)
             then (var x#9 := Matches.TheType.x(t#0); x#9 > 3)
             else true))
       ==> (Matches.TheType.TheType__builder_q(t#0)
           ==> (var x#11 := Matches.TheType.x(t#0); Matches.__default.f1#canCall(x#11)))
         && Matches.__default.basic__test(t#0)
           == (if Matches.TheType.TheType__builder_q(t#0)
             then (var x#10 := Matches.TheType.x(t#0); Matches.__default.f1(x#10))
             else (var t#5 := Matches.TheType.t(t#0); Lit(true))));

// definition axiom for Matches.__default.basic__test for all literals (revealed)
axiom true
   ==> (forall t#0: DatatypeType :: 
    {:weight 3} { Matches.__default.basic__test(Lit(t#0)) } 
    Matches.__default.basic__test#canCall(Lit(t#0))
         || ($Is(t#0, Tclass.Matches.TheType())
           && (if Matches.TheType.TheType__builder_q(Lit(t#0))
             then (var x#12 := LitInt(Matches.TheType.x(Lit(t#0))); Lit(x#12 > 3))
             else true))
       ==> (Lit(Matches.TheType.TheType__builder_q(Lit(t#0)))
           ==> (var x#14 := LitInt(Matches.TheType.x(Lit(t#0))); 
            Matches.__default.f1#canCall(x#14)))
         && Matches.__default.basic__test(Lit(t#0))
           == (if Matches.TheType.TheType__builder_q(Lit(t#0))
             then (var x#13 := LitInt(Matches.TheType.x(Lit(t#0))); Matches.__default.f1(x#13))
             else (var t#7 := Lit(Matches.TheType.t(Lit(t#0))); Lit(true))));

const unique class.StaticTest.__default: ClassName;

function Tclass.StaticTest.__default() : Ty;

const unique Tagclass.StaticTest.__default: TyTag;

// Tclass.StaticTest.__default Tag
axiom Tag(Tclass.StaticTest.__default()) == Tagclass.StaticTest.__default
   && TagFamily(Tclass.StaticTest.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.StaticTest.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.StaticTest.__default()) } 
  $IsBox(bx, Tclass.StaticTest.__default())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.StaticTest.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.StaticTest.__default()) } 
  $Is($o, Tclass.StaticTest.__default())
     <==> $o == null || dtype($o) == Tclass.StaticTest.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.StaticTest.__default(), $h) } 
  $IsAlloc($o, Tclass.StaticTest.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

// function declaration for StaticTest._default.f
function StaticTest.__default.f(x#0: int) : bool;

function StaticTest.__default.f#canCall(x#0: int) : bool;

// consequence axiom for StaticTest.__default.f
axiom true
   ==> (forall x#0: int :: 
    { StaticTest.__default.f(x#0) } 
    StaticTest.__default.f#canCall(x#0) || x#0 > 3 ==> true);

function StaticTest.__default.f#requires(int) : bool;

// #requires axiom for StaticTest.__default.f
axiom (forall x#0: int :: 
  { StaticTest.__default.f#requires(x#0) } 
  StaticTest.__default.f#requires(x#0) == (x#0 > 3));

// definition axiom for StaticTest.__default.f (revealed)
axiom true
   ==> (forall x#0: int :: 
    { StaticTest.__default.f(x#0) } 
    StaticTest.__default.f#canCall(x#0) || x#0 > 3
       ==> StaticTest.__default.f(x#0) == (x#0 > 7));

// definition axiom for StaticTest.__default.f for all literals (revealed)
axiom true
   ==> (forall x#0: int :: 
    {:weight 3} { StaticTest.__default.f(LitInt(x#0)) } 
    StaticTest.__default.f#canCall(LitInt(x#0)) || Lit(x#0 > 3)
       ==> StaticTest.__default.f(LitInt(x#0)) == Lit(x#0 > 7));

// function declaration for StaticTest._default.g
function StaticTest.__default.g(z#0: int) : bool;

function StaticTest.__default.g#canCall(z#0: int) : bool;

// consequence axiom for StaticTest.__default.g
axiom true
   ==> (forall z#0: int :: 
    { StaticTest.__default.g(z#0) } 
    StaticTest.__default.g#canCall(z#0) || (z#0 > 3 && StaticTest.__default.f(z#0))
       ==> true);

function StaticTest.__default.g#requires(int) : bool;

// #requires axiom for StaticTest.__default.g
axiom (forall z#0: int :: 
  { StaticTest.__default.g#requires(z#0) } 
  StaticTest.__default.g#requires(z#0) == (z#0 > 3 && StaticTest.__default.f(z#0)));

// definition axiom for StaticTest.__default.g (revealed)
axiom true
   ==> (forall z#0: int :: 
    { StaticTest.__default.g(z#0) } 
    StaticTest.__default.g#canCall(z#0) || (z#0 > 3 && StaticTest.__default.f(z#0))
       ==> StaticTest.__default.g(z#0) == Lit(true));

// definition axiom for StaticTest.__default.g for all literals (revealed)
axiom true
   ==> (forall z#0: int :: 
    {:weight 3} { StaticTest.__default.g(LitInt(z#0)) } 
    StaticTest.__default.g#canCall(LitInt(z#0))
         || (Lit(z#0 > 3) && Lit(StaticTest.__default.f(LitInt(z#0))))
       ==> StaticTest.__default.g(LitInt(z#0)) == Lit(true));

// function declaration for StaticTest._default.h
function StaticTest.__default.h(y#0: int) : bool;

function StaticTest.__default.h#canCall(y#0: int) : bool;

// consequence axiom for StaticTest.__default.h
axiom true
   ==> (forall y#0: int :: 
    { StaticTest.__default.h(y#0) } 
    StaticTest.__default.h#canCall(y#0) || (y#0 > 3 && StaticTest.__default.f(y#0))
       ==> true);

function StaticTest.__default.h#requires(int) : bool;

// #requires axiom for StaticTest.__default.h
axiom (forall y#0: int :: 
  { StaticTest.__default.h#requires(y#0) } 
  StaticTest.__default.h#requires(y#0) == (y#0 > 3 && StaticTest.__default.f(y#0)));

// definition axiom for StaticTest.__default.h (revealed)
axiom true
   ==> (forall y#0: int :: 
    { StaticTest.__default.h(y#0) } 
    StaticTest.__default.h#canCall(y#0) || (y#0 > 3 && StaticTest.__default.f(y#0))
       ==> StaticTest.__default.g#canCall(y#0)
         && StaticTest.__default.h(y#0) == StaticTest.__default.g(y#0));

// definition axiom for StaticTest.__default.h for all literals (revealed)
axiom true
   ==> (forall y#0: int :: 
    {:weight 3} { StaticTest.__default.h(LitInt(y#0)) } 
    StaticTest.__default.h#canCall(LitInt(y#0))
         || (Lit(y#0 > 3) && Lit(StaticTest.__default.f(LitInt(y#0))))
       ==> StaticTest.__default.g#canCall(LitInt(y#0))
         && StaticTest.__default.h(LitInt(y#0)) == Lit(StaticTest.__default.g(LitInt(y#0))));

// function declaration for StaticTest._default.IsEven
function StaticTest.__default.IsEven(x#0: int) : bool;

function StaticTest.__default.IsEven#canCall(x#0: int) : bool;

// consequence axiom for StaticTest.__default.IsEven
axiom true ==> (forall x#0: int :: { StaticTest.__default.IsEven(x#0) } true ==> true);

function StaticTest.__default.IsEven#requires(int) : bool;

// #requires axiom for StaticTest.__default.IsEven
axiom (forall x#0: int :: 
  { StaticTest.__default.IsEven#requires(x#0) } 
  StaticTest.__default.IsEven#requires(x#0) == true);

// function declaration for StaticTest._default.EvenDoubler
function StaticTest.__default.EvenDoubler(x#0: int) : int;

function StaticTest.__default.EvenDoubler#canCall(x#0: int) : bool;

// consequence axiom for StaticTest.__default.EvenDoubler
axiom true
   ==> (forall x#0: int :: 
    { StaticTest.__default.EvenDoubler(x#0) } 
    StaticTest.__default.EvenDoubler#canCall(x#0)
         || StaticTest.__default.IsEven(x#0)
       ==> true);

function StaticTest.__default.EvenDoubler#requires(int) : bool;

// #requires axiom for StaticTest.__default.EvenDoubler
axiom (forall x#0: int :: 
  { StaticTest.__default.EvenDoubler#requires(x#0) } 
  StaticTest.__default.EvenDoubler#requires(x#0)
     == StaticTest.__default.IsEven(x#0));

// function declaration for StaticTest._default.test
function StaticTest.__default.test(y#0: int) : int;

function StaticTest.__default.test#canCall(y#0: int) : bool;

// consequence axiom for StaticTest.__default.test
axiom true
   ==> (forall y#0: int :: 
    { StaticTest.__default.test(y#0) } 
    StaticTest.__default.test#canCall(y#0) || StaticTest.__default.IsEven(y#0)
       ==> true);

function StaticTest.__default.test#requires(int) : bool;

// #requires axiom for StaticTest.__default.test
axiom (forall y#0: int :: 
  { StaticTest.__default.test#requires(y#0) } 
  StaticTest.__default.test#requires(y#0) == StaticTest.__default.IsEven(y#0));

// definition axiom for StaticTest.__default.test (revealed)
axiom true
   ==> (forall y#0: int :: 
    { StaticTest.__default.test(y#0) } 
    StaticTest.__default.test#canCall(y#0) || StaticTest.__default.IsEven(y#0)
       ==> StaticTest.__default.EvenDoubler#canCall(y#0)
         && StaticTest.__default.test(y#0) == StaticTest.__default.EvenDoubler(y#0));

// definition axiom for StaticTest.__default.test for all literals (revealed)
axiom true
   ==> (forall y#0: int :: 
    {:weight 3} { StaticTest.__default.test(LitInt(y#0)) } 
    StaticTest.__default.test#canCall(LitInt(y#0))
         || StaticTest.__default.IsEven(LitInt(y#0))
       ==> StaticTest.__default.EvenDoubler#canCall(LitInt(y#0))
         && StaticTest.__default.test(LitInt(y#0))
           == StaticTest.__default.EvenDoubler(LitInt(y#0)));

const unique class.OpaqueTest.__default: ClassName;

function Tclass.OpaqueTest.__default() : Ty;

const unique Tagclass.OpaqueTest.__default: TyTag;

// Tclass.OpaqueTest.__default Tag
axiom Tag(Tclass.OpaqueTest.__default()) == Tagclass.OpaqueTest.__default
   && TagFamily(Tclass.OpaqueTest.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.OpaqueTest.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.OpaqueTest.__default()) } 
  $IsBox(bx, Tclass.OpaqueTest.__default())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.OpaqueTest.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.OpaqueTest.__default()) } 
  $Is($o, Tclass.OpaqueTest.__default())
     <==> $o == null || dtype($o) == Tclass.OpaqueTest.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.OpaqueTest.__default(), $h) } 
  $IsAlloc($o, Tclass.OpaqueTest.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

// function declaration for OpaqueTest._default.bar
function OpaqueTest.__default.bar(x#0: int) : int;

function OpaqueTest.__default.bar#canCall(x#0: int) : bool;

// consequence axiom for OpaqueTest.__default.bar
axiom true
   ==> (forall x#0: int :: 
    { OpaqueTest.__default.bar(x#0) } 
    OpaqueTest.__default.bar#canCall(x#0) || x#0 > 7 ==> true);

function OpaqueTest.__default.bar#requires(int) : bool;

// #requires axiom for OpaqueTest.__default.bar
axiom (forall x#0: int :: 
  { OpaqueTest.__default.bar#requires(x#0) } 
  OpaqueTest.__default.bar#requires(x#0) == (x#0 > 7));

// definition axiom for OpaqueTest.__default.bar (revealed)
axiom true
   ==> (forall x#0: int :: 
    { OpaqueTest.__default.bar(x#0) } 
    OpaqueTest.__default.bar#canCall(x#0) || x#0 > 7
       ==> OpaqueTest.__default.bar(x#0) == x#0 - 2);

// definition axiom for OpaqueTest.__default.bar for all literals (revealed)
axiom true
   ==> (forall x#0: int :: 
    {:weight 3} { OpaqueTest.__default.bar(LitInt(x#0)) } 
    OpaqueTest.__default.bar#canCall(LitInt(x#0)) || Lit(x#0 > 7)
       ==> OpaqueTest.__default.bar(LitInt(x#0)) == LitInt(x#0 - 2));

// function declaration for OpaqueTest._default.foo
function OpaqueTest.__default.foo($ly: LayerType, x#0: int) : int;

function OpaqueTest.__default.foo#canCall(x#0: int) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, x#0: int :: 
  { OpaqueTest.__default.foo($LS($ly), x#0) } 
  OpaqueTest.__default.foo($LS($ly), x#0) == OpaqueTest.__default.foo($ly, x#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, x#0: int :: 
  { OpaqueTest.__default.foo(AsFuelBottom($ly), x#0) } 
  OpaqueTest.__default.foo($ly, x#0) == OpaqueTest.__default.foo($LZ, x#0));

// consequence axiom for OpaqueTest.__default.foo
axiom true
   ==> (forall $ly: LayerType, x#0: int :: 
    { OpaqueTest.__default.foo($ly, x#0) } 
    OpaqueTest.__default.foo#canCall(x#0) || x#0 > 7 ==> true);

function OpaqueTest.__default.foo#requires(LayerType, int) : bool;

// #requires axiom for OpaqueTest.__default.foo
axiom (forall $ly: LayerType, x#0: int :: 
  { OpaqueTest.__default.foo#requires($ly, x#0) } 
  OpaqueTest.__default.foo#requires($ly, x#0) == (x#0 > 7));

// definition axiom for OpaqueTest.__default.foo (revealed)
axiom true
   ==> (forall $ly: LayerType, x#0: int :: 
    { OpaqueTest.__default.foo($LS($ly), x#0) } 
    OpaqueTest.__default.foo#canCall(x#0) || x#0 > 7
       ==> OpaqueTest.__default.bar#canCall(x#0)
         && OpaqueTest.__default.foo($LS($ly), x#0) == OpaqueTest.__default.bar(x#0));

// definition axiom for OpaqueTest.__default.foo for all literals (revealed)
axiom true
   ==> (forall $ly: LayerType, x#0: int :: 
    {:weight 3} { OpaqueTest.__default.foo($LS($ly), LitInt(x#0)) } 
    OpaqueTest.__default.foo#canCall(LitInt(x#0)) || Lit(x#0 > 7)
       ==> OpaqueTest.__default.bar#canCall(LitInt(x#0))
         && OpaqueTest.__default.foo($LS($ly), LitInt(x#0))
           == LitInt(OpaqueTest.__default.bar(LitInt(x#0))));

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

const unique tytagFamily$_default: TyTagFamily;

const unique tytagFamily$TheType: TyTagFamily;
