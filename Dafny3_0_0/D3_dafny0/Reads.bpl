// Dafny 3.0.0.30204
// Command Line Options: -compile:0 -noVerify /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Reads.dfy -print:./Reads.bpl

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
axiom (forall a#5#0#0: Box, a#5#1#0: Box :: 
  { #_System._tuple#2._#Make2(a#5#0#0, a#5#1#0) } 
  DatatypeCtorId(#_System._tuple#2._#Make2(a#5#0#0, a#5#1#0))
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
     ==> (exists a#6#0#0: Box, a#6#1#0: Box :: 
      d == #_System._tuple#2._#Make2(a#6#0#0, a#6#1#0)));

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
axiom (forall _System._tuple#2$T0: Ty, _System._tuple#2$T1: Ty, a#7#0#0: Box, a#7#1#0: Box :: 
  { $Is(#_System._tuple#2._#Make2(a#7#0#0, a#7#1#0), 
      Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1)) } 
  $Is(#_System._tuple#2._#Make2(a#7#0#0, a#7#1#0), 
      Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1))
     <==> $IsBox(a#7#0#0, _System._tuple#2$T0) && $IsBox(a#7#1#0, _System._tuple#2$T1));

// Constructor $IsAlloc
axiom (forall _System._tuple#2$T0: Ty, 
    _System._tuple#2$T1: Ty, 
    a#8#0#0: Box, 
    a#8#1#0: Box, 
    $h: Heap :: 
  { $IsAlloc(#_System._tuple#2._#Make2(a#8#0#0, a#8#1#0), 
      Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_System._tuple#2._#Make2(a#8#0#0, a#8#1#0), 
        Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1), 
        $h)
       <==> $IsAllocBox(a#8#0#0, _System._tuple#2$T0, $h)
         && $IsAllocBox(a#8#1#0, _System._tuple#2$T1, $h)));

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
axiom (forall a#9#0#0: Box, a#9#1#0: Box :: 
  { #_System._tuple#2._#Make2(Lit(a#9#0#0), Lit(a#9#1#0)) } 
  #_System._tuple#2._#Make2(Lit(a#9#0#0), Lit(a#9#1#0))
     == Lit(#_System._tuple#2._#Make2(a#9#0#0, a#9#1#0)));

// Constructor injectivity
axiom (forall a#10#0#0: Box, a#10#1#0: Box :: 
  { #_System._tuple#2._#Make2(a#10#0#0, a#10#1#0) } 
  _System.Tuple2._0(#_System._tuple#2._#Make2(a#10#0#0, a#10#1#0)) == a#10#0#0);

// Inductive rank
axiom (forall a#11#0#0: Box, a#11#1#0: Box :: 
  { #_System._tuple#2._#Make2(a#11#0#0, a#11#1#0) } 
  BoxRank(a#11#0#0) < DtRank(#_System._tuple#2._#Make2(a#11#0#0, a#11#1#0)));

// Constructor injectivity
axiom (forall a#12#0#0: Box, a#12#1#0: Box :: 
  { #_System._tuple#2._#Make2(a#12#0#0, a#12#1#0) } 
  _System.Tuple2._1(#_System._tuple#2._#Make2(a#12#0#0, a#12#1#0)) == a#12#1#0);

// Inductive rank
axiom (forall a#13#0#0: Box, a#13#1#0: Box :: 
  { #_System._tuple#2._#Make2(a#13#0#0, a#13#1#0) } 
  BoxRank(a#13#1#0) < DtRank(#_System._tuple#2._#Make2(a#13#0#0, a#13#1#0)));

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

axiom FDim(_module.C.u) == 0
   && FieldOfDecl(class._module.C?, field$u) == _module.C.u
   && !$IsGhostField(_module.C.u);

const _module.C.u: Field int;

// C.u: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.C.u) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.C?()
     ==> $Is(read($h, $o, _module.C.u), TInt));

// C.u: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.C.u) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.C?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.C.u), TInt, $h));

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

// _module.C: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.C()) } 
  $Is(c#0, Tclass._module.C()) <==> $Is(c#0, Tclass._module.C?()) && c#0 != null);

// _module.C: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.C(), $h) } 
  $IsAlloc(c#0, Tclass._module.C(), $h)
     <==> $IsAlloc(c#0, Tclass._module.C?(), $h));

const unique class._module.R?: ClassName;

function Tclass._module.R?() : Ty;

const unique Tagclass._module.R?: TyTag;

// Tclass._module.R? Tag
axiom Tag(Tclass._module.R?()) == Tagclass._module.R?
   && TagFamily(Tclass._module.R?()) == tytagFamily$R;

// Box/unbox axiom for Tclass._module.R?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.R?()) } 
  $IsBox(bx, Tclass._module.R?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.R?()));

// R: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.R?()) } 
  $Is($o, Tclass._module.R?()) <==> $o == null || dtype($o) == Tclass._module.R?());

// R: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.R?(), $h) } 
  $IsAlloc($o, Tclass._module.R?(), $h) <==> $o == null || read($h, $o, alloc));

axiom FDim(_module.R.r) == 0
   && FieldOfDecl(class._module.R?, field$r) == _module.R.r
   && !$IsGhostField(_module.R.r);

const _module.R.r: Field ref;

function Tclass._module.R() : Ty;

const unique Tagclass._module.R: TyTag;

// Tclass._module.R Tag
axiom Tag(Tclass._module.R()) == Tagclass._module.R
   && TagFamily(Tclass._module.R()) == tytagFamily$R;

// Box/unbox axiom for Tclass._module.R
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.R()) } 
  $IsBox(bx, Tclass._module.R())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.R()));

// R.r: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.R.r) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.R?()
     ==> $Is(read($h, $o, _module.R.r), Tclass._module.R()));

// R.r: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.R.r) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.R?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.R.r), Tclass._module.R(), $h));

procedure CheckWellformed$$_module.R.__ctor(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.R())
         && $IsAlloc(this, Tclass._module.R(), $Heap));
  free requires 21 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.R.__ctor()
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass._module.R())
         && $IsAlloc(this, Tclass._module.R(), $Heap));
  modifies $Heap, $Tick;
  // constructor allocates the object
  ensures !read(old($Heap), this, alloc);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.R.__ctor()
   returns (this: ref where this != null && $Is(this, Tclass._module.R()), 
    $_reverifyPost: bool);
  free requires 21 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.R.__ctor() returns (this: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var this.r: ref;
  var defass#this.r: bool;

    // AddMethodImpl: _ctor, Impl$$_module.R.__ctor
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Reads.dfy(50,17): initial state"} true;
    $_reverifyPost := false;
    // ----- divided block before new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Reads.dfy(50,18)
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Reads.dfy(51,7)
    assume true;
    assume true;
    this.r := this;
    defass#this.r := true;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Reads.dfy(51,13)"} true;
    // ----- new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Reads.dfy(50,18)
    assert defass#this.r;
    assume !read($Heap, this, alloc);
    assume read($Heap, this, _module.R.r) == this.r;
    $Heap := update($Heap, this, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    // ----- divided block after new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Reads.dfy(50,18)
}



// _module.R: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.R()) } 
  $Is(c#0, Tclass._module.R()) <==> $Is(c#0, Tclass._module.R?()) && c#0 != null);

// _module.R: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.R(), $h) } 
  $IsAlloc(c#0, Tclass._module.R(), $h)
     <==> $IsAlloc(c#0, Tclass._module.R?(), $h));

const unique class._module.CircularChecking?: ClassName;

function Tclass._module.CircularChecking?() : Ty;

const unique Tagclass._module.CircularChecking?: TyTag;

// Tclass._module.CircularChecking? Tag
axiom Tag(Tclass._module.CircularChecking?()) == Tagclass._module.CircularChecking?
   && TagFamily(Tclass._module.CircularChecking?()) == tytagFamily$CircularChecking;

// Box/unbox axiom for Tclass._module.CircularChecking?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.CircularChecking?()) } 
  $IsBox(bx, Tclass._module.CircularChecking?())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.CircularChecking?()));

// CircularChecking: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.CircularChecking?()) } 
  $Is($o, Tclass._module.CircularChecking?())
     <==> $o == null || dtype($o) == Tclass._module.CircularChecking?());

// CircularChecking: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.CircularChecking?(), $h) } 
  $IsAlloc($o, Tclass._module.CircularChecking?(), $h)
     <==> $o == null || read($h, $o, alloc));

axiom FDim(_module.CircularChecking.Repr) == 0
   && FieldOfDecl(class._module.CircularChecking?, field$Repr)
     == _module.CircularChecking.Repr
   && $IsGhostField(_module.CircularChecking.Repr);

const _module.CircularChecking.Repr: Field (Set Box);

// CircularChecking.Repr: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.CircularChecking.Repr) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.CircularChecking?()
     ==> $Is(read($h, $o, _module.CircularChecking.Repr), TSet(Tclass._System.object())));

// CircularChecking.Repr: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.CircularChecking.Repr) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.CircularChecking?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.CircularChecking.Repr), TSet(Tclass._System.object()), $h));

// function declaration for _module.CircularChecking.F
function _module.CircularChecking.F($heap: Heap, this: ref) : int;

function _module.CircularChecking.F#canCall($heap: Heap, this: ref) : bool;

function Tclass._module.CircularChecking() : Ty;

const unique Tagclass._module.CircularChecking: TyTag;

// Tclass._module.CircularChecking Tag
axiom Tag(Tclass._module.CircularChecking()) == Tagclass._module.CircularChecking
   && TagFamily(Tclass._module.CircularChecking()) == tytagFamily$CircularChecking;

// Box/unbox axiom for Tclass._module.CircularChecking
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.CircularChecking()) } 
  $IsBox(bx, Tclass._module.CircularChecking())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.CircularChecking()));

// frame axiom for _module.CircularChecking.F
axiom (forall $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.CircularChecking.F($h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.CircularChecking())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && ($o == this || read($h0, this, _module.CircularChecking.Repr)[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.CircularChecking.F($h0, this) == _module.CircularChecking.F($h1, this));

// consequence axiom for _module.CircularChecking.F
axiom 16 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref :: 
    { _module.CircularChecking.F($Heap, this) } 
    _module.CircularChecking.F#canCall($Heap, this)
         || (16 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.CircularChecking())
           && $IsAlloc(this, Tclass._module.CircularChecking(), $Heap))
       ==> true);

function _module.CircularChecking.F#requires(Heap, ref) : bool;

// #requires axiom for _module.CircularChecking.F
axiom (forall $Heap: Heap, this: ref :: 
  { _module.CircularChecking.F#requires($Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.CircularChecking())
       && $IsAlloc(this, Tclass._module.CircularChecking(), $Heap)
     ==> _module.CircularChecking.F#requires($Heap, this) == true);

procedure CheckWellformed$$_module.CircularChecking.F(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.CircularChecking())
         && $IsAlloc(this, Tclass._module.CircularChecking(), $Heap));
  free requires 16 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.CircularChecking.F(this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function F
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Reads.dfy(68,11): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> $o == this || read($Heap, this, _module.CircularChecking.Repr)[$Box($o)]);
    b$reqreads#0 := $_Frame[this, _module.CircularChecking.Repr];
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



// function declaration for _module.CircularChecking.F'
function _module.CircularChecking.F_k($heap: Heap, this: ref) : int;

function _module.CircularChecking.F_k#canCall($heap: Heap, this: ref) : bool;

// frame axiom for _module.CircularChecking.F_k
axiom (forall $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.CircularChecking.F_k($h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.CircularChecking())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && (read($h0, this, _module.CircularChecking.Repr)[$Box($o)] || $o == this)
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.CircularChecking.F_k($h0, this)
       == _module.CircularChecking.F_k($h1, this));

// consequence axiom for _module.CircularChecking.F_k
axiom 24 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref :: 
    { _module.CircularChecking.F_k($Heap, this) } 
    _module.CircularChecking.F_k#canCall($Heap, this)
         || (24 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.CircularChecking())
           && $IsAlloc(this, Tclass._module.CircularChecking(), $Heap))
       ==> true);

function _module.CircularChecking.F_k#requires(Heap, ref) : bool;

// #requires axiom for _module.CircularChecking.F_k
axiom (forall $Heap: Heap, this: ref :: 
  { _module.CircularChecking.F_k#requires($Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.CircularChecking())
       && $IsAlloc(this, Tclass._module.CircularChecking(), $Heap)
     ==> _module.CircularChecking.F_k#requires($Heap, this) == true);

procedure CheckWellformed$$_module.CircularChecking.F_k(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.CircularChecking())
         && $IsAlloc(this, Tclass._module.CircularChecking(), $Heap));
  free requires 24 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.CircularChecking.F_k(this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function F'
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Reads.dfy(71,11): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.CircularChecking.Repr)[$Box($o)] || $o == this);
    b$reqreads#0 := $_Frame[this, _module.CircularChecking.Repr];
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



// function declaration for _module.CircularChecking.G0
function _module.CircularChecking.G0($heap: Heap, this: ref) : int;

function _module.CircularChecking.G0#canCall($heap: Heap, this: ref) : bool;

// frame axiom for _module.CircularChecking.G0
axiom (forall $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.CircularChecking.G0($h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.CircularChecking())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && $o == this ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.CircularChecking.G0($h0, this) == _module.CircularChecking.G0($h1, this));

// consequence axiom for _module.CircularChecking.G0
axiom 17 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref :: 
    { _module.CircularChecking.G0($Heap, this) } 
    _module.CircularChecking.G0#canCall($Heap, this)
         || (17 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.CircularChecking())
           && $IsAlloc(this, Tclass._module.CircularChecking(), $Heap)
           && 
          Set#Equal(read($Heap, this, _module.CircularChecking.Repr), Set#Empty(): Set Box)
           && _module.CircularChecking.F($Heap, this) == LitInt(100))
       ==> true);

function _module.CircularChecking.G0#requires(Heap, ref) : bool;

// #requires axiom for _module.CircularChecking.G0
axiom (forall $Heap: Heap, this: ref :: 
  { _module.CircularChecking.G0#requires($Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.CircularChecking())
       && $IsAlloc(this, Tclass._module.CircularChecking(), $Heap)
     ==> _module.CircularChecking.G0#requires($Heap, this)
       == (Set#Equal(read($Heap, this, _module.CircularChecking.Repr), Set#Empty(): Set Box)
         && _module.CircularChecking.F($Heap, this) == LitInt(100)));

procedure CheckWellformed$$_module.CircularChecking.G0(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.CircularChecking())
         && $IsAlloc(this, Tclass._module.CircularChecking(), $Heap));
  free requires 17 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.CircularChecking.G0(this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function G0
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Reads.dfy(74,11): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    b$reqreads#0 := $_Frame[this, _module.CircularChecking.Repr];
    assume Set#Equal(read($Heap, this, _module.CircularChecking.Repr), Set#Empty(): Set Box);
    b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && read($Heap, $o, alloc)
           && ($o == this || read($Heap, this, _module.CircularChecking.Repr)[$Box($o)])
         ==> $_Frame[$o, $f]);
    assume _module.CircularChecking.F#canCall($Heap, this);
    assume _module.CircularChecking.F($Heap, this) == LitInt(100);
    assert b$reqreads#0;
    assert b$reqreads#1;
    if (*)
    {
        assume false;
    }
    else
    {
        assume false;
    }
}



// function declaration for _module.CircularChecking.G1
function _module.CircularChecking.G1($heap: Heap, this: ref) : int;

function _module.CircularChecking.G1#canCall($heap: Heap, this: ref) : bool;

// frame axiom for _module.CircularChecking.G1
axiom (forall $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.CircularChecking.G1($h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.CircularChecking())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && $o == this ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.CircularChecking.G1($h0, this) == _module.CircularChecking.G1($h1, this));

// consequence axiom for _module.CircularChecking.G1
axiom 18 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref :: 
    { _module.CircularChecking.G1($Heap, this) } 
    _module.CircularChecking.G1#canCall($Heap, this)
         || (18 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.CircularChecking())
           && $IsAlloc(this, Tclass._module.CircularChecking(), $Heap)
           && 
          _module.CircularChecking.F($Heap, this) == LitInt(100)
           && Set#Equal(read($Heap, this, _module.CircularChecking.Repr), Set#Empty(): Set Box))
       ==> true);

function _module.CircularChecking.G1#requires(Heap, ref) : bool;

// #requires axiom for _module.CircularChecking.G1
axiom (forall $Heap: Heap, this: ref :: 
  { _module.CircularChecking.G1#requires($Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.CircularChecking())
       && $IsAlloc(this, Tclass._module.CircularChecking(), $Heap)
     ==> _module.CircularChecking.G1#requires($Heap, this)
       == (_module.CircularChecking.F($Heap, this) == LitInt(100)
         && Set#Equal(read($Heap, this, _module.CircularChecking.Repr), Set#Empty(): Set Box)));

procedure CheckWellformed$$_module.CircularChecking.G1(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.CircularChecking())
         && $IsAlloc(this, Tclass._module.CircularChecking(), $Heap));
  free requires 18 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.CircularChecking.G1(this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function G1
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Reads.dfy(78,11): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && read($Heap, $o, alloc)
           && ($o == this || read($Heap, this, _module.CircularChecking.Repr)[$Box($o)])
         ==> $_Frame[$o, $f]);
    assume _module.CircularChecking.F#canCall($Heap, this);
    assume _module.CircularChecking.F($Heap, this) == LitInt(100);
    b$reqreads#1 := $_Frame[this, _module.CircularChecking.Repr];
    assume Set#Equal(read($Heap, this, _module.CircularChecking.Repr), Set#Empty(): Set Box);
    assert b$reqreads#0;
    assert b$reqreads#1;
    if (*)
    {
        assume false;
    }
    else
    {
        assume false;
    }
}



// function declaration for _module.CircularChecking.H0
function _module.CircularChecking.H0($heap: Heap, this: ref, cell#0: ref) : int;

function _module.CircularChecking.H0#canCall($heap: Heap, this: ref, cell#0: ref) : bool;

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

// frame axiom for _module.CircularChecking.H0
axiom (forall $h0: Heap, $h1: Heap, this: ref, cell#0: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.CircularChecking.H0($h1, this, cell#0) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.CircularChecking())
       && (_module.CircularChecking.H0#canCall($h0, this, cell#0)
         || $Is(cell#0, Tclass._module.Cell()))
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($h0, this, _module.CircularChecking.Repr)[$Box($o)]
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.CircularChecking.H0($h0, this, cell#0)
       == _module.CircularChecking.H0($h1, this, cell#0));

// consequence axiom for _module.CircularChecking.H0
axiom 1 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref, cell#0: ref :: 
    { _module.CircularChecking.H0($Heap, this, cell#0) } 
    _module.CircularChecking.H0#canCall($Heap, this, cell#0)
         || (1 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.CircularChecking())
           && $IsAlloc(this, Tclass._module.CircularChecking(), $Heap)
           && $Is(cell#0, Tclass._module.Cell())
           && read($Heap, this, _module.CircularChecking.Repr)[$Box(this)])
       ==> true);

function _module.CircularChecking.H0#requires(Heap, ref, ref) : bool;

// #requires axiom for _module.CircularChecking.H0
axiom (forall $Heap: Heap, this: ref, cell#0: ref :: 
  { _module.CircularChecking.H0#requires($Heap, this, cell#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.CircularChecking())
       && $IsAlloc(this, Tclass._module.CircularChecking(), $Heap)
       && $Is(cell#0, Tclass._module.Cell())
     ==> _module.CircularChecking.H0#requires($Heap, this, cell#0)
       == read($Heap, this, _module.CircularChecking.Repr)[$Box(this)]);

procedure CheckWellformed$$_module.CircularChecking.H0(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.CircularChecking())
         && $IsAlloc(this, Tclass._module.CircularChecking(), $Heap), 
    cell#0: ref where $Is(cell#0, Tclass._module.Cell()));
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.CircularChecking.H0(this: ref, cell#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function H0
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Reads.dfy(83,11): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.CircularChecking.Repr)[$Box($o)]);
    b$reqreads#0 := $_Frame[this, _module.CircularChecking.Repr];
    assume read($Heap, this, _module.CircularChecking.Repr)[$Box(this)];
    assert b$reqreads#0;
    b$reqreads#1 := $_Frame[this, _module.CircularChecking.Repr];
    assert b$reqreads#1;
    if (*)
    {
        assume false;
    }
    else
    {
        assume false;
    }
}



// function declaration for _module.CircularChecking.H1
function _module.CircularChecking.H1($heap: Heap, this: ref, cell#0: ref) : int;

function _module.CircularChecking.H1#canCall($heap: Heap, this: ref, cell#0: ref) : bool;

// frame axiom for _module.CircularChecking.H1
axiom (forall $h0: Heap, $h1: Heap, this: ref, cell#0: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.CircularChecking.H1($h1, this, cell#0) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.CircularChecking())
       && (_module.CircularChecking.H1#canCall($h0, this, cell#0)
         || $Is(cell#0, Tclass._module.Cell()))
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && ($o == this || read($h0, this, _module.CircularChecking.Repr)[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.CircularChecking.H1($h0, this, cell#0)
       == _module.CircularChecking.H1($h1, this, cell#0));

axiom FDim(_module.Cell.data) == 0
   && FieldOfDecl(class._module.Cell?, field$data) == _module.Cell.data
   && !$IsGhostField(_module.Cell.data);

// consequence axiom for _module.CircularChecking.H1
axiom 2 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref, cell#0: ref :: 
    { _module.CircularChecking.H1($Heap, this, cell#0) } 
    _module.CircularChecking.H1#canCall($Heap, this, cell#0)
         || (2 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.CircularChecking())
           && $IsAlloc(this, Tclass._module.CircularChecking(), $Heap)
           && $Is(cell#0, Tclass._module.Cell())
           && 
          read($Heap, this, _module.CircularChecking.Repr)[$Box(cell#0)]
           && read($Heap, cell#0, _module.Cell.data) == LitInt(10))
       ==> true);

function _module.CircularChecking.H1#requires(Heap, ref, ref) : bool;

// #requires axiom for _module.CircularChecking.H1
axiom (forall $Heap: Heap, this: ref, cell#0: ref :: 
  { _module.CircularChecking.H1#requires($Heap, this, cell#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.CircularChecking())
       && $IsAlloc(this, Tclass._module.CircularChecking(), $Heap)
       && $Is(cell#0, Tclass._module.Cell())
     ==> _module.CircularChecking.H1#requires($Heap, this, cell#0)
       == (read($Heap, this, _module.CircularChecking.Repr)[$Box(cell#0)]
         && read($Heap, cell#0, _module.Cell.data) == LitInt(10)));

procedure CheckWellformed$$_module.CircularChecking.H1(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.CircularChecking())
         && $IsAlloc(this, Tclass._module.CircularChecking(), $Heap), 
    cell#0: ref where $Is(cell#0, Tclass._module.Cell()));
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.CircularChecking.H1(this: ref, cell#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;
  var b$reqreads#2: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;

    // AddWellformednessCheck for function H1
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Reads.dfy(87,11): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> $o == this || read($Heap, this, _module.CircularChecking.Repr)[$Box($o)]);
    b$reqreads#0 := $_Frame[this, _module.CircularChecking.Repr];
    assume read($Heap, this, _module.CircularChecking.Repr)[$Box(cell#0)];
    assert cell#0 != null;
    b$reqreads#1 := $_Frame[cell#0, _module.Cell.data];
    assume read($Heap, cell#0, _module.Cell.data) == LitInt(10);
    assert b$reqreads#0;
    assert b$reqreads#1;
    b$reqreads#2 := $_Frame[this, _module.CircularChecking.Repr];
    assert b$reqreads#2;
    if (*)
    {
        assume false;
    }
    else
    {
        assume false;
    }
}



// function declaration for _module.CircularChecking.H2
function _module.CircularChecking.H2($heap: Heap, this: ref, cell#0: ref) : int;

function _module.CircularChecking.H2#canCall($heap: Heap, this: ref, cell#0: ref) : bool;

// frame axiom for _module.CircularChecking.H2
axiom (forall $h0: Heap, $h1: Heap, this: ref, cell#0: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.CircularChecking.H2($h1, this, cell#0) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.CircularChecking())
       && (_module.CircularChecking.H2#canCall($h0, this, cell#0)
         || $Is(cell#0, Tclass._module.Cell()))
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && ($o == this || read($h0, this, _module.CircularChecking.Repr)[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.CircularChecking.H2($h0, this, cell#0)
       == _module.CircularChecking.H2($h1, this, cell#0));

// consequence axiom for _module.CircularChecking.H2
axiom 3 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref, cell#0: ref :: 
    { _module.CircularChecking.H2($Heap, this, cell#0) } 
    _module.CircularChecking.H2#canCall($Heap, this, cell#0)
         || (3 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.CircularChecking())
           && $IsAlloc(this, Tclass._module.CircularChecking(), $Heap)
           && $Is(cell#0, Tclass._module.Cell())
           && 
          read($Heap, cell#0, _module.Cell.data) == LitInt(10)
           && read($Heap, this, _module.CircularChecking.Repr)[$Box(cell#0)])
       ==> true);

function _module.CircularChecking.H2#requires(Heap, ref, ref) : bool;

// #requires axiom for _module.CircularChecking.H2
axiom (forall $Heap: Heap, this: ref, cell#0: ref :: 
  { _module.CircularChecking.H2#requires($Heap, this, cell#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.CircularChecking())
       && $IsAlloc(this, Tclass._module.CircularChecking(), $Heap)
       && $Is(cell#0, Tclass._module.Cell())
     ==> _module.CircularChecking.H2#requires($Heap, this, cell#0)
       == (read($Heap, cell#0, _module.Cell.data) == LitInt(10)
         && read($Heap, this, _module.CircularChecking.Repr)[$Box(cell#0)]));

procedure CheckWellformed$$_module.CircularChecking.H2(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.CircularChecking())
         && $IsAlloc(this, Tclass._module.CircularChecking(), $Heap), 
    cell#0: ref where $Is(cell#0, Tclass._module.Cell()));
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.CircularChecking.H2(this: ref, cell#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;
  var b$reqreads#2: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;

    // AddWellformednessCheck for function H2
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Reads.dfy(92,11): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> $o == this || read($Heap, this, _module.CircularChecking.Repr)[$Box($o)]);
    assert cell#0 != null;
    b$reqreads#0 := $_Frame[cell#0, _module.Cell.data];
    assume read($Heap, cell#0, _module.Cell.data) == LitInt(10);
    b$reqreads#1 := $_Frame[this, _module.CircularChecking.Repr];
    assume read($Heap, this, _module.CircularChecking.Repr)[$Box(cell#0)];
    assert b$reqreads#0;
    assert b$reqreads#1;
    b$reqreads#2 := $_Frame[this, _module.CircularChecking.Repr];
    assert b$reqreads#2;
    if (*)
    {
        assume false;
    }
    else
    {
        assume false;
    }
}



// _module.CircularChecking: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.CircularChecking()) } 
  $Is(c#0, Tclass._module.CircularChecking())
     <==> $Is(c#0, Tclass._module.CircularChecking?()) && c#0 != null);

// _module.CircularChecking: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.CircularChecking(), $h) } 
  $IsAlloc(c#0, Tclass._module.CircularChecking(), $h)
     <==> $IsAlloc(c#0, Tclass._module.CircularChecking?(), $h));

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

const unique class._module.DynamicFramesIdiom?: ClassName;

function Tclass._module.DynamicFramesIdiom?() : Ty;

const unique Tagclass._module.DynamicFramesIdiom?: TyTag;

// Tclass._module.DynamicFramesIdiom? Tag
axiom Tag(Tclass._module.DynamicFramesIdiom?())
     == Tagclass._module.DynamicFramesIdiom?
   && TagFamily(Tclass._module.DynamicFramesIdiom?())
     == tytagFamily$DynamicFramesIdiom;

// Box/unbox axiom for Tclass._module.DynamicFramesIdiom?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.DynamicFramesIdiom?()) } 
  $IsBox(bx, Tclass._module.DynamicFramesIdiom?())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.DynamicFramesIdiom?()));

// DynamicFramesIdiom: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.DynamicFramesIdiom?()) } 
  $Is($o, Tclass._module.DynamicFramesIdiom?())
     <==> $o == null || dtype($o) == Tclass._module.DynamicFramesIdiom?());

// DynamicFramesIdiom: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.DynamicFramesIdiom?(), $h) } 
  $IsAlloc($o, Tclass._module.DynamicFramesIdiom?(), $h)
     <==> $o == null || read($h, $o, alloc));

axiom FDim(_module.DynamicFramesIdiom.Repr) == 0
   && FieldOfDecl(class._module.DynamicFramesIdiom?, field$Repr)
     == _module.DynamicFramesIdiom.Repr
   && $IsGhostField(_module.DynamicFramesIdiom.Repr);

const _module.DynamicFramesIdiom.Repr: Field (Set Box);

// DynamicFramesIdiom.Repr: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.DynamicFramesIdiom.Repr) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.DynamicFramesIdiom?()
     ==> $Is(read($h, $o, _module.DynamicFramesIdiom.Repr), TSet(Tclass._System.object())));

// DynamicFramesIdiom.Repr: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.DynamicFramesIdiom.Repr) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.DynamicFramesIdiom?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.DynamicFramesIdiom.Repr), TSet(Tclass._System.object()), $h));

// function declaration for _module.DynamicFramesIdiom.IllFormed_Valid
function _module.DynamicFramesIdiom.IllFormed__Valid($heap: Heap, this: ref) : bool;

function _module.DynamicFramesIdiom.IllFormed__Valid#canCall($heap: Heap, this: ref) : bool;

function Tclass._module.DynamicFramesIdiom() : Ty;

const unique Tagclass._module.DynamicFramesIdiom: TyTag;

// Tclass._module.DynamicFramesIdiom Tag
axiom Tag(Tclass._module.DynamicFramesIdiom()) == Tagclass._module.DynamicFramesIdiom
   && TagFamily(Tclass._module.DynamicFramesIdiom()) == tytagFamily$DynamicFramesIdiom;

// Box/unbox axiom for Tclass._module.DynamicFramesIdiom
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.DynamicFramesIdiom()) } 
  $IsBox(bx, Tclass._module.DynamicFramesIdiom())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.DynamicFramesIdiom()));

// frame axiom for _module.DynamicFramesIdiom.IllFormed__Valid
axiom (forall $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.DynamicFramesIdiom.IllFormed__Valid($h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.DynamicFramesIdiom())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($h0, this, _module.DynamicFramesIdiom.Repr)[$Box($o)]
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.DynamicFramesIdiom.IllFormed__Valid($h0, this)
       == _module.DynamicFramesIdiom.IllFormed__Valid($h1, this));

// consequence axiom for _module.DynamicFramesIdiom.IllFormed__Valid
axiom 22 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref :: 
    { _module.DynamicFramesIdiom.IllFormed__Valid($Heap, this) } 
    _module.DynamicFramesIdiom.IllFormed__Valid#canCall($Heap, this)
         || (22 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.DynamicFramesIdiom())
           && $IsAlloc(this, Tclass._module.DynamicFramesIdiom(), $Heap))
       ==> true);

function _module.DynamicFramesIdiom.IllFormed__Valid#requires(Heap, ref) : bool;

// #requires axiom for _module.DynamicFramesIdiom.IllFormed__Valid
axiom (forall $Heap: Heap, this: ref :: 
  { _module.DynamicFramesIdiom.IllFormed__Valid#requires($Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.DynamicFramesIdiom())
       && $IsAlloc(this, Tclass._module.DynamicFramesIdiom(), $Heap)
     ==> _module.DynamicFramesIdiom.IllFormed__Valid#requires($Heap, this) == true);

// definition axiom for _module.DynamicFramesIdiom.IllFormed__Valid (revealed)
axiom 22 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref :: 
    { _module.DynamicFramesIdiom.IllFormed__Valid($Heap, this), $IsGoodHeap($Heap) } 
    _module.DynamicFramesIdiom.IllFormed__Valid#canCall($Heap, this)
         || (22 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.DynamicFramesIdiom())
           && $IsAlloc(this, Tclass._module.DynamicFramesIdiom(), $Heap))
       ==> _module.DynamicFramesIdiom.IllFormed__Valid($Heap, this)
         == read($Heap, this, _module.DynamicFramesIdiom.Repr)[$Box(this)]);

procedure CheckWellformed$$_module.DynamicFramesIdiom.IllFormed__Valid(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.DynamicFramesIdiom())
         && $IsAlloc(this, Tclass._module.DynamicFramesIdiom(), $Heap));
  free requires 22 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.DynamicFramesIdiom.IllFormed__Valid(this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function IllFormed_Valid
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Reads.dfy(137,12): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.DynamicFramesIdiom.Repr)[$Box($o)]);
    b$reqreads#0 := $_Frame[this, _module.DynamicFramesIdiom.Repr];
    assert b$reqreads#0;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc)
             ==> read($Heap, this, _module.DynamicFramesIdiom.Repr)[$Box($o)]);
        b$reqreads#1 := $_Frame[this, _module.DynamicFramesIdiom.Repr];
        assume _module.DynamicFramesIdiom.IllFormed__Valid($Heap, this)
           == read($Heap, this, _module.DynamicFramesIdiom.Repr)[$Box(this)];
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.DynamicFramesIdiom.IllFormed__Valid($Heap, this), TBool);
        assert b$reqreads#1;
    }
}



// _module.DynamicFramesIdiom: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.DynamicFramesIdiom()) } 
  $Is(c#0, Tclass._module.DynamicFramesIdiom())
     <==> $Is(c#0, Tclass._module.DynamicFramesIdiom?()) && c#0 != null);

// _module.DynamicFramesIdiom: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.DynamicFramesIdiom(), $h) } 
  $IsAlloc(c#0, Tclass._module.DynamicFramesIdiom(), $h)
     <==> $IsAlloc(c#0, Tclass._module.DynamicFramesIdiom?(), $h));

const unique class._module.ReadsTestsInsideLetSuchThat?: ClassName;

function Tclass._module.ReadsTestsInsideLetSuchThat?() : Ty;

const unique Tagclass._module.ReadsTestsInsideLetSuchThat?: TyTag;

// Tclass._module.ReadsTestsInsideLetSuchThat? Tag
axiom Tag(Tclass._module.ReadsTestsInsideLetSuchThat?())
     == Tagclass._module.ReadsTestsInsideLetSuchThat?
   && TagFamily(Tclass._module.ReadsTestsInsideLetSuchThat?())
     == tytagFamily$ReadsTestsInsideLetSuchThat;

// Box/unbox axiom for Tclass._module.ReadsTestsInsideLetSuchThat?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.ReadsTestsInsideLetSuchThat?()) } 
  $IsBox(bx, Tclass._module.ReadsTestsInsideLetSuchThat?())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.ReadsTestsInsideLetSuchThat?()));

// ReadsTestsInsideLetSuchThat: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.ReadsTestsInsideLetSuchThat?()) } 
  $Is($o, Tclass._module.ReadsTestsInsideLetSuchThat?())
     <==> $o == null || dtype($o) == Tclass._module.ReadsTestsInsideLetSuchThat?());

// ReadsTestsInsideLetSuchThat: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.ReadsTestsInsideLetSuchThat?(), $h) } 
  $IsAlloc($o, Tclass._module.ReadsTestsInsideLetSuchThat?(), $h)
     <==> $o == null || read($h, $o, alloc));

axiom FDim(_module.ReadsTestsInsideLetSuchThat.y) == 0
   && FieldOfDecl(class._module.ReadsTestsInsideLetSuchThat?, field$y)
     == _module.ReadsTestsInsideLetSuchThat.y
   && !$IsGhostField(_module.ReadsTestsInsideLetSuchThat.y);

const _module.ReadsTestsInsideLetSuchThat.y: Field int;

// ReadsTestsInsideLetSuchThat.y: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.ReadsTestsInsideLetSuchThat.y) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.ReadsTestsInsideLetSuchThat?()
     ==> $Is(read($h, $o, _module.ReadsTestsInsideLetSuchThat.y), TInt));

// ReadsTestsInsideLetSuchThat.y: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.ReadsTestsInsideLetSuchThat.y) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.ReadsTestsInsideLetSuchThat?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.ReadsTestsInsideLetSuchThat.y), TInt, $h));

// function declaration for _module.ReadsTestsInsideLetSuchThat.F
function _module.ReadsTestsInsideLetSuchThat.F(this: ref) : int;

function _module.ReadsTestsInsideLetSuchThat.F#canCall(this: ref) : bool;

function Tclass._module.ReadsTestsInsideLetSuchThat() : Ty;

const unique Tagclass._module.ReadsTestsInsideLetSuchThat: TyTag;

// Tclass._module.ReadsTestsInsideLetSuchThat Tag
axiom Tag(Tclass._module.ReadsTestsInsideLetSuchThat())
     == Tagclass._module.ReadsTestsInsideLetSuchThat
   && TagFamily(Tclass._module.ReadsTestsInsideLetSuchThat())
     == tytagFamily$ReadsTestsInsideLetSuchThat;

// Box/unbox axiom for Tclass._module.ReadsTestsInsideLetSuchThat
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.ReadsTestsInsideLetSuchThat()) } 
  $IsBox(bx, Tclass._module.ReadsTestsInsideLetSuchThat())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.ReadsTestsInsideLetSuchThat()));

// consequence axiom for _module.ReadsTestsInsideLetSuchThat.F
axiom 23 <= $FunctionContextHeight
   ==> (forall this: ref :: 
    { _module.ReadsTestsInsideLetSuchThat.F(this) } 
    _module.ReadsTestsInsideLetSuchThat.F#canCall(this)
         || (23 != $FunctionContextHeight
           && 
          this != null
           && $Is(this, Tclass._module.ReadsTestsInsideLetSuchThat()))
       ==> true);

function _module.ReadsTestsInsideLetSuchThat.F#requires(ref) : bool;

// #requires axiom for _module.ReadsTestsInsideLetSuchThat.F
axiom (forall $Heap: Heap, this: ref :: 
  { _module.ReadsTestsInsideLetSuchThat.F#requires(this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.ReadsTestsInsideLetSuchThat())
       && $IsAlloc(this, Tclass._module.ReadsTestsInsideLetSuchThat(), $Heap)
     ==> _module.ReadsTestsInsideLetSuchThat.F#requires(this) == true);

function $let#0_yy($heap: Heap, this: ref) : int;

function $let#0$canCall($heap: Heap, this: ref) : bool;

axiom (forall $heap: Heap, this: ref :: 
  { $let#0_yy($heap, this) } 
  $let#0$canCall($heap, this)
     ==> $let#0_yy($heap, this)
       == read($heap, this, _module.ReadsTestsInsideLetSuchThat.y));

// definition axiom for _module.ReadsTestsInsideLetSuchThat.F (revealed)
axiom 23 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref :: 
    { _module.ReadsTestsInsideLetSuchThat.F(this), $IsGoodHeap($Heap) } 
    _module.ReadsTestsInsideLetSuchThat.F#canCall(this)
         || (23 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.ReadsTestsInsideLetSuchThat())
           && $IsAlloc(this, Tclass._module.ReadsTestsInsideLetSuchThat(), $Heap))
       ==> $let#0$canCall($Heap, this)
         && _module.ReadsTestsInsideLetSuchThat.F(this)
           == (var yy#0 := $let#0_yy($Heap, this); yy#0));

// definition axiom for _module.ReadsTestsInsideLetSuchThat.F for all literals (revealed)
axiom 23 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref :: 
    {:weight 3} { _module.ReadsTestsInsideLetSuchThat.F(Lit(this)), $IsGoodHeap($Heap) } 
    _module.ReadsTestsInsideLetSuchThat.F#canCall(Lit(this))
         || (23 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.ReadsTestsInsideLetSuchThat())
           && $IsAlloc(this, Tclass._module.ReadsTestsInsideLetSuchThat(), $Heap))
       ==> $let#0$canCall($Heap, this)
         && _module.ReadsTestsInsideLetSuchThat.F(Lit(this))
           == (var yy#1 := $let#0_yy($Heap, this); yy#1));

procedure CheckWellformed$$_module.ReadsTestsInsideLetSuchThat.F(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.ReadsTestsInsideLetSuchThat())
         && $IsAlloc(this, Tclass._module.ReadsTestsInsideLetSuchThat(), $Heap));
  free requires 23 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.ReadsTestsInsideLetSuchThat.F(this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var yy#2: int;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function F
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Reads.dfy(148,11): initial state"} true;
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
        havoc yy#2;
        if (true)
        {
            b$reqreads#0 := $_Frame[this, _module.ReadsTestsInsideLetSuchThat.y];
        }

        assert ($Is(read($Heap, this, _module.ReadsTestsInsideLetSuchThat.y), TInt)
             && read($Heap, this, _module.ReadsTestsInsideLetSuchThat.y)
               == read($Heap, this, _module.ReadsTestsInsideLetSuchThat.y))
           || 
          ($Is(LitInt(0), TInt)
             && LitInt(0) == read($Heap, this, _module.ReadsTestsInsideLetSuchThat.y))
           || (exists yy#3: int :: 
            yy#3 == read($Heap, this, _module.ReadsTestsInsideLetSuchThat.y));
        assume true;
        assume yy#2 == read($Heap, this, _module.ReadsTestsInsideLetSuchThat.y);
        assume $let#0$canCall($Heap, this);
        assume _module.ReadsTestsInsideLetSuchThat.F(this) == yy#2;
        assume true;
        // CheckWellformedWithResult: Let expression
        assume $Is(_module.ReadsTestsInsideLetSuchThat.F(this), TInt);
        assert b$reqreads#0;
    }
}



// _module.ReadsTestsInsideLetSuchThat: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.ReadsTestsInsideLetSuchThat()) } 
  $Is(c#0, Tclass._module.ReadsTestsInsideLetSuchThat())
     <==> $Is(c#0, Tclass._module.ReadsTestsInsideLetSuchThat?()) && c#0 != null);

// _module.ReadsTestsInsideLetSuchThat: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.ReadsTestsInsideLetSuchThat(), $h) } 
  $IsAlloc(c#0, Tclass._module.ReadsTestsInsideLetSuchThat(), $h)
     <==> $IsAlloc(c#0, Tclass._module.ReadsTestsInsideLetSuchThat?(), $h));

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

// function declaration for _module._default.nope1
function _module.__default.nope1(c#0: ref) : DatatypeType;

function _module.__default.nope1#canCall(c#0: ref) : bool;

// consequence axiom for _module.__default.nope1
axiom 6 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, c#0: ref :: 
    { _module.__default.nope1(c#0), $IsGoodHeap($Heap) } 
    _module.__default.nope1#canCall(c#0)
         || (6 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(c#0, Tclass._module.C())
           && read($Heap, c#0, _module.C.u) > 0)
       ==> $Is(_module.__default.nope1(c#0), Tclass._System.Tuple0()));

function _module.__default.nope1#requires(ref) : bool;

// #requires axiom for _module.__default.nope1
axiom (forall $Heap: Heap, c#0: ref :: 
  { _module.__default.nope1#requires(c#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap) && $Is(c#0, Tclass._module.C())
     ==> _module.__default.nope1#requires(c#0) == (read($Heap, c#0, _module.C.u) > 0));

// definition axiom for _module.__default.nope1 (revealed)
axiom 6 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, c#0: ref :: 
    { _module.__default.nope1(c#0), $IsGoodHeap($Heap) } 
    _module.__default.nope1#canCall(c#0)
         || (6 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(c#0, Tclass._module.C())
           && read($Heap, c#0, _module.C.u) > 0)
       ==> _module.__default.nope1(c#0) == Lit(#_System._tuple#0._#Make0()));

// definition axiom for _module.__default.nope1 for all literals (revealed)
axiom 6 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, c#0: ref :: 
    {:weight 3} { _module.__default.nope1(Lit(c#0)), $IsGoodHeap($Heap) } 
    _module.__default.nope1#canCall(Lit(c#0))
         || (6 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(c#0, Tclass._module.C())
           && read($Heap, Lit(c#0), _module.C.u) > 0)
       ==> _module.__default.nope1(Lit(c#0)) == Lit(#_System._tuple#0._#Make0()));

procedure CheckWellformed$$_module.__default.nope1(c#0: ref where $Is(c#0, Tclass._module.C()));
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.nope1(c#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function nope1
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Reads.dfy(8,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assert c#0 != null;
    b$reqreads#0 := $_Frame[c#0, _module.C.u];
    assume read($Heap, c#0, _module.C.u) > 0;
    assert b$reqreads#0;
    if (*)
    {
        assume $Is(_module.__default.nope1(c#0), Tclass._System.Tuple0());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        assume _module.__default.nope1(c#0) == Lit(#_System._tuple#0._#Make0());
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.nope1(c#0), Tclass._System.Tuple0());
    }
}



// function declaration for _module._default.ok1
function _module.__default.ok1($heap: Heap, c#0: ref) : DatatypeType;

function _module.__default.ok1#canCall($heap: Heap, c#0: ref) : bool;

// frame axiom for _module.__default.ok1
axiom (forall $h0: Heap, $h1: Heap, c#0: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.__default.ok1($h1, c#0) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && (_module.__default.ok1#canCall($h0, c#0) || $Is(c#0, Tclass._module.C()))
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && $o == c#0 ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.__default.ok1($h0, c#0) == _module.__default.ok1($h1, c#0));

// consequence axiom for _module.__default.ok1
axiom 7 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, c#0: ref :: 
    { _module.__default.ok1($Heap, c#0) } 
    _module.__default.ok1#canCall($Heap, c#0)
         || (7 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(c#0, Tclass._module.C())
           && read($Heap, c#0, _module.C.u) > 0)
       ==> $Is(_module.__default.ok1($Heap, c#0), Tclass._System.Tuple0()));

function _module.__default.ok1#requires(Heap, ref) : bool;

// #requires axiom for _module.__default.ok1
axiom (forall $Heap: Heap, c#0: ref :: 
  { _module.__default.ok1#requires($Heap, c#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap) && $Is(c#0, Tclass._module.C())
     ==> _module.__default.ok1#requires($Heap, c#0)
       == (read($Heap, c#0, _module.C.u) > 0));

// definition axiom for _module.__default.ok1 (revealed)
axiom 7 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, c#0: ref :: 
    { _module.__default.ok1($Heap, c#0), $IsGoodHeap($Heap) } 
    _module.__default.ok1#canCall($Heap, c#0)
         || (7 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(c#0, Tclass._module.C())
           && read($Heap, c#0, _module.C.u) > 0)
       ==> _module.__default.ok1($Heap, c#0) == Lit(#_System._tuple#0._#Make0()));

procedure CheckWellformed$$_module.__default.ok1(c#0: ref where $Is(c#0, Tclass._module.C()));
  free requires 7 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.ok1(c#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function ok1
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Reads.dfy(12,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == c#0);
    assert c#0 != null;
    b$reqreads#0 := $_Frame[c#0, _module.C.u];
    assume read($Heap, c#0, _module.C.u) > 0;
    assert b$reqreads#0;
    if (*)
    {
        assume $Is(_module.__default.ok1($Heap, c#0), Tclass._System.Tuple0());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> $o == c#0);
        assume _module.__default.ok1($Heap, c#0) == Lit(#_System._tuple#0._#Make0());
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.ok1($Heap, c#0), Tclass._System.Tuple0());
    }
}



// function declaration for _module._default.nope2
function _module.__default.nope2($heap: Heap, c#0: ref) : DatatypeType;

function _module.__default.nope2#canCall($heap: Heap, c#0: ref) : bool;

// frame axiom for _module.__default.nope2
axiom (forall $h0: Heap, $h1: Heap, c#0: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.__default.nope2($h1, c#0) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && (_module.__default.nope2#canCall($h0, c#0) || $Is(c#0, Tclass._module.C?()))
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && (if c#0 != null
             then Set#Empty(): Set Box
             else Set#UnionOne(Set#Empty(): Set Box, $Box(c#0)))[$Box($o)]
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.__default.nope2($h0, c#0) == _module.__default.nope2($h1, c#0));

// consequence axiom for _module.__default.nope2
axiom 8 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, c#0: ref :: 
    { _module.__default.nope2($Heap, c#0) } 
    _module.__default.nope2#canCall($Heap, c#0)
         || (8 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(c#0, Tclass._module.C?())
           && 
          c#0 != null
           && read($Heap, c#0, _module.C.u) > 0)
       ==> $Is(_module.__default.nope2($Heap, c#0), Tclass._System.Tuple0()));

function _module.__default.nope2#requires(Heap, ref) : bool;

// #requires axiom for _module.__default.nope2
axiom (forall $Heap: Heap, c#0: ref :: 
  { _module.__default.nope2#requires($Heap, c#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap) && $Is(c#0, Tclass._module.C?())
     ==> _module.__default.nope2#requires($Heap, c#0)
       == (c#0 != null && read($Heap, c#0, _module.C.u) > 0));

// definition axiom for _module.__default.nope2 (revealed)
axiom 8 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, c#0: ref :: 
    { _module.__default.nope2($Heap, c#0), $IsGoodHeap($Heap) } 
    _module.__default.nope2#canCall($Heap, c#0)
         || (8 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(c#0, Tclass._module.C?())
           && 
          c#0 != null
           && read($Heap, c#0, _module.C.u) > 0)
       ==> _module.__default.nope2($Heap, c#0) == Lit(#_System._tuple#0._#Make0()));

procedure CheckWellformed$$_module.__default.nope2(c#0: ref where $Is(c#0, Tclass._module.C?()));
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.nope2(c#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function nope2
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Reads.dfy(17,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> (if c#0 != null
           then Set#Empty(): Set Box
           else Set#UnionOne(Set#Empty(): Set Box, $Box(c#0)))[$Box($o)]);
    assume c#0 != null;
    assert c#0 != null;
    b$reqreads#0 := $_Frame[c#0, _module.C.u];
    assume read($Heap, c#0, _module.C.u) > 0;
    assert b$reqreads#0;
    if (c#0 != null)
    {
    }
    else
    {
    }

    if (c#0 != null)
    {
    }
    else
    {
    }

    if (*)
    {
        assume $Is(_module.__default.nope2($Heap, c#0), Tclass._System.Tuple0());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc)
             ==> (if c#0 != null
               then Set#Empty(): Set Box
               else Set#UnionOne(Set#Empty(): Set Box, $Box(c#0)))[$Box($o)]);
        assume _module.__default.nope2($Heap, c#0) == Lit(#_System._tuple#0._#Make0());
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.nope2($Heap, c#0), Tclass._System.Tuple0());
    }
}



// function declaration for _module._default.ok2
function _module.__default.ok2($heap: Heap, c#0: ref) : DatatypeType;

function _module.__default.ok2#canCall($heap: Heap, c#0: ref) : bool;

// frame axiom for _module.__default.ok2
axiom (forall $h0: Heap, $h1: Heap, c#0: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.__default.ok2($h1, c#0) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && (_module.__default.ok2#canCall($h0, c#0) || $Is(c#0, Tclass._module.C?()))
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && (if c#0 != null
             then Set#UnionOne(Set#Empty(): Set Box, $Box(c#0))
             else Set#Empty(): Set Box)[$Box($o)]
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.__default.ok2($h0, c#0) == _module.__default.ok2($h1, c#0));

// consequence axiom for _module.__default.ok2
axiom 9 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, c#0: ref :: 
    { _module.__default.ok2($Heap, c#0) } 
    _module.__default.ok2#canCall($Heap, c#0)
         || (9 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(c#0, Tclass._module.C?())
           && 
          c#0 != null
           && read($Heap, c#0, _module.C.u) > 0)
       ==> $Is(_module.__default.ok2($Heap, c#0), Tclass._System.Tuple0()));

function _module.__default.ok2#requires(Heap, ref) : bool;

// #requires axiom for _module.__default.ok2
axiom (forall $Heap: Heap, c#0: ref :: 
  { _module.__default.ok2#requires($Heap, c#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap) && $Is(c#0, Tclass._module.C?())
     ==> _module.__default.ok2#requires($Heap, c#0)
       == (c#0 != null && read($Heap, c#0, _module.C.u) > 0));

// definition axiom for _module.__default.ok2 (revealed)
axiom 9 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, c#0: ref :: 
    { _module.__default.ok2($Heap, c#0), $IsGoodHeap($Heap) } 
    _module.__default.ok2#canCall($Heap, c#0)
         || (9 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(c#0, Tclass._module.C?())
           && 
          c#0 != null
           && read($Heap, c#0, _module.C.u) > 0)
       ==> _module.__default.ok2($Heap, c#0) == Lit(#_System._tuple#0._#Make0()));

procedure CheckWellformed$$_module.__default.ok2(c#0: ref where $Is(c#0, Tclass._module.C?()));
  free requires 9 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.ok2(c#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function ok2
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Reads.dfy(22,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> (if c#0 != null
           then Set#UnionOne(Set#Empty(): Set Box, $Box(c#0))
           else Set#Empty(): Set Box)[$Box($o)]);
    assume c#0 != null;
    assert c#0 != null;
    b$reqreads#0 := $_Frame[c#0, _module.C.u];
    assume read($Heap, c#0, _module.C.u) > 0;
    assert b$reqreads#0;
    if (c#0 != null)
    {
    }
    else
    {
    }

    if (c#0 != null)
    {
    }
    else
    {
    }

    if (*)
    {
        assume $Is(_module.__default.ok2($Heap, c#0), Tclass._System.Tuple0());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc)
             ==> (if c#0 != null
               then Set#UnionOne(Set#Empty(): Set Box, $Box(c#0))
               else Set#Empty(): Set Box)[$Box($o)]);
        assume _module.__default.ok2($Heap, c#0) == Lit(#_System._tuple#0._#Make0());
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.ok2($Heap, c#0), Tclass._System.Tuple0());
    }
}



// function declaration for _module._default.nope3
function _module.__default.nope3(xs#0: Seq Box) : DatatypeType;

function _module.__default.nope3#canCall(xs#0: Seq Box) : bool;

// consequence axiom for _module.__default.nope3
axiom 10 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, xs#0: Seq Box :: 
    { _module.__default.nope3(xs#0), $IsGoodHeap($Heap) } 
    _module.__default.nope3#canCall(xs#0)
         || (10 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(xs#0, TSeq(Tclass._module.C()))
           && 
          Seq#Length(xs#0) > 0
           && read($Heap, $Unbox(Seq#Index(xs#0, LitInt(0))): ref, _module.C.u) > 0)
       ==> $Is(_module.__default.nope3(xs#0), Tclass._System.Tuple0()));

function _module.__default.nope3#requires(Seq Box) : bool;

// #requires axiom for _module.__default.nope3
axiom (forall $Heap: Heap, xs#0: Seq Box :: 
  { _module.__default.nope3#requires(xs#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap) && $Is(xs#0, TSeq(Tclass._module.C()))
     ==> _module.__default.nope3#requires(xs#0)
       == (Seq#Length(xs#0) > 0
         && read($Heap, $Unbox(Seq#Index(xs#0, LitInt(0))): ref, _module.C.u) > 0));

// definition axiom for _module.__default.nope3 (revealed)
axiom 10 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, xs#0: Seq Box :: 
    { _module.__default.nope3(xs#0), $IsGoodHeap($Heap) } 
    _module.__default.nope3#canCall(xs#0)
         || (10 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(xs#0, TSeq(Tclass._module.C()))
           && 
          Seq#Length(xs#0) > 0
           && read($Heap, $Unbox(Seq#Index(xs#0, LitInt(0))): ref, _module.C.u) > 0)
       ==> _module.__default.nope3(xs#0) == Lit(#_System._tuple#0._#Make0()));

// definition axiom for _module.__default.nope3 for all literals (revealed)
axiom 10 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, xs#0: Seq Box :: 
    {:weight 3} { _module.__default.nope3(Lit(xs#0)), $IsGoodHeap($Heap) } 
    _module.__default.nope3#canCall(Lit(xs#0))
         || (10 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(xs#0, TSeq(Tclass._module.C()))
           && 
          Seq#Length(Lit(xs#0)) > 0
           && read($Heap, $Unbox(Seq#Index(Lit(xs#0), LitInt(0))): ref, _module.C.u) > 0)
       ==> _module.__default.nope3(Lit(xs#0)) == Lit(#_System._tuple#0._#Make0()));

procedure CheckWellformed$$_module.__default.nope3(xs#0: Seq Box where $Is(xs#0, TSeq(Tclass._module.C())));
  free requires 10 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.nope3(xs#0: Seq Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function nope3
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Reads.dfy(27,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume Seq#Length(xs#0) > 0;
    assert 0 <= LitInt(0) && LitInt(0) < Seq#Length(xs#0);
    assert $Unbox(Seq#Index(xs#0, LitInt(0))): ref != null;
    b$reqreads#0 := $_Frame[$Unbox(Seq#Index(xs#0, LitInt(0))): ref, _module.C.u];
    assume read($Heap, $Unbox(Seq#Index(xs#0, LitInt(0))): ref, _module.C.u) > 0;
    assert b$reqreads#0;
    if (*)
    {
        assume $Is(_module.__default.nope3(xs#0), Tclass._System.Tuple0());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        assume _module.__default.nope3(xs#0) == Lit(#_System._tuple#0._#Make0());
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.nope3(xs#0), Tclass._System.Tuple0());
    }
}



// function declaration for _module._default.ok3
function _module.__default.ok3($heap: Heap, xs#0: Seq Box) : DatatypeType;

function _module.__default.ok3#canCall($heap: Heap, xs#0: Seq Box) : bool;

// frame axiom for _module.__default.ok3
axiom (forall $h0: Heap, $h1: Heap, xs#0: Seq Box :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.__default.ok3($h1, xs#0) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && (_module.__default.ok3#canCall($h0, xs#0)
         || $Is(xs#0, TSeq(Tclass._module.C())))
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && (exists $i: int :: 
            0 <= $i && $i < Seq#Length(xs#0) && Seq#Index(xs#0, $i) == $Box($o))
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.__default.ok3($h0, xs#0) == _module.__default.ok3($h1, xs#0));

// consequence axiom for _module.__default.ok3
axiom 11 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, xs#0: Seq Box :: 
    { _module.__default.ok3($Heap, xs#0) } 
    _module.__default.ok3#canCall($Heap, xs#0)
         || (11 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(xs#0, TSeq(Tclass._module.C()))
           && 
          Seq#Length(xs#0) > 0
           && read($Heap, $Unbox(Seq#Index(xs#0, LitInt(0))): ref, _module.C.u) > 0)
       ==> $Is(_module.__default.ok3($Heap, xs#0), Tclass._System.Tuple0()));

function _module.__default.ok3#requires(Heap, Seq Box) : bool;

// #requires axiom for _module.__default.ok3
axiom (forall $Heap: Heap, xs#0: Seq Box :: 
  { _module.__default.ok3#requires($Heap, xs#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap) && $Is(xs#0, TSeq(Tclass._module.C()))
     ==> _module.__default.ok3#requires($Heap, xs#0)
       == (Seq#Length(xs#0) > 0
         && read($Heap, $Unbox(Seq#Index(xs#0, LitInt(0))): ref, _module.C.u) > 0));

// definition axiom for _module.__default.ok3 (revealed)
axiom 11 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, xs#0: Seq Box :: 
    { _module.__default.ok3($Heap, xs#0), $IsGoodHeap($Heap) } 
    _module.__default.ok3#canCall($Heap, xs#0)
         || (11 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(xs#0, TSeq(Tclass._module.C()))
           && 
          Seq#Length(xs#0) > 0
           && read($Heap, $Unbox(Seq#Index(xs#0, LitInt(0))): ref, _module.C.u) > 0)
       ==> _module.__default.ok3($Heap, xs#0) == Lit(#_System._tuple#0._#Make0()));

procedure CheckWellformed$$_module.__default.ok3(xs#0: Seq Box where $Is(xs#0, TSeq(Tclass._module.C())));
  free requires 11 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.ok3(xs#0: Seq Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;
  var _s2s_0#0: ref;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function ok3
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Reads.dfy(31,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> (exists $i: int :: 
          0 <= $i && $i < Seq#Length(xs#0) && Seq#Index(xs#0, $i) == $Box($o)));
    assume Seq#Length(xs#0) > 0;
    assert 0 <= LitInt(0) && LitInt(0) < Seq#Length(xs#0);
    assert $Unbox(Seq#Index(xs#0, LitInt(0))): ref != null;
    b$reqreads#0 := $_Frame[$Unbox(Seq#Index(xs#0, LitInt(0))): ref, _module.C.u];
    assume read($Heap, $Unbox(Seq#Index(xs#0, LitInt(0))): ref, _module.C.u) > 0;
    assert b$reqreads#0;
    // Begin Comprehension WF check
    havoc _s2s_0#0;
    if ($Is(_s2s_0#0, Tclass._module.C()))
    {
        if (Seq#Contains(xs#0, $Box(_s2s_0#0)))
        {
        }
    }

    // End Comprehension WF check
    if (*)
    {
        assume $Is(_module.__default.ok3($Heap, xs#0), Tclass._System.Tuple0());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc)
             ==> (exists $i: int :: 
              0 <= $i && $i < Seq#Length(xs#0) && Seq#Index(xs#0, $i) == $Box($o)));
        assume _module.__default.ok3($Heap, xs#0) == Lit(#_System._tuple#0._#Make0());
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.ok3($Heap, xs#0), Tclass._System.Tuple0());
    }
}



// function declaration for _module._default.nope4
function _module.__default.nope4($heap: Heap, c#0: ref, xs#0: Set Box) : DatatypeType;

function _module.__default.nope4#canCall($heap: Heap, c#0: ref, xs#0: Set Box) : bool;

// frame axiom for _module.__default.nope4
axiom (forall $h0: Heap, $h1: Heap, c#0: ref, xs#0: Set Box :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.__default.nope4($h1, c#0, xs#0) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && (_module.__default.nope4#canCall($h0, c#0, xs#0)
         || ($Is(c#0, Tclass._module.C()) && $Is(xs#0, TSet(Tclass._module.C()))))
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && xs#0[$Box($o)] ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.__default.nope4($h0, c#0, xs#0)
       == _module.__default.nope4($h1, c#0, xs#0));

// consequence axiom for _module.__default.nope4
axiom 12 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, c#0: ref, xs#0: Set Box :: 
    { _module.__default.nope4($Heap, c#0, xs#0) } 
    _module.__default.nope4#canCall($Heap, c#0, xs#0)
         || (12 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(c#0, Tclass._module.C())
           && $Is(xs#0, TSet(Tclass._module.C()))
           && (!xs#0[$Box(c#0)] ==> read($Heap, c#0, _module.C.u) > 0))
       ==> $Is(_module.__default.nope4($Heap, c#0, xs#0), Tclass._System.Tuple0()));

function _module.__default.nope4#requires(Heap, ref, Set Box) : bool;

// #requires axiom for _module.__default.nope4
axiom (forall $Heap: Heap, c#0: ref, xs#0: Set Box :: 
  { _module.__default.nope4#requires($Heap, c#0, xs#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && $Is(c#0, Tclass._module.C())
       && $Is(xs#0, TSet(Tclass._module.C()))
     ==> _module.__default.nope4#requires($Heap, c#0, xs#0)
       == (!xs#0[$Box(c#0)] ==> read($Heap, c#0, _module.C.u) > 0));

// definition axiom for _module.__default.nope4 (revealed)
axiom 12 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, c#0: ref, xs#0: Set Box :: 
    { _module.__default.nope4($Heap, c#0, xs#0), $IsGoodHeap($Heap) } 
    _module.__default.nope4#canCall($Heap, c#0, xs#0)
         || (12 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(c#0, Tclass._module.C())
           && $Is(xs#0, TSet(Tclass._module.C()))
           && (!xs#0[$Box(c#0)] ==> read($Heap, c#0, _module.C.u) > 0))
       ==> _module.__default.nope4($Heap, c#0, xs#0) == Lit(#_System._tuple#0._#Make0()));

procedure CheckWellformed$$_module.__default.nope4(c#0: ref where $Is(c#0, Tclass._module.C()), 
    xs#0: Set Box where $Is(xs#0, TSet(Tclass._module.C())));
  free requires 12 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.nope4(c#0: ref, xs#0: Set Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function nope4
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Reads.dfy(36,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> xs#0[$Box($o)]);
    if (*)
    {
        assume !xs#0[$Box(c#0)];
        assert c#0 != null;
        b$reqreads#0 := $_Frame[c#0, _module.C.u];
        assume read($Heap, c#0, _module.C.u) > 0;
    }
    else
    {
        assume !xs#0[$Box(c#0)] ==> read($Heap, c#0, _module.C.u) > 0;
    }

    assert b$reqreads#0;
    if (*)
    {
        assume $Is(_module.__default.nope4($Heap, c#0, xs#0), Tclass._System.Tuple0());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> xs#0[$Box($o)]);
        assume _module.__default.nope4($Heap, c#0, xs#0) == Lit(#_System._tuple#0._#Make0());
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.nope4($Heap, c#0, xs#0), Tclass._System.Tuple0());
    }
}



// function declaration for _module._default.ok4
function _module.__default.ok4($heap: Heap, c#0: ref, xs#0: Set Box) : DatatypeType;

function _module.__default.ok4#canCall($heap: Heap, c#0: ref, xs#0: Set Box) : bool;

// frame axiom for _module.__default.ok4
axiom (forall $h0: Heap, $h1: Heap, c#0: ref, xs#0: Set Box :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.__default.ok4($h1, c#0, xs#0) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && (_module.__default.ok4#canCall($h0, c#0, xs#0)
         || ($Is(c#0, Tclass._module.C()) && $Is(xs#0, TSet(Tclass._module.C()))))
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && xs#0[$Box($o)] ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.__default.ok4($h0, c#0, xs#0) == _module.__default.ok4($h1, c#0, xs#0));

// consequence axiom for _module.__default.ok4
axiom 13 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, c#0: ref, xs#0: Set Box :: 
    { _module.__default.ok4($Heap, c#0, xs#0) } 
    _module.__default.ok4#canCall($Heap, c#0, xs#0)
         || (13 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(c#0, Tclass._module.C())
           && $Is(xs#0, TSet(Tclass._module.C()))
           && (xs#0[$Box(c#0)] ==> read($Heap, c#0, _module.C.u) > 0))
       ==> $Is(_module.__default.ok4($Heap, c#0, xs#0), Tclass._System.Tuple0()));

function _module.__default.ok4#requires(Heap, ref, Set Box) : bool;

// #requires axiom for _module.__default.ok4
axiom (forall $Heap: Heap, c#0: ref, xs#0: Set Box :: 
  { _module.__default.ok4#requires($Heap, c#0, xs#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && $Is(c#0, Tclass._module.C())
       && $Is(xs#0, TSet(Tclass._module.C()))
     ==> _module.__default.ok4#requires($Heap, c#0, xs#0)
       == (xs#0[$Box(c#0)] ==> read($Heap, c#0, _module.C.u) > 0));

// definition axiom for _module.__default.ok4 (revealed)
axiom 13 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, c#0: ref, xs#0: Set Box :: 
    { _module.__default.ok4($Heap, c#0, xs#0), $IsGoodHeap($Heap) } 
    _module.__default.ok4#canCall($Heap, c#0, xs#0)
         || (13 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(c#0, Tclass._module.C())
           && $Is(xs#0, TSet(Tclass._module.C()))
           && (xs#0[$Box(c#0)] ==> read($Heap, c#0, _module.C.u) > 0))
       ==> _module.__default.ok4($Heap, c#0, xs#0) == Lit(#_System._tuple#0._#Make0()));

procedure CheckWellformed$$_module.__default.ok4(c#0: ref where $Is(c#0, Tclass._module.C()), 
    xs#0: Set Box where $Is(xs#0, TSet(Tclass._module.C())));
  free requires 13 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.ok4(c#0: ref, xs#0: Set Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function ok4
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Reads.dfy(41,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> xs#0[$Box($o)]);
    if (*)
    {
        assume xs#0[$Box(c#0)];
        assert c#0 != null;
        b$reqreads#0 := $_Frame[c#0, _module.C.u];
        assume read($Heap, c#0, _module.C.u) > 0;
    }
    else
    {
        assume xs#0[$Box(c#0)] ==> read($Heap, c#0, _module.C.u) > 0;
    }

    assert b$reqreads#0;
    if (*)
    {
        assume $Is(_module.__default.ok4($Heap, c#0, xs#0), Tclass._System.Tuple0());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> xs#0[$Box($o)]);
        assume _module.__default.ok4($Heap, c#0, xs#0) == Lit(#_System._tuple#0._#Make0());
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.ok4($Heap, c#0, xs#0), Tclass._System.Tuple0());
    }
}



// function declaration for _module._default.nope5
function _module.__default.nope5($heap: Heap, r#0: ref) : DatatypeType;

function _module.__default.nope5#canCall($heap: Heap, r#0: ref) : bool;

// frame axiom for _module.__default.nope5
axiom (forall $h0: Heap, $h1: Heap, r#0: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.__default.nope5($h1, r#0) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && (_module.__default.nope5#canCall($h0, r#0) || $Is(r#0, Tclass._module.R?()))
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && (if r#0 != null
             then Set#UnionOne(Set#Empty(): Set Box, $Box(read($h0, r#0, _module.R.r)))
             else Set#Empty(): Set Box)[$Box($o)]
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.__default.nope5($h0, r#0) == _module.__default.nope5($h1, r#0));

// consequence axiom for _module.__default.nope5
axiom 14 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, r#0: ref :: 
    { _module.__default.nope5($Heap, r#0) } 
    _module.__default.nope5#canCall($Heap, r#0)
         || (14 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(r#0, Tclass._module.R?()))
       ==> $Is(_module.__default.nope5($Heap, r#0), Tclass._System.Tuple0()));

function _module.__default.nope5#requires(Heap, ref) : bool;

// #requires axiom for _module.__default.nope5
axiom (forall $Heap: Heap, r#0: ref :: 
  { _module.__default.nope5#requires($Heap, r#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap) && $Is(r#0, Tclass._module.R?())
     ==> _module.__default.nope5#requires($Heap, r#0) == true);

// definition axiom for _module.__default.nope5 (revealed)
axiom 14 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, r#0: ref :: 
    { _module.__default.nope5($Heap, r#0), $IsGoodHeap($Heap) } 
    _module.__default.nope5#canCall($Heap, r#0)
         || (14 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(r#0, Tclass._module.R?()))
       ==> _module.__default.nope5($Heap, r#0) == Lit(#_System._tuple#0._#Make0()));

procedure CheckWellformed$$_module.__default.nope5(r#0: ref where $Is(r#0, Tclass._module.R?()));
  free requires 14 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.nope5(r#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function nope5
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Reads.dfy(55,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> (if r#0 != null
           then Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, r#0, _module.R.r)))
           else Set#Empty(): Set Box)[$Box($o)]);
    if (r#0 != null)
    {
        assert r#0 != null;
        b$reqreads#0 := $_Frame[r#0, _module.R.r];
    }
    else
    {
    }

    assert b$reqreads#0;
    if (r#0 != null)
    {
        assert r#0 != null;
    }
    else
    {
    }

    if (*)
    {
        assume $Is(_module.__default.nope5($Heap, r#0), Tclass._System.Tuple0());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc)
             ==> (if r#0 != null
               then Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, r#0, _module.R.r)))
               else Set#Empty(): Set Box)[$Box($o)]);
        assume _module.__default.nope5($Heap, r#0) == Lit(#_System._tuple#0._#Make0());
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.nope5($Heap, r#0), Tclass._System.Tuple0());
    }
}



// function declaration for _module._default.ok5
function _module.__default.ok5($heap: Heap, r#0: ref) : DatatypeType;

function _module.__default.ok5#canCall($heap: Heap, r#0: ref) : bool;

// frame axiom for _module.__default.ok5
axiom (forall $h0: Heap, $h1: Heap, r#0: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.__default.ok5($h1, r#0) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && (_module.__default.ok5#canCall($h0, r#0) || $Is(r#0, Tclass._module.R?()))
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && (if r#0 != null
             then Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(r#0)), $Box(read($h0, r#0, _module.R.r)))
             else Set#Empty(): Set Box)[$Box($o)]
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.__default.ok5($h0, r#0) == _module.__default.ok5($h1, r#0));

// consequence axiom for _module.__default.ok5
axiom 15 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, r#0: ref :: 
    { _module.__default.ok5($Heap, r#0) } 
    _module.__default.ok5#canCall($Heap, r#0)
         || (15 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(r#0, Tclass._module.R?()))
       ==> $Is(_module.__default.ok5($Heap, r#0), Tclass._System.Tuple0()));

function _module.__default.ok5#requires(Heap, ref) : bool;

// #requires axiom for _module.__default.ok5
axiom (forall $Heap: Heap, r#0: ref :: 
  { _module.__default.ok5#requires($Heap, r#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap) && $Is(r#0, Tclass._module.R?())
     ==> _module.__default.ok5#requires($Heap, r#0) == true);

// definition axiom for _module.__default.ok5 (revealed)
axiom 15 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, r#0: ref :: 
    { _module.__default.ok5($Heap, r#0), $IsGoodHeap($Heap) } 
    _module.__default.ok5#canCall($Heap, r#0)
         || (15 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(r#0, Tclass._module.R?()))
       ==> _module.__default.ok5($Heap, r#0) == Lit(#_System._tuple#0._#Make0()));

procedure CheckWellformed$$_module.__default.ok5(r#0: ref where $Is(r#0, Tclass._module.R?()));
  free requires 15 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.ok5(r#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function ok5
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Reads.dfy(59,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> (if r#0 != null
           then Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(r#0)), 
            $Box(read($Heap, r#0, _module.R.r)))
           else Set#Empty(): Set Box)[$Box($o)]);
    if (r#0 != null)
    {
        assert r#0 != null;
        b$reqreads#0 := $_Frame[r#0, _module.R.r];
    }
    else
    {
    }

    assert b$reqreads#0;
    if (r#0 != null)
    {
        assert r#0 != null;
    }
    else
    {
    }

    if (*)
    {
        assume $Is(_module.__default.ok5($Heap, r#0), Tclass._System.Tuple0());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc)
             ==> (if r#0 != null
               then Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(r#0)), 
                $Box(read($Heap, r#0, _module.R.r)))
               else Set#Empty(): Set Box)[$Box($o)]);
        assume _module.__default.ok5($Heap, r#0) == Lit(#_System._tuple#0._#Make0());
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.ok5($Heap, r#0), Tclass._System.Tuple0());
    }
}



// function declaration for _module._default.ApplyToSet
function _module.__default.ApplyToSet(_module._default.ApplyToSet$X: Ty, $ly: LayerType, S#0: Set Box, f#0: HandleType)
   : Set Box;

function _module.__default.ApplyToSet#canCall(_module._default.ApplyToSet$X: Ty, S#0: Set Box, f#0: HandleType) : bool;

// layer synonym axiom
axiom (forall _module._default.ApplyToSet$X: Ty, $ly: LayerType, S#0: Set Box, f#0: HandleType :: 
  { _module.__default.ApplyToSet(_module._default.ApplyToSet$X, $LS($ly), S#0, f#0) } 
  _module.__default.ApplyToSet(_module._default.ApplyToSet$X, $LS($ly), S#0, f#0)
     == _module.__default.ApplyToSet(_module._default.ApplyToSet$X, $ly, S#0, f#0));

// fuel synonym axiom
axiom (forall _module._default.ApplyToSet$X: Ty, $ly: LayerType, S#0: Set Box, f#0: HandleType :: 
  { _module.__default.ApplyToSet(_module._default.ApplyToSet$X, AsFuelBottom($ly), S#0, f#0) } 
  _module.__default.ApplyToSet(_module._default.ApplyToSet$X, $ly, S#0, f#0)
     == _module.__default.ApplyToSet(_module._default.ApplyToSet$X, $LZ, S#0, f#0));

// consequence axiom for _module.__default.ApplyToSet
axiom 19 <= $FunctionContextHeight
   ==> (forall _module._default.ApplyToSet$X: Ty, 
      $ly: LayerType, 
      $Heap: Heap, 
      S#0: Set Box, 
      f#0: HandleType :: 
    { _module.__default.ApplyToSet(_module._default.ApplyToSet$X, $ly, S#0, f#0), $IsGoodHeap($Heap) } 
    _module.__default.ApplyToSet#canCall(_module._default.ApplyToSet$X, S#0, f#0)
         || (19 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(S#0, TSet(_module._default.ApplyToSet$X))
           && $Is(f#0, 
            Tclass._System.___hFunc1(_module._default.ApplyToSet$X, _module._default.ApplyToSet$X))
           && (forall x#0: Box :: 
            { Requires1(_module._default.ApplyToSet$X, _module._default.ApplyToSet$X, $Heap, f#0, x#0) } 
              { Reads1(_module._default.ApplyToSet$X, _module._default.ApplyToSet$X, $Heap, f#0, x#0) } 
              { S#0[x#0] } 
            $IsBox(x#0, _module._default.ApplyToSet$X)
               ==> (S#0[x#0]
                   ==> Set#Equal(Reads1(_module._default.ApplyToSet$X, _module._default.ApplyToSet$X, $Heap, f#0, x#0), 
                    Set#Empty(): Set Box))
                 && (S#0[x#0]
                   ==> Requires1(_module._default.ApplyToSet$X, _module._default.ApplyToSet$X, $Heap, f#0, x#0))))
       ==> $Is(_module.__default.ApplyToSet(_module._default.ApplyToSet$X, $ly, S#0, f#0), 
        TSet(_module._default.ApplyToSet$X)));

function _module.__default.ApplyToSet#requires(Ty, LayerType, Set Box, HandleType) : bool;

// #requires axiom for _module.__default.ApplyToSet
axiom (forall _module._default.ApplyToSet$X: Ty, 
    $ly: LayerType, 
    $Heap: Heap, 
    S#0: Set Box, 
    f#0: HandleType :: 
  { _module.__default.ApplyToSet#requires(_module._default.ApplyToSet$X, $ly, S#0, f#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && $Is(S#0, TSet(_module._default.ApplyToSet$X))
       && $Is(f#0, 
        Tclass._System.___hFunc1(_module._default.ApplyToSet$X, _module._default.ApplyToSet$X))
     ==> _module.__default.ApplyToSet#requires(_module._default.ApplyToSet$X, $ly, S#0, f#0)
       == (forall x#1: Box :: 
        { Requires1(_module._default.ApplyToSet$X, _module._default.ApplyToSet$X, $Heap, f#0, x#1) } 
          { Reads1(_module._default.ApplyToSet$X, _module._default.ApplyToSet$X, $Heap, f#0, x#1) } 
          { S#0[x#1] } 
        $IsBox(x#1, _module._default.ApplyToSet$X)
           ==> (S#0[x#1]
               ==> Set#Equal(Reads1(_module._default.ApplyToSet$X, _module._default.ApplyToSet$X, $Heap, f#0, x#1), 
                Set#Empty(): Set Box))
             && (S#0[x#1]
               ==> Requires1(_module._default.ApplyToSet$X, _module._default.ApplyToSet$X, $Heap, f#0, x#1))));

function $let#3_x(_module._default.ApplyToSet$X: Ty, S: Set Box) : Box;

function $let#3$canCall(_module._default.ApplyToSet$X: Ty, S: Set Box) : bool;

axiom (forall _module._default.ApplyToSet$X: Ty, S: Set Box :: 
  { $let#3_x(_module._default.ApplyToSet$X, S) } 
  $let#3$canCall(_module._default.ApplyToSet$X, S)
     ==> S[$let#3_x(_module._default.ApplyToSet$X, S)]);

// definition axiom for _module.__default.ApplyToSet (revealed)
axiom 19 <= $FunctionContextHeight
   ==> (forall _module._default.ApplyToSet$X: Ty, 
      $ly: LayerType, 
      $Heap: Heap, 
      S#0: Set Box, 
      f#0: HandleType :: 
    { _module.__default.ApplyToSet(_module._default.ApplyToSet$X, $LS($ly), S#0, f#0), $IsGoodHeap($Heap) } 
    _module.__default.ApplyToSet#canCall(_module._default.ApplyToSet$X, S#0, f#0)
         || (19 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(S#0, TSet(_module._default.ApplyToSet$X))
           && $Is(f#0, 
            Tclass._System.___hFunc1(_module._default.ApplyToSet$X, _module._default.ApplyToSet$X))
           && (forall x#1: Box :: 
            { Requires1(_module._default.ApplyToSet$X, _module._default.ApplyToSet$X, $Heap, f#0, x#1) } 
              { Reads1(_module._default.ApplyToSet$X, _module._default.ApplyToSet$X, $Heap, f#0, x#1) } 
              { S#0[x#1] } 
            $IsBox(x#1, _module._default.ApplyToSet$X)
               ==> (S#0[x#1]
                   ==> Set#Equal(Reads1(_module._default.ApplyToSet$X, _module._default.ApplyToSet$X, $Heap, f#0, x#1), 
                    Set#Empty(): Set Box))
                 && (S#0[x#1]
                   ==> Requires1(_module._default.ApplyToSet$X, _module._default.ApplyToSet$X, $Heap, f#0, x#1))))
       ==> (!Set#Equal(S#0, Set#Empty(): Set Box)
           ==> $let#3$canCall(_module._default.ApplyToSet$X, S#0)
             && _module.__default.ApplyToSet#canCall(_module._default.ApplyToSet$X, 
              Set#Difference(S#0, 
                Set#UnionOne(Set#Empty(): Set Box, $let#3_x(_module._default.ApplyToSet$X, S#0))), 
              f#0))
         && _module.__default.ApplyToSet(_module._default.ApplyToSet$X, $LS($ly), S#0, f#0)
           == (if Set#Equal(S#0, Set#Empty(): Set Box)
             then Set#Empty(): Set Box
             else (var x#2 := $let#3_x(_module._default.ApplyToSet$X, S#0); 
              Set#Union(_module.__default.ApplyToSet(_module._default.ApplyToSet$X, 
                  $ly, 
                  Set#Difference(S#0, Set#UnionOne(Set#Empty(): Set Box, x#2)), 
                  f#0), 
                Set#UnionOne(Set#Empty(): Set Box, 
                  Apply1(_module._default.ApplyToSet$X, _module._default.ApplyToSet$X, $Heap, f#0, x#2))))));

// definition axiom for _module.__default.ApplyToSet for decreasing-related literals (revealed)
axiom 19 <= $FunctionContextHeight
   ==> (forall _module._default.ApplyToSet$X: Ty, 
      $ly: LayerType, 
      $Heap: Heap, 
      S#0: Set Box, 
      f#0: HandleType :: 
    {:weight 3} { _module.__default.ApplyToSet(_module._default.ApplyToSet$X, $LS($ly), Lit(S#0), f#0), $IsGoodHeap($Heap) } 
    _module.__default.ApplyToSet#canCall(_module._default.ApplyToSet$X, Lit(S#0), f#0)
         || (19 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(S#0, TSet(_module._default.ApplyToSet$X))
           && $Is(f#0, 
            Tclass._System.___hFunc1(_module._default.ApplyToSet$X, _module._default.ApplyToSet$X))
           && (forall x#3: Box :: 
            { Requires1(_module._default.ApplyToSet$X, _module._default.ApplyToSet$X, $Heap, f#0, x#3) } 
              { Reads1(_module._default.ApplyToSet$X, _module._default.ApplyToSet$X, $Heap, f#0, x#3) } 
              { S#0[x#3] } 
            $IsBox(x#3, _module._default.ApplyToSet$X)
               ==> (Lit(S#0)[x#3]
                   ==> Set#Equal(Reads1(_module._default.ApplyToSet$X, _module._default.ApplyToSet$X, $Heap, f#0, x#3), 
                    Set#Empty(): Set Box))
                 && (Lit(S#0)[x#3]
                   ==> Requires1(_module._default.ApplyToSet$X, _module._default.ApplyToSet$X, $Heap, f#0, x#3))))
       ==> (!Set#Equal(S#0, Set#Empty(): Set Box)
           ==> $let#3$canCall(_module._default.ApplyToSet$X, Lit(S#0))
             && _module.__default.ApplyToSet#canCall(_module._default.ApplyToSet$X, 
              Set#Difference(S#0, 
                Set#UnionOne(Set#Empty(): Set Box, $let#3_x(_module._default.ApplyToSet$X, Lit(S#0)))), 
              f#0))
         && _module.__default.ApplyToSet(_module._default.ApplyToSet$X, $LS($ly), Lit(S#0), f#0)
           == (if Set#Equal(S#0, Set#Empty(): Set Box)
             then Set#Empty(): Set Box
             else (var x#4 := $let#3_x(_module._default.ApplyToSet$X, Lit(S#0)); 
              Set#Union(_module.__default.ApplyToSet(_module._default.ApplyToSet$X, 
                  $LS($ly), 
                  Set#Difference(S#0, Set#UnionOne(Set#Empty(): Set Box, x#4)), 
                  f#0), 
                Set#UnionOne(Set#Empty(): Set Box, 
                  Apply1(_module._default.ApplyToSet$X, _module._default.ApplyToSet$X, $Heap, f#0, x#4))))));

// definition axiom for _module.__default.ApplyToSet for all literals (revealed)
axiom 19 <= $FunctionContextHeight
   ==> (forall _module._default.ApplyToSet$X: Ty, 
      $ly: LayerType, 
      $Heap: Heap, 
      S#0: Set Box, 
      f#0: HandleType :: 
    {:weight 3} { _module.__default.ApplyToSet(_module._default.ApplyToSet$X, $LS($ly), Lit(S#0), Lit(f#0)), $IsGoodHeap($Heap) } 
    _module.__default.ApplyToSet#canCall(_module._default.ApplyToSet$X, Lit(S#0), Lit(f#0))
         || (19 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(S#0, TSet(_module._default.ApplyToSet$X))
           && $Is(f#0, 
            Tclass._System.___hFunc1(_module._default.ApplyToSet$X, _module._default.ApplyToSet$X))
           && (forall x#5: Box :: 
            { Requires1(_module._default.ApplyToSet$X, _module._default.ApplyToSet$X, $Heap, f#0, x#5) } 
              { Reads1(_module._default.ApplyToSet$X, _module._default.ApplyToSet$X, $Heap, f#0, x#5) } 
              { S#0[x#5] } 
            $IsBox(x#5, _module._default.ApplyToSet$X)
               ==> (Lit(S#0)[x#5]
                   ==> Set#Equal(Reads1(_module._default.ApplyToSet$X, 
                      _module._default.ApplyToSet$X, 
                      $Heap, 
                      Lit(f#0), 
                      x#5), 
                    Set#Empty(): Set Box))
                 && (Lit(S#0)[x#5]
                   ==> Requires1(_module._default.ApplyToSet$X, 
                    _module._default.ApplyToSet$X, 
                    $Heap, 
                    Lit(f#0), 
                    x#5))))
       ==> (!Set#Equal(S#0, Set#Empty(): Set Box)
           ==> $let#3$canCall(_module._default.ApplyToSet$X, Lit(S#0))
             && _module.__default.ApplyToSet#canCall(_module._default.ApplyToSet$X, 
              Set#Difference(S#0, 
                Set#UnionOne(Set#Empty(): Set Box, $let#3_x(_module._default.ApplyToSet$X, Lit(S#0)))), 
              Lit(f#0)))
         && _module.__default.ApplyToSet(_module._default.ApplyToSet$X, $LS($ly), Lit(S#0), Lit(f#0))
           == (if Set#Equal(S#0, Set#Empty(): Set Box)
             then Set#Empty(): Set Box
             else (var x#6 := $let#3_x(_module._default.ApplyToSet$X, Lit(S#0)); 
              Set#Union(_module.__default.ApplyToSet(_module._default.ApplyToSet$X, 
                  $LS($ly), 
                  Set#Difference(S#0, Set#UnionOne(Set#Empty(): Set Box, x#6)), 
                  Lit(f#0)), 
                Set#UnionOne(Set#Empty(): Set Box, 
                  Apply1(_module._default.ApplyToSet$X, 
                    _module._default.ApplyToSet$X, 
                    $Heap, 
                    Lit(f#0), 
                    x#6))))));

procedure CheckWellformed$$_module.__default.ApplyToSet(_module._default.ApplyToSet$X: Ty, 
    S#0: Set Box where $Is(S#0, TSet(_module._default.ApplyToSet$X)), 
    f#0: HandleType
       where $Is(f#0, 
        Tclass._System.___hFunc1(_module._default.ApplyToSet$X, _module._default.ApplyToSet$X)));
  free requires 19 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.ApplyToSet(_module._default.ApplyToSet$X: Ty, S#0: Set Box, f#0: HandleType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var x#7: Box;
  var ##x0#0: Box;
  var ##x0#1: Box;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;
  var x#9: Box;
  var ##S#0: Set Box;
  var ##f#0: HandleType;
  var b$reqreads#2: bool;
  var b$reqreads#3: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;
    b$reqreads#3 := true;

    // AddWellformednessCheck for function ApplyToSet
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Reads.dfy(102,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    havoc x#7;
    assume $IsBox(x#7, _module._default.ApplyToSet$X);
    if (*)
    {
        assume S#0[x#7];
        ##x0#0 := x#7;
        // assume allocatedness for argument to function
        assume $IsAllocBox(##x0#0, _module._default.ApplyToSet$X, $Heap);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null
               && read($Heap, $o, alloc)
               && Reads1(_module._default.ApplyToSet$X, _module._default.ApplyToSet$X, $Heap, f#0, ##x0#0)[$Box($o)]
             ==> $_Frame[$o, $f]);
        assume Reads1#canCall(_module._default.ApplyToSet$X, _module._default.ApplyToSet$X, $Heap, f#0, x#7);
        assume Set#Equal(Reads1(_module._default.ApplyToSet$X, _module._default.ApplyToSet$X, $Heap, f#0, x#7), 
          Set#Empty(): Set Box);
        ##x0#1 := x#7;
        // assume allocatedness for argument to function
        assume $IsAllocBox(##x0#1, _module._default.ApplyToSet$X, $Heap);
        b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null
               && read($Heap, $o, alloc)
               && Reads1(_module._default.ApplyToSet$X, _module._default.ApplyToSet$X, $Heap, f#0, ##x0#1)[$Box($o)]
             ==> $_Frame[$o, $f]);
        assume Requires1#canCall(_module._default.ApplyToSet$X, _module._default.ApplyToSet$X, $Heap, f#0, x#7);
        assume Requires1(_module._default.ApplyToSet$X, _module._default.ApplyToSet$X, $Heap, f#0, x#7);
    }
    else
    {
        assume S#0[x#7]
           ==> Set#Equal(Reads1(_module._default.ApplyToSet$X, _module._default.ApplyToSet$X, $Heap, f#0, x#7), 
              Set#Empty(): Set Box)
             && Requires1(_module._default.ApplyToSet$X, _module._default.ApplyToSet$X, $Heap, f#0, x#7);
    }

    assume (forall x#8: Box :: 
      { Requires1(_module._default.ApplyToSet$X, _module._default.ApplyToSet$X, $Heap, f#0, x#8) } 
        { Reads1(_module._default.ApplyToSet$X, _module._default.ApplyToSet$X, $Heap, f#0, x#8) } 
        { S#0[x#8] } 
      $IsBox(x#8, _module._default.ApplyToSet$X)
         ==> (S#0[x#8]
             ==> Set#Equal(Reads1(_module._default.ApplyToSet$X, _module._default.ApplyToSet$X, $Heap, f#0, x#8), 
              Set#Empty(): Set Box))
           && (S#0[x#8]
             ==> Requires1(_module._default.ApplyToSet$X, _module._default.ApplyToSet$X, $Heap, f#0, x#8)));
    assert b$reqreads#0;
    assert b$reqreads#1;
    if (*)
    {
        assume $Is(_module.__default.ApplyToSet(_module._default.ApplyToSet$X, $LS($LZ), S#0, f#0), 
          TSet(_module._default.ApplyToSet$X));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (Set#Equal(S#0, Set#Empty(): Set Box))
        {
            assume _module.__default.ApplyToSet(_module._default.ApplyToSet$X, $LS($LZ), S#0, f#0)
               == Lit(Set#Empty(): Set Box);
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.ApplyToSet(_module._default.ApplyToSet$X, $LS($LZ), S#0, f#0), 
              TSet(_module._default.ApplyToSet$X));
        }
        else
        {
            havoc x#9;
            if ($IsBox(x#9, _module._default.ApplyToSet$X))
            {
            }

            assert (exists x#10: Box :: $IsBox(x#10, _module._default.ApplyToSet$X) && S#0[x#10]);
            assume $IsBox(x#9, _module._default.ApplyToSet$X);
            assume S#0[x#9];
            ##S#0 := Set#Difference(S#0, Set#UnionOne(Set#Empty(): Set Box, x#9));
            // assume allocatedness for argument to function
            assume $IsAlloc(##S#0, TSet(_module._default.ApplyToSet$X), $Heap);
            ##f#0 := f#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##f#0, 
              Tclass._System.___hFunc1(_module._default.ApplyToSet$X, _module._default.ApplyToSet$X), 
              $Heap);
            assert {:subsumption 0} (forall x#11: Box :: 
              { Requires1(_module._default.ApplyToSet$X, _module._default.ApplyToSet$X, $Heap, ##f#0, x#11) } 
                { Reads1(_module._default.ApplyToSet$X, _module._default.ApplyToSet$X, $Heap, ##f#0, x#11) } 
                { ##S#0[x#11] } 
              $IsBox(x#11, _module._default.ApplyToSet$X)
                 ==> (##S#0[x#11]
                     ==> Set#Equal(Reads1(_module._default.ApplyToSet$X, _module._default.ApplyToSet$X, $Heap, ##f#0, x#11), 
                      Set#Empty(): Set Box))
                   && (##S#0[x#11]
                     ==> Requires1(_module._default.ApplyToSet$X, _module._default.ApplyToSet$X, $Heap, ##f#0, x#11)));
            assume (forall x#11: Box :: 
              { Requires1(_module._default.ApplyToSet$X, _module._default.ApplyToSet$X, $Heap, ##f#0, x#11) } 
                { Reads1(_module._default.ApplyToSet$X, _module._default.ApplyToSet$X, $Heap, ##f#0, x#11) } 
                { ##S#0[x#11] } 
              $IsBox(x#11, _module._default.ApplyToSet$X)
                 ==> (##S#0[x#11]
                     ==> Set#Equal(Reads1(_module._default.ApplyToSet$X, _module._default.ApplyToSet$X, $Heap, ##f#0, x#11), 
                      Set#Empty(): Set Box))
                   && (##S#0[x#11]
                     ==> Requires1(_module._default.ApplyToSet$X, _module._default.ApplyToSet$X, $Heap, ##f#0, x#11)));
            b$reqreads#2 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert Set#Subset(##S#0, S#0) && !Set#Subset(S#0, ##S#0);
            assume _module.__default.ApplyToSet#canCall(_module._default.ApplyToSet$X, 
              Set#Difference(S#0, Set#UnionOne(Set#Empty(): Set Box, x#9)), 
              f#0);
            assert Requires1(_module._default.ApplyToSet$X, _module._default.ApplyToSet$X, $Heap, f#0, x#9);
            b$reqreads#3 := (forall<alpha> $o: ref, $f: Field alpha :: 
              $o != null
                   && read($Heap, $o, alloc)
                   && Reads1(_module._default.ApplyToSet$X, _module._default.ApplyToSet$X, $Heap, f#0, x#9)[$Box($o)]
                 ==> $_Frame[$o, $f]);
            assume $let#3$canCall(_module._default.ApplyToSet$X, S#0);
            assume _module.__default.ApplyToSet(_module._default.ApplyToSet$X, $LS($LZ), S#0, f#0)
               == Set#Union(_module.__default.ApplyToSet(_module._default.ApplyToSet$X, 
                  $LS($LZ), 
                  Set#Difference(S#0, Set#UnionOne(Set#Empty(): Set Box, x#9)), 
                  f#0), 
                Set#UnionOne(Set#Empty(): Set Box, 
                  Apply1(_module._default.ApplyToSet$X, _module._default.ApplyToSet$X, $Heap, f#0, x#9)));
            assume _module.__default.ApplyToSet#canCall(_module._default.ApplyToSet$X, 
              Set#Difference(S#0, Set#UnionOne(Set#Empty(): Set Box, x#9)), 
              f#0);
            // CheckWellformedWithResult: Let expression
            assume $Is(_module.__default.ApplyToSet(_module._default.ApplyToSet$X, $LS($LZ), S#0, f#0), 
              TSet(_module._default.ApplyToSet$X));
        }

        assert b$reqreads#2;
        assert b$reqreads#3;
    }
}



// function declaration for _module._default.ApplyToSet_AltSignature0
function _module.__default.ApplyToSet__AltSignature0(_module._default.ApplyToSet_AltSignature0$X: Ty, S#0: Set Box, f#0: HandleType)
   : Set Box;

function _module.__default.ApplyToSet__AltSignature0#canCall(_module._default.ApplyToSet_AltSignature0$X: Ty, S#0: Set Box, f#0: HandleType)
   : bool;

// consequence axiom for _module.__default.ApplyToSet__AltSignature0
axiom 25 <= $FunctionContextHeight
   ==> (forall _module._default.ApplyToSet_AltSignature0$X: Ty, 
      $Heap: Heap, 
      S#0: Set Box, 
      f#0: HandleType :: 
    { _module.__default.ApplyToSet__AltSignature0(_module._default.ApplyToSet_AltSignature0$X, S#0, f#0), $IsGoodHeap($Heap) } 
    _module.__default.ApplyToSet__AltSignature0#canCall(_module._default.ApplyToSet_AltSignature0$X, S#0, f#0)
         || (25 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(S#0, TSet(_module._default.ApplyToSet_AltSignature0$X))
           && $Is(f#0, 
            Tclass._System.___hFunc1(_module._default.ApplyToSet_AltSignature0$X, 
              _module._default.ApplyToSet_AltSignature0$X))
           && (forall x#0: Box :: 
            { Reads1(_module._default.ApplyToSet_AltSignature0$X, 
                _module._default.ApplyToSet_AltSignature0$X, 
                $Heap, 
                f#0, 
                x#0) } 
              { Requires1(_module._default.ApplyToSet_AltSignature0$X, 
                _module._default.ApplyToSet_AltSignature0$X, 
                $Heap, 
                f#0, 
                x#0) } 
              { S#0[x#0] } 
            $IsBox(x#0, _module._default.ApplyToSet_AltSignature0$X)
               ==> (S#0[x#0]
                   ==> Requires1(_module._default.ApplyToSet_AltSignature0$X, 
                    _module._default.ApplyToSet_AltSignature0$X, 
                    $Heap, 
                    f#0, 
                    x#0))
                 && (S#0[x#0]
                   ==> Set#Equal(Reads1(_module._default.ApplyToSet_AltSignature0$X, 
                      _module._default.ApplyToSet_AltSignature0$X, 
                      $Heap, 
                      f#0, 
                      x#0), 
                    Set#Empty(): Set Box))))
       ==> $Is(_module.__default.ApplyToSet__AltSignature0(_module._default.ApplyToSet_AltSignature0$X, S#0, f#0), 
        TSet(_module._default.ApplyToSet_AltSignature0$X)));

function _module.__default.ApplyToSet__AltSignature0#requires(Ty, Set Box, HandleType) : bool;

// #requires axiom for _module.__default.ApplyToSet__AltSignature0
axiom (forall _module._default.ApplyToSet_AltSignature0$X: Ty, 
    $Heap: Heap, 
    S#0: Set Box, 
    f#0: HandleType :: 
  { _module.__default.ApplyToSet__AltSignature0#requires(_module._default.ApplyToSet_AltSignature0$X, S#0, f#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && $Is(S#0, TSet(_module._default.ApplyToSet_AltSignature0$X))
       && $Is(f#0, 
        Tclass._System.___hFunc1(_module._default.ApplyToSet_AltSignature0$X, 
          _module._default.ApplyToSet_AltSignature0$X))
     ==> _module.__default.ApplyToSet__AltSignature0#requires(_module._default.ApplyToSet_AltSignature0$X, S#0, f#0)
       == (forall x#1: Box :: 
        { Reads1(_module._default.ApplyToSet_AltSignature0$X, 
            _module._default.ApplyToSet_AltSignature0$X, 
            $Heap, 
            f#0, 
            x#1) } 
          { Requires1(_module._default.ApplyToSet_AltSignature0$X, 
            _module._default.ApplyToSet_AltSignature0$X, 
            $Heap, 
            f#0, 
            x#1) } 
          { S#0[x#1] } 
        $IsBox(x#1, _module._default.ApplyToSet_AltSignature0$X)
           ==> (S#0[x#1]
               ==> Requires1(_module._default.ApplyToSet_AltSignature0$X, 
                _module._default.ApplyToSet_AltSignature0$X, 
                $Heap, 
                f#0, 
                x#1))
             && (S#0[x#1]
               ==> Set#Equal(Reads1(_module._default.ApplyToSet_AltSignature0$X, 
                  _module._default.ApplyToSet_AltSignature0$X, 
                  $Heap, 
                  f#0, 
                  x#1), 
                Set#Empty(): Set Box))));

procedure CheckWellformed$$_module.__default.ApplyToSet__AltSignature0(_module._default.ApplyToSet_AltSignature0$X: Ty, 
    S#0: Set Box where $Is(S#0, TSet(_module._default.ApplyToSet_AltSignature0$X)), 
    f#0: HandleType
       where $Is(f#0, 
        Tclass._System.___hFunc1(_module._default.ApplyToSet_AltSignature0$X, 
          _module._default.ApplyToSet_AltSignature0$X)));
  free requires 25 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.ApplyToSet__AltSignature0(_module._default.ApplyToSet_AltSignature0$X: Ty, S#0: Set Box, f#0: HandleType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var x#2: Box;
  var ##x0#0: Box;
  var ##x0#1: Box;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function ApplyToSet_AltSignature0
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Reads.dfy(110,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    havoc x#2;
    assume $IsBox(x#2, _module._default.ApplyToSet_AltSignature0$X);
    if (*)
    {
        assume S#0[x#2];
        ##x0#0 := x#2;
        // assume allocatedness for argument to function
        assume $IsAllocBox(##x0#0, _module._default.ApplyToSet_AltSignature0$X, $Heap);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null
               && read($Heap, $o, alloc)
               && Reads1(_module._default.ApplyToSet_AltSignature0$X, 
                _module._default.ApplyToSet_AltSignature0$X, 
                $Heap, 
                f#0, 
                ##x0#0)[$Box($o)]
             ==> $_Frame[$o, $f]);
        assume Requires1#canCall(_module._default.ApplyToSet_AltSignature0$X, 
          _module._default.ApplyToSet_AltSignature0$X, 
          $Heap, 
          f#0, 
          x#2);
        assume Requires1(_module._default.ApplyToSet_AltSignature0$X, 
          _module._default.ApplyToSet_AltSignature0$X, 
          $Heap, 
          f#0, 
          x#2);
        ##x0#1 := x#2;
        // assume allocatedness for argument to function
        assume $IsAllocBox(##x0#1, _module._default.ApplyToSet_AltSignature0$X, $Heap);
        b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null
               && read($Heap, $o, alloc)
               && Reads1(_module._default.ApplyToSet_AltSignature0$X, 
                _module._default.ApplyToSet_AltSignature0$X, 
                $Heap, 
                f#0, 
                ##x0#1)[$Box($o)]
             ==> $_Frame[$o, $f]);
        assume Reads1#canCall(_module._default.ApplyToSet_AltSignature0$X, 
          _module._default.ApplyToSet_AltSignature0$X, 
          $Heap, 
          f#0, 
          x#2);
        assume Set#Equal(Reads1(_module._default.ApplyToSet_AltSignature0$X, 
            _module._default.ApplyToSet_AltSignature0$X, 
            $Heap, 
            f#0, 
            x#2), 
          Set#Empty(): Set Box);
    }
    else
    {
        assume S#0[x#2]
           ==> Requires1(_module._default.ApplyToSet_AltSignature0$X, 
              _module._default.ApplyToSet_AltSignature0$X, 
              $Heap, 
              f#0, 
              x#2)
             && Set#Equal(Reads1(_module._default.ApplyToSet_AltSignature0$X, 
                _module._default.ApplyToSet_AltSignature0$X, 
                $Heap, 
                f#0, 
                x#2), 
              Set#Empty(): Set Box);
    }

    assume (forall x#3: Box :: 
      { Reads1(_module._default.ApplyToSet_AltSignature0$X, 
          _module._default.ApplyToSet_AltSignature0$X, 
          $Heap, 
          f#0, 
          x#3) } 
        { Requires1(_module._default.ApplyToSet_AltSignature0$X, 
          _module._default.ApplyToSet_AltSignature0$X, 
          $Heap, 
          f#0, 
          x#3) } 
        { S#0[x#3] } 
      $IsBox(x#3, _module._default.ApplyToSet_AltSignature0$X)
         ==> (S#0[x#3]
             ==> Requires1(_module._default.ApplyToSet_AltSignature0$X, 
              _module._default.ApplyToSet_AltSignature0$X, 
              $Heap, 
              f#0, 
              x#3))
           && (S#0[x#3]
             ==> Set#Equal(Reads1(_module._default.ApplyToSet_AltSignature0$X, 
                _module._default.ApplyToSet_AltSignature0$X, 
                $Heap, 
                f#0, 
                x#3), 
              Set#Empty(): Set Box)));
    assert b$reqreads#0;
    assert b$reqreads#1;
    if (*)
    {
        assume $Is(_module.__default.ApplyToSet__AltSignature0(_module._default.ApplyToSet_AltSignature0$X, S#0, f#0), 
          TSet(_module._default.ApplyToSet_AltSignature0$X));
        assume false;
    }
    else
    {
        assume false;
    }
}



// function declaration for _module._default.ApplyToSet_AltSignature1
function _module.__default.ApplyToSet__AltSignature1(_module._default.ApplyToSet_AltSignature1$X: Ty, S#0: Set Box, f#0: HandleType)
   : Set Box;

function _module.__default.ApplyToSet__AltSignature1#canCall(_module._default.ApplyToSet_AltSignature1$X: Ty, S#0: Set Box, f#0: HandleType)
   : bool;

// consequence axiom for _module.__default.ApplyToSet__AltSignature1
axiom 26 <= $FunctionContextHeight
   ==> (forall _module._default.ApplyToSet_AltSignature1$X: Ty, 
      $Heap: Heap, 
      S#0: Set Box, 
      f#0: HandleType :: 
    { _module.__default.ApplyToSet__AltSignature1(_module._default.ApplyToSet_AltSignature1$X, S#0, f#0), $IsGoodHeap($Heap) } 
    _module.__default.ApplyToSet__AltSignature1#canCall(_module._default.ApplyToSet_AltSignature1$X, S#0, f#0)
         || (26 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(S#0, TSet(_module._default.ApplyToSet_AltSignature1$X))
           && $Is(f#0, 
            Tclass._System.___hFunc1(_module._default.ApplyToSet_AltSignature1$X, 
              _module._default.ApplyToSet_AltSignature1$X))
           && 
          (forall x#0: Box :: 
            { Reads1(_module._default.ApplyToSet_AltSignature1$X, 
                _module._default.ApplyToSet_AltSignature1$X, 
                $Heap, 
                f#0, 
                x#0) } 
              { S#0[x#0] } 
            $IsBox(x#0, _module._default.ApplyToSet_AltSignature1$X)
               ==> 
              S#0[x#0]
               ==> Set#Equal(Reads1(_module._default.ApplyToSet_AltSignature1$X, 
                  _module._default.ApplyToSet_AltSignature1$X, 
                  $Heap, 
                  f#0, 
                  x#0), 
                Set#Empty(): Set Box))
           && (forall x#1: Box :: 
            { Requires1(_module._default.ApplyToSet_AltSignature1$X, 
                _module._default.ApplyToSet_AltSignature1$X, 
                $Heap, 
                f#0, 
                x#1) } 
              { S#0[x#1] } 
            $IsBox(x#1, _module._default.ApplyToSet_AltSignature1$X)
               ==> 
              S#0[x#1]
               ==> Requires1(_module._default.ApplyToSet_AltSignature1$X, 
                _module._default.ApplyToSet_AltSignature1$X, 
                $Heap, 
                f#0, 
                x#1)))
       ==> $Is(_module.__default.ApplyToSet__AltSignature1(_module._default.ApplyToSet_AltSignature1$X, S#0, f#0), 
        TSet(_module._default.ApplyToSet_AltSignature1$X)));

function _module.__default.ApplyToSet__AltSignature1#requires(Ty, Set Box, HandleType) : bool;

// #requires axiom for _module.__default.ApplyToSet__AltSignature1
axiom (forall _module._default.ApplyToSet_AltSignature1$X: Ty, 
    $Heap: Heap, 
    S#0: Set Box, 
    f#0: HandleType :: 
  { _module.__default.ApplyToSet__AltSignature1#requires(_module._default.ApplyToSet_AltSignature1$X, S#0, f#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && $Is(S#0, TSet(_module._default.ApplyToSet_AltSignature1$X))
       && $Is(f#0, 
        Tclass._System.___hFunc1(_module._default.ApplyToSet_AltSignature1$X, 
          _module._default.ApplyToSet_AltSignature1$X))
     ==> _module.__default.ApplyToSet__AltSignature1#requires(_module._default.ApplyToSet_AltSignature1$X, S#0, f#0)
       == ((forall x#2: Box :: 
          { Reads1(_module._default.ApplyToSet_AltSignature1$X, 
              _module._default.ApplyToSet_AltSignature1$X, 
              $Heap, 
              f#0, 
              x#2) } 
            { S#0[x#2] } 
          $IsBox(x#2, _module._default.ApplyToSet_AltSignature1$X)
             ==> 
            S#0[x#2]
             ==> Set#Equal(Reads1(_module._default.ApplyToSet_AltSignature1$X, 
                _module._default.ApplyToSet_AltSignature1$X, 
                $Heap, 
                f#0, 
                x#2), 
              Set#Empty(): Set Box))
         && (forall x#3: Box :: 
          { Requires1(_module._default.ApplyToSet_AltSignature1$X, 
              _module._default.ApplyToSet_AltSignature1$X, 
              $Heap, 
              f#0, 
              x#3) } 
            { S#0[x#3] } 
          $IsBox(x#3, _module._default.ApplyToSet_AltSignature1$X)
             ==> 
            S#0[x#3]
             ==> Requires1(_module._default.ApplyToSet_AltSignature1$X, 
              _module._default.ApplyToSet_AltSignature1$X, 
              $Heap, 
              f#0, 
              x#3))));

procedure CheckWellformed$$_module.__default.ApplyToSet__AltSignature1(_module._default.ApplyToSet_AltSignature1$X: Ty, 
    S#0: Set Box where $Is(S#0, TSet(_module._default.ApplyToSet_AltSignature1$X)), 
    f#0: HandleType
       where $Is(f#0, 
        Tclass._System.___hFunc1(_module._default.ApplyToSet_AltSignature1$X, 
          _module._default.ApplyToSet_AltSignature1$X)));
  free requires 26 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.ApplyToSet__AltSignature1(_module._default.ApplyToSet_AltSignature1$X: Ty, S#0: Set Box, f#0: HandleType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var x#4: Box;
  var ##x0#0: Box;
  var x#6: Box;
  var ##x0#1: Box;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function ApplyToSet_AltSignature1
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Reads.dfy(113,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    havoc x#4;
    assume $IsBox(x#4, _module._default.ApplyToSet_AltSignature1$X);
    if (*)
    {
        assume S#0[x#4];
        ##x0#0 := x#4;
        // assume allocatedness for argument to function
        assume $IsAllocBox(##x0#0, _module._default.ApplyToSet_AltSignature1$X, $Heap);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null
               && read($Heap, $o, alloc)
               && Reads1(_module._default.ApplyToSet_AltSignature1$X, 
                _module._default.ApplyToSet_AltSignature1$X, 
                $Heap, 
                f#0, 
                ##x0#0)[$Box($o)]
             ==> $_Frame[$o, $f]);
        assume Reads1#canCall(_module._default.ApplyToSet_AltSignature1$X, 
          _module._default.ApplyToSet_AltSignature1$X, 
          $Heap, 
          f#0, 
          x#4);
        assume Set#Equal(Reads1(_module._default.ApplyToSet_AltSignature1$X, 
            _module._default.ApplyToSet_AltSignature1$X, 
            $Heap, 
            f#0, 
            x#4), 
          Set#Empty(): Set Box);
    }
    else
    {
        assume S#0[x#4]
           ==> Set#Equal(Reads1(_module._default.ApplyToSet_AltSignature1$X, 
              _module._default.ApplyToSet_AltSignature1$X, 
              $Heap, 
              f#0, 
              x#4), 
            Set#Empty(): Set Box);
    }

    assume (forall x#5: Box :: 
      { Reads1(_module._default.ApplyToSet_AltSignature1$X, 
          _module._default.ApplyToSet_AltSignature1$X, 
          $Heap, 
          f#0, 
          x#5) } 
        { S#0[x#5] } 
      $IsBox(x#5, _module._default.ApplyToSet_AltSignature1$X)
         ==> 
        S#0[x#5]
         ==> Set#Equal(Reads1(_module._default.ApplyToSet_AltSignature1$X, 
            _module._default.ApplyToSet_AltSignature1$X, 
            $Heap, 
            f#0, 
            x#5), 
          Set#Empty(): Set Box));
    havoc x#6;
    assume $IsBox(x#6, _module._default.ApplyToSet_AltSignature1$X);
    if (*)
    {
        assume S#0[x#6];
        ##x0#1 := x#6;
        // assume allocatedness for argument to function
        assume $IsAllocBox(##x0#1, _module._default.ApplyToSet_AltSignature1$X, $Heap);
        b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null
               && read($Heap, $o, alloc)
               && Reads1(_module._default.ApplyToSet_AltSignature1$X, 
                _module._default.ApplyToSet_AltSignature1$X, 
                $Heap, 
                f#0, 
                ##x0#1)[$Box($o)]
             ==> $_Frame[$o, $f]);
        assume Requires1#canCall(_module._default.ApplyToSet_AltSignature1$X, 
          _module._default.ApplyToSet_AltSignature1$X, 
          $Heap, 
          f#0, 
          x#6);
        assume Requires1(_module._default.ApplyToSet_AltSignature1$X, 
          _module._default.ApplyToSet_AltSignature1$X, 
          $Heap, 
          f#0, 
          x#6);
    }
    else
    {
        assume S#0[x#6]
           ==> Requires1(_module._default.ApplyToSet_AltSignature1$X, 
            _module._default.ApplyToSet_AltSignature1$X, 
            $Heap, 
            f#0, 
            x#6);
    }

    assume (forall x#7: Box :: 
      { Requires1(_module._default.ApplyToSet_AltSignature1$X, 
          _module._default.ApplyToSet_AltSignature1$X, 
          $Heap, 
          f#0, 
          x#7) } 
        { S#0[x#7] } 
      $IsBox(x#7, _module._default.ApplyToSet_AltSignature1$X)
         ==> 
        S#0[x#7]
         ==> Requires1(_module._default.ApplyToSet_AltSignature1$X, 
          _module._default.ApplyToSet_AltSignature1$X, 
          $Heap, 
          f#0, 
          x#7));
    assert b$reqreads#0;
    assert b$reqreads#1;
    if (*)
    {
        assume $Is(_module.__default.ApplyToSet__AltSignature1(_module._default.ApplyToSet_AltSignature1$X, S#0, f#0), 
          TSet(_module._default.ApplyToSet_AltSignature1$X));
        assume false;
    }
    else
    {
        assume false;
    }
}



// function declaration for _module._default.ApplyToSet_AltSignature2
function _module.__default.ApplyToSet__AltSignature2(_module._default.ApplyToSet_AltSignature2$X: Ty, S#0: Set Box, f#0: HandleType)
   : Set Box;

function _module.__default.ApplyToSet__AltSignature2#canCall(_module._default.ApplyToSet_AltSignature2$X: Ty, S#0: Set Box, f#0: HandleType)
   : bool;

// consequence axiom for _module.__default.ApplyToSet__AltSignature2
axiom 27 <= $FunctionContextHeight
   ==> (forall _module._default.ApplyToSet_AltSignature2$X: Ty, 
      $Heap: Heap, 
      S#0: Set Box, 
      f#0: HandleType :: 
    { _module.__default.ApplyToSet__AltSignature2(_module._default.ApplyToSet_AltSignature2$X, S#0, f#0), $IsGoodHeap($Heap) } 
    _module.__default.ApplyToSet__AltSignature2#canCall(_module._default.ApplyToSet_AltSignature2$X, S#0, f#0)
         || (27 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(S#0, TSet(_module._default.ApplyToSet_AltSignature2$X))
           && $Is(f#0, 
            Tclass._System.___hFunc1(_module._default.ApplyToSet_AltSignature2$X, 
              _module._default.ApplyToSet_AltSignature2$X))
           && ((forall x#0: Box :: 
              { Reads1(_module._default.ApplyToSet_AltSignature2$X, 
                  _module._default.ApplyToSet_AltSignature2$X, 
                  $Heap, 
                  f#0, 
                  x#0) } 
                { S#0[x#0] } 
              $IsBox(x#0, _module._default.ApplyToSet_AltSignature2$X)
                 ==> 
                S#0[x#0]
                 ==> Set#Equal(Reads1(_module._default.ApplyToSet_AltSignature2$X, 
                    _module._default.ApplyToSet_AltSignature2$X, 
                    $Heap, 
                    f#0, 
                    x#0), 
                  Set#Empty(): Set Box))
             ==> (forall x#1: Box :: 
              { Requires1(_module._default.ApplyToSet_AltSignature2$X, 
                  _module._default.ApplyToSet_AltSignature2$X, 
                  $Heap, 
                  f#0, 
                  x#1) } 
                { S#0[x#1] } 
              $IsBox(x#1, _module._default.ApplyToSet_AltSignature2$X)
                 ==> 
                S#0[x#1]
                 ==> Requires1(_module._default.ApplyToSet_AltSignature2$X, 
                  _module._default.ApplyToSet_AltSignature2$X, 
                  $Heap, 
                  f#0, 
                  x#1))))
       ==> $Is(_module.__default.ApplyToSet__AltSignature2(_module._default.ApplyToSet_AltSignature2$X, S#0, f#0), 
        TSet(_module._default.ApplyToSet_AltSignature2$X)));

function _module.__default.ApplyToSet__AltSignature2#requires(Ty, Set Box, HandleType) : bool;

// #requires axiom for _module.__default.ApplyToSet__AltSignature2
axiom (forall _module._default.ApplyToSet_AltSignature2$X: Ty, 
    $Heap: Heap, 
    S#0: Set Box, 
    f#0: HandleType :: 
  { _module.__default.ApplyToSet__AltSignature2#requires(_module._default.ApplyToSet_AltSignature2$X, S#0, f#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && $Is(S#0, TSet(_module._default.ApplyToSet_AltSignature2$X))
       && $Is(f#0, 
        Tclass._System.___hFunc1(_module._default.ApplyToSet_AltSignature2$X, 
          _module._default.ApplyToSet_AltSignature2$X))
     ==> _module.__default.ApplyToSet__AltSignature2#requires(_module._default.ApplyToSet_AltSignature2$X, S#0, f#0)
       == ((forall x#2: Box :: 
          { Reads1(_module._default.ApplyToSet_AltSignature2$X, 
              _module._default.ApplyToSet_AltSignature2$X, 
              $Heap, 
              f#0, 
              x#2) } 
            { S#0[x#2] } 
          $IsBox(x#2, _module._default.ApplyToSet_AltSignature2$X)
             ==> 
            S#0[x#2]
             ==> Set#Equal(Reads1(_module._default.ApplyToSet_AltSignature2$X, 
                _module._default.ApplyToSet_AltSignature2$X, 
                $Heap, 
                f#0, 
                x#2), 
              Set#Empty(): Set Box))
         ==> (forall x#3: Box :: 
          { Requires1(_module._default.ApplyToSet_AltSignature2$X, 
              _module._default.ApplyToSet_AltSignature2$X, 
              $Heap, 
              f#0, 
              x#3) } 
            { S#0[x#3] } 
          $IsBox(x#3, _module._default.ApplyToSet_AltSignature2$X)
             ==> 
            S#0[x#3]
             ==> Requires1(_module._default.ApplyToSet_AltSignature2$X, 
              _module._default.ApplyToSet_AltSignature2$X, 
              $Heap, 
              f#0, 
              x#3))));

procedure CheckWellformed$$_module.__default.ApplyToSet__AltSignature2(_module._default.ApplyToSet_AltSignature2$X: Ty, 
    S#0: Set Box where $Is(S#0, TSet(_module._default.ApplyToSet_AltSignature2$X)), 
    f#0: HandleType
       where $Is(f#0, 
        Tclass._System.___hFunc1(_module._default.ApplyToSet_AltSignature2$X, 
          _module._default.ApplyToSet_AltSignature2$X)));
  free requires 27 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.ApplyToSet__AltSignature2(_module._default.ApplyToSet_AltSignature2$X: Ty, S#0: Set Box, f#0: HandleType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var x#4: Box;
  var ##x0#0: Box;
  var x#6: Box;
  var ##x0#1: Box;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function ApplyToSet_AltSignature2
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Reads.dfy(117,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        // Begin Comprehension WF check
        havoc x#4;
        if ($IsBox(x#4, _module._default.ApplyToSet_AltSignature2$X))
        {
            if (S#0[x#4])
            {
                ##x0#0 := x#4;
                // assume allocatedness for argument to function
                assume $IsAllocBox(##x0#0, _module._default.ApplyToSet_AltSignature2$X, $Heap);
                b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: 
                  $o != null
                       && read($Heap, $o, alloc)
                       && Reads1(_module._default.ApplyToSet_AltSignature2$X, 
                        _module._default.ApplyToSet_AltSignature2$X, 
                        $Heap, 
                        f#0, 
                        ##x0#0)[$Box($o)]
                     ==> $_Frame[$o, $f]);
                assume Reads1#canCall(_module._default.ApplyToSet_AltSignature2$X, 
                  _module._default.ApplyToSet_AltSignature2$X, 
                  $Heap, 
                  f#0, 
                  x#4);
            }
        }

        // End Comprehension WF check
        assume (forall x#5: Box :: 
          { Reads1(_module._default.ApplyToSet_AltSignature2$X, 
              _module._default.ApplyToSet_AltSignature2$X, 
              $Heap, 
              f#0, 
              x#5) } 
            { S#0[x#5] } 
          $IsBox(x#5, _module._default.ApplyToSet_AltSignature2$X)
             ==> 
            S#0[x#5]
             ==> Set#Equal(Reads1(_module._default.ApplyToSet_AltSignature2$X, 
                _module._default.ApplyToSet_AltSignature2$X, 
                $Heap, 
                f#0, 
                x#5), 
              Set#Empty(): Set Box));
        havoc x#6;
        assume $IsBox(x#6, _module._default.ApplyToSet_AltSignature2$X);
        if (*)
        {
            assume S#0[x#6];
            ##x0#1 := x#6;
            // assume allocatedness for argument to function
            assume $IsAllocBox(##x0#1, _module._default.ApplyToSet_AltSignature2$X, $Heap);
            b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: 
              $o != null
                   && read($Heap, $o, alloc)
                   && Reads1(_module._default.ApplyToSet_AltSignature2$X, 
                    _module._default.ApplyToSet_AltSignature2$X, 
                    $Heap, 
                    f#0, 
                    ##x0#1)[$Box($o)]
                 ==> $_Frame[$o, $f]);
            assume Requires1#canCall(_module._default.ApplyToSet_AltSignature2$X, 
              _module._default.ApplyToSet_AltSignature2$X, 
              $Heap, 
              f#0, 
              x#6);
            assume Requires1(_module._default.ApplyToSet_AltSignature2$X, 
              _module._default.ApplyToSet_AltSignature2$X, 
              $Heap, 
              f#0, 
              x#6);
        }
        else
        {
            assume S#0[x#6]
               ==> Requires1(_module._default.ApplyToSet_AltSignature2$X, 
                _module._default.ApplyToSet_AltSignature2$X, 
                $Heap, 
                f#0, 
                x#6);
        }

        assume (forall x#7: Box :: 
          { Requires1(_module._default.ApplyToSet_AltSignature2$X, 
              _module._default.ApplyToSet_AltSignature2$X, 
              $Heap, 
              f#0, 
              x#7) } 
            { S#0[x#7] } 
          $IsBox(x#7, _module._default.ApplyToSet_AltSignature2$X)
             ==> 
            S#0[x#7]
             ==> Requires1(_module._default.ApplyToSet_AltSignature2$X, 
              _module._default.ApplyToSet_AltSignature2$X, 
              $Heap, 
              f#0, 
              x#7));
    }
    else
    {
        assume (forall x#5: Box :: 
            { Reads1(_module._default.ApplyToSet_AltSignature2$X, 
                _module._default.ApplyToSet_AltSignature2$X, 
                $Heap, 
                f#0, 
                x#5) } 
              { S#0[x#5] } 
            $IsBox(x#5, _module._default.ApplyToSet_AltSignature2$X)
               ==> 
              S#0[x#5]
               ==> Set#Equal(Reads1(_module._default.ApplyToSet_AltSignature2$X, 
                  _module._default.ApplyToSet_AltSignature2$X, 
                  $Heap, 
                  f#0, 
                  x#5), 
                Set#Empty(): Set Box))
           ==> (forall x#7: Box :: 
            { Requires1(_module._default.ApplyToSet_AltSignature2$X, 
                _module._default.ApplyToSet_AltSignature2$X, 
                $Heap, 
                f#0, 
                x#7) } 
              { S#0[x#7] } 
            $IsBox(x#7, _module._default.ApplyToSet_AltSignature2$X)
               ==> 
              S#0[x#7]
               ==> Requires1(_module._default.ApplyToSet_AltSignature2$X, 
                _module._default.ApplyToSet_AltSignature2$X, 
                $Heap, 
                f#0, 
                x#7));
    }

    assert b$reqreads#0;
    assert b$reqreads#1;
    if (*)
    {
        assume $Is(_module.__default.ApplyToSet__AltSignature2(_module._default.ApplyToSet_AltSignature2$X, S#0, f#0), 
          TSet(_module._default.ApplyToSet_AltSignature2$X));
        assume false;
    }
    else
    {
        assume false;
    }
}



// function declaration for _module._default.FunctionInQuantifier0
function _module.__default.FunctionInQuantifier0() : int;

function _module.__default.FunctionInQuantifier0#canCall() : bool;

// consequence axiom for _module.__default.FunctionInQuantifier0
axiom 28 <= $FunctionContextHeight
   ==> (forall $Heap: Heap :: 
    { _module.__default.FunctionInQuantifier0(), $IsGoodHeap($Heap) } 
    _module.__default.FunctionInQuantifier0#canCall()
         || (28 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && (exists f#0: HandleType :: 
            { $Unbox(Apply1(TInt, TInt, $Heap, f#0, $Box(10))): int } 
            $Is(f#0, Tclass._System.___hFunc1(TInt, TInt))
               && $Unbox(Apply1(TInt, TInt, $Heap, f#0, $Box(LitInt(10)))): int == LitInt(100)))
       ==> true);

function _module.__default.FunctionInQuantifier0#requires() : bool;

// #requires axiom for _module.__default.FunctionInQuantifier0
axiom (forall $Heap: Heap :: 
  { _module.__default.FunctionInQuantifier0#requires(), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
     ==> _module.__default.FunctionInQuantifier0#requires()
       == (exists f#1: HandleType :: 
        { $Unbox(Apply1(TInt, TInt, $Heap, f#1, $Box(10))): int } 
        $Is(f#1, Tclass._System.___hFunc1(TInt, TInt))
           && $Unbox(Apply1(TInt, TInt, $Heap, f#1, $Box(LitInt(10)))): int == LitInt(100)));

procedure CheckWellformed$$_module.__default.FunctionInQuantifier0();
  free requires 28 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.FunctionInQuantifier0()
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var f#2: HandleType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function FunctionInQuantifier0
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Reads.dfy(121,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    havoc f#2;
    assume $Is(f#2, Tclass._System.___hFunc1(TInt, TInt));
    assert Requires1(TInt, TInt, $Heap, f#2, $Box(LitInt(10)));
    b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && read($Heap, $o, alloc)
           && Reads1(TInt, TInt, $Heap, f#2, $Box(LitInt(10)))[$Box($o)]
         ==> $_Frame[$o, $f]);
    assume $Unbox(Apply1(TInt, TInt, $Heap, f#2, $Box(LitInt(10)))): int == LitInt(100);
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



// function declaration for _module._default.FunctionInQuantifier1
function _module.__default.FunctionInQuantifier1() : int;

function _module.__default.FunctionInQuantifier1#canCall() : bool;

// consequence axiom for _module.__default.FunctionInQuantifier1
axiom 29 <= $FunctionContextHeight
   ==> (forall $Heap: Heap :: 
    { _module.__default.FunctionInQuantifier1(), $IsGoodHeap($Heap) } 
    _module.__default.FunctionInQuantifier1#canCall()
         || (29 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && (exists f#0: HandleType :: 
            { $Unbox(Apply1(TInt, TInt, $Heap, f#0, $Box(10))): int } 
              { Requires1(TInt, TInt, $Heap, f#0, $Box(10)) } 
            $Is(f#0, Tclass._System.___hFunc1(TInt, TInt))
               && 
              Requires1(TInt, TInt, $Heap, f#0, $Box(LitInt(10)))
               && $Unbox(Apply1(TInt, TInt, $Heap, f#0, $Box(LitInt(10)))): int == LitInt(100)))
       ==> true);

function _module.__default.FunctionInQuantifier1#requires() : bool;

// #requires axiom for _module.__default.FunctionInQuantifier1
axiom (forall $Heap: Heap :: 
  { _module.__default.FunctionInQuantifier1#requires(), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
     ==> _module.__default.FunctionInQuantifier1#requires()
       == (exists f#1: HandleType :: 
        { $Unbox(Apply1(TInt, TInt, $Heap, f#1, $Box(10))): int } 
          { Requires1(TInt, TInt, $Heap, f#1, $Box(10)) } 
        $Is(f#1, Tclass._System.___hFunc1(TInt, TInt))
           && 
          Requires1(TInt, TInt, $Heap, f#1, $Box(LitInt(10)))
           && $Unbox(Apply1(TInt, TInt, $Heap, f#1, $Box(LitInt(10)))): int == LitInt(100)));

procedure CheckWellformed$$_module.__default.FunctionInQuantifier1();
  free requires 29 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.FunctionInQuantifier1()
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var f#2: HandleType;
  var ##x0#0: int;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function FunctionInQuantifier1
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Reads.dfy(124,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    havoc f#2;
    assume $Is(f#2, Tclass._System.___hFunc1(TInt, TInt));
    ##x0#0 := LitInt(10);
    // assume allocatedness for argument to function
    assume $IsAlloc(##x0#0, TInt, $Heap);
    b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && read($Heap, $o, alloc)
           && Reads1(TInt, TInt, $Heap, f#2, $Box(##x0#0))[$Box($o)]
         ==> $_Frame[$o, $f]);
    assume Requires1#canCall(TInt, TInt, $Heap, f#2, $Box(LitInt(10)));
    assume Requires1(TInt, TInt, $Heap, f#2, $Box(LitInt(10)));
    assert Requires1(TInt, TInt, $Heap, f#2, $Box(LitInt(10)));
    b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && read($Heap, $o, alloc)
           && Reads1(TInt, TInt, $Heap, f#2, $Box(LitInt(10)))[$Box($o)]
         ==> $_Frame[$o, $f]);
    assume $Unbox(Apply1(TInt, TInt, $Heap, f#2, $Box(LitInt(10)))): int == LitInt(100);
    assert b$reqreads#0;
    assert b$reqreads#1;
    if (*)
    {
        assume false;
    }
    else
    {
        assume false;
    }
}



// function declaration for _module._default.FunctionInQuantifier2
function _module.__default.FunctionInQuantifier2() : int;

function _module.__default.FunctionInQuantifier2#canCall() : bool;

// consequence axiom for _module.__default.FunctionInQuantifier2
axiom 20 <= $FunctionContextHeight
   ==> (forall $Heap: Heap :: 
    { _module.__default.FunctionInQuantifier2(), $IsGoodHeap($Heap) } 
    _module.__default.FunctionInQuantifier2#canCall()
         || (20 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && (exists f#0: HandleType :: 
            { $Unbox(Apply1(TInt, TInt, $Heap, f#0, $Box(10))): int } 
              { Requires1(TInt, TInt, $Heap, f#0, $Box(10)) } 
              { Reads1(TInt, TInt, $Heap, f#0, $Box(10)) } 
            $Is(f#0, Tclass._System.___hFunc1(TInt, TInt))
               && 
              Set#Equal(Reads1(TInt, TInt, $Heap, f#0, $Box(LitInt(10))), Set#Empty(): Set Box)
               && Requires1(TInt, TInt, $Heap, f#0, $Box(LitInt(10)))
               && $Unbox(Apply1(TInt, TInt, $Heap, f#0, $Box(LitInt(10)))): int == LitInt(100)))
       ==> LitInt(_module.__default.FunctionInQuantifier2()) == LitInt(100));

function _module.__default.FunctionInQuantifier2#requires() : bool;

// #requires axiom for _module.__default.FunctionInQuantifier2
axiom (forall $Heap: Heap :: 
  { _module.__default.FunctionInQuantifier2#requires(), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
     ==> _module.__default.FunctionInQuantifier2#requires()
       == (exists f#1: HandleType :: 
        { $Unbox(Apply1(TInt, TInt, $Heap, f#1, $Box(10))): int } 
          { Requires1(TInt, TInt, $Heap, f#1, $Box(10)) } 
          { Reads1(TInt, TInt, $Heap, f#1, $Box(10)) } 
        $Is(f#1, Tclass._System.___hFunc1(TInt, TInt))
           && 
          Set#Equal(Reads1(TInt, TInt, $Heap, f#1, $Box(LitInt(10))), Set#Empty(): Set Box)
           && Requires1(TInt, TInt, $Heap, f#1, $Box(LitInt(10)))
           && $Unbox(Apply1(TInt, TInt, $Heap, f#1, $Box(LitInt(10)))): int == LitInt(100)));

function $let#7_f($heap: Heap) : HandleType;

function $let#7$canCall($heap: Heap) : bool;

axiom (forall $heap: Heap :: 
  { $let#7_f($heap) } 
  $let#7$canCall($heap)
     ==> $Is($let#7_f($heap), Tclass._System.___hFunc1(TInt, TInt))
       && 
      Set#Equal(Reads1(TInt, TInt, $heap, $let#7_f($heap), $Box(LitInt(10))), 
        Set#Empty(): Set Box)
       && Requires1(TInt, TInt, $heap, $let#7_f($heap), $Box(LitInt(10)))
       && $Unbox(Apply1(TInt, TInt, $heap, $let#7_f($heap), $Box(LitInt(10)))): int
         == LitInt(100));

// definition axiom for _module.__default.FunctionInQuantifier2 (revealed)
axiom 20 <= $FunctionContextHeight
   ==> (forall $Heap: Heap :: 
    { _module.__default.FunctionInQuantifier2(), $IsGoodHeap($Heap) } 
    _module.__default.FunctionInQuantifier2#canCall()
         || (20 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && (exists f#1: HandleType :: 
            { $Unbox(Apply1(TInt, TInt, $Heap, f#1, $Box(10))): int } 
              { Requires1(TInt, TInt, $Heap, f#1, $Box(10)) } 
              { Reads1(TInt, TInt, $Heap, f#1, $Box(10)) } 
            $Is(f#1, Tclass._System.___hFunc1(TInt, TInt))
               && 
              Set#Equal(Reads1(TInt, TInt, $Heap, f#1, $Box(LitInt(10))), Set#Empty(): Set Box)
               && Requires1(TInt, TInt, $Heap, f#1, $Box(LitInt(10)))
               && $Unbox(Apply1(TInt, TInt, $Heap, f#1, $Box(LitInt(10)))): int == LitInt(100)))
       ==> $let#7$canCall($Heap)
         && _module.__default.FunctionInQuantifier2()
           == (var f#2 := $let#7_f($Heap); 
            $Unbox(Apply1(TInt, TInt, $Heap, f#2, $Box(LitInt(10)))): int));

// definition axiom for _module.__default.FunctionInQuantifier2 for all literals (revealed)
axiom 20 <= $FunctionContextHeight
   ==> (forall $Heap: Heap :: 
    {:weight 3} { _module.__default.FunctionInQuantifier2(), $IsGoodHeap($Heap) } 
    _module.__default.FunctionInQuantifier2#canCall()
         || (20 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && (exists f#3: HandleType :: 
            { $Unbox(Apply1(TInt, TInt, $Heap, f#3, $Box(10))): int } 
              { Requires1(TInt, TInt, $Heap, f#3, $Box(10)) } 
              { Reads1(TInt, TInt, $Heap, f#3, $Box(10)) } 
            $Is(f#3, Tclass._System.___hFunc1(TInt, TInt))
               && 
              Set#Equal(Reads1(TInt, TInt, $Heap, f#3, $Box(LitInt(10))), Set#Empty(): Set Box)
               && Requires1(TInt, TInt, $Heap, f#3, $Box(LitInt(10)))
               && $Unbox(Apply1(TInt, TInt, $Heap, f#3, $Box(LitInt(10)))): int == LitInt(100)))
       ==> $let#7$canCall($Heap)
         && _module.__default.FunctionInQuantifier2()
           == (var f#4 := $let#7_f($Heap); 
            $Unbox(Apply1(TInt, TInt, $Heap, f#4, $Box(LitInt(10)))): int));

procedure CheckWellformed$$_module.__default.FunctionInQuantifier2();
  free requires 20 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures LitInt(_module.__default.FunctionInQuantifier2()) == LitInt(100);



implementation CheckWellformed$$_module.__default.FunctionInQuantifier2()
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var f#5: HandleType;
  var ##x0#0: int;
  var ##x0#1: int;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;
  var b$reqreads#2: bool;
  var f#7: HandleType;
  var ##x0#2: int;
  var ##x0#3: int;
  var b$reqreads#3: bool;
  var b$reqreads#4: bool;
  var b$reqreads#5: bool;
  var b$reqreads#6: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;
    b$reqreads#3 := true;
    b$reqreads#4 := true;
    b$reqreads#5 := true;
    b$reqreads#6 := true;

    // AddWellformednessCheck for function FunctionInQuantifier2
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Reads.dfy(127,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    havoc f#5;
    assume $Is(f#5, Tclass._System.___hFunc1(TInt, TInt));
    ##x0#0 := LitInt(10);
    // assume allocatedness for argument to function
    assume $IsAlloc(##x0#0, TInt, $Heap);
    b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && read($Heap, $o, alloc)
           && Reads1(TInt, TInt, $Heap, f#5, $Box(##x0#0))[$Box($o)]
         ==> $_Frame[$o, $f]);
    assume Reads1#canCall(TInt, TInt, $Heap, f#5, $Box(LitInt(10)));
    assume Set#Equal(Reads1(TInt, TInt, $Heap, f#5, $Box(LitInt(10))), Set#Empty(): Set Box);
    ##x0#1 := LitInt(10);
    // assume allocatedness for argument to function
    assume $IsAlloc(##x0#1, TInt, $Heap);
    b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && read($Heap, $o, alloc)
           && Reads1(TInt, TInt, $Heap, f#5, $Box(##x0#1))[$Box($o)]
         ==> $_Frame[$o, $f]);
    assume Requires1#canCall(TInt, TInt, $Heap, f#5, $Box(LitInt(10)));
    assume Requires1(TInt, TInt, $Heap, f#5, $Box(LitInt(10)));
    assert Requires1(TInt, TInt, $Heap, f#5, $Box(LitInt(10)));
    b$reqreads#2 := (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && read($Heap, $o, alloc)
           && Reads1(TInt, TInt, $Heap, f#5, $Box(LitInt(10)))[$Box($o)]
         ==> $_Frame[$o, $f]);
    assume $Unbox(Apply1(TInt, TInt, $Heap, f#5, $Box(LitInt(10)))): int == LitInt(100);
    assert b$reqreads#0;
    assert b$reqreads#1;
    assert b$reqreads#2;
    if (*)
    {
        assert {:subsumption 0} (exists f#6: HandleType :: 
          { $Unbox(Apply1(TInt, TInt, $Heap, f#6, $Box(10))): int } 
            { Requires1(TInt, TInt, $Heap, f#6, $Box(10)) } 
            { Reads1(TInt, TInt, $Heap, f#6, $Box(10)) } 
          $Is(f#6, Tclass._System.___hFunc1(TInt, TInt))
             && 
            Set#Equal(Reads1(TInt, TInt, $Heap, f#6, $Box(LitInt(10))), Set#Empty(): Set Box)
             && Requires1(TInt, TInt, $Heap, f#6, $Box(LitInt(10)))
             && $Unbox(Apply1(TInt, TInt, $Heap, f#6, $Box(LitInt(10)))): int == LitInt(100));
        assume (exists f#6: HandleType :: 
          { $Unbox(Apply1(TInt, TInt, $Heap, f#6, $Box(10))): int } 
            { Requires1(TInt, TInt, $Heap, f#6, $Box(10)) } 
            { Reads1(TInt, TInt, $Heap, f#6, $Box(10)) } 
          $Is(f#6, Tclass._System.___hFunc1(TInt, TInt))
             && 
            Set#Equal(Reads1(TInt, TInt, $Heap, f#6, $Box(LitInt(10))), Set#Empty(): Set Box)
             && Requires1(TInt, TInt, $Heap, f#6, $Box(LitInt(10)))
             && $Unbox(Apply1(TInt, TInt, $Heap, f#6, $Box(LitInt(10)))): int == LitInt(100));
        assert true;
        assume true;
        assume LitInt(_module.__default.FunctionInQuantifier2()) == LitInt(100);
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        havoc f#7;
        if ($Is(f#7, Tclass._System.___hFunc1(TInt, TInt)))
        {
            ##x0#2 := LitInt(10);
            // assume allocatedness for argument to function
            assume $IsAlloc(##x0#2, TInt, $Heap);
            b$reqreads#3 := (forall<alpha> $o: ref, $f: Field alpha :: 
              $o != null
                   && read($Heap, $o, alloc)
                   && Reads1(TInt, TInt, $Heap, f#7, $Box(##x0#2))[$Box($o)]
                 ==> $_Frame[$o, $f]);
            assume Reads1#canCall(TInt, TInt, $Heap, f#7, $Box(LitInt(10)));
            if (Set#Equal(Reads1(TInt, TInt, $Heap, f#7, $Box(LitInt(10))), Set#Empty(): Set Box))
            {
                ##x0#3 := LitInt(10);
                // assume allocatedness for argument to function
                assume $IsAlloc(##x0#3, TInt, $Heap);
                b$reqreads#4 := (forall<alpha> $o: ref, $f: Field alpha :: 
                  $o != null
                       && read($Heap, $o, alloc)
                       && Reads1(TInt, TInt, $Heap, f#7, $Box(##x0#3))[$Box($o)]
                     ==> $_Frame[$o, $f]);
                assume Requires1#canCall(TInt, TInt, $Heap, f#7, $Box(LitInt(10)));
            }

            if (Set#Equal(Reads1(TInt, TInt, $Heap, f#7, $Box(LitInt(10))), Set#Empty(): Set Box)
               && Requires1(TInt, TInt, $Heap, f#7, $Box(LitInt(10))))
            {
                assert Requires1(TInt, TInt, $Heap, f#7, $Box(LitInt(10)));
                b$reqreads#5 := (forall<alpha> $o: ref, $f: Field alpha :: 
                  $o != null
                       && read($Heap, $o, alloc)
                       && Reads1(TInt, TInt, $Heap, f#7, $Box(LitInt(10)))[$Box($o)]
                     ==> $_Frame[$o, $f]);
            }
        }

        assert (exists f#8: HandleType :: 
          $Is(f#8, Tclass._System.___hFunc1(TInt, TInt))
             && 
            Set#Equal(Reads1(TInt, TInt, $Heap, f#8, $Box(LitInt(10))), Set#Empty(): Set Box)
             && Requires1(TInt, TInt, $Heap, f#8, $Box(LitInt(10)))
             && $Unbox(Apply1(TInt, TInt, $Heap, f#8, $Box(LitInt(10)))): int == LitInt(100));
        assume $Is(f#7, Tclass._System.___hFunc1(TInt, TInt));
        assume Set#Equal(Reads1(TInt, TInt, $Heap, f#7, $Box(LitInt(10))), Set#Empty(): Set Box)
           && Requires1(TInt, TInt, $Heap, f#7, $Box(LitInt(10)))
           && $Unbox(Apply1(TInt, TInt, $Heap, f#7, $Box(LitInt(10)))): int == LitInt(100);
        assert Requires1(TInt, TInt, $Heap, f#7, $Box(LitInt(10)));
        b$reqreads#6 := (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null
               && read($Heap, $o, alloc)
               && Reads1(TInt, TInt, $Heap, f#7, $Box(LitInt(10)))[$Box($o)]
             ==> $_Frame[$o, $f]);
        assume $let#7$canCall($Heap);
        assume _module.__default.FunctionInQuantifier2()
           == $Unbox(Apply1(TInt, TInt, $Heap, f#7, $Box(LitInt(10)))): int;
        assume true;
        // CheckWellformedWithResult: Let expression
        assume $Is(_module.__default.FunctionInQuantifier2(), TInt);
        assert b$reqreads#3;
        assert b$reqreads#4;
        assert b$reqreads#5;
        assert b$reqreads#6;
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

const unique tytagFamily$_tuple#0: TyTagFamily;

const unique tytagFamily$_#Func2: TyTagFamily;

const unique tytagFamily$_#PartialFunc2: TyTagFamily;

const unique tytagFamily$_#TotalFunc2: TyTagFamily;

const unique tytagFamily$_tuple#2: TyTagFamily;

const unique tytagFamily$C: TyTagFamily;

const unique tytagFamily$R: TyTagFamily;

const unique tytagFamily$CircularChecking: TyTagFamily;

const unique tytagFamily$Cell: TyTagFamily;

const unique tytagFamily$DynamicFramesIdiom: TyTagFamily;

const unique tytagFamily$ReadsTestsInsideLetSuchThat: TyTagFamily;

const unique tytagFamily$_default: TyTagFamily;

const unique field$u: NameFamily;

const unique field$r: NameFamily;

const unique field$Repr: NameFamily;

const unique field$data: NameFamily;

const unique field$y: NameFamily;
