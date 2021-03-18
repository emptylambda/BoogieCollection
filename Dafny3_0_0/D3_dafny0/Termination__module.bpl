// Dafny 3.0.0.30204
// Command Line Options: -compile:0 -noVerify /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy -print:./Termination.bpl

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

const unique class._module.Termination?: ClassName;

function Tclass._module.Termination?() : Ty;

const unique Tagclass._module.Termination?: TyTag;

// Tclass._module.Termination? Tag
axiom Tag(Tclass._module.Termination?()) == Tagclass._module.Termination?
   && TagFamily(Tclass._module.Termination?()) == tytagFamily$Termination;

// Box/unbox axiom for Tclass._module.Termination?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Termination?()) } 
  $IsBox(bx, Tclass._module.Termination?())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.Termination?()));

// Termination: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.Termination?()) } 
  $Is($o, Tclass._module.Termination?())
     <==> $o == null || dtype($o) == Tclass._module.Termination?());

// Termination: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.Termination?(), $h) } 
  $IsAlloc($o, Tclass._module.Termination?(), $h)
     <==> $o == null || read($h, $o, alloc));

function Tclass._module.Termination() : Ty;

const unique Tagclass._module.Termination: TyTag;

// Tclass._module.Termination Tag
axiom Tag(Tclass._module.Termination()) == Tagclass._module.Termination
   && TagFamily(Tclass._module.Termination()) == tytagFamily$Termination;

// Box/unbox axiom for Tclass._module.Termination
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Termination()) } 
  $IsBox(bx, Tclass._module.Termination())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.Termination()));

procedure CheckWellformed$$_module.Termination.A(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Termination())
         && $IsAlloc(this, Tclass._module.Termination(), $Heap), 
    N#0: int);
  free requires 37 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Termination.A(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Termination())
         && $IsAlloc(this, Tclass._module.Termination(), $Heap), 
    N#0: int);
  // user-defined preconditions
  requires LitInt(0) <= N#0;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Termination.A(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Termination())
         && $IsAlloc(this, Tclass._module.Termination(), $Heap), 
    N#0: int)
   returns ($_reverifyPost: bool);
  free requires 37 == $FunctionContextHeight;
  // user-defined preconditions
  requires LitInt(0) <= N#0;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Termination.A(this: ref, N#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var i#0: int;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var $decr$loop#00: int;

    // AddMethodImpl: A, Impl$$_module.Termination.A
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(7,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(8,11)
    assume true;
    assume true;
    i#0 := LitInt(0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(8,14)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(9,5)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := N#0 - i#0;
    havoc $w$loop#0;
    while (true)
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> i#0 <= N#0;
      free invariant (forall $o: ref :: 
        { $Heap[$o] } 
        $o != null && read(old($Heap), $o, alloc)
           ==> $Heap[$o] == $PreLoopHeap$loop#0[$o]);
      free invariant $HeapSucc($PreLoopHeap$loop#0, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
        { read($Heap, $o, $f) } 
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
      free invariant N#0 - i#0 <= $decr_init$loop#00 && (N#0 - i#0 == $decr_init$loop#00 ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(9,4): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assume true;
            assume i#0 <= N#0;
            assume true;
            assume false;
        }

        assume true;
        if (N#0 <= i#0)
        {
            break;
        }

        $decr$loop#00 := N#0 - i#0;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(13,9)
        assume true;
        assume true;
        i#0 := i#0 + 1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(13,16)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(9,5)
        assert 0 <= $decr$loop#00 || N#0 - i#0 == $decr$loop#00;
        assert N#0 - i#0 < $decr$loop#00;
        assume true;
    }
}



procedure CheckWellformed$$_module.Termination.B(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Termination())
         && $IsAlloc(this, Tclass._module.Termination(), $Heap), 
    N#0: int);
  free requires 38 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Termination.B(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Termination())
         && $IsAlloc(this, Tclass._module.Termination(), $Heap), 
    N#0: int);
  // user-defined preconditions
  requires LitInt(0) <= N#0;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Termination.B(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Termination())
         && $IsAlloc(this, Tclass._module.Termination(), $Heap), 
    N#0: int)
   returns ($_reverifyPost: bool);
  free requires 38 == $FunctionContextHeight;
  // user-defined preconditions
  requires LitInt(0) <= N#0;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Termination.B(this: ref, N#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var i#0: int;
  var $Heap_at_0: Heap;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var $decr$loop#00: int;

    // AddMethodImpl: B, Impl$$_module.Termination.B
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(19,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(20,11)
    assume true;
    assume true;
    i#0 := N#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(20,14)"} true;
    $Heap_at_0 := $Heap;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(21,5)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := i#0;
    havoc $w$loop#0;
    while (true)
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> LitInt(0) <= i#0;
      free invariant (forall $o: ref :: 
        { $Heap[$o] } 
        $o != null && read(old($Heap), $o, alloc)
           ==> $Heap[$o] == $PreLoopHeap$loop#0[$o]);
      free invariant $HeapSucc($PreLoopHeap$loop#0, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
        { read($Heap, $o, $f) } 
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
      free invariant i#0 <= $decr_init$loop#00 && (i#0 == $decr_init$loop#00 ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(21,4): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assume true;
            assume LitInt(0) <= i#0;
            assume true;
            assume false;
        }

        assume true;
        if (!Lit(true))
        {
            break;
        }

        $decr$loop#00 := i#0;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(25,9)
        assume true;
        assume true;
        i#0 := i#0 - 1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(25,16)"} true;
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(26,7)
        assume true;
        if (!(LitInt(0) <= i#0))
        {
            // ----- break statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(27,9)
            goto after_0;
        }
        else
        {
        }

        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(21,5)
        assert 0 <= $decr$loop#00 || i#0 == $decr$loop#00;
        assert i#0 < $decr$loop#00;
        assume true;
    }

  after_0:
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(30,5)
    assume true;
    assert i#0 == LitInt(-1);
}



procedure CheckWellformed$$_module.Termination.Lex(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Termination())
         && $IsAlloc(this, Tclass._module.Termination(), $Heap));
  free requires 20 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Termination.Lex(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Termination())
         && $IsAlloc(this, Tclass._module.Termination(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Termination.Lex(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Termination())
         && $IsAlloc(this, Tclass._module.Termination(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 20 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Termination.Lex(this: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var x#0: int;
  var $rhs##0: int;
  var y#0: int;
  var $rhs##1: int;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: int;
  var $decr_init$loop#01: int;
  var $w$loop#0: bool;
  var $decr$loop#00: int;
  var $decr$loop#01: int;
  var $rhs##0_0: int;

    // AddMethodImpl: Lex, Impl$$_module.Termination.Lex
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(33,15): initial state"} true;
    $_reverifyPost := false;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(34,20)
    assume true;
    // TrCallStmt: Adding lhs with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0 := Call$$_module.Termination.Update(this);
    // TrCallStmt: After ProcessCallStmt
    x#0 := $rhs##0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(34,21)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(35,20)
    assume true;
    // TrCallStmt: Adding lhs with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##1 := Call$$_module.Termination.Update(this);
    // TrCallStmt: After ProcessCallStmt
    y#0 := $rhs##1;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(35,21)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(36,5)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := x#0;
    $decr_init$loop#01 := y#0;
    havoc $w$loop#0;
    while (true)
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> LitInt(0) <= x#0;
      invariant $w$loop#0 ==> LitInt(0) <= y#0;
      free invariant (forall $o: ref :: 
        { $Heap[$o] } 
        $o != null && read(old($Heap), $o, alloc)
           ==> $Heap[$o] == $PreLoopHeap$loop#0[$o]);
      free invariant $HeapSucc($PreLoopHeap$loop#0, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
        { read($Heap, $o, $f) } 
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
      free invariant x#0 <= $decr_init$loop#00
         && (x#0 == $decr_init$loop#00
           ==> y#0 <= $decr_init$loop#01 && (y#0 == $decr_init$loop#01 ==> true));
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(36,4): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            if (LitInt(0) <= x#0)
            {
            }

            assume true;
            assume LitInt(0) <= x#0 && LitInt(0) <= y#0;
            assume true;
            assume true;
            assume false;
        }

        if (x#0 == LitInt(0))
        {
        }

        assume true;
        if (x#0 == LitInt(0) && y#0 == LitInt(0))
        {
            break;
        }

        $decr$loop#00 := x#0;
        $decr$loop#01 := y#0;
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(40,7)
        assume true;
        if (0 < y#0)
        {
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(41,11)
            assume true;
            assume true;
            y#0 := y#0 - 1;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(41,18)"} true;
        }
        else
        {
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(43,11)
            assume true;
            assume true;
            x#0 := x#0 - 1;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(43,18)"} true;
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(44,20)
            assume true;
            // TrCallStmt: Adding lhs with type int
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call $rhs##0_0 := Call$$_module.Termination.Update(this);
            // TrCallStmt: After ProcessCallStmt
            y#0 := $rhs##0_0;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(44,21)"} true;
        }

        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(36,5)
        assert 0 <= $decr$loop#00 || x#0 == $decr$loop#00;
        assert 0 <= $decr$loop#01 || x#0 < $decr$loop#00 || y#0 == $decr$loop#01;
        assert x#0 < $decr$loop#00 || (x#0 == $decr$loop#00 && y#0 < $decr$loop#01);
        assume true;
    }
}



procedure CheckWellformed$$_module.Termination.Update(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Termination())
         && $IsAlloc(this, Tclass._module.Termination(), $Heap))
   returns (r#0: int);
  free requires 19 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Termination.Update(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Termination())
         && $IsAlloc(this, Tclass._module.Termination(), $Heap))
   returns (r#0: int);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures LitInt(0) <= r#0;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Termination.Update(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Termination())
         && $IsAlloc(this, Tclass._module.Termination(), $Heap))
   returns (r#0: int, $_reverifyPost: bool);
  free requires 19 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures LitInt(0) <= r#0;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Termination.Update(this: ref) returns (r#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Update, Impl$$_module.Termination.Update
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(51,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(52,7)
    assume true;
    assume true;
    r#0 := LitInt(8);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(52,10)"} true;
}



procedure CheckWellformed$$_module.Termination.M(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Termination())
         && $IsAlloc(this, Tclass._module.Termination(), $Heap));
  free requires 22 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Termination.M(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Termination())
         && $IsAlloc(this, Tclass._module.Termination(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Termination.M(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Termination())
         && $IsAlloc(this, Tclass._module.Termination(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 22 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Termination.M(this: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b#0: bool;
  var i#0: int;
  var r#0: ref
     where $Is(r#0, Tclass._module.Termination?())
       && $IsAlloc(r#0, Tclass._module.Termination?(), $Heap);
  var $nw: ref;
  var s#0: Set Box where $Is(s#0, TSet(TInt)) && $IsAlloc(s#0, TSet(TInt), $Heap);
  var q#0: Seq Box where $Is(q#0, TSeq(TInt)) && $IsAlloc(q#0, TSeq(TInt), $Heap);
  var $Heap_at_0: Heap;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: bool;
  var $decr_init$loop#01: int;
  var $decr_init$loop#02: ref;
  var $decr_init$loop#03: Set Box;
  var $decr_init$loop#04: Seq Box;
  var $w$loop#0: bool;
  var $decr$loop#00: bool;
  var $decr$loop#01: int;
  var $decr$loop#02: ref;
  var $decr$loop#03: Set Box;
  var $decr$loop#04: Seq Box;

    // AddMethodImpl: M, Impl$$_module.Termination.M
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(55,13): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(56,11)
    assume true;
    assume true;
    b#0 := Lit(true);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(56,17)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(57,11)
    assume true;
    assume true;
    i#0 := LitInt(500);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(57,16)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(58,11)
    assume true;
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._module.Termination?();
    assume !read($Heap, $nw, alloc);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    r#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(58,28)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(59,11)
    assume true;
    assume true;
    s#0 := Lit(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(LitInt(12))), $Box(LitInt(200))));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(59,22)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(60,11)
    assume true;
    assume true;
    q#0 := Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(5))), $Box(LitInt(8))), 
        $Box(LitInt(13))));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(60,23)"} true;
    $Heap_at_0 := $Heap;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(61,5)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := b#0;
    $decr_init$loop#01 := i#0;
    $decr_init$loop#02 := r#0;
    $decr_init$loop#03 := s#0;
    $decr_init$loop#04 := q#0;
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
      free invariant (b#0 ==> $decr_init$loop#00)
         && ((b#0 <==> $decr_init$loop#00)
           ==> i#0 <= $decr_init$loop#01
             && (i#0 == $decr_init$loop#01
               ==> (r#0 != null ==> $decr_init$loop#02 != null)
                 && ((r#0 != null <==> $decr_init$loop#02 != null)
                   ==> Set#Subset(s#0, $decr_init$loop#03)
                     && (Set#Equal(s#0, $decr_init$loop#03)
                       ==> Seq#Rank(q#0) <= Seq#Rank($decr_init$loop#04)
                         && (Seq#Rank(q#0) == Seq#Rank($decr_init$loop#04) ==> true)))));
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(61,4): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assume true;
            assume true;
            assume true;
            assume true;
            assume true;
            assume false;
        }

        assume true;
        if (!Lit(true))
        {
            break;
        }

        $decr$loop#00 := b#0;
        $decr$loop#01 := i#0;
        $decr$loop#02 := r#0;
        $decr$loop#03 := s#0;
        $decr$loop#04 := q#0;
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(66,7)
        assume true;
        if (s#0[$Box(LitInt(12))])
        {
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(67,11)
            assume true;
            assume true;
            s#0 := Set#Difference(s#0, Set#UnionOne(Set#Empty(): Set Box, $Box(LitInt(12))));
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(67,21)"} true;
        }
        else
        {
            // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(68,14)
            assume true;
            if (b#0)
            {
                // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(69,11)
                assume true;
                assume true;
                b#0 := !b#0;
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(69,15)"} true;
                // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(70,11)
                assume true;
                assume true;
                i#0 := i#0 + 1;
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(70,18)"} true;
            }
            else
            {
                // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(71,14)
                assume true;
                if (LitInt(20) <= i#0)
                {
                    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(72,11)
                    assume true;
                    assume true;
                    i#0 := i#0 - 20;
                    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(72,19)"} true;
                }
                else
                {
                    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(73,14)
                    assume true;
                    if (r#0 != null)
                    {
                        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(74,11)
                        assume true;
                        assume true;
                        r#0 := null;
                        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(74,17)"} true;
                    }
                    else
                    {
                        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(75,14)
                        assume true;
                        if (Seq#Length(q#0) != 0)
                        {
                            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(76,11)
                            assume true;
                            assert 0 <= LitInt(1) && LitInt(1) <= Seq#Length(q#0);
                            assume true;
                            q#0 := Seq#Drop(q#0, LitInt(1));
                            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(76,19)"} true;
                        }
                        else
                        {
                            // ----- break statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(78,9)
                            goto after_0;
                        }
                    }
                }
            }
        }

        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(61,5)
        assert 0 <= $decr$loop#01 || (!b#0 && $decr$loop#00) || i#0 == $decr$loop#01;
        assert (!b#0 && $decr$loop#00)
           || ((b#0 <==> $decr$loop#00)
             && (i#0 < $decr$loop#01
               || (i#0 == $decr$loop#01
                 && ((r#0 == null && $decr$loop#02 != null)
                   || ((r#0 != null <==> $decr$loop#02 != null)
                     && ((Set#Subset(s#0, $decr$loop#03) && !Set#Subset($decr$loop#03, s#0))
                       || (Set#Equal(s#0, $decr$loop#03) && Seq#Rank(q#0) < Seq#Rank($decr$loop#04))))))));
    }

  after_0:
}



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

procedure CheckWellformed$$_module.Termination.Q(_module.Termination.Q$T: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Termination())
         && $IsAlloc(this, Tclass._module.Termination(), $Heap), 
    list#0: DatatypeType
       where $Is(list#0, Tclass._module.List(_module.Termination.Q$T))
         && $IsAlloc(list#0, Tclass._module.List(_module.Termination.Q$T), $Heap)
         && $IsA#_module.List(list#0));
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Termination.Q(_module.Termination.Q$T: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Termination())
         && $IsAlloc(this, Tclass._module.Termination(), $Heap), 
    list#0: DatatypeType
       where $Is(list#0, Tclass._module.List(_module.Termination.Q$T))
         && $IsAlloc(list#0, Tclass._module.List(_module.Termination.Q$T), $Heap)
         && $IsA#_module.List(list#0));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Termination.Q(_module.Termination.Q$T: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Termination())
         && $IsAlloc(this, Tclass._module.Termination(), $Heap), 
    list#0: DatatypeType
       where $Is(list#0, Tclass._module.List(_module.Termination.Q$T))
         && $IsAlloc(list#0, Tclass._module.List(_module.Termination.Q$T), $Heap)
         && $IsA#_module.List(list#0))
   returns ($_reverifyPost: bool);
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Termination.Q(_module.Termination.Q$T: Ty, this: ref, list#0: DatatypeType)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var l#0: DatatypeType
     where $Is(l#0, Tclass._module.List(_module.Termination.Q$T))
       && $IsAlloc(l#0, Tclass._module.List(_module.Termination.Q$T), $Heap);
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: DatatypeType;
  var $w$loop#0: bool;
  var $decr$loop#00: DatatypeType;
  var defass#x#0_0: bool;
  var x#0_0: Box
     where defass#x#0_0
       ==> $IsBox(x#0_0, _module.Termination.Q$T)
         && $IsAllocBox(x#0_0, _module.Termination.Q$T, $Heap);
  var $rhs##0_0: Box
     where $IsBox($rhs##0_0, _module.Termination.Q$T)
       && $IsAllocBox($rhs##0_0, _module.Termination.Q$T, $Heap);
  var $rhs##0_1: DatatypeType
     where $Is($rhs##0_1, Tclass._module.List(_module.Termination.Q$T))
       && $IsAlloc($rhs##0_1, Tclass._module.List(_module.Termination.Q$T), $Heap);
  var a##0_0: DatatypeType;

    // AddMethodImpl: Q, Impl$$_module.Termination.Q
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(83,29): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(84,11)
    assume true;
    assume true;
    l#0 := list#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(84,17)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(85,5)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := l#0;
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
      free invariant DtRank(l#0) <= DtRank($decr_init$loop#00)
         && (DtRank(l#0) == DtRank($decr_init$loop#00) ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(85,4): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assume true;
            assume false;
        }

        assume $IsA#_module.List(l#0);
        if (_module.List#Equal(l#0, #_module.List.Nil()))
        {
            break;
        }

        $decr$loop#00 := l#0;
        havoc x#0_0 /* where defass#x#0_0
           ==> $IsBox(x#0_0, _module.Termination.Q$T)
             && $IsAllocBox(x#0_0, _module.Termination.Q$T, $Heap) */;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(89,23)
        assume true;
        assume true;
        // TrCallStmt: Adding lhs with type T
        // TrCallStmt: Adding lhs with type List<T>
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        assume true;
        // ProcessCallStmt: CheckSubrange
        a##0_0 := l#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call $rhs##0_0, $rhs##0_1 := Call$$_module.Termination.Traverse(_module.Termination.Q$T, this, a##0_0);
        // TrCallStmt: After ProcessCallStmt
        x#0_0 := $rhs##0_0;
        defass#x#0_0 := true;
        l#0 := $rhs##0_1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(89,25)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(85,5)
        assert DtRank(l#0) < DtRank($decr$loop#00);
    }
}



procedure CheckWellformed$$_module.Termination.Traverse(_module.Termination.Traverse$T: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Termination())
         && $IsAlloc(this, Tclass._module.Termination(), $Heap), 
    a#0: DatatypeType
       where $Is(a#0, Tclass._module.List(_module.Termination.Traverse$T))
         && $IsAlloc(a#0, Tclass._module.List(_module.Termination.Traverse$T), $Heap)
         && $IsA#_module.List(a#0))
   returns (val#0: Box
       where $IsBox(val#0, _module.Termination.Traverse$T)
         && $IsAllocBox(val#0, _module.Termination.Traverse$T, $Heap), 
    b#0: DatatypeType
       where $Is(b#0, Tclass._module.List(_module.Termination.Traverse$T))
         && $IsAlloc(b#0, Tclass._module.List(_module.Termination.Traverse$T), $Heap));
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Termination.Traverse(_module.Termination.Traverse$T: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Termination())
         && $IsAlloc(this, Tclass._module.Termination(), $Heap), 
    a#0: DatatypeType
       where $Is(a#0, Tclass._module.List(_module.Termination.Traverse$T))
         && $IsAlloc(a#0, Tclass._module.List(_module.Termination.Traverse$T), $Heap)
         && $IsA#_module.List(a#0))
   returns (val#0: Box
       where $IsBox(val#0, _module.Termination.Traverse$T)
         && $IsAllocBox(val#0, _module.Termination.Traverse$T, $Heap), 
    b#0: DatatypeType
       where $Is(b#0, Tclass._module.List(_module.Termination.Traverse$T))
         && $IsAlloc(b#0, Tclass._module.List(_module.Termination.Traverse$T), $Heap));
  // user-defined preconditions
  requires !_module.List#Equal(a#0, #_module.List.Nil());
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.List(a#0);
  ensures _module.List#Equal(a#0, #_module.List.Cons(val#0, b#0));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Termination.Traverse(_module.Termination.Traverse$T: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Termination())
         && $IsAlloc(this, Tclass._module.Termination(), $Heap), 
    a#0: DatatypeType
       where $Is(a#0, Tclass._module.List(_module.Termination.Traverse$T))
         && $IsAlloc(a#0, Tclass._module.List(_module.Termination.Traverse$T), $Heap)
         && $IsA#_module.List(a#0))
   returns (defass#val#0: bool, 
    val#0: Box
       where defass#val#0
         ==> $IsBox(val#0, _module.Termination.Traverse$T)
           && $IsAllocBox(val#0, _module.Termination.Traverse$T, $Heap), 
    b#0: DatatypeType
       where $Is(b#0, Tclass._module.List(_module.Termination.Traverse$T))
         && $IsAlloc(b#0, Tclass._module.List(_module.Termination.Traverse$T), $Heap), 
    $_reverifyPost: bool);
  free requires 1 == $FunctionContextHeight;
  // user-defined preconditions
  requires !_module.List#Equal(a#0, #_module.List.Nil());
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.List(a#0);
  ensures _module.List#Equal(a#0, #_module.List.Cons(val#0, b#0));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Termination.Traverse(_module.Termination.Traverse$T: Ty, this: ref, a#0: DatatypeType)
   returns (defass#val#0: bool, val#0: Box, b#0: DatatypeType, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0_0: Box;
  var _mcc#1#0_0: DatatypeType;
  var r#0_0: DatatypeType;
  var let#0_0#0#0: DatatypeType;
  var v#0_0: Box;
  var let#0_1#0#0: Box;

    // AddMethodImpl: Traverse, Impl$$_module.Termination.Traverse
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(96,2): initial state"} true;
    $_reverifyPost := false;
    assume true;
    havoc _mcc#0#0_0, _mcc#1#0_0;
    if (a#0 == #_module.List.Cons(_mcc#0#0_0, _mcc#1#0_0))
    {
        assume $IsBox(_mcc#0#0_0, _module.Termination.Traverse$T)
           && $IsAllocBox(_mcc#0#0_0, _module.Termination.Traverse$T, $Heap);
        assume $Is(_mcc#1#0_0, Tclass._module.List(_module.Termination.Traverse$T))
           && $IsAlloc(_mcc#1#0_0, Tclass._module.List(_module.Termination.Traverse$T), $Heap);
        havoc r#0_0;
        assume $Is(r#0_0, Tclass._module.List(_module.Termination.Traverse$T))
           && $IsAlloc(r#0_0, Tclass._module.List(_module.Termination.Traverse$T), $Heap);
        assume let#0_0#0#0 == _mcc#1#0_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_0#0#0, Tclass._module.List(_module.Termination.Traverse$T));
        assume r#0_0 == let#0_0#0#0;
        havoc v#0_0;
        assume $IsBox(v#0_0, _module.Termination.Traverse$T)
           && $IsAllocBox(v#0_0, _module.Termination.Traverse$T, $Heap);
        assume let#0_1#0#0 == _mcc#0#0_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $IsBox(let#0_1#0#0, _module.Termination.Traverse$T);
        assume v#0_0 == let#0_1#0#0;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(98,30)
        assume true;
        assume true;
        val#0 := v#0_0;
        defass#val#0 := true;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(98,33)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(98,38)
        assume true;
        assume true;
        b#0 := r#0_0;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(98,41)"} true;
    }
    else if (a#0 == #_module.List.Nil())
    {
        assert false;
    }
    else
    {
        assume false;
    }

    assert defass#val#0;
}



// _module.Termination: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.Termination()) } 
  $Is(c#0, Tclass._module.Termination())
     <==> $Is(c#0, Tclass._module.Termination?()) && c#0 != null);

// _module.Termination: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.Termination(), $h) } 
  $IsAlloc(c#0, Tclass._module.Termination(), $h)
     <==> $IsAlloc(c#0, Tclass._module.Termination?(), $h));

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
axiom (forall a#5#0#0: Box, a#5#1#0: DatatypeType :: 
  { #_module.List.Cons(a#5#0#0, a#5#1#0) } 
  DatatypeCtorId(#_module.List.Cons(a#5#0#0, a#5#1#0)) == ##_module.List.Cons);

function _module.List.Cons_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.List.Cons_q(d) } 
  _module.List.Cons_q(d) <==> DatatypeCtorId(d) == ##_module.List.Cons);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.List.Cons_q(d) } 
  _module.List.Cons_q(d)
     ==> (exists a#6#0#0: Box, a#6#1#0: DatatypeType :: 
      d == #_module.List.Cons(a#6#0#0, a#6#1#0)));

// Constructor $Is
axiom (forall _module.List$T: Ty, a#7#0#0: Box, a#7#1#0: DatatypeType :: 
  { $Is(#_module.List.Cons(a#7#0#0, a#7#1#0), Tclass._module.List(_module.List$T)) } 
  $Is(#_module.List.Cons(a#7#0#0, a#7#1#0), Tclass._module.List(_module.List$T))
     <==> $IsBox(a#7#0#0, _module.List$T)
       && $Is(a#7#1#0, Tclass._module.List(_module.List$T)));

// Constructor $IsAlloc
axiom (forall _module.List$T: Ty, a#8#0#0: Box, a#8#1#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#_module.List.Cons(a#8#0#0, a#8#1#0), Tclass._module.List(_module.List$T), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.List.Cons(a#8#0#0, a#8#1#0), Tclass._module.List(_module.List$T), $h)
       <==> $IsAllocBox(a#8#0#0, _module.List$T, $h)
         && $IsAlloc(a#8#1#0, Tclass._module.List(_module.List$T), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _module.List$T: Ty, $h: Heap :: 
  { $IsAllocBox(_module.List._h0(d), _module.List$T, $h) } 
  $IsGoodHeap($h)
       && 
      _module.List.Cons_q(d)
       && $IsAlloc(d, Tclass._module.List(_module.List$T), $h)
     ==> $IsAllocBox(_module.List._h0(d), _module.List$T, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _module.List$T: Ty, $h: Heap :: 
  { $IsAlloc(_module.List._h1(d), Tclass._module.List(_module.List$T), $h) } 
  $IsGoodHeap($h)
       && 
      _module.List.Cons_q(d)
       && $IsAlloc(d, Tclass._module.List(_module.List$T), $h)
     ==> $IsAlloc(_module.List._h1(d), Tclass._module.List(_module.List$T), $h));

// Constructor literal
axiom (forall a#9#0#0: Box, a#9#1#0: DatatypeType :: 
  { #_module.List.Cons(Lit(a#9#0#0), Lit(a#9#1#0)) } 
  #_module.List.Cons(Lit(a#9#0#0), Lit(a#9#1#0))
     == Lit(#_module.List.Cons(a#9#0#0, a#9#1#0)));

function _module.List._h0(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#10#0#0: Box, a#10#1#0: DatatypeType :: 
  { #_module.List.Cons(a#10#0#0, a#10#1#0) } 
  _module.List._h0(#_module.List.Cons(a#10#0#0, a#10#1#0)) == a#10#0#0);

// Inductive rank
axiom (forall a#11#0#0: Box, a#11#1#0: DatatypeType :: 
  { #_module.List.Cons(a#11#0#0, a#11#1#0) } 
  BoxRank(a#11#0#0) < DtRank(#_module.List.Cons(a#11#0#0, a#11#1#0)));

function _module.List._h1(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#12#0#0: Box, a#12#1#0: DatatypeType :: 
  { #_module.List.Cons(a#12#0#0, a#12#1#0) } 
  _module.List._h1(#_module.List.Cons(a#12#0#0, a#12#1#0)) == a#12#1#0);

// Inductive rank
axiom (forall a#13#0#0: Box, a#13#1#0: DatatypeType :: 
  { #_module.List.Cons(a#13#0#0, a#13#1#0) } 
  DtRank(a#13#1#0) < DtRank(#_module.List.Cons(a#13#0#0, a#13#1#0)));

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
       <==> _module.List._h0(a) == _module.List._h0(b)
         && _module.List#Equal(_module.List._h1(a), _module.List._h1(b))));

// Datatype extensionality axiom: _module.List
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.List#Equal(a, b) } 
  _module.List#Equal(a, b) <==> a == b);

const unique class._module.List: ClassName;

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

axiom FDim(_module.Node.next) == 0
   && FieldOfDecl(class._module.Node?, field$next) == _module.Node.next
   && !$IsGhostField(_module.Node.next);

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

axiom FDim(_module.Node.footprint) == 0
   && FieldOfDecl(class._module.Node?, field$footprint) == _module.Node.footprint
   && !$IsGhostField(_module.Node.footprint);

const _module.Node.footprint: Field (Set Box);

// Node.footprint: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Node.footprint) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Node?()
     ==> $Is(read($h, $o, _module.Node.footprint), TSet(Tclass._module.Node?())));

// Node.footprint: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Node.footprint) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Node?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Node.footprint), TSet(Tclass._module.Node?()), $h));

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
      $o != null && ($o == this || read($h0, this, _module.Node.footprint)[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.Node.Valid($ly, $h0, this) == _module.Node.Valid($ly, $h1, this));

// consequence axiom for _module.Node.Valid
axiom 23 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, this: ref :: 
    { _module.Node.Valid($ly, $Heap, this) } 
    _module.Node.Valid#canCall($Heap, this)
         || (23 != $FunctionContextHeight
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

// definition axiom for _module.Node.Valid (revealed)
axiom 23 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, this: ref :: 
    { _module.Node.Valid($LS($ly), $Heap, this), $IsGoodHeap($Heap) } 
    _module.Node.Valid#canCall($Heap, this)
         || (23 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.Node())
           && $IsAlloc(this, Tclass._module.Node(), $Heap))
       ==> (read($Heap, this, _module.Node.footprint)[$Box(this)]
           ==> 
          !read($Heap, this, _module.Node.footprint)[$Box(null)]
           ==> 
          read($Heap, this, _module.Node.next) != null
           ==> 
          read($Heap, this, _module.Node.footprint)[$Box(read($Heap, this, _module.Node.next))]
           ==> 
          Set#Subset(read($Heap, read($Heap, this, _module.Node.next), _module.Node.footprint), 
              read($Heap, this, _module.Node.footprint))
             && !Set#Subset(read($Heap, this, _module.Node.footprint), 
              read($Heap, read($Heap, this, _module.Node.next), _module.Node.footprint))
           ==> 
          !read($Heap, read($Heap, this, _module.Node.next), _module.Node.footprint)[$Box(this)]
           ==> _module.Node.Valid#canCall($Heap, read($Heap, this, _module.Node.next)))
         && _module.Node.Valid($LS($ly), $Heap, this)
           == (
            read($Heap, this, _module.Node.footprint)[$Box(this)]
             && !read($Heap, this, _module.Node.footprint)[$Box(null)]
             && (read($Heap, this, _module.Node.next) != null
               ==> read($Heap, this, _module.Node.footprint)[$Box(read($Heap, this, _module.Node.next))]
                 && 
                Set#Subset(read($Heap, read($Heap, this, _module.Node.next), _module.Node.footprint), 
                  read($Heap, this, _module.Node.footprint))
                 && !Set#Subset(read($Heap, this, _module.Node.footprint), 
                  read($Heap, read($Heap, this, _module.Node.next), _module.Node.footprint))
                 && !read($Heap, read($Heap, this, _module.Node.next), _module.Node.footprint)[$Box(this)]
                 && _module.Node.Valid($ly, $Heap, read($Heap, this, _module.Node.next)))));

procedure CheckWellformed$$_module.Node.Valid(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), $Heap));
  free requires 23 == $FunctionContextHeight;
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
  var b$reqreads#12: bool;

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

    // AddWellformednessCheck for function Valid
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(165,11): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> $o == this || read($Heap, this, _module.Node.footprint)[$Box($o)]);
    b$reqreads#0 := $_Frame[this, _module.Node.footprint];
    assert b$reqreads#0;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc)
             ==> $o == this || read($Heap, this, _module.Node.footprint)[$Box($o)]);
        b$reqreads#1 := $_Frame[this, _module.Node.footprint];
        if (read($Heap, this, _module.Node.footprint)[$Box(this)])
        {
            b$reqreads#2 := $_Frame[this, _module.Node.footprint];
        }

        if (read($Heap, this, _module.Node.footprint)[$Box(this)]
           && !read($Heap, this, _module.Node.footprint)[$Box(null)])
        {
            b$reqreads#3 := $_Frame[this, _module.Node.next];
            if (read($Heap, this, _module.Node.next) != null)
            {
                b$reqreads#4 := $_Frame[this, _module.Node.next];
                b$reqreads#5 := $_Frame[this, _module.Node.footprint];
                if (read($Heap, this, _module.Node.footprint)[$Box(read($Heap, this, _module.Node.next))])
                {
                    b$reqreads#6 := $_Frame[this, _module.Node.next];
                    assert read($Heap, this, _module.Node.next) != null;
                    b$reqreads#7 := $_Frame[read($Heap, this, _module.Node.next), _module.Node.footprint];
                    b$reqreads#8 := $_Frame[this, _module.Node.footprint];
                }

                if (read($Heap, this, _module.Node.footprint)[$Box(read($Heap, this, _module.Node.next))]
                   && 
                  Set#Subset(read($Heap, read($Heap, this, _module.Node.next), _module.Node.footprint), 
                    read($Heap, this, _module.Node.footprint))
                   && !Set#Subset(read($Heap, this, _module.Node.footprint), 
                    read($Heap, read($Heap, this, _module.Node.next), _module.Node.footprint)))
                {
                    b$reqreads#9 := $_Frame[this, _module.Node.next];
                    assert read($Heap, this, _module.Node.next) != null;
                    b$reqreads#10 := $_Frame[read($Heap, this, _module.Node.next), _module.Node.footprint];
                }

                if (read($Heap, this, _module.Node.footprint)[$Box(read($Heap, this, _module.Node.next))]
                   && 
                  Set#Subset(read($Heap, read($Heap, this, _module.Node.next), _module.Node.footprint), 
                    read($Heap, this, _module.Node.footprint))
                   && !Set#Subset(read($Heap, this, _module.Node.footprint), 
                    read($Heap, read($Heap, this, _module.Node.next), _module.Node.footprint))
                   && !read($Heap, read($Heap, this, _module.Node.next), _module.Node.footprint)[$Box(this)])
                {
                    b$reqreads#11 := $_Frame[this, _module.Node.next];
                    assert read($Heap, this, _module.Node.next) != null;
                    b$reqreads#12 := (forall<alpha> $o: ref, $f: Field alpha :: 
                      $o != null
                           && read($Heap, $o, alloc)
                           && ($o == read($Heap, this, _module.Node.next)
                             || read($Heap, read($Heap, this, _module.Node.next), _module.Node.footprint)[$Box($o)])
                         ==> $_Frame[$o, $f]);
                    assert Set#Subset(Set#Union(read($Heap, read($Heap, this, _module.Node.next), _module.Node.footprint), 
                          Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.next)))), 
                        Set#Union(read($Heap, this, _module.Node.footprint), 
                          Set#UnionOne(Set#Empty(): Set Box, $Box(this))))
                       && !Set#Subset(Set#Union(read($Heap, this, _module.Node.footprint), 
                          Set#UnionOne(Set#Empty(): Set Box, $Box(this))), 
                        Set#Union(read($Heap, read($Heap, this, _module.Node.next), _module.Node.footprint), 
                          Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.next)))));
                    assume _module.Node.Valid#canCall($Heap, read($Heap, this, _module.Node.next));
                }
            }
        }

        assume _module.Node.Valid($LS($LZ), $Heap, this)
           == (
            read($Heap, this, _module.Node.footprint)[$Box(this)]
             && !read($Heap, this, _module.Node.footprint)[$Box(null)]
             && (read($Heap, this, _module.Node.next) != null
               ==> read($Heap, this, _module.Node.footprint)[$Box(read($Heap, this, _module.Node.next))]
                 && 
                Set#Subset(read($Heap, read($Heap, this, _module.Node.next), _module.Node.footprint), 
                  read($Heap, this, _module.Node.footprint))
                 && !Set#Subset(read($Heap, this, _module.Node.footprint), 
                  read($Heap, read($Heap, this, _module.Node.next), _module.Node.footprint))
                 && !read($Heap, read($Heap, this, _module.Node.next), _module.Node.footprint)[$Box(this)]
                 && _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.next))));
        assume read($Heap, this, _module.Node.footprint)[$Box(this)]
           ==> 
          !read($Heap, this, _module.Node.footprint)[$Box(null)]
           ==> 
          read($Heap, this, _module.Node.next) != null
           ==> 
          read($Heap, this, _module.Node.footprint)[$Box(read($Heap, this, _module.Node.next))]
           ==> 
          Set#Subset(read($Heap, read($Heap, this, _module.Node.next), _module.Node.footprint), 
              read($Heap, this, _module.Node.footprint))
             && !Set#Subset(read($Heap, this, _module.Node.footprint), 
              read($Heap, read($Heap, this, _module.Node.next), _module.Node.footprint))
           ==> 
          !read($Heap, read($Heap, this, _module.Node.next), _module.Node.footprint)[$Box(this)]
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
        assert b$reqreads#12;
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

const unique class._module.TopElements?: ClassName;

function Tclass._module.TopElements?() : Ty;

const unique Tagclass._module.TopElements?: TyTag;

// Tclass._module.TopElements? Tag
axiom Tag(Tclass._module.TopElements?()) == Tagclass._module.TopElements?
   && TagFamily(Tclass._module.TopElements?()) == tytagFamily$TopElements;

// Box/unbox axiom for Tclass._module.TopElements?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.TopElements?()) } 
  $IsBox(bx, Tclass._module.TopElements?())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.TopElements?()));

// TopElements: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.TopElements?()) } 
  $Is($o, Tclass._module.TopElements?())
     <==> $o == null || dtype($o) == Tclass._module.TopElements?());

// TopElements: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.TopElements?(), $h) } 
  $IsAlloc($o, Tclass._module.TopElements?(), $h)
     <==> $o == null || read($h, $o, alloc));

axiom FDim(_module.TopElements.count) == 0
   && FieldOfDecl(class._module.TopElements?, field$count)
     == _module.TopElements.count
   && !$IsGhostField(_module.TopElements.count);

const _module.TopElements.count: Field int;

// TopElements.count: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.TopElements.count) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.TopElements?()
     ==> $Is(read($h, $o, _module.TopElements.count), TInt));

// TopElements.count: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.TopElements.count) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.TopElements?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.TopElements.count), TInt, $h));

function Tclass._module.TopElements() : Ty;

const unique Tagclass._module.TopElements: TyTag;

// Tclass._module.TopElements Tag
axiom Tag(Tclass._module.TopElements()) == Tagclass._module.TopElements
   && TagFamily(Tclass._module.TopElements()) == tytagFamily$TopElements;

// Box/unbox axiom for Tclass._module.TopElements
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.TopElements()) } 
  $IsBox(bx, Tclass._module.TopElements())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.TopElements()));

procedure CheckWellformed$$_module.TopElements.OuterOld(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.TopElements())
         && $IsAlloc(this, Tclass._module.TopElements(), $Heap), 
    a#0: int);
  free requires 24 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.TopElements.OuterOld(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.TopElements())
         && $IsAlloc(this, Tclass._module.TopElements(), $Heap), 
    a#0: int);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.TopElements.OuterOld(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.TopElements())
         && $IsAlloc(this, Tclass._module.TopElements(), $Heap), 
    a#0: int)
   returns ($_reverifyPost: bool);
  free requires 24 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.TopElements.OuterOld(this: ref, a#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: int;
  var a##0: int;
  var b##0: int;

    // AddMethodImpl: OuterOld, Impl$$_module.TopElements.OuterOld
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(212,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(213,11)
    assume true;
    assert $_Frame[this, _module.TopElements.count];
    assume true;
    $rhs#0 := read($Heap, this, _module.TopElements.count) + 1;
    $Heap := update($Heap, this, _module.TopElements.count, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(213,22)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(214,13)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##0 := a#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    b##0 := read($Heap, this, _module.TopElements.count);
    assert (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) && $o == this ==> $_Frame[$o, $f]);
    assert 0 <= a#0 || a##0 == a#0;
    assert a##0 <= a#0
       && (a##0 == a#0
         ==> (Lit(false) ==> Lit(true)) && ((Lit(false) <==> Lit(true)) ==> true));
    // ProcessCallStmt: Make the call
    call Call$$_module.TopElements.InnerOld(this, a##0, b##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(214,22)"} true;
}



procedure CheckWellformed$$_module.TopElements.InnerOld(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.TopElements())
         && $IsAlloc(this, Tclass._module.TopElements(), $Heap), 
    a#0: int, 
    b#0: int);
  free requires 24 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.TopElements.InnerOld(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.TopElements())
         && $IsAlloc(this, Tclass._module.TopElements(), $Heap), 
    a#0: int, 
    b#0: int);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.TopElements.InnerOld(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.TopElements())
         && $IsAlloc(this, Tclass._module.TopElements(), $Heap), 
    a#0: int, 
    b#0: int)
   returns ($_reverifyPost: bool);
  free requires 24 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.TopElements.InnerOld(this: ref, a#0: int, b#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: int;
  var a##0_0: int;
  var a##1_0: int;
  var b##1_0: int;

    // AddMethodImpl: InnerOld, Impl$$_module.TopElements.InnerOld
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(220,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(221,11)
    assume true;
    assert $_Frame[this, _module.TopElements.count];
    assume true;
    $rhs#0 := read($Heap, this, _module.TopElements.count) + 1;
    $Heap := update($Heap, this, _module.TopElements.count, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(221,22)"} true;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(222,5)
    if (b#0 == LitInt(0))
    {
    }

    assume true;
    if (b#0 == LitInt(0) && LitInt(1) <= a#0)
    {
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(223,15)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        assume true;
        // ProcessCallStmt: CheckSubrange
        a##0_0 := a#0 - 1;
        assert (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) && $o == this ==> $_Frame[$o, $f]);
        assert 0 <= a#0 || a##0_0 == a#0;
        assert a##0_0 < a#0 || (a##0_0 == a#0 && !Lit(true) && Lit(false));
        // ProcessCallStmt: Make the call
        call Call$$_module.TopElements.OuterOld(this, a##0_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(223,21)"} true;
    }
    else
    {
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(224,12)
        assume true;
        if (LitInt(1) <= b#0)
        {
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(225,15)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            assume true;
            // ProcessCallStmt: CheckSubrange
            a##1_0 := a#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            b##1_0 := b#0 - 1;
            assert (forall<alpha> $o: ref, $f: Field alpha :: 
              $o != null && read($Heap, $o, alloc) && $o == this ==> $_Frame[$o, $f]);
            assert 0 <= a#0 || a##1_0 == a#0;
            assert 0 <= b#0 || a##1_0 < a#0 || (!Lit(false) && Lit(false)) || b##1_0 == b#0;
            assert a##1_0 < a#0
               || (a##1_0 == a#0
                 && ((!Lit(false) && Lit(false)) || ((Lit(false) <==> Lit(false)) && b##1_0 < b#0)));
            // ProcessCallStmt: Make the call
            call Call$$_module.TopElements.InnerOld(this, a##1_0, b##1_0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(225,24)"} true;
        }
        else
        {
        }
    }
}



procedure CheckWellformed$$_module.TopElements.Outer(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.TopElements())
         && $IsAlloc(this, Tclass._module.TopElements(), $Heap), 
    a#0: int);
  free requires 25 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.TopElements.Outer(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.TopElements())
         && $IsAlloc(this, Tclass._module.TopElements(), $Heap), 
    a#0: int);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.TopElements.Outer(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.TopElements())
         && $IsAlloc(this, Tclass._module.TopElements(), $Heap), 
    a#0: int)
   returns ($_reverifyPost: bool);
  free requires 25 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.TopElements.Outer(this: ref, a#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: int;
  var a##0: int;
  var b##0: int;

    // AddMethodImpl: Outer, Impl$$_module.TopElements.Outer
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(233,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(234,11)
    assume true;
    assert $_Frame[this, _module.TopElements.count];
    assume true;
    $rhs#0 := read($Heap, this, _module.TopElements.count) + 1;
    $Heap := update($Heap, this, _module.TopElements.count, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(234,22)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(235,10)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##0 := a#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    b##0 := read($Heap, this, _module.TopElements.count);
    assert (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) && $o == this ==> $_Frame[$o, $f]);
    assert 0 <= a#0 || a##0 == a#0;
    assert a##0 <= a#0 && (a##0 == a#0 ==> true);
    // ProcessCallStmt: Make the call
    call Call$$_module.TopElements.Inner(this, a##0, b##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(235,19)"} true;
}



procedure CheckWellformed$$_module.TopElements.Inner(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.TopElements())
         && $IsAlloc(this, Tclass._module.TopElements(), $Heap), 
    a#0: int, 
    b#0: int);
  free requires 25 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.TopElements.Inner(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.TopElements())
         && $IsAlloc(this, Tclass._module.TopElements(), $Heap), 
    a#0: int, 
    b#0: int);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.TopElements.Inner(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.TopElements())
         && $IsAlloc(this, Tclass._module.TopElements(), $Heap), 
    a#0: int, 
    b#0: int)
   returns ($_reverifyPost: bool);
  free requires 25 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.TopElements.Inner(this: ref, a#0: int, b#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: int;
  var a##0_0: int;
  var a##1_0: int;
  var b##1_0: int;

    // AddMethodImpl: Inner, Impl$$_module.TopElements.Inner
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(240,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(241,11)
    assume true;
    assert $_Frame[this, _module.TopElements.count];
    assume true;
    $rhs#0 := read($Heap, this, _module.TopElements.count) + 1;
    $Heap := update($Heap, this, _module.TopElements.count, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(241,22)"} true;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(242,5)
    if (b#0 == LitInt(0))
    {
    }

    assume true;
    if (b#0 == LitInt(0) && LitInt(1) <= a#0)
    {
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(243,12)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        assume true;
        // ProcessCallStmt: CheckSubrange
        a##0_0 := a#0 - 1;
        assert (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) && $o == this ==> $_Frame[$o, $f]);
        assert 0 <= a#0 || a##0_0 == a#0;
        assert a##0_0 < a#0;
        // ProcessCallStmt: Make the call
        call Call$$_module.TopElements.Outer(this, a##0_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(243,18)"} true;
    }
    else
    {
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(244,12)
        assume true;
        if (LitInt(1) <= b#0)
        {
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(245,12)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            assume true;
            // ProcessCallStmt: CheckSubrange
            a##1_0 := a#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            b##1_0 := b#0 - 1;
            assert (forall<alpha> $o: ref, $f: Field alpha :: 
              $o != null && read($Heap, $o, alloc) && $o == this ==> $_Frame[$o, $f]);
            assert 0 <= a#0 || a##1_0 == a#0;
            assert 0 <= b#0 || a##1_0 < a#0 || b##1_0 == b#0;
            assert a##1_0 < a#0 || (a##1_0 == a#0 && b##1_0 < b#0);
            // ProcessCallStmt: Make the call
            call Call$$_module.TopElements.Inner(this, a##1_0, b##1_0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(245,21)"} true;
        }
        else
        {
        }
    }
}



// _module.TopElements: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.TopElements()) } 
  $Is(c#0, Tclass._module.TopElements())
     <==> $Is(c#0, Tclass._module.TopElements?()) && c#0 != null);

// _module.TopElements: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.TopElements(), $h) } 
  $IsAlloc(c#0, Tclass._module.TopElements(), $h)
     <==> $IsAlloc(c#0, Tclass._module.TopElements?(), $h));

const unique class._module.DefaultDecreasesFunction?: ClassName;

function Tclass._module.DefaultDecreasesFunction?() : Ty;

const unique Tagclass._module.DefaultDecreasesFunction?: TyTag;

// Tclass._module.DefaultDecreasesFunction? Tag
axiom Tag(Tclass._module.DefaultDecreasesFunction?())
     == Tagclass._module.DefaultDecreasesFunction?
   && TagFamily(Tclass._module.DefaultDecreasesFunction?())
     == tytagFamily$DefaultDecreasesFunction;

// Box/unbox axiom for Tclass._module.DefaultDecreasesFunction?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.DefaultDecreasesFunction?()) } 
  $IsBox(bx, Tclass._module.DefaultDecreasesFunction?())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.DefaultDecreasesFunction?()));

// DefaultDecreasesFunction: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.DefaultDecreasesFunction?()) } 
  $Is($o, Tclass._module.DefaultDecreasesFunction?())
     <==> $o == null || dtype($o) == Tclass._module.DefaultDecreasesFunction?());

// DefaultDecreasesFunction: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.DefaultDecreasesFunction?(), $h) } 
  $IsAlloc($o, Tclass._module.DefaultDecreasesFunction?(), $h)
     <==> $o == null || read($h, $o, alloc));

axiom FDim(_module.DefaultDecreasesFunction.data) == 0
   && FieldOfDecl(class._module.DefaultDecreasesFunction?, field$data)
     == _module.DefaultDecreasesFunction.data
   && !$IsGhostField(_module.DefaultDecreasesFunction.data);

const _module.DefaultDecreasesFunction.data: Field int;

// DefaultDecreasesFunction.data: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.DefaultDecreasesFunction.data) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.DefaultDecreasesFunction?()
     ==> $Is(read($h, $o, _module.DefaultDecreasesFunction.data), TInt));

// DefaultDecreasesFunction.data: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.DefaultDecreasesFunction.data) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.DefaultDecreasesFunction?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.DefaultDecreasesFunction.data), TInt, $h));

axiom FDim(_module.DefaultDecreasesFunction.Repr) == 0
   && FieldOfDecl(class._module.DefaultDecreasesFunction?, field$Repr)
     == _module.DefaultDecreasesFunction.Repr
   && $IsGhostField(_module.DefaultDecreasesFunction.Repr);

const _module.DefaultDecreasesFunction.Repr: Field (Set Box);

// DefaultDecreasesFunction.Repr: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.DefaultDecreasesFunction.Repr) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.DefaultDecreasesFunction?()
     ==> $Is(read($h, $o, _module.DefaultDecreasesFunction.Repr), 
      TSet(Tclass._System.object?())));

// DefaultDecreasesFunction.Repr: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.DefaultDecreasesFunction.Repr) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.DefaultDecreasesFunction?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.DefaultDecreasesFunction.Repr), 
      TSet(Tclass._System.object?()), 
      $h));

axiom FDim(_module.DefaultDecreasesFunction.next) == 0
   && FieldOfDecl(class._module.DefaultDecreasesFunction?, field$next)
     == _module.DefaultDecreasesFunction.next
   && !$IsGhostField(_module.DefaultDecreasesFunction.next);

const _module.DefaultDecreasesFunction.next: Field ref;

// DefaultDecreasesFunction.next: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.DefaultDecreasesFunction.next) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.DefaultDecreasesFunction?()
     ==> $Is(read($h, $o, _module.DefaultDecreasesFunction.next), 
      Tclass._module.DefaultDecreasesFunction?()));

// DefaultDecreasesFunction.next: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.DefaultDecreasesFunction.next) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.DefaultDecreasesFunction?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.DefaultDecreasesFunction.next), 
      Tclass._module.DefaultDecreasesFunction?(), 
      $h));

// function declaration for _module.DefaultDecreasesFunction.Valid
function _module.DefaultDecreasesFunction.Valid($ly: LayerType, $heap: Heap, this: ref) : bool;

function _module.DefaultDecreasesFunction.Valid#canCall($heap: Heap, this: ref) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, $Heap: Heap, this: ref :: 
  { _module.DefaultDecreasesFunction.Valid($LS($ly), $Heap, this) } 
  _module.DefaultDecreasesFunction.Valid($LS($ly), $Heap, this)
     == _module.DefaultDecreasesFunction.Valid($ly, $Heap, this));

// fuel synonym axiom
axiom (forall $ly: LayerType, $Heap: Heap, this: ref :: 
  { _module.DefaultDecreasesFunction.Valid(AsFuelBottom($ly), $Heap, this) } 
  _module.DefaultDecreasesFunction.Valid($ly, $Heap, this)
     == _module.DefaultDecreasesFunction.Valid($LZ, $Heap, this));

function Tclass._module.DefaultDecreasesFunction() : Ty;

const unique Tagclass._module.DefaultDecreasesFunction: TyTag;

// Tclass._module.DefaultDecreasesFunction Tag
axiom Tag(Tclass._module.DefaultDecreasesFunction())
     == Tagclass._module.DefaultDecreasesFunction
   && TagFamily(Tclass._module.DefaultDecreasesFunction())
     == tytagFamily$DefaultDecreasesFunction;

// Box/unbox axiom for Tclass._module.DefaultDecreasesFunction
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.DefaultDecreasesFunction()) } 
  $IsBox(bx, Tclass._module.DefaultDecreasesFunction())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.DefaultDecreasesFunction()));

// frame axiom for _module.DefaultDecreasesFunction.Valid
axiom (forall $ly: LayerType, $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.DefaultDecreasesFunction.Valid($ly, $h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.DefaultDecreasesFunction())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && ($o == this || read($h0, this, _module.DefaultDecreasesFunction.Repr)[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.DefaultDecreasesFunction.Valid($ly, $h0, this)
       == _module.DefaultDecreasesFunction.Valid($ly, $h1, this));

// consequence axiom for _module.DefaultDecreasesFunction.Valid
axiom 26 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, this: ref :: 
    { _module.DefaultDecreasesFunction.Valid($ly, $Heap, this) } 
    _module.DefaultDecreasesFunction.Valid#canCall($Heap, this)
         || (26 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.DefaultDecreasesFunction())
           && $IsAlloc(this, Tclass._module.DefaultDecreasesFunction(), $Heap))
       ==> true);

function _module.DefaultDecreasesFunction.Valid#requires(LayerType, Heap, ref) : bool;

// #requires axiom for _module.DefaultDecreasesFunction.Valid
axiom (forall $ly: LayerType, $Heap: Heap, this: ref :: 
  { _module.DefaultDecreasesFunction.Valid#requires($ly, $Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.DefaultDecreasesFunction())
       && $IsAlloc(this, Tclass._module.DefaultDecreasesFunction(), $Heap)
     ==> _module.DefaultDecreasesFunction.Valid#requires($ly, $Heap, this) == true);

// definition axiom for _module.DefaultDecreasesFunction.Valid (revealed)
axiom 26 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, this: ref :: 
    { _module.DefaultDecreasesFunction.Valid($LS($ly), $Heap, this), $IsGoodHeap($Heap) } 
    _module.DefaultDecreasesFunction.Valid#canCall($Heap, this)
         || (26 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.DefaultDecreasesFunction())
           && $IsAlloc(this, Tclass._module.DefaultDecreasesFunction(), $Heap))
       ==> (read($Heap, this, _module.DefaultDecreasesFunction.Repr)[$Box(this)]
           ==> 
          !read($Heap, this, _module.DefaultDecreasesFunction.Repr)[$Box(null)]
           ==> 
          read($Heap, this, _module.DefaultDecreasesFunction.next) != null
           ==> 
          read($Heap, this, _module.DefaultDecreasesFunction.Repr)[$Box(read($Heap, this, _module.DefaultDecreasesFunction.next))]
           ==> 
          Set#Subset(read($Heap, 
              read($Heap, this, _module.DefaultDecreasesFunction.next), 
              _module.DefaultDecreasesFunction.Repr), 
            read($Heap, this, _module.DefaultDecreasesFunction.Repr))
           ==> 
          !read($Heap, 
            read($Heap, this, _module.DefaultDecreasesFunction.next), 
            _module.DefaultDecreasesFunction.Repr)[$Box(this)]
           ==> _module.DefaultDecreasesFunction.Valid#canCall($Heap, read($Heap, this, _module.DefaultDecreasesFunction.next)))
         && _module.DefaultDecreasesFunction.Valid($LS($ly), $Heap, this)
           == (
            read($Heap, this, _module.DefaultDecreasesFunction.Repr)[$Box(this)]
             && !read($Heap, this, _module.DefaultDecreasesFunction.Repr)[$Box(null)]
             && (read($Heap, this, _module.DefaultDecreasesFunction.next) != null
               ==> read($Heap, this, _module.DefaultDecreasesFunction.Repr)[$Box(read($Heap, this, _module.DefaultDecreasesFunction.next))]
                 && Set#Subset(read($Heap, 
                    read($Heap, this, _module.DefaultDecreasesFunction.next), 
                    _module.DefaultDecreasesFunction.Repr), 
                  read($Heap, this, _module.DefaultDecreasesFunction.Repr))
                 && !read($Heap, 
                  read($Heap, this, _module.DefaultDecreasesFunction.next), 
                  _module.DefaultDecreasesFunction.Repr)[$Box(this)]
                 && _module.DefaultDecreasesFunction.Valid($ly, $Heap, read($Heap, this, _module.DefaultDecreasesFunction.next)))));

procedure CheckWellformed$$_module.DefaultDecreasesFunction.Valid(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.DefaultDecreasesFunction())
         && $IsAlloc(this, Tclass._module.DefaultDecreasesFunction(), $Heap));
  free requires 26 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.DefaultDecreasesFunction.Valid(this: ref)
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

    // AddWellformednessCheck for function Valid
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(343,12): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> $o == this || read($Heap, this, _module.DefaultDecreasesFunction.Repr)[$Box($o)]);
    b$reqreads#0 := $_Frame[this, _module.DefaultDecreasesFunction.Repr];
    assert b$reqreads#0;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc)
             ==> $o == this || read($Heap, this, _module.DefaultDecreasesFunction.Repr)[$Box($o)]);
        b$reqreads#1 := $_Frame[this, _module.DefaultDecreasesFunction.Repr];
        if (read($Heap, this, _module.DefaultDecreasesFunction.Repr)[$Box(this)])
        {
            b$reqreads#2 := $_Frame[this, _module.DefaultDecreasesFunction.Repr];
        }

        if (read($Heap, this, _module.DefaultDecreasesFunction.Repr)[$Box(this)]
           && !read($Heap, this, _module.DefaultDecreasesFunction.Repr)[$Box(null)])
        {
            b$reqreads#3 := $_Frame[this, _module.DefaultDecreasesFunction.next];
            if (read($Heap, this, _module.DefaultDecreasesFunction.next) != null)
            {
                b$reqreads#4 := $_Frame[this, _module.DefaultDecreasesFunction.next];
                b$reqreads#5 := $_Frame[this, _module.DefaultDecreasesFunction.Repr];
                if (read($Heap, this, _module.DefaultDecreasesFunction.Repr)[$Box(read($Heap, this, _module.DefaultDecreasesFunction.next))])
                {
                    b$reqreads#6 := $_Frame[this, _module.DefaultDecreasesFunction.next];
                    assert read($Heap, this, _module.DefaultDecreasesFunction.next) != null;
                    b$reqreads#7 := $_Frame[read($Heap, this, _module.DefaultDecreasesFunction.next), _module.DefaultDecreasesFunction.Repr];
                    b$reqreads#8 := $_Frame[this, _module.DefaultDecreasesFunction.Repr];
                }

                if (read($Heap, this, _module.DefaultDecreasesFunction.Repr)[$Box(read($Heap, this, _module.DefaultDecreasesFunction.next))]
                   && Set#Subset(read($Heap, 
                      read($Heap, this, _module.DefaultDecreasesFunction.next), 
                      _module.DefaultDecreasesFunction.Repr), 
                    read($Heap, this, _module.DefaultDecreasesFunction.Repr)))
                {
                    b$reqreads#9 := $_Frame[this, _module.DefaultDecreasesFunction.next];
                    assert read($Heap, this, _module.DefaultDecreasesFunction.next) != null;
                    b$reqreads#10 := $_Frame[read($Heap, this, _module.DefaultDecreasesFunction.next), _module.DefaultDecreasesFunction.Repr];
                }

                if (read($Heap, this, _module.DefaultDecreasesFunction.Repr)[$Box(read($Heap, this, _module.DefaultDecreasesFunction.next))]
                   && Set#Subset(read($Heap, 
                      read($Heap, this, _module.DefaultDecreasesFunction.next), 
                      _module.DefaultDecreasesFunction.Repr), 
                    read($Heap, this, _module.DefaultDecreasesFunction.Repr))
                   && !read($Heap, 
                    read($Heap, this, _module.DefaultDecreasesFunction.next), 
                    _module.DefaultDecreasesFunction.Repr)[$Box(this)])
                {
                    b$reqreads#11 := $_Frame[this, _module.DefaultDecreasesFunction.next];
                    assert read($Heap, this, _module.DefaultDecreasesFunction.next) != null;
                    b$reqreads#12 := (forall<alpha> $o: ref, $f: Field alpha :: 
                      $o != null
                           && read($Heap, $o, alloc)
                           && ($o == read($Heap, this, _module.DefaultDecreasesFunction.next)
                             || read($Heap, 
                              read($Heap, this, _module.DefaultDecreasesFunction.next), 
                              _module.DefaultDecreasesFunction.Repr)[$Box($o)])
                         ==> $_Frame[$o, $f]);
                    assert Set#Subset(Set#Union(read($Heap, 
                            read($Heap, this, _module.DefaultDecreasesFunction.next), 
                            _module.DefaultDecreasesFunction.Repr), 
                          Set#UnionOne(Set#Empty(): Set Box, 
                            $Box(read($Heap, this, _module.DefaultDecreasesFunction.next)))), 
                        Set#Union(read($Heap, this, _module.DefaultDecreasesFunction.Repr), 
                          Set#UnionOne(Set#Empty(): Set Box, $Box(this))))
                       && !Set#Subset(Set#Union(read($Heap, this, _module.DefaultDecreasesFunction.Repr), 
                          Set#UnionOne(Set#Empty(): Set Box, $Box(this))), 
                        Set#Union(read($Heap, 
                            read($Heap, this, _module.DefaultDecreasesFunction.next), 
                            _module.DefaultDecreasesFunction.Repr), 
                          Set#UnionOne(Set#Empty(): Set Box, 
                            $Box(read($Heap, this, _module.DefaultDecreasesFunction.next)))));
                    assume _module.DefaultDecreasesFunction.Valid#canCall($Heap, read($Heap, this, _module.DefaultDecreasesFunction.next));
                }
            }
        }

        assume _module.DefaultDecreasesFunction.Valid($LS($LZ), $Heap, this)
           == (
            read($Heap, this, _module.DefaultDecreasesFunction.Repr)[$Box(this)]
             && !read($Heap, this, _module.DefaultDecreasesFunction.Repr)[$Box(null)]
             && (read($Heap, this, _module.DefaultDecreasesFunction.next) != null
               ==> read($Heap, this, _module.DefaultDecreasesFunction.Repr)[$Box(read($Heap, this, _module.DefaultDecreasesFunction.next))]
                 && Set#Subset(read($Heap, 
                    read($Heap, this, _module.DefaultDecreasesFunction.next), 
                    _module.DefaultDecreasesFunction.Repr), 
                  read($Heap, this, _module.DefaultDecreasesFunction.Repr))
                 && !read($Heap, 
                  read($Heap, this, _module.DefaultDecreasesFunction.next), 
                  _module.DefaultDecreasesFunction.Repr)[$Box(this)]
                 && _module.DefaultDecreasesFunction.Valid($LS($LZ), $Heap, read($Heap, this, _module.DefaultDecreasesFunction.next))));
        assume read($Heap, this, _module.DefaultDecreasesFunction.Repr)[$Box(this)]
           ==> 
          !read($Heap, this, _module.DefaultDecreasesFunction.Repr)[$Box(null)]
           ==> 
          read($Heap, this, _module.DefaultDecreasesFunction.next) != null
           ==> 
          read($Heap, this, _module.DefaultDecreasesFunction.Repr)[$Box(read($Heap, this, _module.DefaultDecreasesFunction.next))]
           ==> 
          Set#Subset(read($Heap, 
              read($Heap, this, _module.DefaultDecreasesFunction.next), 
              _module.DefaultDecreasesFunction.Repr), 
            read($Heap, this, _module.DefaultDecreasesFunction.Repr))
           ==> 
          !read($Heap, 
            read($Heap, this, _module.DefaultDecreasesFunction.next), 
            _module.DefaultDecreasesFunction.Repr)[$Box(this)]
           ==> _module.DefaultDecreasesFunction.Valid#canCall($Heap, read($Heap, this, _module.DefaultDecreasesFunction.next));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.DefaultDecreasesFunction.Valid($LS($LZ), $Heap, this), TBool);
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
    }
}



// function declaration for _module.DefaultDecreasesFunction.F
function _module.DefaultDecreasesFunction.F($ly: LayerType, $heap: Heap, this: ref, x#0: int) : int;

function _module.DefaultDecreasesFunction.F#canCall($heap: Heap, this: ref, x#0: int) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, $Heap: Heap, this: ref, x#0: int :: 
  { _module.DefaultDecreasesFunction.F($LS($ly), $Heap, this, x#0) } 
  _module.DefaultDecreasesFunction.F($LS($ly), $Heap, this, x#0)
     == _module.DefaultDecreasesFunction.F($ly, $Heap, this, x#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, $Heap: Heap, this: ref, x#0: int :: 
  { _module.DefaultDecreasesFunction.F(AsFuelBottom($ly), $Heap, this, x#0) } 
  _module.DefaultDecreasesFunction.F($ly, $Heap, this, x#0)
     == _module.DefaultDecreasesFunction.F($LZ, $Heap, this, x#0));

// frame axiom for _module.DefaultDecreasesFunction.F
axiom (forall $ly: LayerType, $h0: Heap, $h1: Heap, this: ref, x#0: int :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.DefaultDecreasesFunction.F($ly, $h1, this, x#0) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.DefaultDecreasesFunction())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && ($o == this || read($h0, this, _module.DefaultDecreasesFunction.Repr)[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.DefaultDecreasesFunction.F($ly, $h0, this, x#0)
       == _module.DefaultDecreasesFunction.F($ly, $h1, this, x#0));

// consequence axiom for _module.DefaultDecreasesFunction.F
axiom 27 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, this: ref, x#0: int :: 
    { _module.DefaultDecreasesFunction.F($ly, $Heap, this, x#0) } 
    _module.DefaultDecreasesFunction.F#canCall($Heap, this, x#0)
         || (27 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.DefaultDecreasesFunction())
           && $IsAlloc(this, Tclass._module.DefaultDecreasesFunction(), $Heap)
           && _module.DefaultDecreasesFunction.Valid($LS($LZ), $Heap, this))
       ==> true);

function _module.DefaultDecreasesFunction.F#requires(LayerType, Heap, ref, int) : bool;

// #requires axiom for _module.DefaultDecreasesFunction.F
axiom (forall $ly: LayerType, $Heap: Heap, this: ref, x#0: int :: 
  { _module.DefaultDecreasesFunction.F#requires($ly, $Heap, this, x#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.DefaultDecreasesFunction())
       && $IsAlloc(this, Tclass._module.DefaultDecreasesFunction(), $Heap)
     ==> _module.DefaultDecreasesFunction.F#requires($ly, $Heap, this, x#0)
       == _module.DefaultDecreasesFunction.Valid($LS($LZ), $Heap, this));

// definition axiom for _module.DefaultDecreasesFunction.F (revealed)
axiom 27 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, this: ref, x#0: int :: 
    { _module.DefaultDecreasesFunction.F($LS($ly), $Heap, this, x#0), $IsGoodHeap($Heap) } 
    _module.DefaultDecreasesFunction.F#canCall($Heap, this, x#0)
         || (27 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.DefaultDecreasesFunction())
           && $IsAlloc(this, Tclass._module.DefaultDecreasesFunction(), $Heap)
           && _module.DefaultDecreasesFunction.Valid($LS($LZ), $Heap, this))
       ==> (!(read($Heap, this, _module.DefaultDecreasesFunction.next) == null || x#0 < 0)
           ==> _module.DefaultDecreasesFunction.F#canCall($Heap, 
            read($Heap, this, _module.DefaultDecreasesFunction.next), 
            x#0 + read($Heap, this, _module.DefaultDecreasesFunction.data)))
         && _module.DefaultDecreasesFunction.F($LS($ly), $Heap, this, x#0)
           == (if read($Heap, this, _module.DefaultDecreasesFunction.next) == null || x#0 < 0
             then x#0
             else _module.DefaultDecreasesFunction.F($ly, 
              $Heap, 
              read($Heap, this, _module.DefaultDecreasesFunction.next), 
              x#0 + read($Heap, this, _module.DefaultDecreasesFunction.data))));

procedure CheckWellformed$$_module.DefaultDecreasesFunction.F(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.DefaultDecreasesFunction())
         && $IsAlloc(this, Tclass._module.DefaultDecreasesFunction(), $Heap), 
    x#0: int);
  free requires 27 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.DefaultDecreasesFunction.F(this: ref, x#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;
  var ##x#0: int;
  var b$reqreads#2: bool;
  var b$reqreads#3: bool;
  var b$reqreads#4: bool;
  var b$reqreads#5: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;
    b$reqreads#3 := true;
    b$reqreads#4 := true;
    b$reqreads#5 := true;

    // AddWellformednessCheck for function F
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(349,11): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> $o == this || read($Heap, this, _module.DefaultDecreasesFunction.Repr)[$Box($o)]);
    b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && read($Heap, $o, alloc)
           && ($o == this
             || read($Heap, this, _module.DefaultDecreasesFunction.Repr)[$Box($o)])
         ==> $_Frame[$o, $f]);
    assume _module.DefaultDecreasesFunction.Valid#canCall($Heap, this);
    assume _module.DefaultDecreasesFunction.Valid($LS($LZ), $Heap, this);
    assert b$reqreads#0;
    b$reqreads#1 := $_Frame[this, _module.DefaultDecreasesFunction.Repr];
    assert b$reqreads#1;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc)
             ==> $o == this || read($Heap, this, _module.DefaultDecreasesFunction.Repr)[$Box($o)]);
        b$reqreads#2 := $_Frame[this, _module.DefaultDecreasesFunction.next];
        if (read($Heap, this, _module.DefaultDecreasesFunction.next) != null)
        {
        }

        if (read($Heap, this, _module.DefaultDecreasesFunction.next) == null || x#0 < 0)
        {
            assume _module.DefaultDecreasesFunction.F($LS($LZ), $Heap, this, x#0) == x#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.DefaultDecreasesFunction.F($LS($LZ), $Heap, this, x#0), TInt);
        }
        else
        {
            b$reqreads#3 := $_Frame[this, _module.DefaultDecreasesFunction.next];
            assert read($Heap, this, _module.DefaultDecreasesFunction.next) != null;
            b$reqreads#4 := $_Frame[this, _module.DefaultDecreasesFunction.data];
            ##x#0 := x#0 + read($Heap, this, _module.DefaultDecreasesFunction.data);
            // assume allocatedness for argument to function
            assume $IsAlloc(##x#0, TInt, $Heap);
            assert {:subsumption 0} _module.DefaultDecreasesFunction.Valid#canCall($Heap, read($Heap, this, _module.DefaultDecreasesFunction.next))
               ==> _module.DefaultDecreasesFunction.Valid($LS($LZ), $Heap, read($Heap, this, _module.DefaultDecreasesFunction.next))
                 || read($Heap, 
                  read($Heap, this, _module.DefaultDecreasesFunction.next), 
                  _module.DefaultDecreasesFunction.Repr)[$Box(read($Heap, this, _module.DefaultDecreasesFunction.next))];
            assert {:subsumption 0} _module.DefaultDecreasesFunction.Valid#canCall($Heap, read($Heap, this, _module.DefaultDecreasesFunction.next))
               ==> _module.DefaultDecreasesFunction.Valid($LS($LZ), $Heap, read($Heap, this, _module.DefaultDecreasesFunction.next))
                 || !read($Heap, 
                  read($Heap, this, _module.DefaultDecreasesFunction.next), 
                  _module.DefaultDecreasesFunction.Repr)[$Box(null)];
            assert {:subsumption 0} _module.DefaultDecreasesFunction.Valid#canCall($Heap, read($Heap, this, _module.DefaultDecreasesFunction.next))
               ==> _module.DefaultDecreasesFunction.Valid($LS($LZ), $Heap, read($Heap, this, _module.DefaultDecreasesFunction.next))
                 || (read($Heap, 
                      read($Heap, this, _module.DefaultDecreasesFunction.next), 
                      _module.DefaultDecreasesFunction.next)
                     != null
                   ==> read($Heap, 
                    read($Heap, this, _module.DefaultDecreasesFunction.next), 
                    _module.DefaultDecreasesFunction.Repr)[$Box(read($Heap, 
                      read($Heap, this, _module.DefaultDecreasesFunction.next), 
                      _module.DefaultDecreasesFunction.next))]);
            assert {:subsumption 0} _module.DefaultDecreasesFunction.Valid#canCall($Heap, read($Heap, this, _module.DefaultDecreasesFunction.next))
               ==> _module.DefaultDecreasesFunction.Valid($LS($LZ), $Heap, read($Heap, this, _module.DefaultDecreasesFunction.next))
                 || (read($Heap, 
                      read($Heap, this, _module.DefaultDecreasesFunction.next), 
                      _module.DefaultDecreasesFunction.next)
                     != null
                   ==> Set#Subset(read($Heap, 
                      read($Heap, 
                        read($Heap, this, _module.DefaultDecreasesFunction.next), 
                        _module.DefaultDecreasesFunction.next), 
                      _module.DefaultDecreasesFunction.Repr), 
                    read($Heap, 
                      read($Heap, this, _module.DefaultDecreasesFunction.next), 
                      _module.DefaultDecreasesFunction.Repr)));
            assert {:subsumption 0} _module.DefaultDecreasesFunction.Valid#canCall($Heap, read($Heap, this, _module.DefaultDecreasesFunction.next))
               ==> _module.DefaultDecreasesFunction.Valid($LS($LZ), $Heap, read($Heap, this, _module.DefaultDecreasesFunction.next))
                 || (read($Heap, 
                      read($Heap, this, _module.DefaultDecreasesFunction.next), 
                      _module.DefaultDecreasesFunction.next)
                     != null
                   ==> !read($Heap, 
                    read($Heap, 
                      read($Heap, this, _module.DefaultDecreasesFunction.next), 
                      _module.DefaultDecreasesFunction.next), 
                    _module.DefaultDecreasesFunction.Repr)[$Box(read($Heap, this, _module.DefaultDecreasesFunction.next))]);
            assert {:subsumption 0} _module.DefaultDecreasesFunction.Valid#canCall($Heap, read($Heap, this, _module.DefaultDecreasesFunction.next))
               ==> _module.DefaultDecreasesFunction.Valid($LS($LZ), $Heap, read($Heap, this, _module.DefaultDecreasesFunction.next))
                 || (read($Heap, 
                      read($Heap, this, _module.DefaultDecreasesFunction.next), 
                      _module.DefaultDecreasesFunction.next)
                     != null
                   ==> _module.DefaultDecreasesFunction.Valid($LS($LS($LZ)), 
                    $Heap, 
                    read($Heap, 
                      read($Heap, this, _module.DefaultDecreasesFunction.next), 
                      _module.DefaultDecreasesFunction.next)));
            assume _module.DefaultDecreasesFunction.Valid($LS($LZ), $Heap, read($Heap, this, _module.DefaultDecreasesFunction.next));
            b$reqreads#5 := (forall<alpha> $o: ref, $f: Field alpha :: 
              $o != null
                   && read($Heap, $o, alloc)
                   && ($o == read($Heap, this, _module.DefaultDecreasesFunction.next)
                     || read($Heap, 
                      read($Heap, this, _module.DefaultDecreasesFunction.next), 
                      _module.DefaultDecreasesFunction.Repr)[$Box($o)])
                 ==> $_Frame[$o, $f]);
            assert 0 <= x#0
               || (Set#Subset(Set#Union(read($Heap, 
                      read($Heap, this, _module.DefaultDecreasesFunction.next), 
                      _module.DefaultDecreasesFunction.Repr), 
                    Set#UnionOne(Set#Empty(): Set Box, 
                      $Box(read($Heap, this, _module.DefaultDecreasesFunction.next)))), 
                  Set#Union(read($Heap, this, _module.DefaultDecreasesFunction.Repr), 
                    Set#UnionOne(Set#Empty(): Set Box, $Box(this))))
                 && !Set#Subset(Set#Union(read($Heap, this, _module.DefaultDecreasesFunction.Repr), 
                    Set#UnionOne(Set#Empty(): Set Box, $Box(this))), 
                  Set#Union(read($Heap, 
                      read($Heap, this, _module.DefaultDecreasesFunction.next), 
                      _module.DefaultDecreasesFunction.Repr), 
                    Set#UnionOne(Set#Empty(): Set Box, 
                      $Box(read($Heap, this, _module.DefaultDecreasesFunction.next))))))
               || ##x#0 == x#0;
            assert (Set#Subset(Set#Union(read($Heap, 
                      read($Heap, this, _module.DefaultDecreasesFunction.next), 
                      _module.DefaultDecreasesFunction.Repr), 
                    Set#UnionOne(Set#Empty(): Set Box, 
                      $Box(read($Heap, this, _module.DefaultDecreasesFunction.next)))), 
                  Set#Union(read($Heap, this, _module.DefaultDecreasesFunction.Repr), 
                    Set#UnionOne(Set#Empty(): Set Box, $Box(this))))
                 && !Set#Subset(Set#Union(read($Heap, this, _module.DefaultDecreasesFunction.Repr), 
                    Set#UnionOne(Set#Empty(): Set Box, $Box(this))), 
                  Set#Union(read($Heap, 
                      read($Heap, this, _module.DefaultDecreasesFunction.next), 
                      _module.DefaultDecreasesFunction.Repr), 
                    Set#UnionOne(Set#Empty(): Set Box, 
                      $Box(read($Heap, this, _module.DefaultDecreasesFunction.next))))))
               || (Set#Equal(Set#Union(read($Heap, 
                      read($Heap, this, _module.DefaultDecreasesFunction.next), 
                      _module.DefaultDecreasesFunction.Repr), 
                    Set#UnionOne(Set#Empty(): Set Box, 
                      $Box(read($Heap, this, _module.DefaultDecreasesFunction.next)))), 
                  Set#Union(read($Heap, this, _module.DefaultDecreasesFunction.Repr), 
                    Set#UnionOne(Set#Empty(): Set Box, $Box(this))))
                 && ##x#0 < x#0);
            assume _module.DefaultDecreasesFunction.F#canCall($Heap, 
              read($Heap, this, _module.DefaultDecreasesFunction.next), 
              x#0 + read($Heap, this, _module.DefaultDecreasesFunction.data));
            assume _module.DefaultDecreasesFunction.F($LS($LZ), $Heap, this, x#0)
               == _module.DefaultDecreasesFunction.F($LS($LZ), 
                $Heap, 
                read($Heap, this, _module.DefaultDecreasesFunction.next), 
                x#0 + read($Heap, this, _module.DefaultDecreasesFunction.data));
            assume _module.DefaultDecreasesFunction.F#canCall($Heap, 
              read($Heap, this, _module.DefaultDecreasesFunction.next), 
              x#0 + read($Heap, this, _module.DefaultDecreasesFunction.data));
            // CheckWellformedWithResult: any expression
            assume $Is(_module.DefaultDecreasesFunction.F($LS($LZ), $Heap, this, x#0), TInt);
        }

        assert b$reqreads#2;
        assert b$reqreads#3;
        assert b$reqreads#4;
        assert b$reqreads#5;
    }
}



// function declaration for _module.DefaultDecreasesFunction.G
function _module.DefaultDecreasesFunction.G($ly: LayerType, $heap: Heap, this: ref, x#0: int) : int;

function _module.DefaultDecreasesFunction.G#canCall($heap: Heap, this: ref, x#0: int) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, $Heap: Heap, this: ref, x#0: int :: 
  { _module.DefaultDecreasesFunction.G($LS($ly), $Heap, this, x#0) } 
  _module.DefaultDecreasesFunction.G($LS($ly), $Heap, this, x#0)
     == _module.DefaultDecreasesFunction.G($ly, $Heap, this, x#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, $Heap: Heap, this: ref, x#0: int :: 
  { _module.DefaultDecreasesFunction.G(AsFuelBottom($ly), $Heap, this, x#0) } 
  _module.DefaultDecreasesFunction.G($ly, $Heap, this, x#0)
     == _module.DefaultDecreasesFunction.G($LZ, $Heap, this, x#0));

// frame axiom for _module.DefaultDecreasesFunction.G
axiom (forall $ly: LayerType, $h0: Heap, $h1: Heap, this: ref, x#0: int :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.DefaultDecreasesFunction.G($ly, $h1, this, x#0) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.DefaultDecreasesFunction())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && ($o == this || read($h0, this, _module.DefaultDecreasesFunction.Repr)[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.DefaultDecreasesFunction.G($ly, $h0, this, x#0)
       == _module.DefaultDecreasesFunction.G($ly, $h1, this, x#0));

// consequence axiom for _module.DefaultDecreasesFunction.G
axiom 28 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, this: ref, x#0: int :: 
    { _module.DefaultDecreasesFunction.G($ly, $Heap, this, x#0) } 
    _module.DefaultDecreasesFunction.G#canCall($Heap, this, x#0)
         || (28 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.DefaultDecreasesFunction())
           && $IsAlloc(this, Tclass._module.DefaultDecreasesFunction(), $Heap)
           && _module.DefaultDecreasesFunction.Valid($LS($LZ), $Heap, this))
       ==> true);

function _module.DefaultDecreasesFunction.G#requires(LayerType, Heap, ref, int) : bool;

// #requires axiom for _module.DefaultDecreasesFunction.G
axiom (forall $ly: LayerType, $Heap: Heap, this: ref, x#0: int :: 
  { _module.DefaultDecreasesFunction.G#requires($ly, $Heap, this, x#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.DefaultDecreasesFunction())
       && $IsAlloc(this, Tclass._module.DefaultDecreasesFunction(), $Heap)
     ==> _module.DefaultDecreasesFunction.G#requires($ly, $Heap, this, x#0)
       == _module.DefaultDecreasesFunction.Valid($LS($LZ), $Heap, this));

// definition axiom for _module.DefaultDecreasesFunction.G (revealed)
axiom 28 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, this: ref, x#0: int :: 
    { _module.DefaultDecreasesFunction.G($LS($ly), $Heap, this, x#0), $IsGoodHeap($Heap) } 
    _module.DefaultDecreasesFunction.G#canCall($Heap, this, x#0)
         || (28 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.DefaultDecreasesFunction())
           && $IsAlloc(this, Tclass._module.DefaultDecreasesFunction(), $Heap)
           && _module.DefaultDecreasesFunction.Valid($LS($LZ), $Heap, this))
       ==> (!(read($Heap, this, _module.DefaultDecreasesFunction.next) == null || x#0 < 0)
           ==> _module.DefaultDecreasesFunction.G#canCall($Heap, 
            read($Heap, this, _module.DefaultDecreasesFunction.next), 
            x#0 + read($Heap, this, _module.DefaultDecreasesFunction.data)))
         && _module.DefaultDecreasesFunction.G($LS($ly), $Heap, this, x#0)
           == (if read($Heap, this, _module.DefaultDecreasesFunction.next) == null || x#0 < 0
             then x#0
             else _module.DefaultDecreasesFunction.G($ly, 
              $Heap, 
              read($Heap, this, _module.DefaultDecreasesFunction.next), 
              x#0 + read($Heap, this, _module.DefaultDecreasesFunction.data))));

procedure CheckWellformed$$_module.DefaultDecreasesFunction.G(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.DefaultDecreasesFunction())
         && $IsAlloc(this, Tclass._module.DefaultDecreasesFunction(), $Heap), 
    x#0: int);
  free requires 28 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.DefaultDecreasesFunction.G(this: ref, x#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;
  var ##x#0: int;
  var b$reqreads#2: bool;
  var b$reqreads#3: bool;
  var b$reqreads#4: bool;
  var b$reqreads#5: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;
    b$reqreads#3 := true;
    b$reqreads#4 := true;
    b$reqreads#5 := true;

    // AddWellformednessCheck for function G
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(356,11): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> $o == this || read($Heap, this, _module.DefaultDecreasesFunction.Repr)[$Box($o)]);
    b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && read($Heap, $o, alloc)
           && ($o == this
             || read($Heap, this, _module.DefaultDecreasesFunction.Repr)[$Box($o)])
         ==> $_Frame[$o, $f]);
    assume _module.DefaultDecreasesFunction.Valid#canCall($Heap, this);
    assume _module.DefaultDecreasesFunction.Valid($LS($LZ), $Heap, this);
    assert b$reqreads#0;
    b$reqreads#1 := $_Frame[this, _module.DefaultDecreasesFunction.Repr];
    assert b$reqreads#1;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc)
             ==> $o == this || read($Heap, this, _module.DefaultDecreasesFunction.Repr)[$Box($o)]);
        b$reqreads#2 := $_Frame[this, _module.DefaultDecreasesFunction.next];
        if (read($Heap, this, _module.DefaultDecreasesFunction.next) != null)
        {
        }

        if (read($Heap, this, _module.DefaultDecreasesFunction.next) == null || x#0 < 0)
        {
            assume _module.DefaultDecreasesFunction.G($LS($LZ), $Heap, this, x#0) == x#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.DefaultDecreasesFunction.G($LS($LZ), $Heap, this, x#0), TInt);
        }
        else
        {
            b$reqreads#3 := $_Frame[this, _module.DefaultDecreasesFunction.next];
            assert read($Heap, this, _module.DefaultDecreasesFunction.next) != null;
            b$reqreads#4 := $_Frame[this, _module.DefaultDecreasesFunction.data];
            ##x#0 := x#0 + read($Heap, this, _module.DefaultDecreasesFunction.data);
            // assume allocatedness for argument to function
            assume $IsAlloc(##x#0, TInt, $Heap);
            assert {:subsumption 0} _module.DefaultDecreasesFunction.Valid#canCall($Heap, read($Heap, this, _module.DefaultDecreasesFunction.next))
               ==> _module.DefaultDecreasesFunction.Valid($LS($LZ), $Heap, read($Heap, this, _module.DefaultDecreasesFunction.next))
                 || read($Heap, 
                  read($Heap, this, _module.DefaultDecreasesFunction.next), 
                  _module.DefaultDecreasesFunction.Repr)[$Box(read($Heap, this, _module.DefaultDecreasesFunction.next))];
            assert {:subsumption 0} _module.DefaultDecreasesFunction.Valid#canCall($Heap, read($Heap, this, _module.DefaultDecreasesFunction.next))
               ==> _module.DefaultDecreasesFunction.Valid($LS($LZ), $Heap, read($Heap, this, _module.DefaultDecreasesFunction.next))
                 || !read($Heap, 
                  read($Heap, this, _module.DefaultDecreasesFunction.next), 
                  _module.DefaultDecreasesFunction.Repr)[$Box(null)];
            assert {:subsumption 0} _module.DefaultDecreasesFunction.Valid#canCall($Heap, read($Heap, this, _module.DefaultDecreasesFunction.next))
               ==> _module.DefaultDecreasesFunction.Valid($LS($LZ), $Heap, read($Heap, this, _module.DefaultDecreasesFunction.next))
                 || (read($Heap, 
                      read($Heap, this, _module.DefaultDecreasesFunction.next), 
                      _module.DefaultDecreasesFunction.next)
                     != null
                   ==> read($Heap, 
                    read($Heap, this, _module.DefaultDecreasesFunction.next), 
                    _module.DefaultDecreasesFunction.Repr)[$Box(read($Heap, 
                      read($Heap, this, _module.DefaultDecreasesFunction.next), 
                      _module.DefaultDecreasesFunction.next))]);
            assert {:subsumption 0} _module.DefaultDecreasesFunction.Valid#canCall($Heap, read($Heap, this, _module.DefaultDecreasesFunction.next))
               ==> _module.DefaultDecreasesFunction.Valid($LS($LZ), $Heap, read($Heap, this, _module.DefaultDecreasesFunction.next))
                 || (read($Heap, 
                      read($Heap, this, _module.DefaultDecreasesFunction.next), 
                      _module.DefaultDecreasesFunction.next)
                     != null
                   ==> Set#Subset(read($Heap, 
                      read($Heap, 
                        read($Heap, this, _module.DefaultDecreasesFunction.next), 
                        _module.DefaultDecreasesFunction.next), 
                      _module.DefaultDecreasesFunction.Repr), 
                    read($Heap, 
                      read($Heap, this, _module.DefaultDecreasesFunction.next), 
                      _module.DefaultDecreasesFunction.Repr)));
            assert {:subsumption 0} _module.DefaultDecreasesFunction.Valid#canCall($Heap, read($Heap, this, _module.DefaultDecreasesFunction.next))
               ==> _module.DefaultDecreasesFunction.Valid($LS($LZ), $Heap, read($Heap, this, _module.DefaultDecreasesFunction.next))
                 || (read($Heap, 
                      read($Heap, this, _module.DefaultDecreasesFunction.next), 
                      _module.DefaultDecreasesFunction.next)
                     != null
                   ==> !read($Heap, 
                    read($Heap, 
                      read($Heap, this, _module.DefaultDecreasesFunction.next), 
                      _module.DefaultDecreasesFunction.next), 
                    _module.DefaultDecreasesFunction.Repr)[$Box(read($Heap, this, _module.DefaultDecreasesFunction.next))]);
            assert {:subsumption 0} _module.DefaultDecreasesFunction.Valid#canCall($Heap, read($Heap, this, _module.DefaultDecreasesFunction.next))
               ==> _module.DefaultDecreasesFunction.Valid($LS($LZ), $Heap, read($Heap, this, _module.DefaultDecreasesFunction.next))
                 || (read($Heap, 
                      read($Heap, this, _module.DefaultDecreasesFunction.next), 
                      _module.DefaultDecreasesFunction.next)
                     != null
                   ==> _module.DefaultDecreasesFunction.Valid($LS($LS($LZ)), 
                    $Heap, 
                    read($Heap, 
                      read($Heap, this, _module.DefaultDecreasesFunction.next), 
                      _module.DefaultDecreasesFunction.next)));
            assume _module.DefaultDecreasesFunction.Valid($LS($LZ), $Heap, read($Heap, this, _module.DefaultDecreasesFunction.next));
            b$reqreads#5 := (forall<alpha> $o: ref, $f: Field alpha :: 
              $o != null
                   && read($Heap, $o, alloc)
                   && ($o == read($Heap, this, _module.DefaultDecreasesFunction.next)
                     || read($Heap, 
                      read($Heap, this, _module.DefaultDecreasesFunction.next), 
                      _module.DefaultDecreasesFunction.Repr)[$Box($o)])
                 ==> $_Frame[$o, $f]);
            assert 0 <= x#0 || ##x#0 == x#0;
            assert ##x#0 < x#0;
            assume _module.DefaultDecreasesFunction.G#canCall($Heap, 
              read($Heap, this, _module.DefaultDecreasesFunction.next), 
              x#0 + read($Heap, this, _module.DefaultDecreasesFunction.data));
            assume _module.DefaultDecreasesFunction.G($LS($LZ), $Heap, this, x#0)
               == _module.DefaultDecreasesFunction.G($LS($LZ), 
                $Heap, 
                read($Heap, this, _module.DefaultDecreasesFunction.next), 
                x#0 + read($Heap, this, _module.DefaultDecreasesFunction.data));
            assume _module.DefaultDecreasesFunction.G#canCall($Heap, 
              read($Heap, this, _module.DefaultDecreasesFunction.next), 
              x#0 + read($Heap, this, _module.DefaultDecreasesFunction.data));
            // CheckWellformedWithResult: any expression
            assume $Is(_module.DefaultDecreasesFunction.G($LS($LZ), $Heap, this, x#0), TInt);
        }

        assert b$reqreads#2;
        assert b$reqreads#3;
        assert b$reqreads#4;
        assert b$reqreads#5;
    }
}



// function declaration for _module.DefaultDecreasesFunction.H
function _module.DefaultDecreasesFunction.H($ly: LayerType, $heap: Heap, this: ref, x#0: int) : int;

function _module.DefaultDecreasesFunction.H#canCall($heap: Heap, this: ref, x#0: int) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, $Heap: Heap, this: ref, x#0: int :: 
  { _module.DefaultDecreasesFunction.H($LS($ly), $Heap, this, x#0) } 
  _module.DefaultDecreasesFunction.H($LS($ly), $Heap, this, x#0)
     == _module.DefaultDecreasesFunction.H($ly, $Heap, this, x#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, $Heap: Heap, this: ref, x#0: int :: 
  { _module.DefaultDecreasesFunction.H(AsFuelBottom($ly), $Heap, this, x#0) } 
  _module.DefaultDecreasesFunction.H($ly, $Heap, this, x#0)
     == _module.DefaultDecreasesFunction.H($LZ, $Heap, this, x#0));

// frame axiom for _module.DefaultDecreasesFunction.H
axiom (forall $ly: LayerType, $h0: Heap, $h1: Heap, this: ref, x#0: int :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.DefaultDecreasesFunction.H($ly, $h1, this, x#0) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.DefaultDecreasesFunction())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && ($o == this || read($h0, this, _module.DefaultDecreasesFunction.Repr)[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.DefaultDecreasesFunction.H($ly, $h0, this, x#0)
       == _module.DefaultDecreasesFunction.H($ly, $h1, this, x#0));

// consequence axiom for _module.DefaultDecreasesFunction.H
axiom 30 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, this: ref, x#0: int :: 
    { _module.DefaultDecreasesFunction.H($ly, $Heap, this, x#0) } 
    _module.DefaultDecreasesFunction.H#canCall($Heap, this, x#0)
         || (30 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.DefaultDecreasesFunction())
           && $IsAlloc(this, Tclass._module.DefaultDecreasesFunction(), $Heap)
           && 
          _module.DefaultDecreasesFunction.Valid($LS($LZ), $Heap, this)
           && LitInt(0) <= x#0)
       ==> true);

function _module.DefaultDecreasesFunction.H#requires(LayerType, Heap, ref, int) : bool;

// #requires axiom for _module.DefaultDecreasesFunction.H
axiom (forall $ly: LayerType, $Heap: Heap, this: ref, x#0: int :: 
  { _module.DefaultDecreasesFunction.H#requires($ly, $Heap, this, x#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.DefaultDecreasesFunction())
       && $IsAlloc(this, Tclass._module.DefaultDecreasesFunction(), $Heap)
     ==> _module.DefaultDecreasesFunction.H#requires($ly, $Heap, this, x#0)
       == (_module.DefaultDecreasesFunction.Valid($LS($LZ), $Heap, this)
         && LitInt(0) <= x#0));

// definition axiom for _module.DefaultDecreasesFunction.H (revealed)
axiom 30 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, this: ref, x#0: int :: 
    { _module.DefaultDecreasesFunction.H($LS($ly), $Heap, this, x#0), $IsGoodHeap($Heap) } 
    _module.DefaultDecreasesFunction.H#canCall($Heap, this, x#0)
         || (30 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.DefaultDecreasesFunction())
           && $IsAlloc(this, Tclass._module.DefaultDecreasesFunction(), $Heap)
           && 
          _module.DefaultDecreasesFunction.Valid($LS($LZ), $Heap, this)
           && LitInt(0) <= x#0)
       ==> (read($Heap, this, _module.DefaultDecreasesFunction.next) != null
           ==> _module.DefaultDecreasesFunction.Abs#canCall(this, read($Heap, this, _module.DefaultDecreasesFunction.data))
             && _module.DefaultDecreasesFunction.H#canCall($Heap, 
              read($Heap, this, _module.DefaultDecreasesFunction.next), 
              _module.DefaultDecreasesFunction.Abs(this, read($Heap, this, _module.DefaultDecreasesFunction.data))))
         && (read($Heap, this, _module.DefaultDecreasesFunction.next) == null
           ==> 
          78 <= x#0
           ==> _module.DefaultDecreasesFunction.H#canCall($Heap, this, x#0 - 1))
         && _module.DefaultDecreasesFunction.H($LS($ly), $Heap, this, x#0)
           == (if read($Heap, this, _module.DefaultDecreasesFunction.next) != null
             then _module.DefaultDecreasesFunction.H($ly, 
              $Heap, 
              read($Heap, this, _module.DefaultDecreasesFunction.next), 
              _module.DefaultDecreasesFunction.Abs(this, read($Heap, this, _module.DefaultDecreasesFunction.data)))
             else (if x#0 < 78
               then read($Heap, this, _module.DefaultDecreasesFunction.data) + x#0
               else _module.DefaultDecreasesFunction.H($ly, $Heap, this, x#0 - 1))));

procedure CheckWellformed$$_module.DefaultDecreasesFunction.H(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.DefaultDecreasesFunction())
         && $IsAlloc(this, Tclass._module.DefaultDecreasesFunction(), $Heap), 
    x#0: int);
  free requires 30 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.DefaultDecreasesFunction.H(this: ref, x#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;
  var ##x#0: int;
  var ##x#1: int;
  var ##x#2: int;
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

    // AddWellformednessCheck for function H
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(363,11): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> $o == this || read($Heap, this, _module.DefaultDecreasesFunction.Repr)[$Box($o)]);
    b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && read($Heap, $o, alloc)
           && ($o == this
             || read($Heap, this, _module.DefaultDecreasesFunction.Repr)[$Box($o)])
         ==> $_Frame[$o, $f]);
    assume _module.DefaultDecreasesFunction.Valid#canCall($Heap, this);
    assume _module.DefaultDecreasesFunction.Valid($LS($LZ), $Heap, this);
    assume LitInt(0) <= x#0;
    assert b$reqreads#0;
    b$reqreads#1 := $_Frame[this, _module.DefaultDecreasesFunction.Repr];
    assert b$reqreads#1;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc)
             ==> $o == this || read($Heap, this, _module.DefaultDecreasesFunction.Repr)[$Box($o)]);
        b$reqreads#2 := $_Frame[this, _module.DefaultDecreasesFunction.next];
        if (read($Heap, this, _module.DefaultDecreasesFunction.next) != null)
        {
            b$reqreads#3 := $_Frame[this, _module.DefaultDecreasesFunction.next];
            assert read($Heap, this, _module.DefaultDecreasesFunction.next) != null;
            b$reqreads#4 := $_Frame[this, _module.DefaultDecreasesFunction.data];
            ##x#0 := read($Heap, this, _module.DefaultDecreasesFunction.data);
            // assume allocatedness for argument to function
            assume $IsAlloc(##x#0, TInt, $Heap);
            b$reqreads#5 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.DefaultDecreasesFunction.Abs#canCall(this, read($Heap, this, _module.DefaultDecreasesFunction.data));
            ##x#1 := _module.DefaultDecreasesFunction.Abs(this, read($Heap, this, _module.DefaultDecreasesFunction.data));
            // assume allocatedness for argument to function
            assume $IsAlloc(##x#1, TInt, $Heap);
            assert {:subsumption 0} _module.DefaultDecreasesFunction.Valid#canCall($Heap, read($Heap, this, _module.DefaultDecreasesFunction.next))
               ==> _module.DefaultDecreasesFunction.Valid($LS($LZ), $Heap, read($Heap, this, _module.DefaultDecreasesFunction.next))
                 || read($Heap, 
                  read($Heap, this, _module.DefaultDecreasesFunction.next), 
                  _module.DefaultDecreasesFunction.Repr)[$Box(read($Heap, this, _module.DefaultDecreasesFunction.next))];
            assert {:subsumption 0} _module.DefaultDecreasesFunction.Valid#canCall($Heap, read($Heap, this, _module.DefaultDecreasesFunction.next))
               ==> _module.DefaultDecreasesFunction.Valid($LS($LZ), $Heap, read($Heap, this, _module.DefaultDecreasesFunction.next))
                 || !read($Heap, 
                  read($Heap, this, _module.DefaultDecreasesFunction.next), 
                  _module.DefaultDecreasesFunction.Repr)[$Box(null)];
            assert {:subsumption 0} _module.DefaultDecreasesFunction.Valid#canCall($Heap, read($Heap, this, _module.DefaultDecreasesFunction.next))
               ==> _module.DefaultDecreasesFunction.Valid($LS($LZ), $Heap, read($Heap, this, _module.DefaultDecreasesFunction.next))
                 || (read($Heap, 
                      read($Heap, this, _module.DefaultDecreasesFunction.next), 
                      _module.DefaultDecreasesFunction.next)
                     != null
                   ==> read($Heap, 
                    read($Heap, this, _module.DefaultDecreasesFunction.next), 
                    _module.DefaultDecreasesFunction.Repr)[$Box(read($Heap, 
                      read($Heap, this, _module.DefaultDecreasesFunction.next), 
                      _module.DefaultDecreasesFunction.next))]);
            assert {:subsumption 0} _module.DefaultDecreasesFunction.Valid#canCall($Heap, read($Heap, this, _module.DefaultDecreasesFunction.next))
               ==> _module.DefaultDecreasesFunction.Valid($LS($LZ), $Heap, read($Heap, this, _module.DefaultDecreasesFunction.next))
                 || (read($Heap, 
                      read($Heap, this, _module.DefaultDecreasesFunction.next), 
                      _module.DefaultDecreasesFunction.next)
                     != null
                   ==> Set#Subset(read($Heap, 
                      read($Heap, 
                        read($Heap, this, _module.DefaultDecreasesFunction.next), 
                        _module.DefaultDecreasesFunction.next), 
                      _module.DefaultDecreasesFunction.Repr), 
                    read($Heap, 
                      read($Heap, this, _module.DefaultDecreasesFunction.next), 
                      _module.DefaultDecreasesFunction.Repr)));
            assert {:subsumption 0} _module.DefaultDecreasesFunction.Valid#canCall($Heap, read($Heap, this, _module.DefaultDecreasesFunction.next))
               ==> _module.DefaultDecreasesFunction.Valid($LS($LZ), $Heap, read($Heap, this, _module.DefaultDecreasesFunction.next))
                 || (read($Heap, 
                      read($Heap, this, _module.DefaultDecreasesFunction.next), 
                      _module.DefaultDecreasesFunction.next)
                     != null
                   ==> !read($Heap, 
                    read($Heap, 
                      read($Heap, this, _module.DefaultDecreasesFunction.next), 
                      _module.DefaultDecreasesFunction.next), 
                    _module.DefaultDecreasesFunction.Repr)[$Box(read($Heap, this, _module.DefaultDecreasesFunction.next))]);
            assert {:subsumption 0} _module.DefaultDecreasesFunction.Valid#canCall($Heap, read($Heap, this, _module.DefaultDecreasesFunction.next))
               ==> _module.DefaultDecreasesFunction.Valid($LS($LZ), $Heap, read($Heap, this, _module.DefaultDecreasesFunction.next))
                 || (read($Heap, 
                      read($Heap, this, _module.DefaultDecreasesFunction.next), 
                      _module.DefaultDecreasesFunction.next)
                     != null
                   ==> _module.DefaultDecreasesFunction.Valid($LS($LS($LZ)), 
                    $Heap, 
                    read($Heap, 
                      read($Heap, this, _module.DefaultDecreasesFunction.next), 
                      _module.DefaultDecreasesFunction.next)));
            assert {:subsumption 0} LitInt(0) <= ##x#1;
            assume _module.DefaultDecreasesFunction.Valid($LS($LZ), $Heap, read($Heap, this, _module.DefaultDecreasesFunction.next))
               && LitInt(0) <= ##x#1;
            b$reqreads#6 := (forall<alpha> $o: ref, $f: Field alpha :: 
              $o != null
                   && read($Heap, $o, alloc)
                   && ($o == read($Heap, this, _module.DefaultDecreasesFunction.next)
                     || read($Heap, 
                      read($Heap, this, _module.DefaultDecreasesFunction.next), 
                      _module.DefaultDecreasesFunction.Repr)[$Box($o)])
                 ==> $_Frame[$o, $f]);
            assert 0 <= x#0
               || (Set#Subset(Set#Union(read($Heap, 
                      read($Heap, this, _module.DefaultDecreasesFunction.next), 
                      _module.DefaultDecreasesFunction.Repr), 
                    Set#UnionOne(Set#Empty(): Set Box, 
                      $Box(read($Heap, this, _module.DefaultDecreasesFunction.next)))), 
                  Set#Union(read($Heap, this, _module.DefaultDecreasesFunction.Repr), 
                    Set#UnionOne(Set#Empty(): Set Box, $Box(this))))
                 && !Set#Subset(Set#Union(read($Heap, this, _module.DefaultDecreasesFunction.Repr), 
                    Set#UnionOne(Set#Empty(): Set Box, $Box(this))), 
                  Set#Union(read($Heap, 
                      read($Heap, this, _module.DefaultDecreasesFunction.next), 
                      _module.DefaultDecreasesFunction.Repr), 
                    Set#UnionOne(Set#Empty(): Set Box, 
                      $Box(read($Heap, this, _module.DefaultDecreasesFunction.next))))))
               || ##x#1 == x#0;
            assert (Set#Subset(Set#Union(read($Heap, 
                      read($Heap, this, _module.DefaultDecreasesFunction.next), 
                      _module.DefaultDecreasesFunction.Repr), 
                    Set#UnionOne(Set#Empty(): Set Box, 
                      $Box(read($Heap, this, _module.DefaultDecreasesFunction.next)))), 
                  Set#Union(read($Heap, this, _module.DefaultDecreasesFunction.Repr), 
                    Set#UnionOne(Set#Empty(): Set Box, $Box(this))))
                 && !Set#Subset(Set#Union(read($Heap, this, _module.DefaultDecreasesFunction.Repr), 
                    Set#UnionOne(Set#Empty(): Set Box, $Box(this))), 
                  Set#Union(read($Heap, 
                      read($Heap, this, _module.DefaultDecreasesFunction.next), 
                      _module.DefaultDecreasesFunction.Repr), 
                    Set#UnionOne(Set#Empty(): Set Box, 
                      $Box(read($Heap, this, _module.DefaultDecreasesFunction.next))))))
               || (Set#Equal(Set#Union(read($Heap, 
                      read($Heap, this, _module.DefaultDecreasesFunction.next), 
                      _module.DefaultDecreasesFunction.Repr), 
                    Set#UnionOne(Set#Empty(): Set Box, 
                      $Box(read($Heap, this, _module.DefaultDecreasesFunction.next)))), 
                  Set#Union(read($Heap, this, _module.DefaultDecreasesFunction.Repr), 
                    Set#UnionOne(Set#Empty(): Set Box, $Box(this))))
                 && ##x#1 < x#0);
            assume _module.DefaultDecreasesFunction.H#canCall($Heap, 
              read($Heap, this, _module.DefaultDecreasesFunction.next), 
              _module.DefaultDecreasesFunction.Abs(this, read($Heap, this, _module.DefaultDecreasesFunction.data)));
            assume _module.DefaultDecreasesFunction.H($LS($LZ), $Heap, this, x#0)
               == _module.DefaultDecreasesFunction.H($LS($LZ), 
                $Heap, 
                read($Heap, this, _module.DefaultDecreasesFunction.next), 
                _module.DefaultDecreasesFunction.Abs(this, read($Heap, this, _module.DefaultDecreasesFunction.data)));
            assume _module.DefaultDecreasesFunction.Abs#canCall(this, read($Heap, this, _module.DefaultDecreasesFunction.data))
               && _module.DefaultDecreasesFunction.H#canCall($Heap, 
                read($Heap, this, _module.DefaultDecreasesFunction.next), 
                _module.DefaultDecreasesFunction.Abs(this, read($Heap, this, _module.DefaultDecreasesFunction.data)));
            // CheckWellformedWithResult: any expression
            assume $Is(_module.DefaultDecreasesFunction.H($LS($LZ), $Heap, this, x#0), TInt);
        }
        else
        {
            if (x#0 < 78)
            {
                b$reqreads#7 := $_Frame[this, _module.DefaultDecreasesFunction.data];
                assume _module.DefaultDecreasesFunction.H($LS($LZ), $Heap, this, x#0)
                   == read($Heap, this, _module.DefaultDecreasesFunction.data) + x#0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(_module.DefaultDecreasesFunction.H($LS($LZ), $Heap, this, x#0), TInt);
            }
            else
            {
                ##x#2 := x#0 - 1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##x#2, TInt, $Heap);
                assert {:subsumption 0} _module.DefaultDecreasesFunction.Valid#canCall($Heap, this)
                   ==> _module.DefaultDecreasesFunction.Valid($LS($LZ), $Heap, this)
                     || read($Heap, this, _module.DefaultDecreasesFunction.Repr)[$Box(this)];
                assert {:subsumption 0} _module.DefaultDecreasesFunction.Valid#canCall($Heap, this)
                   ==> _module.DefaultDecreasesFunction.Valid($LS($LZ), $Heap, this)
                     || !read($Heap, this, _module.DefaultDecreasesFunction.Repr)[$Box(null)];
                assert {:subsumption 0} _module.DefaultDecreasesFunction.Valid#canCall($Heap, this)
                   ==> _module.DefaultDecreasesFunction.Valid($LS($LZ), $Heap, this)
                     || (read($Heap, this, _module.DefaultDecreasesFunction.next) != null
                       ==> read($Heap, this, _module.DefaultDecreasesFunction.Repr)[$Box(read($Heap, this, _module.DefaultDecreasesFunction.next))]);
                assert {:subsumption 0} _module.DefaultDecreasesFunction.Valid#canCall($Heap, this)
                   ==> _module.DefaultDecreasesFunction.Valid($LS($LZ), $Heap, this)
                     || (read($Heap, this, _module.DefaultDecreasesFunction.next) != null
                       ==> Set#Subset(read($Heap, 
                          read($Heap, this, _module.DefaultDecreasesFunction.next), 
                          _module.DefaultDecreasesFunction.Repr), 
                        read($Heap, this, _module.DefaultDecreasesFunction.Repr)));
                assert {:subsumption 0} _module.DefaultDecreasesFunction.Valid#canCall($Heap, this)
                   ==> _module.DefaultDecreasesFunction.Valid($LS($LZ), $Heap, this)
                     || (read($Heap, this, _module.DefaultDecreasesFunction.next) != null
                       ==> !read($Heap, 
                        read($Heap, this, _module.DefaultDecreasesFunction.next), 
                        _module.DefaultDecreasesFunction.Repr)[$Box(this)]);
                assert {:subsumption 0} _module.DefaultDecreasesFunction.Valid#canCall($Heap, this)
                   ==> _module.DefaultDecreasesFunction.Valid($LS($LZ), $Heap, this)
                     || (read($Heap, this, _module.DefaultDecreasesFunction.next) != null
                       ==> _module.DefaultDecreasesFunction.Valid($LS($LS($LZ)), $Heap, read($Heap, this, _module.DefaultDecreasesFunction.next)));
                assert {:subsumption 0} LitInt(0) <= ##x#2;
                assume _module.DefaultDecreasesFunction.Valid($LS($LZ), $Heap, this)
                   && LitInt(0) <= ##x#2;
                b$reqreads#8 := (forall<alpha> $o: ref, $f: Field alpha :: 
                  $o != null
                       && read($Heap, $o, alloc)
                       && ($o == this
                         || read($Heap, this, _module.DefaultDecreasesFunction.Repr)[$Box($o)])
                     ==> $_Frame[$o, $f]);
                assert 0 <= x#0
                   || (Set#Subset(Set#Union(read($Heap, this, _module.DefaultDecreasesFunction.Repr), 
                        Set#UnionOne(Set#Empty(): Set Box, $Box(this))), 
                      Set#Union(read($Heap, this, _module.DefaultDecreasesFunction.Repr), 
                        Set#UnionOne(Set#Empty(): Set Box, $Box(this))))
                     && !Set#Subset(Set#Union(read($Heap, this, _module.DefaultDecreasesFunction.Repr), 
                        Set#UnionOne(Set#Empty(): Set Box, $Box(this))), 
                      Set#Union(read($Heap, this, _module.DefaultDecreasesFunction.Repr), 
                        Set#UnionOne(Set#Empty(): Set Box, $Box(this)))))
                   || ##x#2 == x#0;
                assert (Set#Subset(Set#Union(read($Heap, this, _module.DefaultDecreasesFunction.Repr), 
                        Set#UnionOne(Set#Empty(): Set Box, $Box(this))), 
                      Set#Union(read($Heap, this, _module.DefaultDecreasesFunction.Repr), 
                        Set#UnionOne(Set#Empty(): Set Box, $Box(this))))
                     && !Set#Subset(Set#Union(read($Heap, this, _module.DefaultDecreasesFunction.Repr), 
                        Set#UnionOne(Set#Empty(): Set Box, $Box(this))), 
                      Set#Union(read($Heap, this, _module.DefaultDecreasesFunction.Repr), 
                        Set#UnionOne(Set#Empty(): Set Box, $Box(this)))))
                   || (Set#Equal(Set#Union(read($Heap, this, _module.DefaultDecreasesFunction.Repr), 
                        Set#UnionOne(Set#Empty(): Set Box, $Box(this))), 
                      Set#Union(read($Heap, this, _module.DefaultDecreasesFunction.Repr), 
                        Set#UnionOne(Set#Empty(): Set Box, $Box(this))))
                     && ##x#2 < x#0);
                assume _module.DefaultDecreasesFunction.H#canCall($Heap, this, x#0 - 1);
                assume _module.DefaultDecreasesFunction.H($LS($LZ), $Heap, this, x#0)
                   == _module.DefaultDecreasesFunction.H($LS($LZ), $Heap, this, x#0 - 1);
                assume _module.DefaultDecreasesFunction.H#canCall($Heap, this, x#0 - 1);
                // CheckWellformedWithResult: any expression
                assume $Is(_module.DefaultDecreasesFunction.H($LS($LZ), $Heap, this, x#0), TInt);
            }
        }

        assert b$reqreads#2;
        assert b$reqreads#3;
        assert b$reqreads#4;
        assert b$reqreads#5;
        assert b$reqreads#6;
        assert b$reqreads#7;
        assert b$reqreads#8;
    }
}



// function declaration for _module.DefaultDecreasesFunction.Abs
function _module.DefaultDecreasesFunction.Abs(this: ref, x#0: int) : int;

function _module.DefaultDecreasesFunction.Abs#canCall(this: ref, x#0: int) : bool;

// consequence axiom for _module.DefaultDecreasesFunction.Abs
axiom 29 <= $FunctionContextHeight
   ==> (forall this: ref, x#0: int :: 
    { _module.DefaultDecreasesFunction.Abs(this, x#0) } 
    _module.DefaultDecreasesFunction.Abs#canCall(this, x#0)
         || (29 != $FunctionContextHeight
           && 
          this != null
           && $Is(this, Tclass._module.DefaultDecreasesFunction()))
       ==> true);

function _module.DefaultDecreasesFunction.Abs#requires(ref, int) : bool;

// #requires axiom for _module.DefaultDecreasesFunction.Abs
axiom (forall this: ref, x#0: int :: 
  { _module.DefaultDecreasesFunction.Abs#requires(this, x#0) } 
  this != null && $Is(this, Tclass._module.DefaultDecreasesFunction())
     ==> _module.DefaultDecreasesFunction.Abs#requires(this, x#0) == true);

// definition axiom for _module.DefaultDecreasesFunction.Abs (revealed)
axiom 29 <= $FunctionContextHeight
   ==> (forall this: ref, x#0: int :: 
    { _module.DefaultDecreasesFunction.Abs(this, x#0) } 
    _module.DefaultDecreasesFunction.Abs#canCall(this, x#0)
         || (29 != $FunctionContextHeight
           && 
          this != null
           && $Is(this, Tclass._module.DefaultDecreasesFunction()))
       ==> _module.DefaultDecreasesFunction.Abs(this, x#0)
         == (if x#0 < 0 then 0 - x#0 else x#0));

// definition axiom for _module.DefaultDecreasesFunction.Abs for decreasing-related literals (revealed)
axiom 29 <= $FunctionContextHeight
   ==> (forall this: ref, x#0: int :: 
    {:weight 3} { _module.DefaultDecreasesFunction.Abs(this, LitInt(x#0)) } 
    _module.DefaultDecreasesFunction.Abs#canCall(this, LitInt(x#0))
         || (29 != $FunctionContextHeight
           && 
          this != null
           && $Is(this, Tclass._module.DefaultDecreasesFunction()))
       ==> _module.DefaultDecreasesFunction.Abs(this, LitInt(x#0))
         == (if x#0 < 0 then 0 - x#0 else x#0));

// definition axiom for _module.DefaultDecreasesFunction.Abs for all literals (revealed)
axiom 29 <= $FunctionContextHeight
   ==> (forall this: ref, x#0: int :: 
    {:weight 3} { _module.DefaultDecreasesFunction.Abs(Lit(this), LitInt(x#0)) } 
    _module.DefaultDecreasesFunction.Abs#canCall(Lit(this), LitInt(x#0))
         || (29 != $FunctionContextHeight
           && 
          this != null
           && $Is(this, Tclass._module.DefaultDecreasesFunction()))
       ==> _module.DefaultDecreasesFunction.Abs(Lit(this), LitInt(x#0))
         == (if x#0 < 0 then 0 - x#0 else x#0));

procedure CheckWellformed$$_module.DefaultDecreasesFunction.Abs(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.DefaultDecreasesFunction())
         && $IsAlloc(this, Tclass._module.DefaultDecreasesFunction(), $Heap), 
    x#0: int);
  free requires 29 == $FunctionContextHeight;
  modifies $Heap, $Tick;



// _module.DefaultDecreasesFunction: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.DefaultDecreasesFunction()) } 
  $Is(c#0, Tclass._module.DefaultDecreasesFunction())
     <==> $Is(c#0, Tclass._module.DefaultDecreasesFunction?()) && c#0 != null);

// _module.DefaultDecreasesFunction: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.DefaultDecreasesFunction(), $h) } 
  $IsAlloc(c#0, Tclass._module.DefaultDecreasesFunction(), $h)
     <==> $IsAlloc(c#0, Tclass._module.DefaultDecreasesFunction?(), $h));

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

axiom FDim(_module.C.v) == 0
   && FieldOfDecl(class._module.C?, field$v) == _module.C.v
   && !$IsGhostField(_module.C.v);

const _module.C.v: Field int;

// C.v: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.C.v) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.C?()
     ==> $Is(read($h, $o, _module.C.v), Tclass._System.nat()));

// C.v: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.C.v) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.C?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.C.v), Tclass._System.nat(), $h));

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

procedure CheckWellformed$$_module.C.Terminate(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.C())
         && $IsAlloc(this, Tclass._module.C(), $Heap));
  free requires 31 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.C.Terminate(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.C())
         && $IsAlloc(this, Tclass._module.C(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.C.Terminate(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.C())
         && $IsAlloc(this, Tclass._module.C(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 31 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.C.Terminate(this: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0_0: int where LitInt(0) <= $rhs#0_0;

    // AddMethodImpl: Terminate, Impl$$_module.C.Terminate
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(427,2): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(428,5)
    assume true;
    if (read($Heap, this, _module.C.v) != 0)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(429,9)
        assume true;
        assert $_Frame[this, _module.C.v];
        assume true;
        assert $Is(read($Heap, this, _module.C.v) - 1, Tclass._System.nat());
        $rhs#0_0 := read($Heap, this, _module.C.v) - 1;
        $Heap := update($Heap, this, _module.C.v, $rhs#0_0);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(429,16)"} true;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(430,16)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        assert (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) && $o == this ==> $_Frame[$o, $f]);
        assert 0 <= read(old($Heap), this, _module.C.v)
           || read($Heap, this, _module.C.v) == read(old($Heap), this, _module.C.v);
        assert read($Heap, this, _module.C.v) < read(old($Heap), this, _module.C.v);
        // ProcessCallStmt: Make the call
        call Call$$_module.C.Terminate(this);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(430,17)"} true;
    }
    else
    {
    }
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

// Constructor function declaration
function #_module.Tree.Empty() : DatatypeType;

const unique ##_module.Tree.Empty: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#_module.Tree.Empty()) == ##_module.Tree.Empty;

function _module.Tree.Empty_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Tree.Empty_q(d) } 
  _module.Tree.Empty_q(d) <==> DatatypeCtorId(d) == ##_module.Tree.Empty);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Tree.Empty_q(d) } 
  _module.Tree.Empty_q(d) ==> d == #_module.Tree.Empty());

function Tclass._module.Tree() : Ty;

const unique Tagclass._module.Tree: TyTag;

// Tclass._module.Tree Tag
axiom Tag(Tclass._module.Tree()) == Tagclass._module.Tree
   && TagFamily(Tclass._module.Tree()) == tytagFamily$Tree;

// Box/unbox axiom for Tclass._module.Tree
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Tree()) } 
  $IsBox(bx, Tclass._module.Tree())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Tree()));

// Constructor $Is
axiom $Is(#_module.Tree.Empty(), Tclass._module.Tree());

// Constructor $IsAlloc
axiom (forall $h: Heap :: 
  { $IsAlloc(#_module.Tree.Empty(), Tclass._module.Tree(), $h) } 
  $IsGoodHeap($h) ==> $IsAlloc(#_module.Tree.Empty(), Tclass._module.Tree(), $h));

// Constructor literal
axiom #_module.Tree.Empty() == Lit(#_module.Tree.Empty());

// Constructor function declaration
function #_module.Tree.Node(int, DatatypeType, DatatypeType) : DatatypeType;

const unique ##_module.Tree.Node: DtCtorId;

// Constructor identifier
axiom (forall a#5#0#0: int, a#5#1#0: DatatypeType, a#5#2#0: DatatypeType :: 
  { #_module.Tree.Node(a#5#0#0, a#5#1#0, a#5#2#0) } 
  DatatypeCtorId(#_module.Tree.Node(a#5#0#0, a#5#1#0, a#5#2#0))
     == ##_module.Tree.Node);

function _module.Tree.Node_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Tree.Node_q(d) } 
  _module.Tree.Node_q(d) <==> DatatypeCtorId(d) == ##_module.Tree.Node);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Tree.Node_q(d) } 
  _module.Tree.Node_q(d)
     ==> (exists a#6#0#0: int, a#6#1#0: DatatypeType, a#6#2#0: DatatypeType :: 
      d == #_module.Tree.Node(a#6#0#0, a#6#1#0, a#6#2#0)));

// Constructor $Is
axiom (forall a#7#0#0: int, a#7#1#0: DatatypeType, a#7#2#0: DatatypeType :: 
  { $Is(#_module.Tree.Node(a#7#0#0, a#7#1#0, a#7#2#0), Tclass._module.Tree()) } 
  $Is(#_module.Tree.Node(a#7#0#0, a#7#1#0, a#7#2#0), Tclass._module.Tree())
     <==> $Is(a#7#0#0, TInt)
       && $Is(a#7#1#0, Tclass._module.Tree())
       && $Is(a#7#2#0, Tclass._module.Tree()));

// Constructor $IsAlloc
axiom (forall a#8#0#0: int, a#8#1#0: DatatypeType, a#8#2#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#_module.Tree.Node(a#8#0#0, a#8#1#0, a#8#2#0), Tclass._module.Tree(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Tree.Node(a#8#0#0, a#8#1#0, a#8#2#0), Tclass._module.Tree(), $h)
       <==> $IsAlloc(a#8#0#0, TInt, $h)
         && $IsAlloc(a#8#1#0, Tclass._module.Tree(), $h)
         && $IsAlloc(a#8#2#0, Tclass._module.Tree(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Tree.root(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Tree.Node_q(d)
       && $IsAlloc(d, Tclass._module.Tree(), $h)
     ==> $IsAlloc(_module.Tree.root(d), TInt, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Tree.left(d), Tclass._module.Tree(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.Tree.Node_q(d)
       && $IsAlloc(d, Tclass._module.Tree(), $h)
     ==> $IsAlloc(_module.Tree.left(d), Tclass._module.Tree(), $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Tree.right(d), Tclass._module.Tree(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.Tree.Node_q(d)
       && $IsAlloc(d, Tclass._module.Tree(), $h)
     ==> $IsAlloc(_module.Tree.right(d), Tclass._module.Tree(), $h));

// Constructor literal
axiom (forall a#9#0#0: int, a#9#1#0: DatatypeType, a#9#2#0: DatatypeType :: 
  { #_module.Tree.Node(LitInt(a#9#0#0), Lit(a#9#1#0), Lit(a#9#2#0)) } 
  #_module.Tree.Node(LitInt(a#9#0#0), Lit(a#9#1#0), Lit(a#9#2#0))
     == Lit(#_module.Tree.Node(a#9#0#0, a#9#1#0, a#9#2#0)));

function _module.Tree.root(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#10#0#0: int, a#10#1#0: DatatypeType, a#10#2#0: DatatypeType :: 
  { #_module.Tree.Node(a#10#0#0, a#10#1#0, a#10#2#0) } 
  _module.Tree.root(#_module.Tree.Node(a#10#0#0, a#10#1#0, a#10#2#0)) == a#10#0#0);

function _module.Tree.left(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#11#0#0: int, a#11#1#0: DatatypeType, a#11#2#0: DatatypeType :: 
  { #_module.Tree.Node(a#11#0#0, a#11#1#0, a#11#2#0) } 
  _module.Tree.left(#_module.Tree.Node(a#11#0#0, a#11#1#0, a#11#2#0)) == a#11#1#0);

// Inductive rank
axiom (forall a#12#0#0: int, a#12#1#0: DatatypeType, a#12#2#0: DatatypeType :: 
  { #_module.Tree.Node(a#12#0#0, a#12#1#0, a#12#2#0) } 
  DtRank(a#12#1#0) < DtRank(#_module.Tree.Node(a#12#0#0, a#12#1#0, a#12#2#0)));

function _module.Tree.right(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#13#0#0: int, a#13#1#0: DatatypeType, a#13#2#0: DatatypeType :: 
  { #_module.Tree.Node(a#13#0#0, a#13#1#0, a#13#2#0) } 
  _module.Tree.right(#_module.Tree.Node(a#13#0#0, a#13#1#0, a#13#2#0)) == a#13#2#0);

// Inductive rank
axiom (forall a#14#0#0: int, a#14#1#0: DatatypeType, a#14#2#0: DatatypeType :: 
  { #_module.Tree.Node(a#14#0#0, a#14#1#0, a#14#2#0) } 
  DtRank(a#14#2#0) < DtRank(#_module.Tree.Node(a#14#0#0, a#14#1#0, a#14#2#0)));

// Depth-one case-split function
function $IsA#_module.Tree(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.Tree(d) } 
  $IsA#_module.Tree(d) ==> _module.Tree.Empty_q(d) || _module.Tree.Node_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.Tree.Node_q(d), $Is(d, Tclass._module.Tree()) } 
    { _module.Tree.Empty_q(d), $Is(d, Tclass._module.Tree()) } 
  $Is(d, Tclass._module.Tree())
     ==> _module.Tree.Empty_q(d) || _module.Tree.Node_q(d));

// Datatype extensional equality declaration
function _module.Tree#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.Tree.Empty
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Tree#Equal(a, b), _module.Tree.Empty_q(a) } 
    { _module.Tree#Equal(a, b), _module.Tree.Empty_q(b) } 
  _module.Tree.Empty_q(a) && _module.Tree.Empty_q(b)
     ==> (_module.Tree#Equal(a, b) <==> true));

// Datatype extensional equality definition: #_module.Tree.Node
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Tree#Equal(a, b), _module.Tree.Node_q(a) } 
    { _module.Tree#Equal(a, b), _module.Tree.Node_q(b) } 
  _module.Tree.Node_q(a) && _module.Tree.Node_q(b)
     ==> (_module.Tree#Equal(a, b)
       <==> _module.Tree.root(a) == _module.Tree.root(b)
         && _module.Tree#Equal(_module.Tree.left(a), _module.Tree.left(b))
         && _module.Tree#Equal(_module.Tree.right(a), _module.Tree.right(b))));

// Datatype extensionality axiom: _module.Tree
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Tree#Equal(a, b) } 
  _module.Tree#Equal(a, b) <==> a == b);

const unique class._module.Tree: ClassName;

// function declaration for _module.Tree.Elements
function _module.Tree.Elements($ly: LayerType, this: DatatypeType) : Set Box;

function _module.Tree.Elements#canCall(this: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, this: DatatypeType :: 
  { _module.Tree.Elements($LS($ly), this) } 
  _module.Tree.Elements($LS($ly), this) == _module.Tree.Elements($ly, this));

// fuel synonym axiom
axiom (forall $ly: LayerType, this: DatatypeType :: 
  { _module.Tree.Elements(AsFuelBottom($ly), this) } 
  _module.Tree.Elements($ly, this) == _module.Tree.Elements($LZ, this));

// consequence axiom for _module.Tree.Elements
axiom 10 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, this: DatatypeType :: 
    { _module.Tree.Elements($ly, this) } 
    _module.Tree.Elements#canCall(this)
         || (10 != $FunctionContextHeight && $Is(this, Tclass._module.Tree()))
       ==> $Is(_module.Tree.Elements($ly, this), TSet(TInt)));

function _module.Tree.Elements#requires(LayerType, DatatypeType) : bool;

// #requires axiom for _module.Tree.Elements
axiom (forall $ly: LayerType, $Heap: Heap, this: DatatypeType :: 
  { _module.Tree.Elements#requires($ly, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      $Is(this, Tclass._module.Tree())
       && $IsAlloc(this, Tclass._module.Tree(), $Heap)
     ==> _module.Tree.Elements#requires($ly, this) == true);

// definition axiom for _module.Tree.Elements (revealed)
axiom 10 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, this: DatatypeType :: 
    { _module.Tree.Elements($LS($ly), this), $IsGoodHeap($Heap) } 
    _module.Tree.Elements#canCall(this)
         || (10 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          $Is(this, Tclass._module.Tree())
           && $IsAlloc(this, Tclass._module.Tree(), $Heap))
       ==> (!_module.Tree.Empty_q(this)
           ==> (var right#1 := _module.Tree.right(this); 
            (var left#1 := _module.Tree.left(this); 
              _module.Tree.Elements#canCall(left#1) && _module.Tree.Elements#canCall(right#1))))
         && _module.Tree.Elements($LS($ly), this)
           == (if _module.Tree.Empty_q(this)
             then Set#Empty(): Set Box
             else (var right#0 := _module.Tree.right(this); 
              (var left#0 := _module.Tree.left(this); 
                (var x#0 := _module.Tree.root(this); 
                  Set#Union(Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(x#0)), 
                      _module.Tree.Elements($ly, left#0)), 
                    _module.Tree.Elements($ly, right#0)))))));

// definition axiom for _module.Tree.Elements for all literals (revealed)
axiom 10 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, this: DatatypeType :: 
    {:weight 3} { _module.Tree.Elements($LS($ly), Lit(this)), $IsGoodHeap($Heap) } 
    _module.Tree.Elements#canCall(Lit(this))
         || (10 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          $Is(this, Tclass._module.Tree())
           && $IsAlloc(this, Tclass._module.Tree(), $Heap))
       ==> (!Lit(_module.Tree.Empty_q(Lit(this)))
           ==> (var right#3 := Lit(_module.Tree.right(Lit(this))); 
            (var left#3 := Lit(_module.Tree.left(Lit(this))); 
              _module.Tree.Elements#canCall(left#3) && _module.Tree.Elements#canCall(right#3))))
         && _module.Tree.Elements($LS($ly), Lit(this))
           == (if _module.Tree.Empty_q(Lit(this))
             then Set#Empty(): Set Box
             else (var right#2 := Lit(_module.Tree.right(Lit(this))); 
              (var left#2 := Lit(_module.Tree.left(Lit(this))); 
                (var x#2 := LitInt(_module.Tree.root(Lit(this))); 
                  Set#Union(Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(x#2)), 
                      _module.Tree.Elements($LS($ly), left#2)), 
                    _module.Tree.Elements($LS($ly), right#2)))))));

procedure CheckWellformed$$_module.Tree.Elements(this: DatatypeType
       where $Is(this, Tclass._module.Tree()) && $IsAlloc(this, Tclass._module.Tree(), $Heap));
  free requires 10 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Tree.Elements(this: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: int;
  var _mcc#1#0: DatatypeType;
  var _mcc#2#0: DatatypeType;
  var right#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var left#Z#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var x#Z#0: int;
  var let#2#0#0: int;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function Elements
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(458,11): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.Tree.Elements($LS($LZ), this), TSet(TInt));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (this == #_module.Tree.Empty())
        {
            assume _module.Tree.Elements($LS($LZ), this) == Lit(Set#Empty(): Set Box);
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.Tree.Elements($LS($LZ), this), TSet(TInt));
        }
        else if (this == #_module.Tree.Node(_mcc#0#0, _mcc#1#0, _mcc#2#0))
        {
            assume $Is(_mcc#1#0, Tclass._module.Tree());
            assume $Is(_mcc#2#0, Tclass._module.Tree());
            havoc right#Z#0;
            assume $Is(right#Z#0, Tclass._module.Tree());
            assume let#0#0#0 == _mcc#2#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.Tree());
            assume right#Z#0 == let#0#0#0;
            havoc left#Z#0;
            assume $Is(left#Z#0, Tclass._module.Tree());
            assume let#1#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#1#0#0, Tclass._module.Tree());
            assume left#Z#0 == let#1#0#0;
            havoc x#Z#0;
            assume true;
            assume let#2#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#2#0#0, TInt);
            assume x#Z#0 == let#2#0#0;
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(left#Z#0) < DtRank(this);
            assume _module.Tree.Elements#canCall(left#Z#0);
            b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(right#Z#0) < DtRank(this);
            assume _module.Tree.Elements#canCall(right#Z#0);
            assume _module.Tree.Elements($LS($LZ), this)
               == Set#Union(Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(x#Z#0)), 
                  _module.Tree.Elements($LS($LZ), left#Z#0)), 
                _module.Tree.Elements($LS($LZ), right#Z#0));
            assume _module.Tree.Elements#canCall(left#Z#0)
               && _module.Tree.Elements#canCall(right#Z#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.Tree.Elements($LS($LZ), this), TSet(TInt));
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



// function declaration for _module.Tree.Sum
function _module.Tree.Sum($ly: LayerType, this: DatatypeType) : int;

function _module.Tree.Sum#canCall(this: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, this: DatatypeType :: 
  { _module.Tree.Sum($LS($ly), this) } 
  _module.Tree.Sum($LS($ly), this) == _module.Tree.Sum($ly, this));

// fuel synonym axiom
axiom (forall $ly: LayerType, this: DatatypeType :: 
  { _module.Tree.Sum(AsFuelBottom($ly), this) } 
  _module.Tree.Sum($ly, this) == _module.Tree.Sum($LZ, this));

// consequence axiom for _module.Tree.Sum
axiom 11 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, this: DatatypeType :: 
    { _module.Tree.Sum($ly, this) } 
    _module.Tree.Sum#canCall(this)
         || (11 != $FunctionContextHeight && $Is(this, Tclass._module.Tree()))
       ==> true);

function _module.Tree.Sum#requires(LayerType, DatatypeType) : bool;

// #requires axiom for _module.Tree.Sum
axiom (forall $ly: LayerType, $Heap: Heap, this: DatatypeType :: 
  { _module.Tree.Sum#requires($ly, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      $Is(this, Tclass._module.Tree())
       && $IsAlloc(this, Tclass._module.Tree(), $Heap)
     ==> _module.Tree.Sum#requires($ly, this) == true);

// definition axiom for _module.Tree.Sum (revealed)
axiom 11 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, this: DatatypeType :: 
    { _module.Tree.Sum($LS($ly), this), $IsGoodHeap($Heap) } 
    _module.Tree.Sum#canCall(this)
         || (11 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          $Is(this, Tclass._module.Tree())
           && $IsAlloc(this, Tclass._module.Tree(), $Heap))
       ==> (!_module.Tree.Empty_q(this)
           ==> (var right#1 := _module.Tree.right(this); 
            (var left#1 := _module.Tree.left(this); 
              _module.Tree.Sum#canCall(left#1) && _module.Tree.Sum#canCall(right#1))))
         && _module.Tree.Sum($LS($ly), this)
           == (if _module.Tree.Empty_q(this)
             then 0
             else (var right#0 := _module.Tree.right(this); 
              (var left#0 := _module.Tree.left(this); 
                (var x#0 := _module.Tree.root(this); 
                  x#0 + _module.Tree.Sum($ly, left#0) + _module.Tree.Sum($ly, right#0))))));

// definition axiom for _module.Tree.Sum for all literals (revealed)
axiom 11 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, this: DatatypeType :: 
    {:weight 3} { _module.Tree.Sum($LS($ly), Lit(this)), $IsGoodHeap($Heap) } 
    _module.Tree.Sum#canCall(Lit(this))
         || (11 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          $Is(this, Tclass._module.Tree())
           && $IsAlloc(this, Tclass._module.Tree(), $Heap))
       ==> (!Lit(_module.Tree.Empty_q(Lit(this)))
           ==> (var right#3 := Lit(_module.Tree.right(Lit(this))); 
            (var left#3 := Lit(_module.Tree.left(Lit(this))); 
              _module.Tree.Sum#canCall(left#3) && _module.Tree.Sum#canCall(right#3))))
         && _module.Tree.Sum($LS($ly), Lit(this))
           == (if _module.Tree.Empty_q(Lit(this))
             then 0
             else (var right#2 := Lit(_module.Tree.right(Lit(this))); 
              (var left#2 := Lit(_module.Tree.left(Lit(this))); 
                (var x#2 := LitInt(_module.Tree.root(Lit(this))); 
                  LitInt(x#2 + _module.Tree.Sum($LS($ly), left#2) + _module.Tree.Sum($LS($ly), right#2)))))));

procedure CheckWellformed$$_module.Tree.Sum(this: DatatypeType
       where $Is(this, Tclass._module.Tree()) && $IsAlloc(this, Tclass._module.Tree(), $Heap));
  free requires 11 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Tree.Sum(this: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: int;
  var _mcc#1#0: DatatypeType;
  var _mcc#2#0: DatatypeType;
  var right#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var left#Z#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var x#Z#0: int;
  var let#2#0#0: int;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function Sum
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(466,11): initial state"} true;
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
        if (this == #_module.Tree.Empty())
        {
            assume _module.Tree.Sum($LS($LZ), this) == LitInt(0);
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.Tree.Sum($LS($LZ), this), TInt);
        }
        else if (this == #_module.Tree.Node(_mcc#0#0, _mcc#1#0, _mcc#2#0))
        {
            assume $Is(_mcc#1#0, Tclass._module.Tree());
            assume $Is(_mcc#2#0, Tclass._module.Tree());
            havoc right#Z#0;
            assume $Is(right#Z#0, Tclass._module.Tree());
            assume let#0#0#0 == _mcc#2#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.Tree());
            assume right#Z#0 == let#0#0#0;
            havoc left#Z#0;
            assume $Is(left#Z#0, Tclass._module.Tree());
            assume let#1#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#1#0#0, Tclass._module.Tree());
            assume left#Z#0 == let#1#0#0;
            havoc x#Z#0;
            assume true;
            assume let#2#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#2#0#0, TInt);
            assume x#Z#0 == let#2#0#0;
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(left#Z#0) < DtRank(this);
            assume _module.Tree.Sum#canCall(left#Z#0);
            b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(right#Z#0) < DtRank(this);
            assume _module.Tree.Sum#canCall(right#Z#0);
            assume _module.Tree.Sum($LS($LZ), this)
               == x#Z#0
                 + _module.Tree.Sum($LS($LZ), left#Z#0)
                 + _module.Tree.Sum($LS($LZ), right#Z#0);
            assume _module.Tree.Sum#canCall(left#Z#0) && _module.Tree.Sum#canCall(right#Z#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.Tree.Sum($LS($LZ), this), TInt);
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



procedure CheckWellformed$$_module.Tree.ComputeSum(this: DatatypeType
       where $Is(this, Tclass._module.Tree()) && $IsAlloc(this, Tclass._module.Tree(), $Heap), 
    n#0: int where LitInt(0) <= n#0)
   returns (s#0: int);
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Tree.ComputeSum(this: DatatypeType
       where $Is(this, Tclass._module.Tree()) && $IsAlloc(this, Tclass._module.Tree(), $Heap), 
    n#0: int where LitInt(0) <= n#0)
   returns (s#0: int);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Tree.ComputeSum(this: DatatypeType
       where $Is(this, Tclass._module.Tree()) && $IsAlloc(this, Tclass._module.Tree(), $Heap), 
    n#0: int where LitInt(0) <= n#0)
   returns (s#0: int, $_reverifyPost: bool);
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Tree.ComputeSum(this: DatatypeType, n#0: int) returns (s#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0_0: int;
  var _mcc#1#0_0: DatatypeType;
  var _mcc#2#0_0: DatatypeType;
  var right#0_0: DatatypeType;
  var let#0_0#0#0: DatatypeType;
  var left#0_0: DatatypeType;
  var let#0_1#0#0: DatatypeType;
  var x#0_0: int;
  var let#0_2#0#0: int;
  var l#0_0_0: int;
  var $rhs##0_0_0: int;
  var n##0_0_0: int;
  var r#0_0_0: int;
  var $rhs##0_0_1: int;
  var n##0_0_1: int;
  var $rhs##0_0: int;
  var n##0_0: int;

    // AddMethodImpl: ComputeSum, Impl$$_module.Tree.ComputeSum
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(476,2): initial state"} true;
    $_reverifyPost := false;
    assume true;
    havoc _mcc#0#0_0, _mcc#1#0_0, _mcc#2#0_0;
    if (this == #_module.Tree.Empty())
    {
        // ----- return statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(479,7)
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(479,7)
        assume true;
        assume true;
        s#0 := LitInt(0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(479,14)"} true;
        return;
    }
    else if (this == #_module.Tree.Node(_mcc#0#0_0, _mcc#1#0_0, _mcc#2#0_0))
    {
        assume $Is(_mcc#1#0_0, Tclass._module.Tree())
           && $IsAlloc(_mcc#1#0_0, Tclass._module.Tree(), $Heap);
        assume $Is(_mcc#2#0_0, Tclass._module.Tree())
           && $IsAlloc(_mcc#2#0_0, Tclass._module.Tree(), $Heap);
        havoc right#0_0;
        assume $Is(right#0_0, Tclass._module.Tree())
           && $IsAlloc(right#0_0, Tclass._module.Tree(), $Heap);
        assume let#0_0#0#0 == _mcc#2#0_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_0#0#0, Tclass._module.Tree());
        assume right#0_0 == let#0_0#0#0;
        havoc left#0_0;
        assume $Is(left#0_0, Tclass._module.Tree())
           && $IsAlloc(left#0_0, Tclass._module.Tree(), $Heap);
        assume let#0_1#0#0 == _mcc#1#0_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_1#0#0, Tclass._module.Tree());
        assume left#0_0 == let#0_1#0#0;
        havoc x#0_0;
        assume let#0_2#0#0 == _mcc#0#0_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_2#0#0, TInt);
        assume x#0_0 == let#0_2#0#0;
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(481,7)
        assume true;
        if (n#0 == LitInt(0))
        {
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(482,33)
            assume true;
            // TrCallStmt: Adding lhs with type int
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            assume true;
            // ProcessCallStmt: CheckSubrange
            assert $Is(LitInt(28), Tclass._System.nat());
            n##0_0_0 := LitInt(28);
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0 <= n#0 || DtRank(left#0_0) < DtRank(this) || n##0_0_0 == n#0;
            assert DtRank(left#0_0) < DtRank(this)
               || (DtRank(left#0_0) == DtRank(this) && n##0_0_0 < n#0);
            // ProcessCallStmt: Make the call
            call $rhs##0_0_0 := Call$$_module.Tree.ComputeSum(left#0_0, n##0_0_0);
            // TrCallStmt: After ProcessCallStmt
            l#0_0_0 := $rhs##0_0_0;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(482,36)"} true;
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(483,34)
            assume true;
            // TrCallStmt: Adding lhs with type int
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            assume true;
            // ProcessCallStmt: CheckSubrange
            assert $Is(LitInt(19), Tclass._System.nat());
            n##0_0_1 := LitInt(19);
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0 <= n#0 || DtRank(right#0_0) < DtRank(this) || n##0_0_1 == n#0;
            assert DtRank(right#0_0) < DtRank(this)
               || (DtRank(right#0_0) == DtRank(this) && n##0_0_1 < n#0);
            // ProcessCallStmt: Make the call
            call $rhs##0_0_1 := Call$$_module.Tree.ComputeSum(right#0_0, n##0_0_1);
            // TrCallStmt: After ProcessCallStmt
            r#0_0_0 := $rhs##0_0_1;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(483,37)"} true;
            // ----- return statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(484,9)
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(484,9)
            assume true;
            assume true;
            s#0 := x#0_0 + l#0_0_0 + r#0_0_0;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(484,24)"} true;
            return;
        }
        else
        {
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(486,24)
            assume true;
            // TrCallStmt: Adding lhs with type int
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            assume true;
            // ProcessCallStmt: CheckSubrange
            assert $Is(n#0 - 1, Tclass._System.nat());
            n##0_0 := n#0 - 1;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0 <= n#0 || DtRank(this) < DtRank(this) || n##0_0 == n#0;
            assert DtRank(this) < DtRank(this) || (DtRank(this) == DtRank(this) && n##0_0 < n#0);
            // ProcessCallStmt: Make the call
            call $rhs##0_0 := Call$$_module.Tree.ComputeSum(this, n##0_0);
            // TrCallStmt: After ProcessCallStmt
            s#0 := $rhs##0_0;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(486,30)"} true;
        }
    }
    else
    {
        assume false;
    }
}



procedure {:induction this} {:_induction this} CheckWellformed$$_module.Tree.EvensSumToEven(this: DatatypeType
       where $Is(this, Tclass._module.Tree()) && $IsAlloc(this, Tclass._module.Tree(), $Heap));
  free requires 32 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:induction this} {:_induction this} CheckWellformed$$_module.Tree.EvensSumToEven(this: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var u#0: int;

    // AddMethodImpl: EvensSumToEven, CheckWellformed$$_module.Tree.EvensSumToEven
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(490,26): initial state"} true;
    havoc u#0;
    assume true;
    if (*)
    {
        assume _module.Tree.Elements#canCall(this);
        assume Lit(_module.Tree.Elements($LS($LZ), this))[$Box(u#0)];
        assert LitInt(2) != 0;
        assume Mod(u#0, LitInt(2)) == LitInt(0);
    }
    else
    {
        assume Lit(_module.Tree.Elements($LS($LZ), this))[$Box(u#0)]
           ==> Mod(u#0, LitInt(2)) == LitInt(0);
    }

    assume (forall u#1: int :: 
      { _module.Tree.Elements($LS($LZ), this)[$Box(u#1)] } 
      true
         ==> 
        Lit(_module.Tree.Elements($LS($LZ), this))[$Box(u#1)]
         ==> Mod(u#1, LitInt(2)) == LitInt(0));
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(492,22): post-state"} true;
    assume _module.Tree.Sum#canCall(this);
    assert LitInt(2) != 0;
    assume LitInt(Mod(_module.Tree.Sum($LS($LZ), this), LitInt(2))) == LitInt(0);
}



procedure {:induction this} {:_induction this} Call$$_module.Tree.EvensSumToEven(this: DatatypeType
       where $Is(this, Tclass._module.Tree()) && $IsAlloc(this, Tclass._module.Tree(), $Heap));
  // user-defined preconditions
  requires (forall u#1: int :: 
    { _module.Tree.Elements($LS($LS($LZ)), this)[$Box(u#1)] } 
    true
       ==> 
      Lit(_module.Tree.Elements($LS($LS($LZ)), this))[$Box(u#1)]
       ==> Mod(u#1, LitInt(2)) == LitInt(0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Tree.Sum#canCall(this);
  ensures LitInt(Mod(_module.Tree.Sum($LS($LS($LZ)), this), LitInt(2))) == LitInt(0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:induction this} {:_induction this} Impl$$_module.Tree.EvensSumToEven(this: DatatypeType
       where $Is(this, Tclass._module.Tree()) && $IsAlloc(this, Tclass._module.Tree(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 32 == $FunctionContextHeight;
  // user-defined preconditions
  free requires (forall u#1: int :: 
    { _module.Tree.Elements($LS($LZ), this)[$Box(u#1)] } 
    true
       ==> 
      Lit(_module.Tree.Elements($LS($LZ), this))[$Box(u#1)]
       ==> Mod(u#1, LitInt(2)) == LitInt(0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Tree.Sum#canCall(this);
  ensures LitInt(Mod(_module.Tree.Sum($LS($LS($LZ)), this), LitInt(2))) == LitInt(0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:induction this} {:_induction this} Impl$$_module.Tree.EvensSumToEven(this: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var _mcc#0#0_0: int;
  var _mcc#1#0_0: DatatypeType;
  var _mcc#2#0_0: DatatypeType;
  var right#0_0: DatatypeType;
  var let#0_0#0#0: DatatypeType;
  var left#0_0: DatatypeType;
  var let#0_1#0#0: DatatypeType;
  var x#0_0: int;
  var let#0_2#0#0: int;

    // AddMethodImpl: EvensSumToEven, Impl$$_module.Tree.EvensSumToEven
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(494,2): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#this0#0: DatatypeType :: 
      $Is($ih#this0#0, Tclass._module.Tree())
           && (forall u#2: int :: 
            { _module.Tree.Elements($LS($LZ), $ih#this0#0)[$Box(u#2)] } 
            true
               ==> 
              Lit(_module.Tree.Elements($LS($LZ), $ih#this0#0))[$Box(u#2)]
               ==> Mod(u#2, LitInt(2)) == LitInt(0))
           && DtRank($ih#this0#0) < DtRank(this)
         ==> LitInt(Mod(_module.Tree.Sum($LS($LZ), this), LitInt(2))) == LitInt(0));
    $_reverifyPost := false;
    assume true;
    havoc _mcc#0#0_0, _mcc#1#0_0, _mcc#2#0_0;
    if (this == #_module.Tree.Empty())
    {
    }
    else if (this == #_module.Tree.Node(_mcc#0#0_0, _mcc#1#0_0, _mcc#2#0_0))
    {
        assume $Is(_mcc#1#0_0, Tclass._module.Tree());
        assume $Is(_mcc#2#0_0, Tclass._module.Tree());
        havoc right#0_0;
        assume $Is(right#0_0, Tclass._module.Tree())
           && $IsAlloc(right#0_0, Tclass._module.Tree(), $Heap);
        assume let#0_0#0#0 == _mcc#2#0_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_0#0#0, Tclass._module.Tree());
        assume right#0_0 == let#0_0#0#0;
        havoc left#0_0;
        assume $Is(left#0_0, Tclass._module.Tree())
           && $IsAlloc(left#0_0, Tclass._module.Tree(), $Heap);
        assume let#0_1#0#0 == _mcc#1#0_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_1#0#0, Tclass._module.Tree());
        assume left#0_0 == let#0_1#0#0;
        havoc x#0_0;
        assume let#0_2#0#0 == _mcc#0#0_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_2#0#0, TInt);
        assume x#0_0 == let#0_2#0#0;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(498,7)
        assume _module.Tree.Elements#canCall(this);
        assume _module.Tree.Elements#canCall(this);
        assert {:subsumption 0} Lit(_module.Tree.Elements($LS($LS($LZ)), this))[$Box(x#0_0)];
        assume Lit(_module.Tree.Elements($LS($LZ), this))[$Box(x#0_0)];
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(499,26)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assert DtRank(left#0_0) < DtRank(this);
        // ProcessCallStmt: Make the call
        call Call$$_module.Tree.EvensSumToEven(left#0_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(499,27)"} true;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(500,27)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assert DtRank(right#0_0) < DtRank(this);
        // ProcessCallStmt: Make the call
        call Call$$_module.Tree.EvensSumToEven(right#0_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(500,28)"} true;
    }
    else
    {
        assume false;
    }
}



procedure {:_induction this} CheckWellformed$$_module.Tree.EvensSumToEvenAutoInduction(this: DatatypeType
       where $Is(this, Tclass._module.Tree()) && $IsAlloc(this, Tclass._module.Tree(), $Heap));
  free requires 33 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:_induction this} CheckWellformed$$_module.Tree.EvensSumToEvenAutoInduction(this: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var u#0: int;

    // AddMethodImpl: EvensSumToEvenAutoInduction, CheckWellformed$$_module.Tree.EvensSumToEvenAutoInduction
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(503,8): initial state"} true;
    havoc u#0;
    assume true;
    if (*)
    {
        assume _module.Tree.Elements#canCall(this);
        assume Lit(_module.Tree.Elements($LS($LZ), this))[$Box(u#0)];
        assert LitInt(2) != 0;
        assume Mod(u#0, LitInt(2)) == LitInt(0);
    }
    else
    {
        assume Lit(_module.Tree.Elements($LS($LZ), this))[$Box(u#0)]
           ==> Mod(u#0, LitInt(2)) == LitInt(0);
    }

    assume (forall u#1: int :: 
      { _module.Tree.Elements($LS($LZ), this)[$Box(u#1)] } 
      true
         ==> 
        Lit(_module.Tree.Elements($LS($LZ), this))[$Box(u#1)]
         ==> Mod(u#1, LitInt(2)) == LitInt(0));
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(505,22): post-state"} true;
    assume _module.Tree.Sum#canCall(this);
    assert LitInt(2) != 0;
    assume LitInt(Mod(_module.Tree.Sum($LS($LZ), this), LitInt(2))) == LitInt(0);
}



procedure {:_induction this} Call$$_module.Tree.EvensSumToEvenAutoInduction(this: DatatypeType
       where $Is(this, Tclass._module.Tree()) && $IsAlloc(this, Tclass._module.Tree(), $Heap));
  // user-defined preconditions
  requires (forall u#1: int :: 
    { _module.Tree.Elements($LS($LS($LZ)), this)[$Box(u#1)] } 
    true
       ==> 
      Lit(_module.Tree.Elements($LS($LS($LZ)), this))[$Box(u#1)]
       ==> Mod(u#1, LitInt(2)) == LitInt(0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Tree.Sum#canCall(this);
  ensures LitInt(Mod(_module.Tree.Sum($LS($LS($LZ)), this), LitInt(2))) == LitInt(0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction this} Impl$$_module.Tree.EvensSumToEvenAutoInduction(this: DatatypeType
       where $Is(this, Tclass._module.Tree()) && $IsAlloc(this, Tclass._module.Tree(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 33 == $FunctionContextHeight;
  // user-defined preconditions
  free requires (forall u#1: int :: 
    { _module.Tree.Elements($LS($LZ), this)[$Box(u#1)] } 
    true
       ==> 
      Lit(_module.Tree.Elements($LS($LZ), this))[$Box(u#1)]
       ==> Mod(u#1, LitInt(2)) == LitInt(0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Tree.Sum#canCall(this);
  ensures LitInt(Mod(_module.Tree.Sum($LS($LS($LZ)), this), LitInt(2))) == LitInt(0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction this} Impl$$_module.Tree.EvensSumToEvenAutoInduction(this: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var _mcc#0#0_0: int;
  var _mcc#1#0_0: DatatypeType;
  var _mcc#2#0_0: DatatypeType;
  var right#0_0: DatatypeType;
  var let#0_0#0#0: DatatypeType;
  var left#0_0: DatatypeType;
  var let#0_1#0#0: DatatypeType;
  var x#0_0: int;
  var let#0_2#0#0: int;

    // AddMethodImpl: EvensSumToEvenAutoInduction, Impl$$_module.Tree.EvensSumToEvenAutoInduction
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(507,2): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#this0#0: DatatypeType :: 
      $Is($ih#this0#0, Tclass._module.Tree())
           && (forall u#2: int :: 
            { _module.Tree.Elements($LS($LZ), $ih#this0#0)[$Box(u#2)] } 
            true
               ==> 
              Lit(_module.Tree.Elements($LS($LZ), $ih#this0#0))[$Box(u#2)]
               ==> Mod(u#2, LitInt(2)) == LitInt(0))
           && DtRank($ih#this0#0) < DtRank(this)
         ==> LitInt(Mod(_module.Tree.Sum($LS($LZ), this), LitInt(2))) == LitInt(0));
    $_reverifyPost := false;
    assume true;
    havoc _mcc#0#0_0, _mcc#1#0_0, _mcc#2#0_0;
    if (this == #_module.Tree.Empty())
    {
    }
    else if (this == #_module.Tree.Node(_mcc#0#0_0, _mcc#1#0_0, _mcc#2#0_0))
    {
        assume $Is(_mcc#1#0_0, Tclass._module.Tree());
        assume $Is(_mcc#2#0_0, Tclass._module.Tree());
        havoc right#0_0;
        assume $Is(right#0_0, Tclass._module.Tree())
           && $IsAlloc(right#0_0, Tclass._module.Tree(), $Heap);
        assume let#0_0#0#0 == _mcc#2#0_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_0#0#0, Tclass._module.Tree());
        assume right#0_0 == let#0_0#0#0;
        havoc left#0_0;
        assume $Is(left#0_0, Tclass._module.Tree())
           && $IsAlloc(left#0_0, Tclass._module.Tree(), $Heap);
        assume let#0_1#0#0 == _mcc#1#0_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_1#0#0, Tclass._module.Tree());
        assume left#0_0 == let#0_1#0#0;
        havoc x#0_0;
        assume let#0_2#0#0 == _mcc#0#0_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_2#0#0, TInt);
        assume x#0_0 == let#0_2#0#0;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(511,7)
        assume _module.Tree.Elements#canCall(this);
        assume _module.Tree.Elements#canCall(this);
        assert {:subsumption 0} Lit(_module.Tree.Elements($LS($LS($LZ)), this))[$Box(x#0_0)];
        assume Lit(_module.Tree.Elements($LS($LZ), this))[$Box(x#0_0)];
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(512,39)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assert DtRank(left#0_0) < DtRank(this);
        // ProcessCallStmt: Make the call
        call Call$$_module.Tree.EvensSumToEvenAutoInduction(left#0_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(512,40)"} true;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(513,40)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assert DtRank(right#0_0) < DtRank(this);
        // ProcessCallStmt: Make the call
        call Call$$_module.Tree.EvensSumToEvenAutoInduction(right#0_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(513,41)"} true;
    }
    else
    {
        assume false;
    }
}



const #$ZOT: Ty;

const unique class._module.ZOT: ClassName;

procedure CheckWellformed$$_module.SubZOT(z#0: Box where $IsBox(z#0, #$ZOT));
  free requires 15 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.SubZOT(z#0: Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;


    // AddWellformednessCheck for subset type SubZOT
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(577,5): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume true;
    }
    else
    {
        assert false;
    }
}



function Tclass._module.SubZOT() : Ty;

const unique Tagclass._module.SubZOT: TyTag;

// Tclass._module.SubZOT Tag
axiom Tag(Tclass._module.SubZOT()) == Tagclass._module.SubZOT
   && TagFamily(Tclass._module.SubZOT()) == tytagFamily$SubZOT;

// _module.SubZOT: subset type $Is
axiom (forall z#0: Box :: 
  { $IsBox(z#0, Tclass._module.SubZOT()) } 
  $IsBox(z#0, Tclass._module.SubZOT()) <==> $IsBox(z#0, #$ZOT) && Lit(true));

// _module.SubZOT: subset type $IsAlloc
axiom (forall z#0: Box, $h: Heap :: 
  { $IsAllocBox(z#0, Tclass._module.SubZOT(), $h) } 
  $IsAllocBox(z#0, Tclass._module.SubZOT(), $h) <==> $IsAllocBox(z#0, #$ZOT, $h));

// Constructor function declaration
function #_module.Forever.More(DatatypeType) : DatatypeType;

const unique ##_module.Forever.More: DtCtorId;

// Constructor identifier
axiom (forall a#0#0#0: DatatypeType :: 
  { #_module.Forever.More(a#0#0#0) } 
  DatatypeCtorId(#_module.Forever.More(a#0#0#0)) == ##_module.Forever.More);

function _module.Forever.More_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Forever.More_q(d) } 
  _module.Forever.More_q(d) <==> DatatypeCtorId(d) == ##_module.Forever.More);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Forever.More_q(d) } 
  _module.Forever.More_q(d)
     ==> (exists a#1#0#0: DatatypeType :: d == #_module.Forever.More(a#1#0#0)));

function Tclass._module.Forever() : Ty;

const unique Tagclass._module.Forever: TyTag;

// Tclass._module.Forever Tag
axiom Tag(Tclass._module.Forever()) == Tagclass._module.Forever
   && TagFamily(Tclass._module.Forever()) == tytagFamily$Forever;

// Box/unbox axiom for Tclass._module.Forever
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Forever()) } 
  $IsBox(bx, Tclass._module.Forever())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Forever()));

// Constructor $Is
axiom (forall a#2#0#0: DatatypeType :: 
  { $Is(#_module.Forever.More(a#2#0#0), Tclass._module.Forever()) } 
  $Is(#_module.Forever.More(a#2#0#0), Tclass._module.Forever())
     <==> $Is(a#2#0#0, Tclass._module.Forever()));

// Constructor $IsAlloc
axiom (forall a#3#0#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#_module.Forever.More(a#3#0#0), Tclass._module.Forever(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Forever.More(a#3#0#0), Tclass._module.Forever(), $h)
       <==> $IsAlloc(a#3#0#0, Tclass._module.Forever(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Forever.next(d), Tclass._module.Forever(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.Forever.More_q(d)
       && $IsAlloc(d, Tclass._module.Forever(), $h)
     ==> $IsAlloc(_module.Forever.next(d), Tclass._module.Forever(), $h));

function _module.Forever.next(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#4#0#0: DatatypeType :: 
  { #_module.Forever.More(a#4#0#0) } 
  _module.Forever.next(#_module.Forever.More(a#4#0#0)) == a#4#0#0);

// Depth-one case-split function
function $IsA#_module.Forever(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.Forever(d) } 
  $IsA#_module.Forever(d) ==> _module.Forever.More_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.Forever.More_q(d), $Is(d, Tclass._module.Forever()) } 
  $Is(d, Tclass._module.Forever()) ==> _module.Forever.More_q(d));

function $Eq#_module.Forever(LayerType, DatatypeType, DatatypeType) : bool;

// Layered co-equality axiom
axiom (forall ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $Eq#_module.Forever($LS(ly), d0, d1) } 
  $Is(d0, Tclass._module.Forever()) && $Is(d1, Tclass._module.Forever())
     ==> ($Eq#_module.Forever($LS(ly), d0, d1)
       <==> _module.Forever.More_q(d0)
         && _module.Forever.More_q(d1)
         && (_module.Forever.More_q(d0) && _module.Forever.More_q(d1)
           ==> $Eq#_module.Forever(ly, _module.Forever.next(d0), _module.Forever.next(d1)))));

// Unbump layer co-equality axiom
axiom (forall ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $Eq#_module.Forever($LS(ly), d0, d1) } 
  $Eq#_module.Forever($LS(ly), d0, d1) <==> $Eq#_module.Forever(ly, d0, d1));

// Equality for codatatypes
axiom (forall ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $Eq#_module.Forever($LS(ly), d0, d1) } 
  $Eq#_module.Forever($LS(ly), d0, d1) <==> d0 == d1);

function $PrefixEq#_module.Forever(Box, LayerType, DatatypeType, DatatypeType) : bool;

// Layered co-equality axiom
axiom (forall k: Box, ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $PrefixEq#_module.Forever(k, $LS(ly), d0, d1) } 
  $Is(d0, Tclass._module.Forever()) && $Is(d1, Tclass._module.Forever())
     ==> ($PrefixEq#_module.Forever(k, $LS(ly), d0, d1)
       <==> (0 < ORD#Offset(k)
           ==> _module.Forever.More_q(d0)
             && _module.Forever.More_q(d1)
             && (_module.Forever.More_q(d0) && _module.Forever.More_q(d1)
               ==> $PrefixEq#_module.Forever(ORD#Minus(k, ORD#FromNat(1)), 
                ly, 
                _module.Forever.next(d0), 
                _module.Forever.next(d1))))
         && (k != ORD#FromNat(0) && ORD#IsLimit(k) ==> $Eq#_module.Forever(ly, d0, d1))));

// Unbump layer co-equality axiom
axiom (forall k: Box, ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $PrefixEq#_module.Forever(k, $LS(ly), d0, d1) } 
  k != ORD#FromNat(0)
     ==> ($PrefixEq#_module.Forever(k, $LS(ly), d0, d1)
       <==> $PrefixEq#_module.Forever(k, ly, d0, d1)));

// Coequality and prefix equality connection
axiom (forall ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $Eq#_module.Forever($LS(ly), d0, d1) } 
  $Eq#_module.Forever($LS(ly), d0, d1)
     <==> (forall k: Box :: 
      { $PrefixEq#_module.Forever(k, $LS(ly), d0, d1) } 
      $PrefixEq#_module.Forever(k, $LS(ly), d0, d1)));

// Coequality and prefix equality connection
axiom (forall ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $Eq#_module.Forever($LS(ly), d0, d1) } 
  (forall k: int :: 
      { $PrefixEq#_module.Forever(ORD#FromNat(k), $LS(ly), d0, d1) } 
      0 <= k ==> $PrefixEq#_module.Forever(ORD#FromNat(k), $LS(ly), d0, d1))
     ==> $Eq#_module.Forever($LS(ly), d0, d1));

// Prefix equality consequence
axiom (forall k: Box, ly: LayerType, d0: DatatypeType, d1: DatatypeType, m: Box :: 
  { $PrefixEq#_module.Forever(k, $LS(ly), d0, d1), $PrefixEq#_module.Forever(m, $LS(ly), d0, d1) } 
  ORD#Less(k, m) && $PrefixEq#_module.Forever(m, $LS(ly), d0, d1)
     ==> $PrefixEq#_module.Forever(k, $LS(ly), d0, d1));

// Prefix equality shortcut
axiom (forall k: Box, ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $PrefixEq#_module.Forever(k, $LS(ly), d0, d1) } 
  d0 == d1 ==> $PrefixEq#_module.Forever(k, $LS(ly), d0, d1));

const unique class._module.Forever: ClassName;

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

procedure CheckWellformed$$_module.__default.FailureToProveTermination0(N#0: int);
  free requires 39 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.FailureToProveTermination0(N#0: int);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.FailureToProveTermination0(N#0: int) returns ($_reverifyPost: bool);
  free requires 39 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.FailureToProveTermination0(N#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var n#0: int;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var $decr$loop#00: int;

    // AddMethodImpl: FailureToProveTermination0, Impl$$_module.__default.FailureToProveTermination0
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(106,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(107,9)
    assume true;
    assume true;
    n#0 := N#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(107,12)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(108,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := 100 - n#0;
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
      free invariant 100 - n#0 <= $decr_init$loop#00 && (100 - n#0 == $decr_init$loop#00 ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(108,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assume true;
            assume false;
        }

        assume true;
        if (100 <= n#0)
        {
            break;
        }

        $decr$loop#00 := 100 - n#0;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(109,7)
        assume true;
        assume true;
        n#0 := n#0 - 1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(109,14)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(108,3)
        assert 0 <= $decr$loop#00 || 100 - n#0 == $decr$loop#00;
        assert 100 - n#0 < $decr$loop#00;
    }
}



procedure CheckWellformed$$_module.__default.FailureToProveTermination1(x#0: int, y#0: int, N#0: int);
  free requires 40 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.FailureToProveTermination1(x#0: int, y#0: int, N#0: int);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.FailureToProveTermination1(x#0: int, y#0: int, N#0: int) returns ($_reverifyPost: bool);
  free requires 40 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.FailureToProveTermination1(x#0: int, y#0: int, N#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var n#0: int;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var $decr$loop#00: int;

    // AddMethodImpl: FailureToProveTermination1, Impl$$_module.__default.FailureToProveTermination1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(114,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(115,9)
    assume true;
    assume true;
    n#0 := N#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(115,12)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(116,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := y#0 - x#0;
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
      free invariant y#0 - x#0 <= $decr_init$loop#00 && (y#0 - x#0 == $decr_init$loop#00 ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(116,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assume true;
            assume false;
        }

        if (x#0 < y#0)
        {
        }

        assume true;
        if (!(x#0 < y#0 && n#0 < 100))
        {
            break;
        }

        $decr$loop#00 := y#0 - x#0;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(118,7)
        assume true;
        assume true;
        n#0 := n#0 + 1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(118,14)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(116,3)
        assert 0 <= $decr$loop#00 || y#0 - x#0 == $decr$loop#00;
        assert y#0 - x#0 < $decr$loop#00;
    }
}



procedure CheckWellformed$$_module.__default.FailureToProveTermination2(x#0: int, y#0: int, N#0: int);
  free requires 41 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.FailureToProveTermination2(x#0: int, y#0: int, N#0: int);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.FailureToProveTermination2(x#0: int, y#0: int, N#0: int) returns ($_reverifyPost: bool);
  free requires 41 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.FailureToProveTermination2(x#0: int, y#0: int, N#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var n#0: int;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var $decr$loop#00: int;

    // AddMethodImpl: FailureToProveTermination2, Impl$$_module.__default.FailureToProveTermination2
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(123,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(124,9)
    assume true;
    assume true;
    n#0 := N#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(124,12)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(125,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := n#0 - x#0;
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
      free invariant n#0 - x#0 <= $decr_init$loop#00 && (n#0 - x#0 == $decr_init$loop#00 ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(125,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assume true;
            assume false;
        }

        if (x#0 < y#0)
        {
        }

        assume true;
        if (!(x#0 < y#0 && n#0 < 100))
        {
            break;
        }

        $decr$loop#00 := n#0 - x#0;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(128,7)
        assume true;
        assume true;
        n#0 := n#0 + 1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(128,14)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(125,3)
        assert 0 <= $decr$loop#00 || n#0 - x#0 == $decr$loop#00;
        assert n#0 - x#0 < $decr$loop#00;
    }
}



procedure CheckWellformed$$_module.__default.FailureToProveTermination3(x#0: int, y#0: int, N#0: int);
  free requires 42 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.FailureToProveTermination3(x#0: int, y#0: int, N#0: int);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.FailureToProveTermination3(x#0: int, y#0: int, N#0: int) returns ($_reverifyPost: bool);
  free requires 42 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.FailureToProveTermination3(x#0: int, y#0: int, N#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var n#0: int;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var $decr$loop#00: int;

    // AddMethodImpl: FailureToProveTermination3, Impl$$_module.__default.FailureToProveTermination3
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(133,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(134,9)
    assume true;
    assume true;
    n#0 := N#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(134,12)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(135,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := 100 - n#0;
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
      free invariant 100 - n#0 <= $decr_init$loop#00 && (100 - n#0 == $decr_init$loop#00 ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(135,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assume true;
            assume false;
        }

        if (x#0 < y#0)
        {
        }

        assume true;
        if (!(x#0 < y#0 && n#0 < 100))
        {
            break;
        }

        $decr$loop#00 := 100 - n#0;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(138,7)
        assume true;
        assume true;
        n#0 := n#0 + 1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(138,14)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(135,3)
        assert 0 <= $decr$loop#00 || 100 - n#0 == $decr$loop#00;
        assert 100 - n#0 < $decr$loop#00;
    }
}



procedure CheckWellformed$$_module.__default.FailureToProveTermination4(x#0: int, y#0: int, N#0: int);
  free requires 43 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.FailureToProveTermination4(x#0: int, y#0: int, N#0: int);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.FailureToProveTermination4(x#0: int, y#0: int, N#0: int) returns ($_reverifyPost: bool);
  free requires 43 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.FailureToProveTermination4(x#0: int, y#0: int, N#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var n#0: int;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var $decr$loop#00: int;

    // AddMethodImpl: FailureToProveTermination4, Impl$$_module.__default.FailureToProveTermination4
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(143,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(144,9)
    assume true;
    assume true;
    n#0 := N#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(144,12)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(145,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := 100 - n#0;
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
      free invariant 100 - n#0 <= $decr_init$loop#00 && (100 - n#0 == $decr_init$loop#00 ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(145,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assume true;
            assume false;
        }

        if (n#0 < 100)
        {
        }

        assume true;
        if (!(n#0 < 100 && x#0 < y#0))
        {
            break;
        }

        $decr$loop#00 := 100 - n#0;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(148,7)
        assume true;
        assume true;
        n#0 := n#0 + 1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(148,14)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(145,3)
        assert 0 <= $decr$loop#00 || 100 - n#0 == $decr$loop#00;
        assert 100 - n#0 < $decr$loop#00;
    }
}



procedure CheckWellformed$$_module.__default.FailureToProveTermination5(b#0: bool, N#0: int);
  free requires 44 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.FailureToProveTermination5(b#0: bool, N#0: int);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.FailureToProveTermination5(b#0: bool, N#0: int) returns ($_reverifyPost: bool);
  free requires 44 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.FailureToProveTermination5(b#0: bool, N#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var n#0: int;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var $decr$loop#00: int;

    // AddMethodImpl: FailureToProveTermination5, Impl$$_module.__default.FailureToProveTermination5
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(153,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(154,9)
    assume true;
    assume true;
    n#0 := N#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(154,12)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(155,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := (if b#0 then 100 - n#0 else 0 - 1);
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
      free invariant (if b#0 then 100 - n#0 else 0 - 1) <= $decr_init$loop#00
         && ((if b#0 then 100 - n#0 else 0 - 1) == $decr_init$loop#00 ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(155,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            if (b#0)
            {
            }
            else
            {
            }

            assume true;
            assume false;
        }

        if (b#0)
        {
        }

        assume true;
        if (!(b#0 && n#0 < 100))
        {
            break;
        }

        $decr$loop#00 := (if b#0 then 100 - n#0 else 0 - 1);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(157,7)
        assume true;
        assume true;
        n#0 := n#0 + 1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(157,14)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(155,3)
        assert 0 <= $decr$loop#00 || (if b#0 then 100 - n#0 else 0 - 1) == $decr$loop#00;
        assert (if b#0 then 100 - n#0 else 0 - 1) < $decr$loop#00;
    }
}



procedure CheckWellformed$$_module.__default.DecreasesYieldsAnInvariant(z#0: int);
  free requires 45 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.DecreasesYieldsAnInvariant(z#0: int);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.DecreasesYieldsAnInvariant(z#0: int) returns ($_reverifyPost: bool);
  free requires 45 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.DecreasesYieldsAnInvariant(z#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var x#0: int;
  var y#0: int;
  var z#1: int;
  var $Heap_at_0: Heap;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var $decr$loop#00: int;

    // AddMethodImpl: DecreasesYieldsAnInvariant, Impl$$_module.__default.DecreasesYieldsAnInvariant
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(180,42): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(181,9)
    assume true;
    assume true;
    x#0 := LitInt(100);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(181,14)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(182,9)
    assume true;
    assume true;
    y#0 := LitInt(1);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(182,12)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(183,9)
    assume true;
    assume true;
    z#1 := z#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(183,12)"} true;
    $Heap_at_0 := $Heap;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(184,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := (if x#0 <= y#0 then y#0 - x#0 else x#0 - y#0);
    havoc $w$loop#0;
    while (true)
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> (0 < x#0 && 0 < y#0) || (x#0 < 0 && y#0 < 0);
      free invariant (forall $o: ref :: 
        { $Heap[$o] } 
        $o != null && read(old($Heap), $o, alloc)
           ==> $Heap[$o] == $PreLoopHeap$loop#0[$o]);
      free invariant $HeapSucc($PreLoopHeap$loop#0, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
        { read($Heap, $o, $f) } 
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
      free invariant (if x#0 <= y#0 then y#0 - x#0 else x#0 - y#0) <= $decr_init$loop#00
         && ((if x#0 <= y#0 then y#0 - x#0 else x#0 - y#0) == $decr_init$loop#00 ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(184,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            if (0 < x#0)
            {
            }

            if (!(0 < x#0 && 0 < y#0))
            {
                if (x#0 < 0)
                {
                }
            }

            assume true;
            assume (0 < x#0 && 0 < y#0) || (x#0 < 0 && y#0 < 0);
            if (x#0 <= y#0)
            {
            }
            else
            {
            }

            assume true;
            assume false;
        }

        assume true;
        if (x#0 == y#0)
        {
            break;
        }

        $decr$loop#00 := (if x#0 <= y#0 then y#0 - x#0 else x#0 - y#0);
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(188,5)
        assume true;
        if (z#1 == LitInt(52))
        {
            // ----- break statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(189,7)
            goto after_0;
        }
        else
        {
            // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(190,12)
            assume true;
            if (x#0 < y#0)
            {
                // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(191,9)
                assume true;
                assume true;
                y#0 := y#0 - 1;
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(191,16)"} true;
            }
            else
            {
                // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(193,9)
                assume true;
                assume true;
                x#0 := x#0 - 1;
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(193,16)"} true;
            }
        }

        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(195,7)
        assume true;
        assume true;
        x#0 := 0 - x#0;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(195,11)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(196,7)
        assume true;
        assume true;
        y#0 := 0 - y#0;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(196,11)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(197,7)
        assume true;
        assume true;
        z#1 := z#1 + 1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(197,14)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(184,3)
        assert 0 <= $decr$loop#00
           || (if x#0 <= y#0 then y#0 - x#0 else x#0 - y#0) == $decr$loop#00;
        assert (if x#0 <= y#0 then y#0 - x#0 else x#0 - y#0) < $decr$loop#00;
        assume true;
    }

  after_0:
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(199,3)
    assume true;
    assert x#0 - y#0 < 100;
}



// function declaration for _module._default.Zipper0
function _module.__default.Zipper0(_module._default.Zipper0$T: Ty, 
    $ly: LayerType, 
    a#0: DatatypeType, 
    b#0: DatatypeType)
   : DatatypeType;

function _module.__default.Zipper0#canCall(_module._default.Zipper0$T: Ty, a#0: DatatypeType, b#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall _module._default.Zipper0$T: Ty, 
    $ly: LayerType, 
    a#0: DatatypeType, 
    b#0: DatatypeType :: 
  { _module.__default.Zipper0(_module._default.Zipper0$T, $LS($ly), a#0, b#0) } 
  _module.__default.Zipper0(_module._default.Zipper0$T, $LS($ly), a#0, b#0)
     == _module.__default.Zipper0(_module._default.Zipper0$T, $ly, a#0, b#0));

// fuel synonym axiom
axiom (forall _module._default.Zipper0$T: Ty, 
    $ly: LayerType, 
    a#0: DatatypeType, 
    b#0: DatatypeType :: 
  { _module.__default.Zipper0(_module._default.Zipper0$T, AsFuelBottom($ly), a#0, b#0) } 
  _module.__default.Zipper0(_module._default.Zipper0$T, $ly, a#0, b#0)
     == _module.__default.Zipper0(_module._default.Zipper0$T, $LZ, a#0, b#0));

// consequence axiom for _module.__default.Zipper0
axiom 7 <= $FunctionContextHeight
   ==> (forall _module._default.Zipper0$T: Ty, 
      $ly: LayerType, 
      a#0: DatatypeType, 
      b#0: DatatypeType :: 
    { _module.__default.Zipper0(_module._default.Zipper0$T, $ly, a#0, b#0) } 
    _module.__default.Zipper0#canCall(_module._default.Zipper0$T, a#0, b#0)
         || (7 != $FunctionContextHeight
           && 
          $Is(a#0, Tclass._module.List(_module._default.Zipper0$T))
           && $Is(b#0, Tclass._module.List(_module._default.Zipper0$T)))
       ==> $Is(_module.__default.Zipper0(_module._default.Zipper0$T, $ly, a#0, b#0), 
        Tclass._module.List(_module._default.Zipper0$T)));

function _module.__default.Zipper0#requires(Ty, LayerType, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.Zipper0
axiom (forall _module._default.Zipper0$T: Ty, 
    $ly: LayerType, 
    a#0: DatatypeType, 
    b#0: DatatypeType :: 
  { _module.__default.Zipper0#requires(_module._default.Zipper0$T, $ly, a#0, b#0) } 
  $Is(a#0, Tclass._module.List(_module._default.Zipper0$T))
       && $Is(b#0, Tclass._module.List(_module._default.Zipper0$T))
     ==> _module.__default.Zipper0#requires(_module._default.Zipper0$T, $ly, a#0, b#0)
       == true);

// definition axiom for _module.__default.Zipper0 (revealed)
axiom 7 <= $FunctionContextHeight
   ==> (forall _module._default.Zipper0$T: Ty, 
      $ly: LayerType, 
      a#0: DatatypeType, 
      b#0: DatatypeType :: 
    { _module.__default.Zipper0(_module._default.Zipper0$T, $LS($ly), a#0, b#0) } 
    _module.__default.Zipper0#canCall(_module._default.Zipper0$T, a#0, b#0)
         || (7 != $FunctionContextHeight
           && 
          $Is(a#0, Tclass._module.List(_module._default.Zipper0$T))
           && $Is(b#0, Tclass._module.List(_module._default.Zipper0$T)))
       ==> (!_module.List.Nil_q(a#0)
           ==> (var c#1 := _module.List._h1(a#0); 
            _module.__default.Zipper0#canCall(_module._default.Zipper0$T, b#0, c#1)))
         && _module.__default.Zipper0(_module._default.Zipper0$T, $LS($ly), a#0, b#0)
           == (if _module.List.Nil_q(a#0)
             then b#0
             else (var c#0 := _module.List._h1(a#0); 
              (var x#0 := _module.List._h0(a#0); 
                #_module.List.Cons(x#0, _module.__default.Zipper0(_module._default.Zipper0$T, $ly, b#0, c#0))))));

// definition axiom for _module.__default.Zipper0 for all literals (revealed)
axiom 7 <= $FunctionContextHeight
   ==> (forall _module._default.Zipper0$T: Ty, 
      $ly: LayerType, 
      a#0: DatatypeType, 
      b#0: DatatypeType :: 
    {:weight 3} { _module.__default.Zipper0(_module._default.Zipper0$T, $LS($ly), Lit(a#0), Lit(b#0)) } 
    _module.__default.Zipper0#canCall(_module._default.Zipper0$T, Lit(a#0), Lit(b#0))
         || (7 != $FunctionContextHeight
           && 
          $Is(a#0, Tclass._module.List(_module._default.Zipper0$T))
           && $Is(b#0, Tclass._module.List(_module._default.Zipper0$T)))
       ==> (!Lit(_module.List.Nil_q(Lit(a#0)))
           ==> (var c#3 := Lit(_module.List._h1(Lit(a#0))); 
            _module.__default.Zipper0#canCall(_module._default.Zipper0$T, Lit(b#0), c#3)))
         && _module.__default.Zipper0(_module._default.Zipper0$T, $LS($ly), Lit(a#0), Lit(b#0))
           == (if _module.List.Nil_q(Lit(a#0))
             then b#0
             else (var c#2 := Lit(_module.List._h1(Lit(a#0))); 
              (var x#2 := Lit(_module.List._h0(Lit(a#0))); 
                Lit(#_module.List.Cons(x#2, 
                    Lit(_module.__default.Zipper0(_module._default.Zipper0$T, $LS($ly), Lit(b#0), c#2))))))));

procedure CheckWellformed$$_module.__default.Zipper0(_module._default.Zipper0$T: Ty, 
    a#0: DatatypeType
       where $Is(a#0, Tclass._module.List(_module._default.Zipper0$T)), 
    b#0: DatatypeType
       where $Is(b#0, Tclass._module.List(_module._default.Zipper0$T)));
  free requires 7 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Zipper0(_module._default.Zipper0$T: Ty, a#0: DatatypeType, b#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: Box;
  var _mcc#1#0: DatatypeType;
  var c#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var x#Z#0: Box;
  var let#1#0#0: Box;
  var ##a#0: DatatypeType;
  var ##b#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function Zipper0
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(251,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.Zipper0(_module._default.Zipper0$T, $LS($LZ), a#0, b#0), 
          Tclass._module.List(_module._default.Zipper0$T));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (a#0 == #_module.List.Nil())
        {
            assume _module.__default.Zipper0(_module._default.Zipper0$T, $LS($LZ), a#0, b#0) == b#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.Zipper0(_module._default.Zipper0$T, $LS($LZ), a#0, b#0), 
              Tclass._module.List(_module._default.Zipper0$T));
        }
        else if (a#0 == #_module.List.Cons(_mcc#0#0, _mcc#1#0))
        {
            assume $IsBox(_mcc#0#0, _module._default.Zipper0$T);
            assume $Is(_mcc#1#0, Tclass._module.List(_module._default.Zipper0$T));
            havoc c#Z#0;
            assume $Is(c#Z#0, Tclass._module.List(_module._default.Zipper0$T));
            assume let#0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.List(_module._default.Zipper0$T));
            assume c#Z#0 == let#0#0#0;
            havoc x#Z#0;
            assume $IsBox(x#Z#0, _module._default.Zipper0$T);
            assume let#1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $IsBox(let#1#0#0, _module._default.Zipper0$T);
            assume x#Z#0 == let#1#0#0;
            ##a#0 := b#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##a#0, Tclass._module.List(_module._default.Zipper0$T), $Heap);
            ##b#0 := c#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#0, Tclass._module.List(_module._default.Zipper0$T), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(##a#0) < DtRank(a#0)
               || (DtRank(##a#0) == DtRank(a#0) && DtRank(##b#0) < DtRank(b#0));
            assume _module.__default.Zipper0#canCall(_module._default.Zipper0$T, b#0, c#Z#0);
            assume _module.__default.Zipper0(_module._default.Zipper0$T, $LS($LZ), a#0, b#0)
               == #_module.List.Cons(x#Z#0, 
                _module.__default.Zipper0(_module._default.Zipper0$T, $LS($LZ), b#0, c#Z#0));
            assume _module.__default.Zipper0#canCall(_module._default.Zipper0$T, b#0, c#Z#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.Zipper0(_module._default.Zipper0$T, $LS($LZ), a#0, b#0), 
              Tclass._module.List(_module._default.Zipper0$T));
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
    }
}



// function declaration for _module._default.Zipper1
function _module.__default.Zipper1(_module._default.Zipper1$T: Ty, 
    $ly: LayerType, 
    a#0: DatatypeType, 
    b#0: DatatypeType, 
    k#0: bool)
   : DatatypeType;

function _module.__default.Zipper1#canCall(_module._default.Zipper1$T: Ty, a#0: DatatypeType, b#0: DatatypeType, k#0: bool)
   : bool;

// layer synonym axiom
axiom (forall _module._default.Zipper1$T: Ty, 
    $ly: LayerType, 
    a#0: DatatypeType, 
    b#0: DatatypeType, 
    k#0: bool :: 
  { _module.__default.Zipper1(_module._default.Zipper1$T, $LS($ly), a#0, b#0, k#0) } 
  _module.__default.Zipper1(_module._default.Zipper1$T, $LS($ly), a#0, b#0, k#0)
     == _module.__default.Zipper1(_module._default.Zipper1$T, $ly, a#0, b#0, k#0));

// fuel synonym axiom
axiom (forall _module._default.Zipper1$T: Ty, 
    $ly: LayerType, 
    a#0: DatatypeType, 
    b#0: DatatypeType, 
    k#0: bool :: 
  { _module.__default.Zipper1(_module._default.Zipper1$T, AsFuelBottom($ly), a#0, b#0, k#0) } 
  _module.__default.Zipper1(_module._default.Zipper1$T, $ly, a#0, b#0, k#0)
     == _module.__default.Zipper1(_module._default.Zipper1$T, $LZ, a#0, b#0, k#0));

// consequence axiom for _module.__default.Zipper1
axiom 8 <= $FunctionContextHeight
   ==> (forall _module._default.Zipper1$T: Ty, 
      $ly: LayerType, 
      a#0: DatatypeType, 
      b#0: DatatypeType, 
      k#0: bool :: 
    { _module.__default.Zipper1(_module._default.Zipper1$T, $ly, a#0, b#0, k#0) } 
    _module.__default.Zipper1#canCall(_module._default.Zipper1$T, a#0, b#0, k#0)
         || (8 != $FunctionContextHeight
           && 
          $Is(a#0, Tclass._module.List(_module._default.Zipper1$T))
           && $Is(b#0, Tclass._module.List(_module._default.Zipper1$T)))
       ==> $Is(_module.__default.Zipper1(_module._default.Zipper1$T, $ly, a#0, b#0, k#0), 
        Tclass._module.List(_module._default.Zipper1$T)));

function _module.__default.Zipper1#requires(Ty, LayerType, DatatypeType, DatatypeType, bool) : bool;

// #requires axiom for _module.__default.Zipper1
axiom (forall _module._default.Zipper1$T: Ty, 
    $ly: LayerType, 
    a#0: DatatypeType, 
    b#0: DatatypeType, 
    k#0: bool :: 
  { _module.__default.Zipper1#requires(_module._default.Zipper1$T, $ly, a#0, b#0, k#0) } 
  $Is(a#0, Tclass._module.List(_module._default.Zipper1$T))
       && $Is(b#0, Tclass._module.List(_module._default.Zipper1$T))
     ==> _module.__default.Zipper1#requires(_module._default.Zipper1$T, $ly, a#0, b#0, k#0)
       == true);

// definition axiom for _module.__default.Zipper1 (revealed)
axiom 8 <= $FunctionContextHeight
   ==> (forall _module._default.Zipper1$T: Ty, 
      $ly: LayerType, 
      a#0: DatatypeType, 
      b#0: DatatypeType, 
      k#0: bool :: 
    { _module.__default.Zipper1(_module._default.Zipper1$T, $LS($ly), a#0, b#0, k#0) } 
    _module.__default.Zipper1#canCall(_module._default.Zipper1$T, a#0, b#0, k#0)
         || (8 != $FunctionContextHeight
           && 
          $Is(a#0, Tclass._module.List(_module._default.Zipper1$T))
           && $Is(b#0, Tclass._module.List(_module._default.Zipper1$T)))
       ==> (!_module.List.Nil_q(a#0)
           ==> (var c#1 := _module.List._h1(a#0); 
            _module.__default.Zipper1#canCall(_module._default.Zipper1$T, b#0, c#1, !k#0)))
         && _module.__default.Zipper1(_module._default.Zipper1$T, $LS($ly), a#0, b#0, k#0)
           == (if _module.List.Nil_q(a#0)
             then b#0
             else (var c#0 := _module.List._h1(a#0); 
              (var x#0 := _module.List._h0(a#0); 
                #_module.List.Cons(x#0, _module.__default.Zipper1(_module._default.Zipper1$T, $ly, b#0, c#0, !k#0))))));

// definition axiom for _module.__default.Zipper1 for all literals (revealed)
axiom 8 <= $FunctionContextHeight
   ==> (forall _module._default.Zipper1$T: Ty, 
      $ly: LayerType, 
      a#0: DatatypeType, 
      b#0: DatatypeType, 
      k#0: bool :: 
    {:weight 3} { _module.__default.Zipper1(_module._default.Zipper1$T, $LS($ly), Lit(a#0), Lit(b#0), Lit(k#0)) } 
    _module.__default.Zipper1#canCall(_module._default.Zipper1$T, Lit(a#0), Lit(b#0), Lit(k#0))
         || (8 != $FunctionContextHeight
           && 
          $Is(a#0, Tclass._module.List(_module._default.Zipper1$T))
           && $Is(b#0, Tclass._module.List(_module._default.Zipper1$T)))
       ==> (!Lit(_module.List.Nil_q(Lit(a#0)))
           ==> (var c#3 := Lit(_module.List._h1(Lit(a#0))); 
            _module.__default.Zipper1#canCall(_module._default.Zipper1$T, Lit(b#0), c#3, !Lit(k#0))))
         && _module.__default.Zipper1(_module._default.Zipper1$T, $LS($ly), Lit(a#0), Lit(b#0), Lit(k#0))
           == (if _module.List.Nil_q(Lit(a#0))
             then b#0
             else (var c#2 := Lit(_module.List._h1(Lit(a#0))); 
              (var x#2 := Lit(_module.List._h0(Lit(a#0))); 
                #_module.List.Cons(x#2, 
                  _module.__default.Zipper1(_module._default.Zipper1$T, $LS($ly), Lit(b#0), c#2, !Lit(k#0)))))));

procedure CheckWellformed$$_module.__default.Zipper1(_module._default.Zipper1$T: Ty, 
    a#0: DatatypeType
       where $Is(a#0, Tclass._module.List(_module._default.Zipper1$T)), 
    b#0: DatatypeType
       where $Is(b#0, Tclass._module.List(_module._default.Zipper1$T)), 
    k#0: bool);
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Zipper1(_module._default.Zipper1$T: Ty, a#0: DatatypeType, b#0: DatatypeType, k#0: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: Box;
  var _mcc#1#0: DatatypeType;
  var c#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var x#Z#0: Box;
  var let#1#0#0: Box;
  var ##a#0: DatatypeType;
  var ##b#0: DatatypeType;
  var ##k#0: bool;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function Zipper1
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(258,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (k#0)
    {
    }
    else
    {
    }

    if (k#0)
    {
    }
    else
    {
    }

    if (*)
    {
        assume $Is(_module.__default.Zipper1(_module._default.Zipper1$T, $LS($LZ), a#0, b#0, k#0), 
          Tclass._module.List(_module._default.Zipper1$T));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (a#0 == #_module.List.Nil())
        {
            assume _module.__default.Zipper1(_module._default.Zipper1$T, $LS($LZ), a#0, b#0, k#0)
               == b#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.Zipper1(_module._default.Zipper1$T, $LS($LZ), a#0, b#0, k#0), 
              Tclass._module.List(_module._default.Zipper1$T));
        }
        else if (a#0 == #_module.List.Cons(_mcc#0#0, _mcc#1#0))
        {
            assume $IsBox(_mcc#0#0, _module._default.Zipper1$T);
            assume $Is(_mcc#1#0, Tclass._module.List(_module._default.Zipper1$T));
            havoc c#Z#0;
            assume $Is(c#Z#0, Tclass._module.List(_module._default.Zipper1$T));
            assume let#0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.List(_module._default.Zipper1$T));
            assume c#Z#0 == let#0#0#0;
            havoc x#Z#0;
            assume $IsBox(x#Z#0, _module._default.Zipper1$T);
            assume let#1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $IsBox(let#1#0#0, _module._default.Zipper1$T);
            assume x#Z#0 == let#1#0#0;
            ##a#0 := b#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##a#0, Tclass._module.List(_module._default.Zipper1$T), $Heap);
            ##b#0 := c#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#0, Tclass._module.List(_module._default.Zipper1$T), $Heap);
            ##k#0 := !k#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##k#0, TBool, $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank((if ##k#0 then ##a#0 else ##b#0)) < DtRank((if k#0 then a#0 else b#0))
               || (DtRank((if ##k#0 then ##a#0 else ##b#0)) == DtRank((if k#0 then a#0 else b#0))
                 && DtRank((if ##k#0 then ##b#0 else ##a#0)) < DtRank((if k#0 then b#0 else a#0)));
            assume _module.__default.Zipper1#canCall(_module._default.Zipper1$T, b#0, c#Z#0, !k#0);
            assume _module.__default.Zipper1(_module._default.Zipper1$T, $LS($LZ), a#0, b#0, k#0)
               == #_module.List.Cons(x#Z#0, 
                _module.__default.Zipper1(_module._default.Zipper1$T, $LS($LZ), b#0, c#Z#0, !k#0));
            assume _module.__default.Zipper1#canCall(_module._default.Zipper1$T, b#0, c#Z#0, !k#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.Zipper1(_module._default.Zipper1$T, $LS($LZ), a#0, b#0, k#0), 
              Tclass._module.List(_module._default.Zipper1$T));
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
    }
}



// function declaration for _module._default.Zipper2
function _module.__default.Zipper2(_module._default.Zipper2$T: Ty, 
    $ly: LayerType, 
    a#0: DatatypeType, 
    b#0: DatatypeType)
   : DatatypeType;

function _module.__default.Zipper2#canCall(_module._default.Zipper2$T: Ty, a#0: DatatypeType, b#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall _module._default.Zipper2$T: Ty, 
    $ly: LayerType, 
    a#0: DatatypeType, 
    b#0: DatatypeType :: 
  { _module.__default.Zipper2(_module._default.Zipper2$T, $LS($ly), a#0, b#0) } 
  _module.__default.Zipper2(_module._default.Zipper2$T, $LS($ly), a#0, b#0)
     == _module.__default.Zipper2(_module._default.Zipper2$T, $ly, a#0, b#0));

// fuel synonym axiom
axiom (forall _module._default.Zipper2$T: Ty, 
    $ly: LayerType, 
    a#0: DatatypeType, 
    b#0: DatatypeType :: 
  { _module.__default.Zipper2(_module._default.Zipper2$T, AsFuelBottom($ly), a#0, b#0) } 
  _module.__default.Zipper2(_module._default.Zipper2$T, $ly, a#0, b#0)
     == _module.__default.Zipper2(_module._default.Zipper2$T, $LZ, a#0, b#0));

// consequence axiom for _module.__default.Zipper2
axiom 9 <= $FunctionContextHeight
   ==> (forall _module._default.Zipper2$T: Ty, 
      $ly: LayerType, 
      a#0: DatatypeType, 
      b#0: DatatypeType :: 
    { _module.__default.Zipper2(_module._default.Zipper2$T, $ly, a#0, b#0) } 
    _module.__default.Zipper2#canCall(_module._default.Zipper2$T, a#0, b#0)
         || (9 != $FunctionContextHeight
           && 
          $Is(a#0, Tclass._module.List(_module._default.Zipper2$T))
           && $Is(b#0, Tclass._module.List(_module._default.Zipper2$T)))
       ==> $Is(_module.__default.Zipper2(_module._default.Zipper2$T, $ly, a#0, b#0), 
        Tclass._module.List(_module._default.Zipper2$T)));

function _module.__default.Zipper2#requires(Ty, LayerType, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.Zipper2
axiom (forall _module._default.Zipper2$T: Ty, 
    $ly: LayerType, 
    a#0: DatatypeType, 
    b#0: DatatypeType :: 
  { _module.__default.Zipper2#requires(_module._default.Zipper2$T, $ly, a#0, b#0) } 
  $Is(a#0, Tclass._module.List(_module._default.Zipper2$T))
       && $Is(b#0, Tclass._module.List(_module._default.Zipper2$T))
     ==> _module.__default.Zipper2#requires(_module._default.Zipper2$T, $ly, a#0, b#0)
       == true);

// definition axiom for _module.__default.Zipper2 (revealed)
axiom 9 <= $FunctionContextHeight
   ==> (forall _module._default.Zipper2$T: Ty, 
      $ly: LayerType, 
      a#0: DatatypeType, 
      b#0: DatatypeType :: 
    { _module.__default.Zipper2(_module._default.Zipper2$T, $LS($ly), a#0, b#0) } 
    _module.__default.Zipper2#canCall(_module._default.Zipper2$T, a#0, b#0)
         || (9 != $FunctionContextHeight
           && 
          $Is(a#0, Tclass._module.List(_module._default.Zipper2$T))
           && $Is(b#0, Tclass._module.List(_module._default.Zipper2$T)))
       ==> (!_module.List.Nil_q(a#0)
           ==> (var c#1 := _module.List._h1(a#0); 
            _module.__default.Zipper2#canCall(_module._default.Zipper2$T, b#0, c#1)))
         && _module.__default.Zipper2(_module._default.Zipper2$T, $LS($ly), a#0, b#0)
           == (if _module.List.Nil_q(a#0)
             then b#0
             else (var c#0 := _module.List._h1(a#0); 
              (var x#0 := _module.List._h0(a#0); 
                #_module.List.Cons(x#0, _module.__default.Zipper2(_module._default.Zipper2$T, $ly, b#0, c#0))))));

// definition axiom for _module.__default.Zipper2 for all literals (revealed)
axiom 9 <= $FunctionContextHeight
   ==> (forall _module._default.Zipper2$T: Ty, 
      $ly: LayerType, 
      a#0: DatatypeType, 
      b#0: DatatypeType :: 
    {:weight 3} { _module.__default.Zipper2(_module._default.Zipper2$T, $LS($ly), Lit(a#0), Lit(b#0)) } 
    _module.__default.Zipper2#canCall(_module._default.Zipper2$T, Lit(a#0), Lit(b#0))
         || (9 != $FunctionContextHeight
           && 
          $Is(a#0, Tclass._module.List(_module._default.Zipper2$T))
           && $Is(b#0, Tclass._module.List(_module._default.Zipper2$T)))
       ==> (!Lit(_module.List.Nil_q(Lit(a#0)))
           ==> (var c#3 := Lit(_module.List._h1(Lit(a#0))); 
            _module.__default.Zipper2#canCall(_module._default.Zipper2$T, Lit(b#0), c#3)))
         && _module.__default.Zipper2(_module._default.Zipper2$T, $LS($ly), Lit(a#0), Lit(b#0))
           == (if _module.List.Nil_q(Lit(a#0))
             then b#0
             else (var c#2 := Lit(_module.List._h1(Lit(a#0))); 
              (var x#2 := Lit(_module.List._h0(Lit(a#0))); 
                Lit(#_module.List.Cons(x#2, 
                    Lit(_module.__default.Zipper2(_module._default.Zipper2$T, $LS($ly), Lit(b#0), c#2))))))));

procedure CheckWellformed$$_module.__default.Zipper2(_module._default.Zipper2$T: Ty, 
    a#0: DatatypeType
       where $Is(a#0, Tclass._module.List(_module._default.Zipper2$T)), 
    b#0: DatatypeType
       where $Is(b#0, Tclass._module.List(_module._default.Zipper2$T)));
  free requires 9 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Zipper2(_module._default.Zipper2$T: Ty, a#0: DatatypeType, b#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: Box;
  var _mcc#1#0: DatatypeType;
  var c#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var x#Z#0: Box;
  var let#1#0#0: Box;
  var ##a#0: DatatypeType;
  var ##b#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function Zipper2
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(266,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (DtRank(a#0) < DtRank(b#0))
    {
    }
    else
    {
    }

    if (DtRank(a#0) < DtRank(b#0))
    {
    }
    else
    {
    }

    if (*)
    {
        assume $Is(_module.__default.Zipper2(_module._default.Zipper2$T, $LS($LZ), a#0, b#0), 
          Tclass._module.List(_module._default.Zipper2$T));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (a#0 == #_module.List.Nil())
        {
            assume _module.__default.Zipper2(_module._default.Zipper2$T, $LS($LZ), a#0, b#0) == b#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.Zipper2(_module._default.Zipper2$T, $LS($LZ), a#0, b#0), 
              Tclass._module.List(_module._default.Zipper2$T));
        }
        else if (a#0 == #_module.List.Cons(_mcc#0#0, _mcc#1#0))
        {
            assume $IsBox(_mcc#0#0, _module._default.Zipper2$T);
            assume $Is(_mcc#1#0, Tclass._module.List(_module._default.Zipper2$T));
            havoc c#Z#0;
            assume $Is(c#Z#0, Tclass._module.List(_module._default.Zipper2$T));
            assume let#0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.List(_module._default.Zipper2$T));
            assume c#Z#0 == let#0#0#0;
            havoc x#Z#0;
            assume $IsBox(x#Z#0, _module._default.Zipper2$T);
            assume let#1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $IsBox(let#1#0#0, _module._default.Zipper2$T);
            assume x#Z#0 == let#1#0#0;
            ##a#0 := b#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##a#0, Tclass._module.List(_module._default.Zipper2$T), $Heap);
            ##b#0 := c#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#0, Tclass._module.List(_module._default.Zipper2$T), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank((if DtRank(##a#0) < DtRank(##b#0) then ##b#0 else ##a#0))
                 < DtRank((if DtRank(a#0) < DtRank(b#0) then b#0 else a#0))
               || (DtRank((if DtRank(##a#0) < DtRank(##b#0) then ##b#0 else ##a#0))
                   == DtRank((if DtRank(a#0) < DtRank(b#0) then b#0 else a#0))
                 && DtRank((if DtRank(##a#0) < DtRank(##b#0) then ##a#0 else ##b#0))
                   < DtRank((if DtRank(a#0) < DtRank(b#0) then a#0 else b#0)));
            assume _module.__default.Zipper2#canCall(_module._default.Zipper2$T, b#0, c#Z#0);
            assume _module.__default.Zipper2(_module._default.Zipper2$T, $LS($LZ), a#0, b#0)
               == #_module.List.Cons(x#Z#0, 
                _module.__default.Zipper2(_module._default.Zipper2$T, $LS($LZ), b#0, c#Z#0));
            assume _module.__default.Zipper2#canCall(_module._default.Zipper2$T, b#0, c#Z#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.Zipper2(_module._default.Zipper2$T, $LS($LZ), a#0, b#0), 
              Tclass._module.List(_module._default.Zipper2$T));
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
    }
}



procedure CheckWellformed$$_module.__default.WhileStar0(n#0: int);
  free requires 46 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.WhileStar0(n#0: int);
  // user-defined preconditions
  requires LitInt(2) <= n#0;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.WhileStar0(n#0: int) returns ($_reverifyPost: bool);
  free requires 46 == $FunctionContextHeight;
  // user-defined preconditions
  requires LitInt(2) <= n#0;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.WhileStar0(n#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var m#0: int;
  var k#0: int;
  var $PreLoopHeap$loop#0: Heap;
  var $w$loop#0: bool;

    // AddMethodImpl: WhileStar0, Impl$$_module.__default.WhileStar0
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(280,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(281,9)
    assume true;
    assume true;
    m#0 := n#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(281,12)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(282,9)
    assume true;
    assume true;
    k#0 := LitInt(0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(282,12)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(283,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    havoc $w$loop#0;
    while (true)
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> LitInt(0) <= k#0;
      invariant $w$loop#0 ==> LitInt(0) <= m#0;
      free invariant (forall $o: ref :: 
        { $Heap[$o] } 
        $o != null && read(old($Heap), $o, alloc)
           ==> $Heap[$o] == $PreLoopHeap$loop#0[$o]);
      free invariant $HeapSucc($PreLoopHeap$loop#0, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
        { read($Heap, $o, $f) } 
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(283,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            if (LitInt(0) <= k#0)
            {
            }

            assume true;
            assume LitInt(0) <= k#0 && LitInt(0) <= m#0;
            assume true;
            assume false;
        }

        if (*)
        {
            break;
        }

        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(287,7)
        assume true;
        assume true;
        k#0 := k#0 + m#0;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(287,14)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(288,7)
        assume true;
        assume true;
        m#0 := m#0 + k#0;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(288,14)"} true;
        assume true;
    }

    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(290,3)
    assume true;
    assert LitInt(0) <= k#0;
}



procedure CheckWellformed$$_module.__default.WhileStar1();
  free requires 47 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.WhileStar1();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.WhileStar1() returns ($_reverifyPost: bool);
  free requires 47 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.WhileStar1() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var k#0: int;
  var $Heap_at_0: Heap;
  var $PreLoopHeap$loop#0: Heap;
  var $w$loop#0: bool;

    // AddMethodImpl: WhileStar1, Impl$$_module.__default.WhileStar1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(294,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(295,9)
    assume true;
    assume true;
    k#0 := LitInt(0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(295,12)"} true;
    $Heap_at_0 := $Heap;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(296,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
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
      free invariant true;
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(296,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assume false;
        }

        if (*)
        {
            break;
        }

        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(298,7)
        assume true;
        assume true;
        k#0 := k#0 + 1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(298,14)"} true;
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(299,5)
        assume true;
        if (k#0 == LitInt(17))
        {
            // ----- break statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(299,20)
            goto after_0;
        }
        else
        {
        }

        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(296,3)
        assert false;
    }

  after_0:
}



procedure CheckWellformed$$_module.__default.WhileStar2();
  free requires 48 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.WhileStar2();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.WhileStar2() returns ($_reverifyPost: bool);
  free requires 48 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.WhileStar2() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var k#0: int;
  var $Heap_at_0: Heap;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var $decr$loop#00: int;

    // AddMethodImpl: WhileStar2, Impl$$_module.__default.WhileStar2
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(304,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(305,9)
    assume true;
    assume true;
    k#0 := LitInt(0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(305,12)"} true;
    $Heap_at_0 := $Heap;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(306,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := 17 - k#0;
    havoc $w$loop#0;
    while (true)
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> k#0 < 17;
      free invariant (forall $o: ref :: 
        { $Heap[$o] } 
        $o != null && read(old($Heap), $o, alloc)
           ==> $Heap[$o] == $PreLoopHeap$loop#0[$o]);
      free invariant $HeapSucc($PreLoopHeap$loop#0, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
        { read($Heap, $o, $f) } 
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
      free invariant 17 - k#0 <= $decr_init$loop#00 && (17 - k#0 == $decr_init$loop#00 ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(306,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assume true;
            assume k#0 < 17;
            assume true;
            assume false;
        }

        if (*)
        {
            break;
        }

        $decr$loop#00 := 17 - k#0;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(310,7)
        assume true;
        assume true;
        k#0 := k#0 + 1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(310,14)"} true;
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(311,5)
        assume true;
        if (k#0 == LitInt(17))
        {
            // ----- break statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(311,20)
            goto after_0;
        }
        else
        {
        }

        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(306,3)
        assert 0 <= $decr$loop#00 || 17 - k#0 == $decr$loop#00;
        assert 17 - k#0 < $decr$loop#00;
        assume true;
    }

  after_0:
}



// function declaration for _module._default.ReachBack
function _module.__default.ReachBack($ly: LayerType, n#0: int) : bool;

function _module.__default.ReachBack#canCall(n#0: int) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, n#0: int :: 
  { _module.__default.ReachBack($LS($ly), n#0) } 
  _module.__default.ReachBack($LS($ly), n#0)
     == _module.__default.ReachBack($ly, n#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, n#0: int :: 
  { _module.__default.ReachBack(AsFuelBottom($ly), n#0) } 
  _module.__default.ReachBack($ly, n#0) == _module.__default.ReachBack($LZ, n#0));

// consequence axiom for _module.__default.ReachBack
axiom 34 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: int :: 
    { _module.__default.ReachBack($ly, n#0) } 
    _module.__default.ReachBack#canCall(n#0)
         || (34 != $FunctionContextHeight && LitInt(0) <= n#0)
       ==> _module.__default.ReachBack($ly, n#0));

function _module.__default.ReachBack#requires(LayerType, int) : bool;

// #requires axiom for _module.__default.ReachBack
axiom (forall $ly: LayerType, n#0: int :: 
  { _module.__default.ReachBack#requires($ly, n#0) } 
  _module.__default.ReachBack#requires($ly, n#0) == (LitInt(0) <= n#0));

// definition axiom for _module.__default.ReachBack (revealed)
axiom 34 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: int :: 
    { _module.__default.ReachBack($LS($ly), n#0) } 
    _module.__default.ReachBack#canCall(n#0)
         || (34 != $FunctionContextHeight && LitInt(0) <= n#0)
       ==> (forall m#0: int :: 
          { _module.__default.ReachBack($ly, m#0) } 
          LitInt(0) <= m#0 ==> m#0 < n#0 ==> _module.__default.ReachBack#canCall(m#0))
         && _module.__default.ReachBack($LS($ly), n#0)
           == (forall m#0: int :: 
            {:induction false} { _module.__default.ReachBack($ly, m#0) } 
            true ==> LitInt(0) <= m#0 && m#0 < n#0 ==> _module.__default.ReachBack($ly, m#0)));

// definition axiom for _module.__default.ReachBack for all literals (revealed)
axiom 34 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: int :: 
    {:weight 3} { _module.__default.ReachBack($LS($ly), LitInt(n#0)) } 
    _module.__default.ReachBack#canCall(LitInt(n#0))
         || (34 != $FunctionContextHeight && LitInt(0) <= LitInt(n#0))
       ==> (forall m#1: int :: 
          { _module.__default.ReachBack($LS($ly), m#1) } 
          LitInt(0) <= m#1 ==> m#1 < n#0 ==> _module.__default.ReachBack#canCall(m#1))
         && _module.__default.ReachBack($LS($ly), LitInt(n#0))
           == (forall m#1: int :: 
            {:induction false} { _module.__default.ReachBack($LS($ly), m#1) } 
            true
               ==> 
              LitInt(0) <= m#1 && m#1 < n#0
               ==> _module.__default.ReachBack($LS($ly), m#1)));

procedure CheckWellformed$$_module.__default.ReachBack(n#0: int);
  free requires 34 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures _module.__default.ReachBack($LS($LS($LZ)), n#0);



implementation CheckWellformed$$_module.__default.ReachBack(n#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##n#0: int;
  var m#2: int;
  var ##n#1: int;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function ReachBack
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(317,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume LitInt(0) <= n#0;
    if (*)
    {
        ##n#0 := n#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#0, TInt, $Heap);
        assert {:subsumption 0} LitInt(0) <= ##n#0;
        assume LitInt(0) <= ##n#0;
        assert 0 <= n#0 || ##n#0 == n#0;
        assert n#0 == n#0 || ##n#0 < n#0;
        assume n#0 == n#0 || _module.__default.ReachBack#canCall(n#0);
        assume _module.__default.ReachBack($LS($LZ), n#0);
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        // Begin Comprehension WF check
        havoc m#2;
        if (true)
        {
            if (LitInt(0) <= m#2)
            {
            }

            if (LitInt(0) <= m#2 && m#2 < n#0)
            {
                ##n#1 := m#2;
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#1, TInt, $Heap);
                assert {:subsumption 0} LitInt(0) <= ##n#1;
                assume LitInt(0) <= ##n#1;
                b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assert 0 <= n#0 || ##n#1 == n#0;
                assert ##n#1 < n#0;
                assume _module.__default.ReachBack#canCall(m#2);
            }
        }

        // End Comprehension WF check
        assume _module.__default.ReachBack($LS($LZ), n#0)
           == (forall m#3: int :: 
            {:induction false} { _module.__default.ReachBack($LS($LZ), m#3) } 
            true
               ==> 
              LitInt(0) <= m#3 && m#3 < n#0
               ==> _module.__default.ReachBack($LS($LZ), m#3));
        assume (forall m#3: int :: 
          { _module.__default.ReachBack($LS($LZ), m#3) } 
          LitInt(0) <= m#3 ==> m#3 < n#0 ==> _module.__default.ReachBack#canCall(m#3));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.ReachBack($LS($LZ), n#0), TBool);
        assert b$reqreads#0;
    }
}



// function declaration for _module._default.ReachBack_Alt
function _module.__default.ReachBack__Alt($ly: LayerType, n#0: int) : bool;

function _module.__default.ReachBack__Alt#canCall(n#0: int) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, n#0: int :: 
  { _module.__default.ReachBack__Alt($LS($ly), n#0) } 
  _module.__default.ReachBack__Alt($LS($ly), n#0)
     == _module.__default.ReachBack__Alt($ly, n#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, n#0: int :: 
  { _module.__default.ReachBack__Alt(AsFuelBottom($ly), n#0) } 
  _module.__default.ReachBack__Alt($ly, n#0)
     == _module.__default.ReachBack__Alt($LZ, n#0));

// consequence axiom for _module.__default.ReachBack__Alt
axiom 35 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: int :: 
    { _module.__default.ReachBack__Alt($ly, n#0) } 
    _module.__default.ReachBack__Alt#canCall(n#0)
         || (35 != $FunctionContextHeight && LitInt(0) <= n#0)
       ==> true);

function _module.__default.ReachBack__Alt#requires(LayerType, int) : bool;

// #requires axiom for _module.__default.ReachBack__Alt
axiom (forall $ly: LayerType, n#0: int :: 
  { _module.__default.ReachBack__Alt#requires($ly, n#0) } 
  _module.__default.ReachBack__Alt#requires($ly, n#0) == (LitInt(0) <= n#0));

// definition axiom for _module.__default.ReachBack__Alt (revealed)
axiom 35 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: int :: 
    { _module.__default.ReachBack__Alt($LS($ly), n#0) } 
    _module.__default.ReachBack__Alt#canCall(n#0)
         || (35 != $FunctionContextHeight && LitInt(0) <= n#0)
       ==> (n#0 != LitInt(0) ==> _module.__default.ReachBack__Alt#canCall(n#0 - 1))
         && _module.__default.ReachBack__Alt($LS($ly), n#0)
           == (n#0 == LitInt(0) || _module.__default.ReachBack__Alt($ly, n#0 - 1)));

// definition axiom for _module.__default.ReachBack__Alt for all literals (revealed)
axiom 35 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: int :: 
    {:weight 3} { _module.__default.ReachBack__Alt($LS($ly), LitInt(n#0)) } 
    _module.__default.ReachBack__Alt#canCall(LitInt(n#0))
         || (35 != $FunctionContextHeight && LitInt(0) <= LitInt(n#0))
       ==> (LitInt(n#0) != LitInt(0)
           ==> _module.__default.ReachBack__Alt#canCall(LitInt(n#0 - 1)))
         && _module.__default.ReachBack__Alt($LS($ly), LitInt(n#0))
           == (LitInt(n#0) == LitInt(0)
             || _module.__default.ReachBack__Alt($LS($ly), LitInt(n#0 - 1))));

procedure CheckWellformed$$_module.__default.ReachBack__Alt(n#0: int);
  free requires 35 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.ReachBack__Alt(n#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##n#0: int;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function ReachBack_Alt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(326,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume LitInt(0) <= n#0;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (n#0 != LitInt(0))
        {
            ##n#0 := n#0 - 1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0, TInt, $Heap);
            assert {:subsumption 0} LitInt(0) <= ##n#0;
            assume LitInt(0) <= ##n#0;
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0 <= n#0 || ##n#0 == n#0;
            assert ##n#0 < n#0;
            assume _module.__default.ReachBack__Alt#canCall(n#0 - 1);
        }

        assume _module.__default.ReachBack__Alt($LS($LZ), n#0)
           == (n#0 == LitInt(0) || _module.__default.ReachBack__Alt($LS($LZ), n#0 - 1));
        assume n#0 != LitInt(0) ==> _module.__default.ReachBack__Alt#canCall(n#0 - 1);
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.ReachBack__Alt($LS($LZ), n#0), TBool);
        assert b$reqreads#0;
    }
}



procedure CheckWellformed$$_module.__default.Lemma__ReachBack();
  free requires 36 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Lemma__ReachBack();
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.Lemma__ReachBack() returns ($_reverifyPost: bool);
  free requires 36 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.Lemma__ReachBack() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var m#0: int;
  var ##n#0: int;

    // AddMethodImpl: Lemma_ReachBack, Impl$$_module.__default.Lemma__ReachBack
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(333,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(334,3)
    // Begin Comprehension WF check
    havoc m#0;
    if (true)
    {
        if (LitInt(0) <= m#0)
        {
            ##n#0 := m#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0, TInt, $Heap);
            assert {:subsumption 0} LitInt(0) <= ##n#0;
            assume _module.__default.ReachBack__Alt#canCall(m#0);
        }
    }

    // End Comprehension WF check
    assume (forall m#1: int :: 
      { _module.__default.ReachBack__Alt($LS($LZ), m#1) } 
      LitInt(0) <= m#1 ==> _module.__default.ReachBack__Alt#canCall(m#1));
    assert {:subsumption 0} (forall m#1: int :: 
      { _module.__default.ReachBack__Alt($LS($LS($LZ)), m#1) } 
      (forall m$ih#0#0: int :: 
            { _module.__default.ReachBack__Alt($LS($LZ), m$ih#0#0) } 
            true
               ==> 
              0 <= m$ih#0#0 && m$ih#0#0 < m#1
               ==> 
              LitInt(0) <= m$ih#0#0
               ==> _module.__default.ReachBack__Alt($LS($LZ), m$ih#0#0))
           && true
         ==> 
        LitInt(0) <= m#1
         ==> _module.__default.ReachBack__Alt($LS($LS($LZ)), m#1));
    assume (forall m#1: int :: 
      {:induction} {:_induction m#1} { _module.__default.ReachBack__Alt($LS($LZ), m#1) } 
      true ==> LitInt(0) <= m#1 ==> _module.__default.ReachBack__Alt($LS($LZ), m#1));
}



procedure {:_induction t#0} CheckWellformed$$_module.__default.ExtEvensSumToEven(t#0: DatatypeType
       where $Is(t#0, Tclass._module.Tree())
         && $IsAlloc(t#0, Tclass._module.Tree(), $Heap)
         && $IsA#_module.Tree(t#0));
  free requires 12 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:_induction t#0} CheckWellformed$$_module.__default.ExtEvensSumToEven(t#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var u#0: int;

    // AddMethodImpl: ExtEvensSumToEven, CheckWellformed$$_module.__default.ExtEvensSumToEven
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(517,6): initial state"} true;
    havoc u#0;
    assume true;
    if (*)
    {
        assume _module.Tree.Elements#canCall(t#0);
        assume Lit(_module.Tree.Elements($LS($LZ), t#0))[$Box(u#0)];
        assert LitInt(2) != 0;
        assume Mod(u#0, LitInt(2)) == LitInt(0);
    }
    else
    {
        assume Lit(_module.Tree.Elements($LS($LZ), t#0))[$Box(u#0)]
           ==> Mod(u#0, LitInt(2)) == LitInt(0);
    }

    assume (forall u#1: int :: 
      { _module.Tree.Elements($LS($LZ), t#0)[$Box(u#1)] } 
      true
         ==> 
        Lit(_module.Tree.Elements($LS($LZ), t#0))[$Box(u#1)]
         ==> Mod(u#1, LitInt(2)) == LitInt(0));
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(519,22): post-state"} true;
    assume _module.Tree.Sum#canCall(t#0);
    assert LitInt(2) != 0;
    assume LitInt(Mod(_module.Tree.Sum($LS($LZ), t#0), LitInt(2))) == LitInt(0);
}



procedure {:_induction t#0} Call$$_module.__default.ExtEvensSumToEven(t#0: DatatypeType
       where $Is(t#0, Tclass._module.Tree())
         && $IsAlloc(t#0, Tclass._module.Tree(), $Heap)
         && $IsA#_module.Tree(t#0));
  // user-defined preconditions
  requires (forall u#1: int :: 
    { _module.Tree.Elements($LS($LS($LZ)), t#0)[$Box(u#1)] } 
    true
       ==> 
      Lit(_module.Tree.Elements($LS($LS($LZ)), t#0))[$Box(u#1)]
       ==> Mod(u#1, LitInt(2)) == LitInt(0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Tree.Sum#canCall(t#0);
  ensures LitInt(Mod(_module.Tree.Sum($LS($LS($LZ)), t#0), LitInt(2))) == LitInt(0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction t#0} Impl$$_module.__default.ExtEvensSumToEven(t#0: DatatypeType
       where $Is(t#0, Tclass._module.Tree())
         && $IsAlloc(t#0, Tclass._module.Tree(), $Heap)
         && $IsA#_module.Tree(t#0))
   returns ($_reverifyPost: bool);
  free requires 12 == $FunctionContextHeight;
  // user-defined preconditions
  free requires (forall u#1: int :: 
    { _module.Tree.Elements($LS($LZ), t#0)[$Box(u#1)] } 
    true
       ==> 
      Lit(_module.Tree.Elements($LS($LZ), t#0))[$Box(u#1)]
       ==> Mod(u#1, LitInt(2)) == LitInt(0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Tree.Sum#canCall(t#0);
  ensures LitInt(Mod(_module.Tree.Sum($LS($LS($LZ)), t#0), LitInt(2))) == LitInt(0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction t#0} Impl$$_module.__default.ExtEvensSumToEven(t#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var _mcc#0#0_0: int;
  var _mcc#1#0_0: DatatypeType;
  var _mcc#2#0_0: DatatypeType;
  var right#0_0: DatatypeType;
  var let#0_0#0#0: DatatypeType;
  var left#0_0: DatatypeType;
  var let#0_1#0#0: DatatypeType;
  var x#0_0: int;
  var let#0_2#0#0: int;

    // AddMethodImpl: ExtEvensSumToEven, Impl$$_module.__default.ExtEvensSumToEven
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(521,0): initial state"} true;
    assume $IsA#_module.Tree(t#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#t0#0: DatatypeType :: 
      $Is($ih#t0#0, Tclass._module.Tree())
           && (forall u#2: int :: 
            { _module.Tree.Elements($LS($LZ), $ih#t0#0)[$Box(u#2)] } 
            true
               ==> 
              Lit(_module.Tree.Elements($LS($LZ), $ih#t0#0))[$Box(u#2)]
               ==> Mod(u#2, LitInt(2)) == LitInt(0))
           && DtRank($ih#t0#0) < DtRank(t#0)
         ==> LitInt(Mod(_module.Tree.Sum($LS($LZ), $ih#t0#0), LitInt(2))) == LitInt(0));
    $_reverifyPost := false;
    assume true;
    havoc _mcc#0#0_0, _mcc#1#0_0, _mcc#2#0_0;
    if (t#0 == #_module.Tree.Empty())
    {
    }
    else if (t#0 == #_module.Tree.Node(_mcc#0#0_0, _mcc#1#0_0, _mcc#2#0_0))
    {
        assume $Is(_mcc#1#0_0, Tclass._module.Tree());
        assume $Is(_mcc#2#0_0, Tclass._module.Tree());
        havoc right#0_0;
        assume $Is(right#0_0, Tclass._module.Tree())
           && $IsAlloc(right#0_0, Tclass._module.Tree(), $Heap);
        assume let#0_0#0#0 == _mcc#2#0_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_0#0#0, Tclass._module.Tree());
        assume right#0_0 == let#0_0#0#0;
        havoc left#0_0;
        assume $Is(left#0_0, Tclass._module.Tree())
           && $IsAlloc(left#0_0, Tclass._module.Tree(), $Heap);
        assume let#0_1#0#0 == _mcc#1#0_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_1#0#0, Tclass._module.Tree());
        assume left#0_0 == let#0_1#0#0;
        havoc x#0_0;
        assume let#0_2#0#0 == _mcc#0#0_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_2#0#0, TInt);
        assume x#0_0 == let#0_2#0#0;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(525,5)
        assume _module.Tree.Elements#canCall(t#0);
        assume _module.Tree.Elements#canCall(t#0);
        assert {:subsumption 0} Lit(_module.Tree.Elements($LS($LS($LZ)), t#0))[$Box(x#0_0)];
        assume Lit(_module.Tree.Elements($LS($LZ), t#0))[$Box(x#0_0)];
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(526,5)
        assume _module.Tree.Sum#canCall(left#0_0);
        assert {:subsumption 0} LitInt(2) != 0;
        assume _module.Tree.Sum#canCall(left#0_0);
        assert {:subsumption 0} LitInt(Mod(_module.Tree.Sum($LS($LS($LZ)), left#0_0), LitInt(2))) == LitInt(0);
        assume LitInt(Mod(_module.Tree.Sum($LS($LZ), left#0_0), LitInt(2))) == LitInt(0);
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(527,5)
        assume _module.Tree.Sum#canCall(right#0_0);
        assert {:subsumption 0} LitInt(2) != 0;
        assume _module.Tree.Sum#canCall(right#0_0);
        assert {:subsumption 0} LitInt(Mod(_module.Tree.Sum($LS($LS($LZ)), right#0_0), LitInt(2))) == LitInt(0);
        assume LitInt(Mod(_module.Tree.Sum($LS($LZ), right#0_0), LitInt(2))) == LitInt(0);
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(528,5)
        assume _module.Tree.Sum#canCall(t#0);
        assert {:subsumption 0} LitInt(2) != 0;
        assume _module.Tree.Sum#canCall(t#0);
        assert {:subsumption 0} LitInt(Mod(_module.Tree.Sum($LS($LS($LZ)), t#0), LitInt(2))) == LitInt(0);
        assume LitInt(Mod(_module.Tree.Sum($LS($LZ), t#0), LitInt(2))) == LitInt(0);
    }
    else
    {
        assume false;
    }
}



procedure CheckWellformed$$_module.__default.LoopyInt(x#0: int);
  free requires 49 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.LoopyInt(x#0: int);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.LoopyInt(x#0: int) returns ($_reverifyPost: bool);
  free requires 49 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.LoopyInt(x#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var $decr$loop#00: int;

    // AddMethodImpl: LoopyInt, Impl$$_module.__default.LoopyInt
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(533,24): initial state"} true;
    $_reverifyPost := false;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(534,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := LitInt(58);
    havoc $w$loop#0;
    while (true)
      free invariant $PreLoopHeap$loop#0 == $Heap;
      free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
        { read($Heap, $o, $f) } 
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
      free invariant LitInt(58) <= $decr_init$loop#00 && (LitInt(58) == $decr_init$loop#00 ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(534,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assume true;
            assume false;
        }

        assume true;
        if (100 <= x#0)
        {
            break;
        }

        $decr$loop#00 := LitInt(58);
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(534,3)
        assert 0 <= $decr$loop#00 || LitInt(58) == $decr$loop#00;
        assert LitInt(58) < $decr$loop#00;
    }
}



procedure CheckWellformed$$_module.__default.LoopyISet(m#0: IMap Box Box
       where $Is(m#0, TIMap(TInt, TInt)) && $IsAlloc(m#0, TIMap(TInt, TInt), $Heap));
  free requires 50 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.LoopyISet(m#0: IMap Box Box
       where $Is(m#0, TIMap(TInt, TInt)) && $IsAlloc(m#0, TIMap(TInt, TInt), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.LoopyISet(m#0: IMap Box Box
       where $Is(m#0, TIMap(TInt, TInt)) && $IsAlloc(m#0, TIMap(TInt, TInt), $Heap))
   returns ($_reverifyPost: bool);
  free requires 50 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.LoopyISet(m#0: IMap Box Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: ISet Box;
  var $w$loop#0: bool;
  var $decr$loop#00: ISet Box;

    // AddMethodImpl: LoopyISet, Impl$$_module.__default.LoopyISet
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(541,0): initial state"} true;
    $_reverifyPost := false;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(542,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := IMap#Domain(m#0);
    havoc $w$loop#0;
    while (true)
      free invariant $PreLoopHeap$loop#0 == $Heap;
      free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
        { read($Heap, $o, $f) } 
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
      free invariant ISet#Equal(IMap#Domain(m#0), $decr_init$loop#00)
         && (ISet#Equal(IMap#Domain(m#0), $decr_init$loop#00) ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(542,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assume true;
            assume false;
        }

        assume true;
        if (IMap#Equal(m#0, IMap#Empty(): IMap Box Box))
        {
            break;
        }

        $decr$loop#00 := IMap#Domain(m#0);
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(542,3)
        assert false;
    }
}



procedure CheckWellformed$$_module.__default.LoopyIMap(x#0: int, 
    m#0: IMap Box Box
       where $Is(m#0, TIMap(TInt, TInt)) && $IsAlloc(m#0, TIMap(TInt, TInt), $Heap));
  free requires 51 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.LoopyIMap(x#0: int, 
    m#0: IMap Box Box
       where $Is(m#0, TIMap(TInt, TInt)) && $IsAlloc(m#0, TIMap(TInt, TInt), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.LoopyIMap(x#0: int, 
    m#0: IMap Box Box
       where $Is(m#0, TIMap(TInt, TInt)) && $IsAlloc(m#0, TIMap(TInt, TInt), $Heap))
   returns ($_reverifyPost: bool);
  free requires 51 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.LoopyIMap(x#0: int, m#0: IMap Box Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: IMap Box Box;
  var $w$loop#0: bool;
  var $decr$loop#00: IMap Box Box;

    // AddMethodImpl: LoopyIMap, Impl$$_module.__default.LoopyIMap
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(548,44): initial state"} true;
    $_reverifyPost := false;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(549,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := m#0;
    havoc $w$loop#0;
    while (true)
      free invariant $PreLoopHeap$loop#0 == $Heap;
      free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
        { read($Heap, $o, $f) } 
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
      free invariant ISet#Equal(IMap#Domain(m#0), IMap#Domain($decr_init$loop#00))
         && (ISet#Equal(IMap#Domain(m#0), IMap#Domain($decr_init$loop#00)) ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(549,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assume true;
            assume false;
        }

        assume true;
        if (100 <= x#0)
        {
            break;
        }

        $decr$loop#00 := m#0;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(549,3)
        assert false;
    }
}



procedure CheckWellformed$$_module.__default.LoopyFunction(x#0: int, 
    f#0: HandleType
       where $Is(f#0, Tclass._System.___hTotalFunc1(TInt, TInt))
         && $IsAlloc(f#0, Tclass._System.___hTotalFunc1(TInt, TInt), $Heap));
  free requires 14 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.LoopyFunction(x#0: int, 
    f#0: HandleType
       where $Is(f#0, Tclass._System.___hTotalFunc1(TInt, TInt))
         && $IsAlloc(f#0, Tclass._System.___hTotalFunc1(TInt, TInt), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.LoopyFunction(x#0: int, 
    f#0: HandleType
       where $Is(f#0, Tclass._System.___hTotalFunc1(TInt, TInt))
         && $IsAlloc(f#0, Tclass._System.___hTotalFunc1(TInt, TInt), $Heap))
   returns ($_reverifyPost: bool);
  free requires 14 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.LoopyFunction(x#0: int, f#0: HandleType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: HandleType;
  var $w$loop#0: bool;
  var $decr$loop#00: HandleType;

    // AddMethodImpl: LoopyFunction, Impl$$_module.__default.LoopyFunction
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(555,44): initial state"} true;
    $_reverifyPost := false;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(556,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := f#0;
    havoc $w$loop#0;
    while (true)
      free invariant $PreLoopHeap$loop#0 == $Heap;
      free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
        { read($Heap, $o, $f) } 
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
      free invariant f#0 == $decr_init$loop#00 && (f#0 == $decr_init$loop#00 ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(556,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assume true;
            assume false;
        }

        assume true;
        if (100 <= x#0)
        {
            break;
        }

        $decr$loop#00 := f#0;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(556,3)
        assert false;
    }
}



procedure CheckWellformed$$_module.__default.LoopyTypeParam(_module._default.LoopyTypeParam$Y: Ty, 
    x#0: int, 
    y#0: Box
       where $IsBox(y#0, _module._default.LoopyTypeParam$Y)
         && $IsAllocBox(y#0, _module._default.LoopyTypeParam$Y, $Heap));
  free requires 52 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.LoopyTypeParam(_module._default.LoopyTypeParam$Y: Ty, 
    x#0: int, 
    y#0: Box
       where $IsBox(y#0, _module._default.LoopyTypeParam$Y)
         && $IsAllocBox(y#0, _module._default.LoopyTypeParam$Y, $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.LoopyTypeParam(_module._default.LoopyTypeParam$Y: Ty, 
    x#0: int, 
    y#0: Box
       where $IsBox(y#0, _module._default.LoopyTypeParam$Y)
         && $IsAllocBox(y#0, _module._default.LoopyTypeParam$Y, $Heap))
   returns ($_reverifyPost: bool);
  free requires 52 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.LoopyTypeParam(_module._default.LoopyTypeParam$Y: Ty, x#0: int, y#0: Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: Box;
  var $w$loop#0: bool;
  var $decr$loop#00: Box;

    // AddMethodImpl: LoopyTypeParam, Impl$$_module.__default.LoopyTypeParam
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(562,39): initial state"} true;
    $_reverifyPost := false;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(563,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := y#0;
    havoc $w$loop#0;
    while (true)
      free invariant $PreLoopHeap$loop#0 == $Heap;
      free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
        { read($Heap, $o, $f) } 
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
      free invariant y#0 == $decr_init$loop#00 && (y#0 == $decr_init$loop#00 ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(563,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assume true;
            assume false;
        }

        assume true;
        if (100 <= x#0)
        {
            break;
        }

        $decr$loop#00 := y#0;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(563,3)
        assert false;
    }
}



procedure CheckWellformed$$_module.__default.LoopyOpaqueType(x#0: int, z#0: Box where $IsBox(z#0, #$ZOT) && $IsAllocBox(z#0, #$ZOT, $Heap));
  free requires 53 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.LoopyOpaqueType(x#0: int, z#0: Box where $IsBox(z#0, #$ZOT) && $IsAllocBox(z#0, #$ZOT, $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.LoopyOpaqueType(x#0: int, z#0: Box where $IsBox(z#0, #$ZOT) && $IsAllocBox(z#0, #$ZOT, $Heap))
   returns ($_reverifyPost: bool);
  free requires 53 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.LoopyOpaqueType(x#0: int, z#0: Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: Box;
  var $w$loop#0: bool;
  var $decr$loop#00: Box;

    // AddMethodImpl: LoopyOpaqueType, Impl$$_module.__default.LoopyOpaqueType
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(570,39): initial state"} true;
    $_reverifyPost := false;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(571,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := z#0;
    havoc $w$loop#0;
    while (true)
      free invariant $PreLoopHeap$loop#0 == $Heap;
      free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
        { read($Heap, $o, $f) } 
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
      free invariant z#0 == $decr_init$loop#00 && (z#0 == $decr_init$loop#00 ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(571,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assume true;
            assume false;
        }

        assume true;
        if (100 <= x#0)
        {
            break;
        }

        $decr$loop#00 := z#0;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(571,3)
        assert false;
    }
}



procedure CheckWellformed$$_module.__default.LoopySubsetType(x#0: int, 
    z#0: Box
       where $IsBox(z#0, Tclass._module.SubZOT())
         && $IsAllocBox(z#0, Tclass._module.SubZOT(), $Heap));
  free requires 16 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.LoopySubsetType(x#0: int, 
    z#0: Box
       where $IsBox(z#0, Tclass._module.SubZOT())
         && $IsAllocBox(z#0, Tclass._module.SubZOT(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.LoopySubsetType(x#0: int, 
    z#0: Box
       where $IsBox(z#0, Tclass._module.SubZOT())
         && $IsAllocBox(z#0, Tclass._module.SubZOT(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 16 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.LoopySubsetType(x#0: int, z#0: Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: Box;
  var $w$loop#0: bool;
  var $decr$loop#00: Box;

    // AddMethodImpl: LoopySubsetType, Impl$$_module.__default.LoopySubsetType
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(578,42): initial state"} true;
    $_reverifyPost := false;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(579,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := z#0;
    havoc $w$loop#0;
    while (true)
      free invariant $PreLoopHeap$loop#0 == $Heap;
      free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
        { read($Heap, $o, $f) } 
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
      free invariant z#0 == $decr_init$loop#00 && (z#0 == $decr_init$loop#00 ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(579,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assume true;
            assume false;
        }

        assume true;
        if (100 <= x#0)
        {
            break;
        }

        $decr$loop#00 := z#0;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(579,3)
        assert false;
    }
}



procedure CheckWellformed$$_module.__default.LoopyForever(x#0: int, 
    f#0: DatatypeType
       where $Is(f#0, Tclass._module.Forever())
         && $IsAlloc(f#0, Tclass._module.Forever(), $Heap)
         && $IsA#_module.Forever(f#0));
  free requires 17 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.LoopyForever(x#0: int, 
    f#0: DatatypeType
       where $Is(f#0, Tclass._module.Forever())
         && $IsAlloc(f#0, Tclass._module.Forever(), $Heap)
         && $IsA#_module.Forever(f#0));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.LoopyForever(x#0: int, 
    f#0: DatatypeType
       where $Is(f#0, Tclass._module.Forever())
         && $IsAlloc(f#0, Tclass._module.Forever(), $Heap)
         && $IsA#_module.Forever(f#0))
   returns ($_reverifyPost: bool);
  free requires 17 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.LoopyForever(x#0: int, f#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var f#1: DatatypeType
     where $Is(f#1, Tclass._module.Forever())
       && $IsAlloc(f#1, Tclass._module.Forever(), $Heap);
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: DatatypeType;
  var $w$loop#0: bool;
  var $decr$loop#00: DatatypeType;

    // AddMethodImpl: LoopyForever, Impl$$_module.__default.LoopyForever
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(587,40): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(588,9)
    assume true;
    assume true;
    f#1 := f#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(588,12)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(589,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := f#1;
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
      free invariant DtRank(f#1) <= DtRank($decr_init$loop#00)
         && (DtRank(f#1) == DtRank($decr_init$loop#00) ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(589,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assume true;
            assume false;
        }

        assume true;
        if (100 <= x#0)
        {
            break;
        }

        $decr$loop#00 := f#1;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(592,7)
        assume true;
        assume _module.Forever.More_q(f#1);
        assume _module.Forever.More_q(f#1);
        f#1 := _module.Forever.next(f#1);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(592,15)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(589,3)
        assert DtRank(f#1) < DtRank($decr$loop#00);
    }
}



procedure CheckWellformed$$_module.__default.GoodLoop(_module._default.GoodLoop$Y: Ty, 
    x#0: int, 
    y#0: Box
       where $IsBox(y#0, _module._default.GoodLoop$Y)
         && $IsAllocBox(y#0, _module._default.GoodLoop$Y, $Heap), 
    z0#0: Box where $IsBox(z0#0, #$ZOT) && $IsAllocBox(z0#0, #$ZOT, $Heap), 
    z1#0: Box
       where $IsBox(z1#0, Tclass._module.SubZOT())
         && $IsAllocBox(z1#0, Tclass._module.SubZOT(), $Heap), 
    f#0: HandleType
       where $Is(f#0, Tclass._System.___hTotalFunc1(TInt, TInt))
         && $IsAlloc(f#0, Tclass._System.___hTotalFunc1(TInt, TInt), $Heap), 
    forever#0: DatatypeType
       where $Is(forever#0, Tclass._module.Forever())
         && $IsAlloc(forever#0, Tclass._module.Forever(), $Heap)
         && $IsA#_module.Forever(forever#0), 
    m#0: IMap Box Box
       where $Is(m#0, TIMap(TInt, TInt)) && $IsAlloc(m#0, TIMap(TInt, TInt), $Heap), 
    s#0: ISet Box where $Is(s#0, TISet(TInt)) && $IsAlloc(s#0, TISet(TInt), $Heap));
  free requires 18 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.GoodLoop(_module._default.GoodLoop$Y: Ty, 
    x#0: int, 
    y#0: Box
       where $IsBox(y#0, _module._default.GoodLoop$Y)
         && $IsAllocBox(y#0, _module._default.GoodLoop$Y, $Heap), 
    z0#0: Box where $IsBox(z0#0, #$ZOT) && $IsAllocBox(z0#0, #$ZOT, $Heap), 
    z1#0: Box
       where $IsBox(z1#0, Tclass._module.SubZOT())
         && $IsAllocBox(z1#0, Tclass._module.SubZOT(), $Heap), 
    f#0: HandleType
       where $Is(f#0, Tclass._System.___hTotalFunc1(TInt, TInt))
         && $IsAlloc(f#0, Tclass._System.___hTotalFunc1(TInt, TInt), $Heap), 
    forever#0: DatatypeType
       where $Is(forever#0, Tclass._module.Forever())
         && $IsAlloc(forever#0, Tclass._module.Forever(), $Heap)
         && $IsA#_module.Forever(forever#0), 
    m#0: IMap Box Box
       where $Is(m#0, TIMap(TInt, TInt)) && $IsAlloc(m#0, TIMap(TInt, TInt), $Heap), 
    s#0: ISet Box where $Is(s#0, TISet(TInt)) && $IsAlloc(s#0, TISet(TInt), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.GoodLoop(_module._default.GoodLoop$Y: Ty, 
    x#0: int, 
    y#0: Box
       where $IsBox(y#0, _module._default.GoodLoop$Y)
         && $IsAllocBox(y#0, _module._default.GoodLoop$Y, $Heap), 
    z0#0: Box where $IsBox(z0#0, #$ZOT) && $IsAllocBox(z0#0, #$ZOT, $Heap), 
    z1#0: Box
       where $IsBox(z1#0, Tclass._module.SubZOT())
         && $IsAllocBox(z1#0, Tclass._module.SubZOT(), $Heap), 
    f#0: HandleType
       where $Is(f#0, Tclass._System.___hTotalFunc1(TInt, TInt))
         && $IsAlloc(f#0, Tclass._System.___hTotalFunc1(TInt, TInt), $Heap), 
    forever#0: DatatypeType
       where $Is(forever#0, Tclass._module.Forever())
         && $IsAlloc(forever#0, Tclass._module.Forever(), $Heap)
         && $IsA#_module.Forever(forever#0), 
    m#0: IMap Box Box
       where $Is(m#0, TIMap(TInt, TInt)) && $IsAlloc(m#0, TIMap(TInt, TInt), $Heap), 
    s#0: ISet Box where $Is(s#0, TISet(TInt)) && $IsAlloc(s#0, TISet(TInt), $Heap))
   returns ($_reverifyPost: bool);
  free requires 18 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.GoodLoop(_module._default.GoodLoop$Y: Ty, 
    x#0: int, 
    y#0: Box, 
    z0#0: Box, 
    z1#0: Box, 
    f#0: HandleType, 
    forever#0: DatatypeType, 
    m#0: IMap Box Box, 
    s#0: ISet Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var i#0: int;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: Box;
  var $decr_init$loop#01: Box;
  var $decr_init$loop#02: Box;
  var $decr_init$loop#03: HandleType;
  var $decr_init$loop#04: DatatypeType;
  var $decr_init$loop#05: IMap Box Box;
  var $decr_init$loop#06: ISet Box;
  var $decr_init$loop#07: int;
  var $w$loop#0: bool;
  var $decr$loop#00: Box;
  var $decr$loop#01: Box;
  var $decr$loop#02: Box;
  var $decr$loop#03: HandleType;
  var $decr$loop#04: DatatypeType;
  var $decr$loop#05: IMap Box Box;
  var $decr$loop#06: ISet Box;
  var $decr$loop#07: int;

    // AddMethodImpl: GoodLoop, Impl$$_module.__default.GoodLoop
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(597,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(598,9)
    assume true;
    assume true;
    i#0 := LitInt(0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(598,12)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(599,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := y#0;
    $decr_init$loop#01 := z0#0;
    $decr_init$loop#02 := z1#0;
    $decr_init$loop#03 := f#0;
    $decr_init$loop#04 := forever#0;
    $decr_init$loop#05 := m#0;
    $decr_init$loop#06 := s#0;
    $decr_init$loop#07 := x#0 - i#0;
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
      free invariant y#0 == $decr_init$loop#00
         && (y#0 == $decr_init$loop#00
           ==> z0#0 == $decr_init$loop#01
             && (z0#0 == $decr_init$loop#01
               ==> z1#0 == $decr_init$loop#02
                 && (z1#0 == $decr_init$loop#02
                   ==> f#0 == $decr_init$loop#03
                     && (f#0 == $decr_init$loop#03
                       ==> DtRank(forever#0) <= DtRank($decr_init$loop#04)
                         && (DtRank(forever#0) == DtRank($decr_init$loop#04)
                           ==> ISet#Equal(IMap#Domain(m#0), IMap#Domain($decr_init$loop#05))
                             && (ISet#Equal(IMap#Domain(m#0), IMap#Domain($decr_init$loop#05))
                               ==> ISet#Equal(s#0, $decr_init$loop#06)
                                 && (ISet#Equal(s#0, $decr_init$loop#06)
                                   ==> x#0 - i#0 <= $decr_init$loop#07 && (x#0 - i#0 == $decr_init$loop#07 ==> true))))))));
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(599,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assume true;
            assume true;
            assume true;
            assume true;
            assume true;
            assume true;
            assume true;
            assume true;
            assume false;
        }

        assume true;
        if (x#0 <= i#0)
        {
            break;
        }

        $decr$loop#00 := y#0;
        $decr$loop#01 := z0#0;
        $decr$loop#02 := z1#0;
        $decr$loop#03 := f#0;
        $decr$loop#04 := forever#0;
        $decr$loop#05 := m#0;
        $decr$loop#06 := s#0;
        $decr$loop#07 := x#0 - i#0;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(602,7)
        assume true;
        assume true;
        i#0 := i#0 + 1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(602,14)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Termination.dfy(599,3)
        assert 0 <= $decr$loop#07
           || DtRank(forever#0) < DtRank($decr$loop#04)
           || x#0 - i#0 == $decr$loop#07;
        assert y#0 == $decr$loop#00
           && 
          z0#0 == $decr$loop#01
           && 
          z1#0 == $decr$loop#02
           && 
          f#0 == $decr$loop#03
           && (DtRank(forever#0) < DtRank($decr$loop#04)
             || (DtRank(forever#0) == DtRank($decr$loop#04)
               && 
              ISet#Equal(IMap#Domain(m#0), IMap#Domain($decr$loop#05))
               && 
              ISet#Equal(s#0, $decr$loop#06)
               && x#0 - i#0 < $decr$loop#07));
    }
}



const unique class.MultisetTests.__default: ClassName;

function Tclass.MultisetTests.__default() : Ty;

const unique Tagclass.MultisetTests.__default: TyTag;

// Tclass.MultisetTests.__default Tag
axiom Tag(Tclass.MultisetTests.__default()) == Tagclass.MultisetTests.__default
   && TagFamily(Tclass.MultisetTests.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.MultisetTests.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.MultisetTests.__default()) } 
  $IsBox(bx, Tclass.MultisetTests.__default())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.MultisetTests.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.MultisetTests.__default()) } 
  $Is($o, Tclass.MultisetTests.__default())
     <==> $o == null || dtype($o) == Tclass.MultisetTests.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.MultisetTests.__default(), $h) } 
  $IsAlloc($o, Tclass.MultisetTests.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

// function declaration for MultisetTests._default.F
function MultisetTests.__default.F($ly: LayerType, a#0: MultiSet Box, n#0: int) : int;

function MultisetTests.__default.F#canCall(a#0: MultiSet Box, n#0: int) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, a#0: MultiSet Box, n#0: int :: 
  { MultisetTests.__default.F($LS($ly), a#0, n#0) } 
  MultisetTests.__default.F($LS($ly), a#0, n#0)
     == MultisetTests.__default.F($ly, a#0, n#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, a#0: MultiSet Box, n#0: int :: 
  { MultisetTests.__default.F(AsFuelBottom($ly), a#0, n#0) } 
  MultisetTests.__default.F($ly, a#0, n#0)
     == MultisetTests.__default.F($LZ, a#0, n#0));

// consequence axiom for MultisetTests.__default.F
axiom true
   ==> (forall $ly: LayerType, a#0: MultiSet Box, n#0: int :: 
    { MultisetTests.__default.F($ly, a#0, n#0) } 
    MultisetTests.__default.F#canCall(a#0, n#0)
         || ($Is(a#0, TMultiSet(TInt)) && LitInt(0) <= n#0)
       ==> true);

function MultisetTests.__default.F#requires(LayerType, MultiSet Box, int) : bool;

// #requires axiom for MultisetTests.__default.F
axiom (forall $ly: LayerType, a#0: MultiSet Box, n#0: int :: 
  { MultisetTests.__default.F#requires($ly, a#0, n#0) } 
  $Is(a#0, TMultiSet(TInt)) && LitInt(0) <= n#0
     ==> MultisetTests.__default.F#requires($ly, a#0, n#0) == true);

// definition axiom for MultisetTests.__default.F (revealed)
axiom true
   ==> (forall $ly: LayerType, a#0: MultiSet Box, n#0: int :: 
    { MultisetTests.__default.F($LS($ly), a#0, n#0) } 
    MultisetTests.__default.F#canCall(a#0, n#0)
         || ($Is(a#0, TMultiSet(TInt)) && LitInt(0) <= n#0)
       ==> (n#0 != LitInt(0) ==> MultisetTests.__default.F#canCall(a#0, n#0 - 1))
         && MultisetTests.__default.F($LS($ly), a#0, n#0)
           == (if n#0 == LitInt(0) then 0 else MultisetTests.__default.F($ly, a#0, n#0 - 1)));

// definition axiom for MultisetTests.__default.F for all literals (revealed)
axiom true
   ==> (forall $ly: LayerType, a#0: MultiSet Box, n#0: int :: 
    {:weight 3} { MultisetTests.__default.F($LS($ly), Lit(a#0), LitInt(n#0)) } 
    MultisetTests.__default.F#canCall(Lit(a#0), LitInt(n#0))
         || ($Is(a#0, TMultiSet(TInt)) && LitInt(0) <= n#0)
       ==> (LitInt(n#0) != LitInt(0)
           ==> MultisetTests.__default.F#canCall(Lit(a#0), LitInt(n#0 - 1)))
         && MultisetTests.__default.F($LS($ly), Lit(a#0), LitInt(n#0))
           == (if LitInt(n#0) == LitInt(0)
             then 0
             else MultisetTests.__default.F($LS($ly), Lit(a#0), LitInt(n#0 - 1))));

// function declaration for MultisetTests._default.F'
function MultisetTests.__default.F_k($ly: LayerType, a#0: MultiSet Box, n#0: int) : int;

function MultisetTests.__default.F_k#canCall(a#0: MultiSet Box, n#0: int) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, a#0: MultiSet Box, n#0: int :: 
  { MultisetTests.__default.F_k($LS($ly), a#0, n#0) } 
  MultisetTests.__default.F_k($LS($ly), a#0, n#0)
     == MultisetTests.__default.F_k($ly, a#0, n#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, a#0: MultiSet Box, n#0: int :: 
  { MultisetTests.__default.F_k(AsFuelBottom($ly), a#0, n#0) } 
  MultisetTests.__default.F_k($ly, a#0, n#0)
     == MultisetTests.__default.F_k($LZ, a#0, n#0));

// consequence axiom for MultisetTests.__default.F_k
axiom true
   ==> (forall $ly: LayerType, a#0: MultiSet Box, n#0: int :: 
    { MultisetTests.__default.F_k($ly, a#0, n#0) } 
    MultisetTests.__default.F_k#canCall(a#0, n#0)
         || ($Is(a#0, TMultiSet(TInt)) && LitInt(0) <= n#0)
       ==> true);

function MultisetTests.__default.F_k#requires(LayerType, MultiSet Box, int) : bool;

// #requires axiom for MultisetTests.__default.F_k
axiom (forall $ly: LayerType, a#0: MultiSet Box, n#0: int :: 
  { MultisetTests.__default.F_k#requires($ly, a#0, n#0) } 
  $Is(a#0, TMultiSet(TInt)) && LitInt(0) <= n#0
     ==> MultisetTests.__default.F_k#requires($ly, a#0, n#0) == true);

// definition axiom for MultisetTests.__default.F_k (revealed)
axiom true
   ==> (forall $ly: LayerType, a#0: MultiSet Box, n#0: int :: 
    { MultisetTests.__default.F_k($LS($ly), a#0, n#0) } 
    MultisetTests.__default.F_k#canCall(a#0, n#0)
         || ($Is(a#0, TMultiSet(TInt)) && LitInt(0) <= n#0)
       ==> (n#0 != LitInt(0) ==> MultisetTests.__default.F_k#canCall(a#0, n#0 - 1))
         && MultisetTests.__default.F_k($LS($ly), a#0, n#0)
           == (if n#0 == LitInt(0) then 0 else MultisetTests.__default.F_k($ly, a#0, n#0 - 1)));

// definition axiom for MultisetTests.__default.F_k for all literals (revealed)
axiom true
   ==> (forall $ly: LayerType, a#0: MultiSet Box, n#0: int :: 
    {:weight 3} { MultisetTests.__default.F_k($LS($ly), Lit(a#0), LitInt(n#0)) } 
    MultisetTests.__default.F_k#canCall(Lit(a#0), LitInt(n#0))
         || ($Is(a#0, TMultiSet(TInt)) && LitInt(0) <= n#0)
       ==> (LitInt(n#0) != LitInt(0)
           ==> MultisetTests.__default.F_k#canCall(Lit(a#0), LitInt(n#0 - 1)))
         && MultisetTests.__default.F_k($LS($ly), Lit(a#0), LitInt(n#0))
           == (if LitInt(n#0) == LitInt(0)
             then 0
             else MultisetTests.__default.F_k($LS($ly), Lit(a#0), LitInt(n#0 - 1))));

const unique class.MapTests.__default: ClassName;

function Tclass.MapTests.__default() : Ty;

const unique Tagclass.MapTests.__default: TyTag;

// Tclass.MapTests.__default Tag
axiom Tag(Tclass.MapTests.__default()) == Tagclass.MapTests.__default
   && TagFamily(Tclass.MapTests.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.MapTests.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.MapTests.__default()) } 
  $IsBox(bx, Tclass.MapTests.__default())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.MapTests.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.MapTests.__default()) } 
  $Is($o, Tclass.MapTests.__default())
     <==> $o == null || dtype($o) == Tclass.MapTests.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.MapTests.__default(), $h) } 
  $IsAlloc($o, Tclass.MapTests.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

// function declaration for MapTests._default.F
function MapTests.__default.F($ly: LayerType, a#0: Map Box Box, n#0: int) : int;

function MapTests.__default.F#canCall(a#0: Map Box Box, n#0: int) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, a#0: Map Box Box, n#0: int :: 
  { MapTests.__default.F($LS($ly), a#0, n#0) } 
  MapTests.__default.F($LS($ly), a#0, n#0) == MapTests.__default.F($ly, a#0, n#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, a#0: Map Box Box, n#0: int :: 
  { MapTests.__default.F(AsFuelBottom($ly), a#0, n#0) } 
  MapTests.__default.F($ly, a#0, n#0) == MapTests.__default.F($LZ, a#0, n#0));

// consequence axiom for MapTests.__default.F
axiom true
   ==> (forall $ly: LayerType, a#0: Map Box Box, n#0: int :: 
    { MapTests.__default.F($ly, a#0, n#0) } 
    MapTests.__default.F#canCall(a#0, n#0)
         || ($Is(a#0, TMap(TInt, TInt)) && LitInt(0) <= n#0)
       ==> true);

function MapTests.__default.F#requires(LayerType, Map Box Box, int) : bool;

// #requires axiom for MapTests.__default.F
axiom (forall $ly: LayerType, a#0: Map Box Box, n#0: int :: 
  { MapTests.__default.F#requires($ly, a#0, n#0) } 
  $Is(a#0, TMap(TInt, TInt)) && LitInt(0) <= n#0
     ==> MapTests.__default.F#requires($ly, a#0, n#0) == true);

// definition axiom for MapTests.__default.F (revealed)
axiom true
   ==> (forall $ly: LayerType, a#0: Map Box Box, n#0: int :: 
    { MapTests.__default.F($LS($ly), a#0, n#0) } 
    MapTests.__default.F#canCall(a#0, n#0)
         || ($Is(a#0, TMap(TInt, TInt)) && LitInt(0) <= n#0)
       ==> (n#0 != LitInt(0) ==> MapTests.__default.F#canCall(a#0, n#0 - 1))
         && MapTests.__default.F($LS($ly), a#0, n#0)
           == (if n#0 == LitInt(0) then 0 else MapTests.__default.F($ly, a#0, n#0 - 1)));

// definition axiom for MapTests.__default.F for all literals (revealed)
axiom true
   ==> (forall $ly: LayerType, a#0: Map Box Box, n#0: int :: 
    {:weight 3} { MapTests.__default.F($LS($ly), Lit(a#0), LitInt(n#0)) } 
    MapTests.__default.F#canCall(Lit(a#0), LitInt(n#0))
         || ($Is(a#0, TMap(TInt, TInt)) && LitInt(0) <= n#0)
       ==> (LitInt(n#0) != LitInt(0)
           ==> MapTests.__default.F#canCall(Lit(a#0), LitInt(n#0 - 1)))
         && MapTests.__default.F($LS($ly), Lit(a#0), LitInt(n#0))
           == (if LitInt(n#0) == LitInt(0)
             then 0
             else MapTests.__default.F($LS($ly), Lit(a#0), LitInt(n#0 - 1))));

// function declaration for MapTests._default.F'
function MapTests.__default.F_k($ly: LayerType, a#0: Map Box Box, n#0: int) : int;

function MapTests.__default.F_k#canCall(a#0: Map Box Box, n#0: int) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, a#0: Map Box Box, n#0: int :: 
  { MapTests.__default.F_k($LS($ly), a#0, n#0) } 
  MapTests.__default.F_k($LS($ly), a#0, n#0)
     == MapTests.__default.F_k($ly, a#0, n#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, a#0: Map Box Box, n#0: int :: 
  { MapTests.__default.F_k(AsFuelBottom($ly), a#0, n#0) } 
  MapTests.__default.F_k($ly, a#0, n#0) == MapTests.__default.F_k($LZ, a#0, n#0));

// consequence axiom for MapTests.__default.F_k
axiom true
   ==> (forall $ly: LayerType, a#0: Map Box Box, n#0: int :: 
    { MapTests.__default.F_k($ly, a#0, n#0) } 
    MapTests.__default.F_k#canCall(a#0, n#0)
         || ($Is(a#0, TMap(TInt, TInt)) && LitInt(0) <= n#0)
       ==> true);

function MapTests.__default.F_k#requires(LayerType, Map Box Box, int) : bool;

// #requires axiom for MapTests.__default.F_k
axiom (forall $ly: LayerType, a#0: Map Box Box, n#0: int :: 
  { MapTests.__default.F_k#requires($ly, a#0, n#0) } 
  $Is(a#0, TMap(TInt, TInt)) && LitInt(0) <= n#0
     ==> MapTests.__default.F_k#requires($ly, a#0, n#0) == true);

// definition axiom for MapTests.__default.F_k (revealed)
axiom true
   ==> (forall $ly: LayerType, a#0: Map Box Box, n#0: int :: 
    { MapTests.__default.F_k($LS($ly), a#0, n#0) } 
    MapTests.__default.F_k#canCall(a#0, n#0)
         || ($Is(a#0, TMap(TInt, TInt)) && LitInt(0) <= n#0)
       ==> (n#0 != LitInt(0) ==> MapTests.__default.F_k#canCall(a#0, n#0 - 1))
         && MapTests.__default.F_k($LS($ly), a#0, n#0)
           == (if n#0 == LitInt(0) then 0 else MapTests.__default.F_k($ly, a#0, n#0 - 1)));

// definition axiom for MapTests.__default.F_k for all literals (revealed)
axiom true
   ==> (forall $ly: LayerType, a#0: Map Box Box, n#0: int :: 
    {:weight 3} { MapTests.__default.F_k($LS($ly), Lit(a#0), LitInt(n#0)) } 
    MapTests.__default.F_k#canCall(Lit(a#0), LitInt(n#0))
         || ($Is(a#0, TMap(TInt, TInt)) && LitInt(0) <= n#0)
       ==> (LitInt(n#0) != LitInt(0)
           ==> MapTests.__default.F_k#canCall(Lit(a#0), LitInt(n#0 - 1)))
         && MapTests.__default.F_k($LS($ly), Lit(a#0), LitInt(n#0))
           == (if LitInt(n#0) == LitInt(0)
             then 0
             else MapTests.__default.F_k($LS($ly), Lit(a#0), LitInt(n#0 - 1))));

const unique class.TerminationRefinement0.__default: ClassName;

function Tclass.TerminationRefinement0.__default() : Ty;

const unique Tagclass.TerminationRefinement0.__default: TyTag;

// Tclass.TerminationRefinement0.__default Tag
axiom Tag(Tclass.TerminationRefinement0.__default())
     == Tagclass.TerminationRefinement0.__default
   && TagFamily(Tclass.TerminationRefinement0.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.TerminationRefinement0.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.TerminationRefinement0.__default()) } 
  $IsBox(bx, Tclass.TerminationRefinement0.__default())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.TerminationRefinement0.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.TerminationRefinement0.__default()) } 
  $Is($o, Tclass.TerminationRefinement0.__default())
     <==> $o == null || dtype($o) == Tclass.TerminationRefinement0.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.TerminationRefinement0.__default(), $h) } 
  $IsAlloc($o, Tclass.TerminationRefinement0.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

const unique class.TerminationRefinement1.__default: ClassName;

function Tclass.TerminationRefinement1.__default() : Ty;

const unique Tagclass.TerminationRefinement1.__default: TyTag;

// Tclass.TerminationRefinement1.__default Tag
axiom Tag(Tclass.TerminationRefinement1.__default())
     == Tagclass.TerminationRefinement1.__default
   && TagFamily(Tclass.TerminationRefinement1.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.TerminationRefinement1.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.TerminationRefinement1.__default()) } 
  $IsBox(bx, Tclass.TerminationRefinement1.__default())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.TerminationRefinement1.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.TerminationRefinement1.__default()) } 
  $Is($o, Tclass.TerminationRefinement1.__default())
     <==> $o == null || dtype($o) == Tclass.TerminationRefinement1.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.TerminationRefinement1.__default(), $h) } 
  $IsAlloc($o, Tclass.TerminationRefinement1.__default(), $h)
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

const unique tytagFamily$_#Func2: TyTagFamily;

const unique tytagFamily$_#PartialFunc2: TyTagFamily;

const unique tytagFamily$_#TotalFunc2: TyTagFamily;

const unique tytagFamily$_#Func3: TyTagFamily;

const unique tytagFamily$_#PartialFunc3: TyTagFamily;

const unique tytagFamily$_#TotalFunc3: TyTagFamily;

const unique tytagFamily$_tuple#2: TyTagFamily;

const unique tytagFamily$_tuple#0: TyTagFamily;

const unique tytagFamily$Termination: TyTagFamily;

const unique tytagFamily$List: TyTagFamily;

const unique tytagFamily$Node: TyTagFamily;

const unique tytagFamily$TopElements: TyTagFamily;

const unique tytagFamily$DefaultDecreasesFunction: TyTagFamily;

const unique tytagFamily$C: TyTagFamily;

const unique tytagFamily$Tree: TyTagFamily;

const unique tytagFamily$SubZOT: TyTagFamily;

const unique tytagFamily$Forever: TyTagFamily;

const unique tytagFamily$_default: TyTagFamily;

const unique field$next: NameFamily;

const unique field$footprint: NameFamily;

const unique field$count: NameFamily;

const unique field$data: NameFamily;

const unique field$Repr: NameFamily;

const unique field$v: NameFamily;
