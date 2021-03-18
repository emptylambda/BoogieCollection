// Dafny 3.0.0.30204
// Command Line Options: -compile:0 -noVerify /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy -print:./Definedness.bpl

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

const unique class._module.SoWellformed?: ClassName;

function Tclass._module.SoWellformed?() : Ty;

const unique Tagclass._module.SoWellformed?: TyTag;

// Tclass._module.SoWellformed? Tag
axiom Tag(Tclass._module.SoWellformed?()) == Tagclass._module.SoWellformed?
   && TagFamily(Tclass._module.SoWellformed?()) == tytagFamily$SoWellformed;

// Box/unbox axiom for Tclass._module.SoWellformed?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.SoWellformed?()) } 
  $IsBox(bx, Tclass._module.SoWellformed?())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.SoWellformed?()));

// SoWellformed: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.SoWellformed?()) } 
  $Is($o, Tclass._module.SoWellformed?())
     <==> $o == null || dtype($o) == Tclass._module.SoWellformed?());

// SoWellformed: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.SoWellformed?(), $h) } 
  $IsAlloc($o, Tclass._module.SoWellformed?(), $h)
     <==> $o == null || read($h, $o, alloc));

axiom FDim(_module.SoWellformed.xyz) == 0
   && FieldOfDecl(class._module.SoWellformed?, field$xyz) == _module.SoWellformed.xyz
   && !$IsGhostField(_module.SoWellformed.xyz);

const _module.SoWellformed.xyz: Field int;

// SoWellformed.xyz: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.SoWellformed.xyz) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.SoWellformed?()
     ==> $Is(read($h, $o, _module.SoWellformed.xyz), TInt));

// SoWellformed.xyz: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.SoWellformed.xyz) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.SoWellformed?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.SoWellformed.xyz), TInt, $h));

axiom FDim(_module.SoWellformed.next) == 0
   && FieldOfDecl(class._module.SoWellformed?, field$next)
     == _module.SoWellformed.next
   && !$IsGhostField(_module.SoWellformed.next);

const _module.SoWellformed.next: Field ref;

// SoWellformed.next: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.SoWellformed.next) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.SoWellformed?()
     ==> $Is(read($h, $o, _module.SoWellformed.next), Tclass._module.SoWellformed?()));

// SoWellformed.next: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.SoWellformed.next) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.SoWellformed?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.SoWellformed.next), Tclass._module.SoWellformed?(), $h));

// function declaration for _module.SoWellformed.F
function _module.SoWellformed.F(this: ref, x#0: int) : int;

function _module.SoWellformed.F#canCall(this: ref, x#0: int) : bool;

function Tclass._module.SoWellformed() : Ty;

const unique Tagclass._module.SoWellformed: TyTag;

// Tclass._module.SoWellformed Tag
axiom Tag(Tclass._module.SoWellformed()) == Tagclass._module.SoWellformed
   && TagFamily(Tclass._module.SoWellformed()) == tytagFamily$SoWellformed;

// Box/unbox axiom for Tclass._module.SoWellformed
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.SoWellformed()) } 
  $IsBox(bx, Tclass._module.SoWellformed())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.SoWellformed()));

// consequence axiom for _module.SoWellformed.F
axiom 11 <= $FunctionContextHeight
   ==> (forall this: ref, x#0: int :: 
    { _module.SoWellformed.F(this, x#0) } 
    _module.SoWellformed.F#canCall(this, x#0)
         || (11 != $FunctionContextHeight
           && 
          this != null
           && $Is(this, Tclass._module.SoWellformed()))
       ==> true);

function _module.SoWellformed.F#requires(ref, int) : bool;

// #requires axiom for _module.SoWellformed.F
axiom (forall this: ref, x#0: int :: 
  { _module.SoWellformed.F#requires(this, x#0) } 
  this != null && $Is(this, Tclass._module.SoWellformed())
     ==> _module.SoWellformed.F#requires(this, x#0) == true);

// definition axiom for _module.SoWellformed.F (revealed)
axiom 11 <= $FunctionContextHeight
   ==> (forall this: ref, x#0: int :: 
    { _module.SoWellformed.F(this, x#0) } 
    _module.SoWellformed.F#canCall(this, x#0)
         || (11 != $FunctionContextHeight
           && 
          this != null
           && $Is(this, Tclass._module.SoWellformed()))
       ==> _module.SoWellformed.F(this, x#0) == Div(5, x#0));

// definition axiom for _module.SoWellformed.F for decreasing-related literals (revealed)
axiom 11 <= $FunctionContextHeight
   ==> (forall this: ref, x#0: int :: 
    {:weight 3} { _module.SoWellformed.F(this, LitInt(x#0)) } 
    _module.SoWellformed.F#canCall(this, LitInt(x#0))
         || (11 != $FunctionContextHeight
           && 
          this != null
           && $Is(this, Tclass._module.SoWellformed()))
       ==> _module.SoWellformed.F(this, LitInt(x#0)) == LitInt(Div(5, LitInt(x#0))));

// definition axiom for _module.SoWellformed.F for all literals (revealed)
axiom 11 <= $FunctionContextHeight
   ==> (forall this: ref, x#0: int :: 
    {:weight 3} { _module.SoWellformed.F(Lit(this), LitInt(x#0)) } 
    _module.SoWellformed.F#canCall(Lit(this), LitInt(x#0))
         || (11 != $FunctionContextHeight
           && 
          this != null
           && $Is(this, Tclass._module.SoWellformed()))
       ==> _module.SoWellformed.F(Lit(this), LitInt(x#0)) == LitInt(Div(5, LitInt(x#0))));

procedure CheckWellformed$$_module.SoWellformed.F(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.SoWellformed())
         && $IsAlloc(this, Tclass._module.SoWellformed(), $Heap), 
    x#0: int);
  free requires 11 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.SoWellformed.F(this: ref, x#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;


    // AddWellformednessCheck for function F
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(10,11): initial state"} true;
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
        assert x#0 != 0;
        assume _module.SoWellformed.F(this, x#0) == Div(5, x#0);
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.SoWellformed.F(this, x#0), TInt);
    }
}



// function declaration for _module.SoWellformed.G
function _module.SoWellformed.G(this: ref, x#0: int) : int;

function _module.SoWellformed.G#canCall(this: ref, x#0: int) : bool;

// consequence axiom for _module.SoWellformed.G
axiom 12 <= $FunctionContextHeight
   ==> (forall this: ref, x#0: int :: 
    { _module.SoWellformed.G(this, x#0) } 
    _module.SoWellformed.G#canCall(this, x#0)
         || (12 != $FunctionContextHeight
           && 
          this != null
           && $Is(this, Tclass._module.SoWellformed())
           && 0 < x#0)
       ==> true);

function _module.SoWellformed.G#requires(ref, int) : bool;

// #requires axiom for _module.SoWellformed.G
axiom (forall this: ref, x#0: int :: 
  { _module.SoWellformed.G#requires(this, x#0) } 
  this != null && $Is(this, Tclass._module.SoWellformed())
     ==> _module.SoWellformed.G#requires(this, x#0) == (0 < x#0));

// definition axiom for _module.SoWellformed.G (revealed)
axiom 12 <= $FunctionContextHeight
   ==> (forall this: ref, x#0: int :: 
    { _module.SoWellformed.G(this, x#0) } 
    _module.SoWellformed.G#canCall(this, x#0)
         || (12 != $FunctionContextHeight
           && 
          this != null
           && $Is(this, Tclass._module.SoWellformed())
           && 0 < x#0)
       ==> _module.SoWellformed.G(this, x#0) == Div(5, x#0));

// definition axiom for _module.SoWellformed.G for decreasing-related literals (revealed)
axiom 12 <= $FunctionContextHeight
   ==> (forall this: ref, x#0: int :: 
    {:weight 3} { _module.SoWellformed.G(this, LitInt(x#0)) } 
    _module.SoWellformed.G#canCall(this, LitInt(x#0))
         || (12 != $FunctionContextHeight
           && 
          this != null
           && $Is(this, Tclass._module.SoWellformed())
           && Lit(0 < x#0))
       ==> _module.SoWellformed.G(this, LitInt(x#0)) == LitInt(Div(5, LitInt(x#0))));

// definition axiom for _module.SoWellformed.G for all literals (revealed)
axiom 12 <= $FunctionContextHeight
   ==> (forall this: ref, x#0: int :: 
    {:weight 3} { _module.SoWellformed.G(Lit(this), LitInt(x#0)) } 
    _module.SoWellformed.G#canCall(Lit(this), LitInt(x#0))
         || (12 != $FunctionContextHeight
           && 
          this != null
           && $Is(this, Tclass._module.SoWellformed())
           && Lit(0 < x#0))
       ==> _module.SoWellformed.G(Lit(this), LitInt(x#0)) == LitInt(Div(5, LitInt(x#0))));

procedure CheckWellformed$$_module.SoWellformed.G(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.SoWellformed())
         && $IsAlloc(this, Tclass._module.SoWellformed(), $Heap), 
    x#0: int);
  free requires 12 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.SoWellformed.G(this: ref, x#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;


    // AddWellformednessCheck for function G
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(13,11): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume 0 < x#0;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        assert x#0 != 0;
        assume _module.SoWellformed.G(this, x#0) == Div(5, x#0);
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.SoWellformed.G(this, x#0), TInt);
    }
}



// function declaration for _module.SoWellformed.H
function _module.SoWellformed.H(this: ref, x#0: int) : int;

function _module.SoWellformed.H#canCall(this: ref, x#0: int) : bool;

// consequence axiom for _module.SoWellformed.H
axiom 13 <= $FunctionContextHeight
   ==> (forall this: ref, x#0: int :: 
    { _module.SoWellformed.H(this, x#0) } 
    _module.SoWellformed.H#canCall(this, x#0)
         || (13 != $FunctionContextHeight
           && 
          this != null
           && $Is(this, Tclass._module.SoWellformed()))
       ==> true);

function _module.SoWellformed.H#requires(ref, int) : bool;

// #requires axiom for _module.SoWellformed.H
axiom (forall this: ref, x#0: int :: 
  { _module.SoWellformed.H#requires(this, x#0) } 
  this != null && $Is(this, Tclass._module.SoWellformed())
     ==> _module.SoWellformed.H#requires(this, x#0) == true);

// definition axiom for _module.SoWellformed.H (revealed)
axiom 13 <= $FunctionContextHeight
   ==> (forall this: ref, x#0: int :: 
    { _module.SoWellformed.H(this, x#0) } 
    _module.SoWellformed.H#canCall(this, x#0)
         || (13 != $FunctionContextHeight
           && 
          this != null
           && $Is(this, Tclass._module.SoWellformed()))
       ==> _module.SoWellformed.H(this, x#0) == LitInt(12));

// definition axiom for _module.SoWellformed.H for decreasing-related literals (revealed)
axiom 13 <= $FunctionContextHeight
   ==> (forall this: ref, x#0: int :: 
    {:weight 3} { _module.SoWellformed.H(this, LitInt(x#0)) } 
    _module.SoWellformed.H#canCall(this, LitInt(x#0))
         || (13 != $FunctionContextHeight
           && 
          this != null
           && $Is(this, Tclass._module.SoWellformed()))
       ==> _module.SoWellformed.H(this, LitInt(x#0)) == LitInt(12));

// definition axiom for _module.SoWellformed.H for all literals (revealed)
axiom 13 <= $FunctionContextHeight
   ==> (forall this: ref, x#0: int :: 
    {:weight 3} { _module.SoWellformed.H(Lit(this), LitInt(x#0)) } 
    _module.SoWellformed.H#canCall(Lit(this), LitInt(x#0))
         || (13 != $FunctionContextHeight
           && 
          this != null
           && $Is(this, Tclass._module.SoWellformed()))
       ==> _module.SoWellformed.H(Lit(this), LitInt(x#0)) == LitInt(12));

procedure CheckWellformed$$_module.SoWellformed.H(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.SoWellformed())
         && $IsAlloc(this, Tclass._module.SoWellformed(), $Heap), 
    x#0: int);
  free requires 13 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.SoWellformed.H(this: ref, x#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;


    // AddWellformednessCheck for function H
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(17,11): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assert x#0 != 0;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        assume _module.SoWellformed.H(this, x#0) == LitInt(12);
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.SoWellformed.H(this, x#0), TInt);
    }
}



// function declaration for _module.SoWellformed.I
function _module.SoWellformed.I(this: ref, x#0: int) : int;

function _module.SoWellformed.I#canCall(this: ref, x#0: int) : bool;

// consequence axiom for _module.SoWellformed.I
axiom 14 <= $FunctionContextHeight
   ==> (forall this: ref, x#0: int :: 
    { _module.SoWellformed.I(this, x#0) } 
    _module.SoWellformed.I#canCall(this, x#0)
         || (14 != $FunctionContextHeight
           && 
          this != null
           && $Is(this, Tclass._module.SoWellformed())
           && 0 < x#0)
       ==> true);

function _module.SoWellformed.I#requires(ref, int) : bool;

// #requires axiom for _module.SoWellformed.I
axiom (forall this: ref, x#0: int :: 
  { _module.SoWellformed.I#requires(this, x#0) } 
  this != null && $Is(this, Tclass._module.SoWellformed())
     ==> _module.SoWellformed.I#requires(this, x#0) == (0 < x#0));

// definition axiom for _module.SoWellformed.I (revealed)
axiom 14 <= $FunctionContextHeight
   ==> (forall this: ref, x#0: int :: 
    { _module.SoWellformed.I(this, x#0) } 
    _module.SoWellformed.I#canCall(this, x#0)
         || (14 != $FunctionContextHeight
           && 
          this != null
           && $Is(this, Tclass._module.SoWellformed())
           && 0 < x#0)
       ==> _module.SoWellformed.I(this, x#0) == LitInt(12));

// definition axiom for _module.SoWellformed.I for decreasing-related literals (revealed)
axiom 14 <= $FunctionContextHeight
   ==> (forall this: ref, x#0: int :: 
    {:weight 3} { _module.SoWellformed.I(this, LitInt(x#0)) } 
    _module.SoWellformed.I#canCall(this, LitInt(x#0))
         || (14 != $FunctionContextHeight
           && 
          this != null
           && $Is(this, Tclass._module.SoWellformed())
           && Lit(0 < x#0))
       ==> _module.SoWellformed.I(this, LitInt(x#0)) == LitInt(12));

// definition axiom for _module.SoWellformed.I for all literals (revealed)
axiom 14 <= $FunctionContextHeight
   ==> (forall this: ref, x#0: int :: 
    {:weight 3} { _module.SoWellformed.I(Lit(this), LitInt(x#0)) } 
    _module.SoWellformed.I#canCall(Lit(this), LitInt(x#0))
         || (14 != $FunctionContextHeight
           && 
          this != null
           && $Is(this, Tclass._module.SoWellformed())
           && Lit(0 < x#0))
       ==> _module.SoWellformed.I(Lit(this), LitInt(x#0)) == LitInt(12));

procedure CheckWellformed$$_module.SoWellformed.I(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.SoWellformed())
         && $IsAlloc(this, Tclass._module.SoWellformed(), $Heap), 
    x#0: int);
  free requires 14 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.SoWellformed.I(this: ref, x#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;


    // AddWellformednessCheck for function I
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(21,11): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume 0 < x#0;
    assert x#0 != 0;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        assume _module.SoWellformed.I(this, x#0) == LitInt(12);
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.SoWellformed.I(this, x#0), TInt);
    }
}



procedure CheckWellformed$$_module.SoWellformed.M(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.SoWellformed())
         && $IsAlloc(this, Tclass._module.SoWellformed(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._module.SoWellformed?())
         && $IsAlloc(a#0, Tclass._module.SoWellformed?(), $Heap), 
    b#0: int)
   returns (c#0: bool, 
    d#0: ref
       where $Is(d#0, Tclass._module.SoWellformed?())
         && $IsAlloc(d#0, Tclass._module.SoWellformed?(), $Heap));
  free requires 15 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.SoWellformed.M(this: ref, a#0: ref, b#0: int) returns (c#0: bool, d#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: M, CheckWellformed$$_module.SoWellformed.M
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(26,9): initial state"} true;
    assert a#0 != null;
    assume read($Heap, a#0, _module.SoWellformed.xyz) == LitInt(7);
    assert b#0 != 0;
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
    assume $HeapSucc(old($Heap), $Heap);
    havoc c#0, d#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(28,14): post-state"} true;
    if (*)
    {
        assume c#0;
        assert d#0 != null;
        assume read($Heap, d#0, _module.SoWellformed.xyz) == LitInt(-7);
    }
    else
    {
        assume c#0 ==> read($Heap, d#0, _module.SoWellformed.xyz) == LitInt(-7);
    }
}



procedure Call$$_module.SoWellformed.M(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.SoWellformed())
         && $IsAlloc(this, Tclass._module.SoWellformed(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._module.SoWellformed?())
         && $IsAlloc(a#0, Tclass._module.SoWellformed?(), $Heap), 
    b#0: int)
   returns (c#0: bool, 
    d#0: ref
       where $Is(d#0, Tclass._module.SoWellformed?())
         && $IsAlloc(d#0, Tclass._module.SoWellformed?(), $Heap));
  // user-defined preconditions
  requires read($Heap, a#0, _module.SoWellformed.xyz) == LitInt(7);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures c#0 ==> read($Heap, d#0, _module.SoWellformed.xyz) == LitInt(-7);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.SoWellformed.M(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.SoWellformed())
         && $IsAlloc(this, Tclass._module.SoWellformed(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._module.SoWellformed?())
         && $IsAlloc(a#0, Tclass._module.SoWellformed?(), $Heap), 
    b#0: int)
   returns (c#0: bool, 
    d#0: ref
       where $Is(d#0, Tclass._module.SoWellformed?())
         && $IsAlloc(d#0, Tclass._module.SoWellformed?(), $Heap), 
    $_reverifyPost: bool);
  free requires 15 == $FunctionContextHeight;
  // user-defined preconditions
  requires read($Heap, a#0, _module.SoWellformed.xyz) == LitInt(7);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures c#0 ==> read($Heap, d#0, _module.SoWellformed.xyz) == LitInt(-7);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.SoWellformed.M(this: ref, a#0: ref, b#0: int)
   returns (c#0: bool, d#0: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: M, Impl$$_module.SoWellformed.M
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(30,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(31,7)
    assume true;
    assume true;
    c#0 := Lit(false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(31,14)"} true;
}



procedure CheckWellformed$$_module.SoWellformed.N(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.SoWellformed())
         && $IsAlloc(this, Tclass._module.SoWellformed(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._module.SoWellformed?())
         && $IsAlloc(a#0, Tclass._module.SoWellformed?(), $Heap), 
    b#0: int)
   returns (c#0: bool, 
    d#0: ref
       where $Is(d#0, Tclass._module.SoWellformed?())
         && $IsAlloc(d#0, Tclass._module.SoWellformed?(), $Heap));
  free requires 16 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.SoWellformed.N(this: ref, a#0: ref, b#0: int) returns (c#0: bool, d#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: N, CheckWellformed$$_module.SoWellformed.N
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(34,9): initial state"} true;
    assert a#0 != null;
    assume read($Heap, a#0, _module.SoWellformed.next) != null;
    assert a#0 != null;
    assert read($Heap, a#0, _module.SoWellformed.next) != null;
    assume read($Heap, read($Heap, a#0, _module.SoWellformed.next), _module.SoWellformed.xyz)
       == LitInt(7);
    assume b#0 < -2;
    assert b#0 != 0;
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
    assume $HeapSucc(old($Heap), $Heap);
    havoc c#0, d#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(39,19): post-state"} true;
    if (*)
    {
        assume LitInt(0) <= b#0;
        assert d#0 != null;
        assume read($Heap, d#0, _module.SoWellformed.xyz) == LitInt(-7);
        assume !c#0;
    }
    else
    {
        assume LitInt(0) <= b#0
           ==> read($Heap, d#0, _module.SoWellformed.xyz) == LitInt(-7) && !c#0;
    }
}



procedure Call$$_module.SoWellformed.N(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.SoWellformed())
         && $IsAlloc(this, Tclass._module.SoWellformed(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._module.SoWellformed?())
         && $IsAlloc(a#0, Tclass._module.SoWellformed?(), $Heap), 
    b#0: int)
   returns (c#0: bool, 
    d#0: ref
       where $Is(d#0, Tclass._module.SoWellformed?())
         && $IsAlloc(d#0, Tclass._module.SoWellformed?(), $Heap));
  // user-defined preconditions
  requires read($Heap, a#0, _module.SoWellformed.next) != null;
  requires read($Heap, read($Heap, a#0, _module.SoWellformed.next), _module.SoWellformed.xyz)
     == LitInt(7);
  requires b#0 < -2;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures LitInt(0) <= b#0 ==> read($Heap, d#0, _module.SoWellformed.xyz) == LitInt(-7);
  ensures LitInt(0) <= b#0 ==> !c#0;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.SoWellformed.N(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.SoWellformed())
         && $IsAlloc(this, Tclass._module.SoWellformed(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._module.SoWellformed?())
         && $IsAlloc(a#0, Tclass._module.SoWellformed?(), $Heap), 
    b#0: int)
   returns (c#0: bool, 
    d#0: ref
       where $Is(d#0, Tclass._module.SoWellformed?())
         && $IsAlloc(d#0, Tclass._module.SoWellformed?(), $Heap), 
    $_reverifyPost: bool);
  free requires 16 == $FunctionContextHeight;
  // user-defined preconditions
  requires read($Heap, a#0, _module.SoWellformed.next) != null;
  requires read($Heap, read($Heap, a#0, _module.SoWellformed.next), _module.SoWellformed.xyz)
     == LitInt(7);
  requires b#0 < -2;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures LitInt(0) <= b#0 ==> read($Heap, d#0, _module.SoWellformed.xyz) == LitInt(-7);
  ensures LitInt(0) <= b#0 ==> !c#0;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.SoWellformed.N(this: ref, a#0: ref, b#0: int)
   returns (c#0: bool, d#0: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: N, Impl$$_module.SoWellformed.N
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(40,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(41,7)
    assume true;
    assume true;
    c#0 := Lit(true);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(41,13)"} true;
}



procedure CheckWellformed$$_module.SoWellformed.O(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.SoWellformed())
         && $IsAlloc(this, Tclass._module.SoWellformed(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._module.SoWellformed?())
         && $IsAlloc(a#0, Tclass._module.SoWellformed?(), $Heap), 
    b#0: int)
   returns (c#0: bool, 
    d#0: ref
       where $Is(d#0, Tclass._module.SoWellformed?())
         && $IsAlloc(d#0, Tclass._module.SoWellformed?(), $Heap));
  free requires 17 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.SoWellformed.O(this: ref, a#0: ref, b#0: int) returns (c#0: bool, d#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: O, CheckWellformed$$_module.SoWellformed.O
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> $o == read($Heap, a#0, _module.SoWellformed.next));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(44,9): initial state"} true;
    assert a#0 != null;
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc)
         ==> $Heap[$o] == old($Heap)[$o]
           || $o == read(old($Heap), a#0, _module.SoWellformed.next));
    assume $HeapSucc(old($Heap), $Heap);
    havoc c#0, d#0;
}



procedure Call$$_module.SoWellformed.O(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.SoWellformed())
         && $IsAlloc(this, Tclass._module.SoWellformed(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._module.SoWellformed?())
         && $IsAlloc(a#0, Tclass._module.SoWellformed?(), $Heap), 
    b#0: int)
   returns (c#0: bool, 
    d#0: ref
       where $Is(d#0, Tclass._module.SoWellformed?())
         && $IsAlloc(d#0, Tclass._module.SoWellformed?(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || $o == read(old($Heap), a#0, _module.SoWellformed.next));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.SoWellformed.O(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.SoWellformed())
         && $IsAlloc(this, Tclass._module.SoWellformed(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._module.SoWellformed?())
         && $IsAlloc(a#0, Tclass._module.SoWellformed?(), $Heap), 
    b#0: int)
   returns (c#0: bool, 
    d#0: ref
       where $Is(d#0, Tclass._module.SoWellformed?())
         && $IsAlloc(d#0, Tclass._module.SoWellformed?(), $Heap), 
    $_reverifyPost: bool);
  free requires 17 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || $o == read(old($Heap), a#0, _module.SoWellformed.next));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure CheckWellformed$$_module.SoWellformed.P(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.SoWellformed())
         && $IsAlloc(this, Tclass._module.SoWellformed(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._module.SoWellformed?())
         && $IsAlloc(a#0, Tclass._module.SoWellformed?(), $Heap), 
    b#0: int)
   returns (c#0: bool, 
    d#0: ref
       where $Is(d#0, Tclass._module.SoWellformed?())
         && $IsAlloc(d#0, Tclass._module.SoWellformed?(), $Heap));
  free requires 18 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.SoWellformed.P(this: ref, a#0: ref, b#0: int) returns (c#0: bool, d#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: P, CheckWellformed$$_module.SoWellformed.P
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(50,9): initial state"} true;
    assume read($Heap, this, _module.SoWellformed.next) != null;
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc)
         ==> $Heap[$o] == old($Heap)[$o] || $o == this);
    assume $HeapSucc(old($Heap), $Heap);
    havoc c#0, d#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(53,21): post-state"} true;
    assert read($Heap, this, _module.SoWellformed.next) != null;
    assume read($Heap, read($Heap, this, _module.SoWellformed.next), _module.SoWellformed.xyz)
       < 100;
}



procedure Call$$_module.SoWellformed.P(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.SoWellformed())
         && $IsAlloc(this, Tclass._module.SoWellformed(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._module.SoWellformed?())
         && $IsAlloc(a#0, Tclass._module.SoWellformed?(), $Heap), 
    b#0: int)
   returns (c#0: bool, 
    d#0: ref
       where $Is(d#0, Tclass._module.SoWellformed?())
         && $IsAlloc(d#0, Tclass._module.SoWellformed?(), $Heap));
  // user-defined preconditions
  requires read($Heap, this, _module.SoWellformed.next) != null;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures read($Heap, read($Heap, this, _module.SoWellformed.next), _module.SoWellformed.xyz)
     < 100;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.SoWellformed.P(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.SoWellformed())
         && $IsAlloc(this, Tclass._module.SoWellformed(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._module.SoWellformed?())
         && $IsAlloc(a#0, Tclass._module.SoWellformed?(), $Heap), 
    b#0: int)
   returns (c#0: bool, 
    d#0: ref
       where $Is(d#0, Tclass._module.SoWellformed?())
         && $IsAlloc(d#0, Tclass._module.SoWellformed?(), $Heap), 
    $_reverifyPost: bool);
  free requires 18 == $FunctionContextHeight;
  // user-defined preconditions
  requires read($Heap, this, _module.SoWellformed.next) != null;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures read($Heap, read($Heap, this, _module.SoWellformed.next), _module.SoWellformed.xyz)
     < 100;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.SoWellformed.P(this: ref, a#0: ref, b#0: int)
   returns (c#0: bool, d#0: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: P, Impl$$_module.SoWellformed.P
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(54,2): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.SoWellformed.Q(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.SoWellformed())
         && $IsAlloc(this, Tclass._module.SoWellformed(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._module.SoWellformed?())
         && $IsAlloc(a#0, Tclass._module.SoWellformed?(), $Heap), 
    s#0: Set Box
       where $Is(s#0, TSet(Tclass._module.SoWellformed?()))
         && $IsAlloc(s#0, TSet(Tclass._module.SoWellformed?()), $Heap))
   returns (c#0: bool, 
    d#0: ref
       where $Is(d#0, Tclass._module.SoWellformed?())
         && $IsAlloc(d#0, Tclass._module.SoWellformed?(), $Heap));
  free requires 19 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.SoWellformed.Q(this: ref, a#0: ref, s#0: Set Box) returns (c#0: bool, d#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Q, CheckWellformed$$_module.SoWellformed.Q
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> s#0[$Box($o)]);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(57,9): initial state"} true;
    assume read($Heap, this, _module.SoWellformed.next) != null;
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc)
         ==> $Heap[$o] == old($Heap)[$o] || s#0[$Box($o)]);
    assume $HeapSucc(old($Heap), $Heap);
    havoc c#0, d#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(60,21): post-state"} true;
    assert read($Heap, this, _module.SoWellformed.next) != null;
    assume read($Heap, read($Heap, this, _module.SoWellformed.next), _module.SoWellformed.xyz)
       < 100;
}



procedure Call$$_module.SoWellformed.Q(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.SoWellformed())
         && $IsAlloc(this, Tclass._module.SoWellformed(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._module.SoWellformed?())
         && $IsAlloc(a#0, Tclass._module.SoWellformed?(), $Heap), 
    s#0: Set Box
       where $Is(s#0, TSet(Tclass._module.SoWellformed?()))
         && $IsAlloc(s#0, TSet(Tclass._module.SoWellformed?()), $Heap))
   returns (c#0: bool, 
    d#0: ref
       where $Is(d#0, Tclass._module.SoWellformed?())
         && $IsAlloc(d#0, Tclass._module.SoWellformed?(), $Heap));
  // user-defined preconditions
  requires read($Heap, this, _module.SoWellformed.next) != null;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures read($Heap, read($Heap, this, _module.SoWellformed.next), _module.SoWellformed.xyz)
     < 100;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || s#0[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.SoWellformed.Q(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.SoWellformed())
         && $IsAlloc(this, Tclass._module.SoWellformed(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._module.SoWellformed?())
         && $IsAlloc(a#0, Tclass._module.SoWellformed?(), $Heap), 
    s#0: Set Box
       where $Is(s#0, TSet(Tclass._module.SoWellformed?()))
         && $IsAlloc(s#0, TSet(Tclass._module.SoWellformed?()), $Heap))
   returns (c#0: bool, 
    d#0: ref
       where $Is(d#0, Tclass._module.SoWellformed?())
         && $IsAlloc(d#0, Tclass._module.SoWellformed?(), $Heap), 
    $_reverifyPost: bool);
  free requires 19 == $FunctionContextHeight;
  // user-defined preconditions
  requires read($Heap, this, _module.SoWellformed.next) != null;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures read($Heap, read($Heap, this, _module.SoWellformed.next), _module.SoWellformed.xyz)
     < 100;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || s#0[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.SoWellformed.Q(this: ref, a#0: ref, s#0: Set Box)
   returns (c#0: bool, d#0: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Q, Impl$$_module.SoWellformed.Q
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> s#0[$Box($o)]);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(61,2): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.SoWellformed.R(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.SoWellformed())
         && $IsAlloc(this, Tclass._module.SoWellformed(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._module.SoWellformed?())
         && $IsAlloc(a#0, Tclass._module.SoWellformed?(), $Heap), 
    s#0: Set Box
       where $Is(s#0, TSet(Tclass._module.SoWellformed?()))
         && $IsAlloc(s#0, TSet(Tclass._module.SoWellformed?()), $Heap))
   returns (c#0: bool, 
    d#0: ref
       where $Is(d#0, Tclass._module.SoWellformed?())
         && $IsAlloc(d#0, Tclass._module.SoWellformed?(), $Heap));
  free requires 20 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.SoWellformed.R(this: ref, a#0: ref, s#0: Set Box) returns (c#0: bool, d#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: R, CheckWellformed$$_module.SoWellformed.R
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> s#0[$Box($o)]);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(64,9): initial state"} true;
    assume read($Heap, this, _module.SoWellformed.next) != null;
    assume !s#0[$Box(this)];
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc)
         ==> $Heap[$o] == old($Heap)[$o] || s#0[$Box($o)]);
    assume $HeapSucc(old($Heap), $Heap);
    havoc c#0, d#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(67,21): post-state"} true;
    assert read($Heap, this, _module.SoWellformed.next) != null;
    assume read($Heap, read($Heap, this, _module.SoWellformed.next), _module.SoWellformed.xyz)
       < 100;
}



procedure Call$$_module.SoWellformed.R(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.SoWellformed())
         && $IsAlloc(this, Tclass._module.SoWellformed(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._module.SoWellformed?())
         && $IsAlloc(a#0, Tclass._module.SoWellformed?(), $Heap), 
    s#0: Set Box
       where $Is(s#0, TSet(Tclass._module.SoWellformed?()))
         && $IsAlloc(s#0, TSet(Tclass._module.SoWellformed?()), $Heap))
   returns (c#0: bool, 
    d#0: ref
       where $Is(d#0, Tclass._module.SoWellformed?())
         && $IsAlloc(d#0, Tclass._module.SoWellformed?(), $Heap));
  // user-defined preconditions
  requires read($Heap, this, _module.SoWellformed.next) != null;
  requires !s#0[$Box(this)];
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures read($Heap, read($Heap, this, _module.SoWellformed.next), _module.SoWellformed.xyz)
     < 100;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || s#0[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.SoWellformed.R(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.SoWellformed())
         && $IsAlloc(this, Tclass._module.SoWellformed(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._module.SoWellformed?())
         && $IsAlloc(a#0, Tclass._module.SoWellformed?(), $Heap), 
    s#0: Set Box
       where $Is(s#0, TSet(Tclass._module.SoWellformed?()))
         && $IsAlloc(s#0, TSet(Tclass._module.SoWellformed?()), $Heap))
   returns (c#0: bool, 
    d#0: ref
       where $Is(d#0, Tclass._module.SoWellformed?())
         && $IsAlloc(d#0, Tclass._module.SoWellformed?(), $Heap), 
    $_reverifyPost: bool);
  free requires 20 == $FunctionContextHeight;
  // user-defined preconditions
  requires read($Heap, this, _module.SoWellformed.next) != null;
  requires !s#0[$Box(this)];
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures read($Heap, read($Heap, this, _module.SoWellformed.next), _module.SoWellformed.xyz)
     < 100;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || s#0[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.SoWellformed.R(this: ref, a#0: ref, s#0: Set Box)
   returns (c#0: bool, d#0: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: R, Impl$$_module.SoWellformed.R
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> s#0[$Box($o)]);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(68,2): initial state"} true;
    $_reverifyPost := false;
}



// _module.SoWellformed: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.SoWellformed()) } 
  $Is(c#0, Tclass._module.SoWellformed())
     <==> $Is(c#0, Tclass._module.SoWellformed?()) && c#0 != null);

// _module.SoWellformed: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.SoWellformed(), $h) } 
  $IsAlloc(c#0, Tclass._module.SoWellformed(), $h)
     <==> $IsAlloc(c#0, Tclass._module.SoWellformed?(), $h));

const unique class._module.StatementTwoShoes?: ClassName;

function Tclass._module.StatementTwoShoes?() : Ty;

const unique Tagclass._module.StatementTwoShoes?: TyTag;

// Tclass._module.StatementTwoShoes? Tag
axiom Tag(Tclass._module.StatementTwoShoes?()) == Tagclass._module.StatementTwoShoes?
   && TagFamily(Tclass._module.StatementTwoShoes?()) == tytagFamily$StatementTwoShoes;

// Box/unbox axiom for Tclass._module.StatementTwoShoes?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.StatementTwoShoes?()) } 
  $IsBox(bx, Tclass._module.StatementTwoShoes?())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.StatementTwoShoes?()));

// StatementTwoShoes: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.StatementTwoShoes?()) } 
  $Is($o, Tclass._module.StatementTwoShoes?())
     <==> $o == null || dtype($o) == Tclass._module.StatementTwoShoes?());

// StatementTwoShoes: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.StatementTwoShoes?(), $h) } 
  $IsAlloc($o, Tclass._module.StatementTwoShoes?(), $h)
     <==> $o == null || read($h, $o, alloc));

axiom FDim(_module.StatementTwoShoes.x) == 0
   && FieldOfDecl(class._module.StatementTwoShoes?, field$x)
     == _module.StatementTwoShoes.x
   && !$IsGhostField(_module.StatementTwoShoes.x);

const _module.StatementTwoShoes.x: Field int;

// StatementTwoShoes.x: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.StatementTwoShoes.x) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.StatementTwoShoes?()
     ==> $Is(read($h, $o, _module.StatementTwoShoes.x), TInt));

// StatementTwoShoes.x: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.StatementTwoShoes.x) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.StatementTwoShoes?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.StatementTwoShoes.x), TInt, $h));

axiom FDim(_module.StatementTwoShoes.s) == 0
   && FieldOfDecl(class._module.StatementTwoShoes?, field$s)
     == _module.StatementTwoShoes.s
   && !$IsGhostField(_module.StatementTwoShoes.s);

const _module.StatementTwoShoes.s: Field ref;

// StatementTwoShoes.s: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.StatementTwoShoes.s) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.StatementTwoShoes?()
     ==> $Is(read($h, $o, _module.StatementTwoShoes.s), Tclass._module.StatementTwoShoes?()));

// StatementTwoShoes.s: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.StatementTwoShoes.s) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.StatementTwoShoes?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.StatementTwoShoes.s), 
      Tclass._module.StatementTwoShoes?(), 
      $h));

// function declaration for _module.StatementTwoShoes.F
function _module.StatementTwoShoes.F($heap: Heap, this: ref, b#0: int) : ref;

function _module.StatementTwoShoes.F#canCall($heap: Heap, this: ref, b#0: int) : bool;

function Tclass._module.StatementTwoShoes() : Ty;

const unique Tagclass._module.StatementTwoShoes: TyTag;

// Tclass._module.StatementTwoShoes Tag
axiom Tag(Tclass._module.StatementTwoShoes()) == Tagclass._module.StatementTwoShoes
   && TagFamily(Tclass._module.StatementTwoShoes()) == tytagFamily$StatementTwoShoes;

// Box/unbox axiom for Tclass._module.StatementTwoShoes
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.StatementTwoShoes()) } 
  $IsBox(bx, Tclass._module.StatementTwoShoes())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.StatementTwoShoes()));

// frame axiom for _module.StatementTwoShoes.F
axiom (forall $h0: Heap, $h1: Heap, this: ref, b#0: int :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.StatementTwoShoes.F($h1, this, b#0) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.StatementTwoShoes())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && $o == this ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.StatementTwoShoes.F($h0, this, b#0)
       == _module.StatementTwoShoes.F($h1, this, b#0));

// consequence axiom for _module.StatementTwoShoes.F
axiom 0 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref, b#0: int :: 
    { _module.StatementTwoShoes.F($Heap, this, b#0) } 
    _module.StatementTwoShoes.F#canCall($Heap, this, b#0)
         || (0 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.StatementTwoShoes())
           && $IsAlloc(this, Tclass._module.StatementTwoShoes(), $Heap)
           && LitInt(0) <= b#0)
       ==> $Is(_module.StatementTwoShoes.F($Heap, this, b#0), 
        Tclass._module.StatementTwoShoes?()));

function _module.StatementTwoShoes.F#requires(Heap, ref, int) : bool;

// #requires axiom for _module.StatementTwoShoes.F
axiom (forall $Heap: Heap, this: ref, b#0: int :: 
  { _module.StatementTwoShoes.F#requires($Heap, this, b#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.StatementTwoShoes())
       && $IsAlloc(this, Tclass._module.StatementTwoShoes(), $Heap)
     ==> _module.StatementTwoShoes.F#requires($Heap, this, b#0) == (LitInt(0) <= b#0));

// definition axiom for _module.StatementTwoShoes.F (revealed)
axiom 0 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref, b#0: int :: 
    { _module.StatementTwoShoes.F($Heap, this, b#0), $IsGoodHeap($Heap) } 
    _module.StatementTwoShoes.F#canCall($Heap, this, b#0)
         || (0 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.StatementTwoShoes())
           && $IsAlloc(this, Tclass._module.StatementTwoShoes(), $Heap)
           && LitInt(0) <= b#0)
       ==> _module.StatementTwoShoes.F($Heap, this, b#0)
         == read($Heap, this, _module.StatementTwoShoes.s));

procedure CheckWellformed$$_module.StatementTwoShoes.F(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.StatementTwoShoes())
         && $IsAlloc(this, Tclass._module.StatementTwoShoes(), $Heap), 
    b#0: int);
  free requires 0 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.StatementTwoShoes.F(this: ref, b#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function F
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(78,18): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume LitInt(0) <= b#0;
    if (*)
    {
        assume $Is(_module.StatementTwoShoes.F($Heap, this, b#0), 
          Tclass._module.StatementTwoShoes?());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> $o == this);
        b$reqreads#0 := $_Frame[this, _module.StatementTwoShoes.s];
        assume _module.StatementTwoShoes.F($Heap, this, b#0)
           == read($Heap, this, _module.StatementTwoShoes.s);
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.StatementTwoShoes.F($Heap, this, b#0), 
          Tclass._module.StatementTwoShoes?());
        assert b$reqreads#0;
    }
}



procedure CheckWellformed$$_module.StatementTwoShoes.M(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.StatementTwoShoes())
         && $IsAlloc(this, Tclass._module.StatementTwoShoes(), $Heap), 
    p#0: ref
       where $Is(p#0, Tclass._module.StatementTwoShoes?())
         && $IsAlloc(p#0, Tclass._module.StatementTwoShoes?(), $Heap), 
    a#0: int);
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.StatementTwoShoes.M(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.StatementTwoShoes())
         && $IsAlloc(this, Tclass._module.StatementTwoShoes(), $Heap), 
    p#0: ref
       where $Is(p#0, Tclass._module.StatementTwoShoes?())
         && $IsAlloc(p#0, Tclass._module.StatementTwoShoes?(), $Heap), 
    a#0: int);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this || $o == p#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.StatementTwoShoes.M(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.StatementTwoShoes())
         && $IsAlloc(this, Tclass._module.StatementTwoShoes(), $Heap), 
    p#0: ref
       where $Is(p#0, Tclass._module.StatementTwoShoes?())
         && $IsAlloc(p#0, Tclass._module.StatementTwoShoes?(), $Heap), 
    a#0: int)
   returns ($_reverifyPost: bool);
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this || $o == p#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.StatementTwoShoes.M(this: ref, p#0: ref, a#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: int;
  var ##b#0: int;
  var $rhs#1: int;
  var $rhs#2: int;
  var ##b#1: int;

    // AddMethodImpl: M, Impl$$_module.StatementTwoShoes.M
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this || $o == p#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(87,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(88,9)
    assert p#0 != null;
    assume true;
    assert $_Frame[p#0, _module.StatementTwoShoes.x];
    assume true;
    $rhs#0 := a#0;
    $Heap := update($Heap, p#0, _module.StatementTwoShoes.x, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(88,12)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(89,12)
    ##b#0 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#0, TInt, $Heap);
    assert {:subsumption 0} LitInt(0) <= ##b#0;
    assume LitInt(0) <= ##b#0;
    assume _module.StatementTwoShoes.F#canCall($Heap, this, a#0);
    assert _module.StatementTwoShoes.F($Heap, this, a#0) != null;
    assume _module.StatementTwoShoes.F#canCall($Heap, this, a#0);
    assert $_Frame[_module.StatementTwoShoes.F($Heap, this, a#0), _module.StatementTwoShoes.x];
    assume true;
    $rhs#1 := a#0;
    $Heap := update($Heap, 
      _module.StatementTwoShoes.F($Heap, this, a#0), 
      _module.StatementTwoShoes.x, 
      $rhs#1);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(89,15)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(90,7)
    assume true;
    assert $_Frame[this, _module.StatementTwoShoes.x];
    ##b#1 := a#0 - 10;
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#1, TInt, $Heap);
    assert {:subsumption 0} LitInt(0) <= ##b#1;
    assume LitInt(0) <= ##b#1;
    assume _module.StatementTwoShoes.F#canCall($Heap, this, a#0 - 10);
    assert _module.StatementTwoShoes.F($Heap, this, a#0 - 10) != null;
    assume _module.StatementTwoShoes.F#canCall($Heap, this, a#0 - 10);
    $rhs#2 := read($Heap, 
      _module.StatementTwoShoes.F($Heap, this, a#0 - 10), 
      _module.StatementTwoShoes.x);
    $Heap := update($Heap, this, _module.StatementTwoShoes.x, $rhs#2);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(90,18)"} true;
}



procedure CheckWellformed$$_module.StatementTwoShoes.N(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.StatementTwoShoes())
         && $IsAlloc(this, Tclass._module.StatementTwoShoes(), $Heap), 
    a#0: int, 
    b#0: int);
  free requires 21 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.StatementTwoShoes.N(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.StatementTwoShoes())
         && $IsAlloc(this, Tclass._module.StatementTwoShoes(), $Heap), 
    a#0: int, 
    b#0: int);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.StatementTwoShoes.N(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.StatementTwoShoes())
         && $IsAlloc(this, Tclass._module.StatementTwoShoes(), $Heap), 
    a#0: int, 
    b#0: int)
   returns ($_reverifyPost: bool);
  free requires 21 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.StatementTwoShoes.N(this: ref, a#0: int, b#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: N, Impl$$_module.StatementTwoShoes.N
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(94,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(95,5)
    assert {:subsumption 0} a#0 != 0;
    assert {:subsumption 0} a#0 != 0;
    assume true;
    assert Div(5, a#0) == Div(5, a#0);
    // ----- assume statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(96,5)
    assert {:subsumption 0} b#0 != 0;
    assume true;
    assume Div(20, b#0) == LitInt(5);
}



procedure CheckWellformed$$_module.StatementTwoShoes.O(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.StatementTwoShoes())
         && $IsAlloc(this, Tclass._module.StatementTwoShoes(), $Heap), 
    a#0: int)
   returns (b#0: int);
  free requires 22 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.StatementTwoShoes.O(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.StatementTwoShoes())
         && $IsAlloc(this, Tclass._module.StatementTwoShoes(), $Heap), 
    a#0: int)
   returns (b#0: int);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.StatementTwoShoes.O(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.StatementTwoShoes())
         && $IsAlloc(this, Tclass._module.StatementTwoShoes(), $Heap), 
    a#0: int)
   returns (b#0: int, $_reverifyPost: bool);
  free requires 22 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.StatementTwoShoes.O(this: ref, a#0: int) returns (b#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: O, Impl$$_module.StatementTwoShoes.O
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(100,2): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(101,5)
    assert a#0 != 0;
    assume true;
    if (Div(20, a#0) == LitInt(5))
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(102,9)
        assume true;
        assume true;
        b#0 := a#0;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(102,12)"} true;
    }
    else
    {
    }
}



procedure CheckWellformed$$_module.StatementTwoShoes.P(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.StatementTwoShoes())
         && $IsAlloc(this, Tclass._module.StatementTwoShoes(), $Heap), 
    a#0: int);
  free requires 23 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.StatementTwoShoes.P(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.StatementTwoShoes())
         && $IsAlloc(this, Tclass._module.StatementTwoShoes(), $Heap), 
    a#0: int);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.StatementTwoShoes.P(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.StatementTwoShoes())
         && $IsAlloc(this, Tclass._module.StatementTwoShoes(), $Heap), 
    a#0: int)
   returns ($_reverifyPost: bool);
  free requires 23 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.StatementTwoShoes.P(this: ref, a#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $Heap_at_0: Heap;
  var $PreLoopHeap$loop#0: Heap;
  var $w$loop#0: bool;

    // AddMethodImpl: P, Impl$$_module.StatementTwoShoes.P
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(107,2): initial state"} true;
    $_reverifyPost := false;
    $Heap_at_0 := $Heap;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(108,5)
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
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(108,4): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assume false;
        }

        assert a#0 != 0;
        assume true;
        if (Div(20, a#0) != LitInt(5))
        {
            break;
        }

        // ----- break statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(109,7)
        goto after_0;

        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(108,5)
        assert false;
    }

  after_0:
}



procedure CheckWellformed$$_module.StatementTwoShoes.Q(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.StatementTwoShoes())
         && $IsAlloc(this, Tclass._module.StatementTwoShoes(), $Heap), 
    a#0: int, 
    b#0: int);
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.StatementTwoShoes.Q(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.StatementTwoShoes())
         && $IsAlloc(this, Tclass._module.StatementTwoShoes(), $Heap), 
    a#0: int, 
    b#0: int);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.StatementTwoShoes.Q(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.StatementTwoShoes())
         && $IsAlloc(this, Tclass._module.StatementTwoShoes(), $Heap), 
    a#0: int, 
    b#0: int)
   returns ($_reverifyPost: bool);
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.StatementTwoShoes.Q(this: ref, a#0: int, b#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var i#0: int;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: ref;
  var $decr_init$loop#01: ref;
  var $decr_init$loop#02: int;
  var $w$loop#0: bool;
  var ##b#0: int;
  var ##b#1: int;
  var $decr$loop#00: ref;
  var $decr$loop#01: ref;
  var $decr$loop#02: int;
  var $PreLoopHeap$loop#1: Heap;
  var $decr_init$loop#10: ref;
  var $decr_init$loop#11: int;
  var $w$loop#1: bool;
  var ##b#2: int;
  var $decr$loop#10: ref;
  var $decr$loop#11: int;

    // AddMethodImpl: Q, Impl$$_module.StatementTwoShoes.Q
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(114,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(115,11)
    assume true;
    assume true;
    i#0 := LitInt(1);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(115,14)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(116,5)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := _module.StatementTwoShoes.F($Heap, this, i#0);
    $decr_init$loop#01 := _module.StatementTwoShoes.F($Heap, this, a#0);
    $decr_init$loop#02 := a#0 - i#0;
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
      free invariant (_module.StatementTwoShoes.F($Heap, this, i#0) != null
           ==> $decr_init$loop#00 != null)
         && ((_module.StatementTwoShoes.F($Heap, this, i#0) != null
             <==> $decr_init$loop#00 != null)
           ==> (_module.StatementTwoShoes.F($Heap, this, a#0) != null
               ==> $decr_init$loop#01 != null)
             && ((_module.StatementTwoShoes.F($Heap, this, a#0) != null
                 <==> $decr_init$loop#01 != null)
               ==> a#0 - i#0 <= $decr_init$loop#02 && (a#0 - i#0 == $decr_init$loop#02 ==> true)));
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(116,4): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            ##b#0 := i#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#0, TInt, $Heap);
            assert {:subsumption 0} LitInt(0) <= ##b#0;
            assume LitInt(0) <= ##b#0;
            assume _module.StatementTwoShoes.F#canCall($Heap, this, i#0);
            assume _module.StatementTwoShoes.F#canCall($Heap, this, i#0);
            ##b#1 := a#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#1, TInt, $Heap);
            assert {:subsumption 0} LitInt(0) <= ##b#1;
            assume LitInt(0) <= ##b#1;
            assume _module.StatementTwoShoes.F#canCall($Heap, this, a#0);
            assume _module.StatementTwoShoes.F#canCall($Heap, this, a#0);
            assume true;
            assume false;
        }

        assume true;
        if (a#0 <= i#0)
        {
            break;
        }

        $decr$loop#00 := _module.StatementTwoShoes.F($Heap, this, i#0);
        $decr$loop#01 := _module.StatementTwoShoes.F($Heap, this, a#0);
        $decr$loop#02 := a#0 - i#0;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(119,9)
        assume true;
        assume true;
        i#0 := i#0 + 1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(119,16)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(116,5)
        assert 0 <= $decr$loop#02
           || (_module.StatementTwoShoes.F($Heap, this, i#0) == null && $decr$loop#00 != null)
           || (_module.StatementTwoShoes.F($Heap, this, a#0) == null && $decr$loop#01 != null)
           || a#0 - i#0 == $decr$loop#02;
        assert (_module.StatementTwoShoes.F($Heap, this, i#0) == null && $decr$loop#00 != null)
           || ((_module.StatementTwoShoes.F($Heap, this, i#0) != null
               <==> $decr$loop#00 != null)
             && ((_module.StatementTwoShoes.F($Heap, this, a#0) == null && $decr$loop#01 != null)
               || ((_module.StatementTwoShoes.F($Heap, this, a#0) != null
                   <==> $decr$loop#01 != null)
                 && a#0 - i#0 < $decr$loop#02)));
    }

    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(121,7)
    assume true;
    assume true;
    i#0 := LitInt(1);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(121,10)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(122,5)
    // Assume Fuel Constant
    $PreLoopHeap$loop#1 := $Heap;
    $decr_init$loop#10 := _module.StatementTwoShoes.F($Heap, this, b#0);
    $decr_init$loop#11 := a#0 - i#0;
    havoc $w$loop#1;
    while (true)
      free invariant (forall $o: ref :: 
        { $Heap[$o] } 
        $o != null && read(old($Heap), $o, alloc)
           ==> $Heap[$o] == $PreLoopHeap$loop#1[$o]);
      free invariant $HeapSucc($PreLoopHeap$loop#1, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
        { read($Heap, $o, $f) } 
        $o != null && read($PreLoopHeap$loop#1, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#1, $o, $f) || $_Frame[$o, $f]);
      free invariant (_module.StatementTwoShoes.F($Heap, this, b#0) != null
           ==> $decr_init$loop#10 != null)
         && ((_module.StatementTwoShoes.F($Heap, this, b#0) != null
             <==> $decr_init$loop#10 != null)
           ==> a#0 - i#0 <= $decr_init$loop#11 && (a#0 - i#0 == $decr_init$loop#11 ==> true));
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(122,4): after some loop iterations"} true;
        if (!$w$loop#1)
        {
            ##b#2 := b#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#2, TInt, $Heap);
            assert {:subsumption 0} LitInt(0) <= ##b#2;
            assume LitInt(0) <= ##b#2;
            assume _module.StatementTwoShoes.F#canCall($Heap, this, b#0);
            assume _module.StatementTwoShoes.F#canCall($Heap, this, b#0);
            assume true;
            assume false;
        }

        assume true;
        if (a#0 <= i#0)
        {
            break;
        }

        $decr$loop#10 := _module.StatementTwoShoes.F($Heap, this, b#0);
        $decr$loop#11 := a#0 - i#0;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(125,9)
        assume true;
        assume true;
        i#0 := i#0 + 1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(125,16)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(122,5)
        assert 0 <= $decr$loop#11
           || (_module.StatementTwoShoes.F($Heap, this, b#0) == null && $decr$loop#10 != null)
           || a#0 - i#0 == $decr$loop#11;
        assert (_module.StatementTwoShoes.F($Heap, this, b#0) == null && $decr$loop#10 != null)
           || ((_module.StatementTwoShoes.F($Heap, this, b#0) != null
               <==> $decr$loop#10 != null)
             && a#0 - i#0 < $decr$loop#11);
    }
}



procedure CheckWellformed$$_module.StatementTwoShoes.R(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.StatementTwoShoes())
         && $IsAlloc(this, Tclass._module.StatementTwoShoes(), $Heap), 
    a#0: int);
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.StatementTwoShoes.R(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.StatementTwoShoes())
         && $IsAlloc(this, Tclass._module.StatementTwoShoes(), $Heap), 
    a#0: int);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.StatementTwoShoes.R(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.StatementTwoShoes())
         && $IsAlloc(this, Tclass._module.StatementTwoShoes(), $Heap), 
    a#0: int)
   returns ($_reverifyPost: bool);
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.StatementTwoShoes.R(this: ref, a#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var i#0: int;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: ref;
  var $decr_init$loop#01: int;
  var $w$loop#0: bool;
  var ##b#0: int;
  var ##b#1: int;
  var $decr$loop#00: ref;
  var $decr$loop#01: int;

    // AddMethodImpl: R, Impl$$_module.StatementTwoShoes.R
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(130,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(131,11)
    assume true;
    assume true;
    i#0 := LitInt(0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(131,14)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(132,5)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := _module.StatementTwoShoes.F($Heap, this, a#0);
    $decr_init$loop#01 := 100 - i#0;
    havoc $w$loop#0;
    while (true)
      free invariant $w$loop#0 ==> _module.StatementTwoShoes.F#canCall($Heap, this, a#0);
      invariant $w$loop#0 ==> _module.StatementTwoShoes.F($Heap, this, a#0) != null;
      free invariant (forall $o: ref :: 
        { $Heap[$o] } 
        $o != null && read(old($Heap), $o, alloc)
           ==> $Heap[$o] == $PreLoopHeap$loop#0[$o]);
      free invariant $HeapSucc($PreLoopHeap$loop#0, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
        { read($Heap, $o, $f) } 
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
      free invariant (_module.StatementTwoShoes.F($Heap, this, a#0) != null
           ==> $decr_init$loop#00 != null)
         && ((_module.StatementTwoShoes.F($Heap, this, a#0) != null
             <==> $decr_init$loop#00 != null)
           ==> 100 - i#0 <= $decr_init$loop#01 && (100 - i#0 == $decr_init$loop#01 ==> true));
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(132,4): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            ##b#0 := a#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#0, TInt, $Heap);
            assert {:subsumption 0} LitInt(0) <= ##b#0;
            assume _module.StatementTwoShoes.F#canCall($Heap, this, a#0);
            assume _module.StatementTwoShoes.F#canCall($Heap, this, a#0);
            assume _module.StatementTwoShoes.F($Heap, this, a#0) != null;
            ##b#1 := a#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#1, TInt, $Heap);
            assert {:subsumption 0} LitInt(0) <= ##b#1;
            assume LitInt(0) <= ##b#1;
            assume _module.StatementTwoShoes.F#canCall($Heap, this, a#0);
            assume _module.StatementTwoShoes.F#canCall($Heap, this, a#0);
            assume true;
            assume false;
        }

        assume true;
        if (100 <= i#0)
        {
            break;
        }

        $decr$loop#00 := _module.StatementTwoShoes.F($Heap, this, a#0);
        $decr$loop#01 := 100 - i#0;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(136,9)
        assume true;
        assume true;
        i#0 := i#0 + 1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(136,16)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(132,5)
        assert 0 <= $decr$loop#01
           || (_module.StatementTwoShoes.F($Heap, this, a#0) == null && $decr$loop#00 != null)
           || 100 - i#0 == $decr$loop#01;
        assert (_module.StatementTwoShoes.F($Heap, this, a#0) == null && $decr$loop#00 != null)
           || ((_module.StatementTwoShoes.F($Heap, this, a#0) != null
               <==> $decr$loop#00 != null)
             && 100 - i#0 < $decr$loop#01);
        assume _module.StatementTwoShoes.F#canCall($Heap, this, a#0);
    }
}



procedure CheckWellformed$$_module.StatementTwoShoes.S(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.StatementTwoShoes())
         && $IsAlloc(this, Tclass._module.StatementTwoShoes(), $Heap), 
    a#0: int);
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.StatementTwoShoes.S(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.StatementTwoShoes())
         && $IsAlloc(this, Tclass._module.StatementTwoShoes(), $Heap), 
    a#0: int);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.StatementTwoShoes.S(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.StatementTwoShoes())
         && $IsAlloc(this, Tclass._module.StatementTwoShoes(), $Heap), 
    a#0: int)
   returns ($_reverifyPost: bool);
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.StatementTwoShoes.S(this: ref, a#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var j#0: int;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: ref;
  var $decr_init$loop#01: int;
  var $w$loop#0: bool;
  var ##b#0: int;
  var $decr$loop#00: ref;
  var $decr$loop#01: int;

    // AddMethodImpl: S, Impl$$_module.StatementTwoShoes.S
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(141,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(142,11)
    assume true;
    assume true;
    j#0 := LitInt(0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(142,14)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(143,5)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := _module.StatementTwoShoes.F($Heap, this, 101 - j#0);
    $decr_init$loop#01 := 100 - j#0;
    havoc $w$loop#0;
    while (true)
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> j#0 <= LitInt(100);
      free invariant (forall $o: ref :: 
        { $Heap[$o] } 
        $o != null && read(old($Heap), $o, alloc)
           ==> $Heap[$o] == $PreLoopHeap$loop#0[$o]);
      free invariant $HeapSucc($PreLoopHeap$loop#0, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
        { read($Heap, $o, $f) } 
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
      free invariant (_module.StatementTwoShoes.F($Heap, this, 101 - j#0) != null
           ==> $decr_init$loop#00 != null)
         && ((_module.StatementTwoShoes.F($Heap, this, 101 - j#0) != null
             <==> $decr_init$loop#00 != null)
           ==> 100 - j#0 <= $decr_init$loop#01 && (100 - j#0 == $decr_init$loop#01 ==> true));
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(143,4): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assume true;
            assume j#0 <= LitInt(100);
            ##b#0 := 101 - j#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#0, TInt, $Heap);
            assert {:subsumption 0} LitInt(0) <= ##b#0;
            assume LitInt(0) <= ##b#0;
            assume _module.StatementTwoShoes.F#canCall($Heap, this, 101 - j#0);
            assume _module.StatementTwoShoes.F#canCall($Heap, this, 101 - j#0);
            assume true;
            assume false;
        }

        assert a#0 != 0;
        if (Div(20, a#0) == LitInt(5))
        {
        }

        assume true;
        if (!(Div(20, a#0) == LitInt(5) && j#0 < 100))
        {
            break;
        }

        $decr$loop#00 := _module.StatementTwoShoes.F($Heap, this, 101 - j#0);
        $decr$loop#01 := 100 - j#0;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(147,9)
        assume true;
        assume true;
        j#0 := j#0 + 1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(147,16)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(143,5)
        assert 0 <= $decr$loop#01
           || (_module.StatementTwoShoes.F($Heap, this, 101 - j#0) == null
             && $decr$loop#00 != null)
           || 100 - j#0 == $decr$loop#01;
        assert (_module.StatementTwoShoes.F($Heap, this, 101 - j#0) == null
             && $decr$loop#00 != null)
           || ((_module.StatementTwoShoes.F($Heap, this, 101 - j#0) != null
               <==> $decr$loop#00 != null)
             && 100 - j#0 < $decr$loop#01);
        assume true;
    }
}



procedure CheckWellformed$$_module.StatementTwoShoes.T(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.StatementTwoShoes())
         && $IsAlloc(this, Tclass._module.StatementTwoShoes(), $Heap), 
    a#0: int);
  free requires 24 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.StatementTwoShoes.T(this: ref, a#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: T, CheckWellformed$$_module.StatementTwoShoes.T
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(151,9): initial state"} true;
    assume a#0 != 0;
    assert a#0 != 0;
    assume Div(20, a#0) == LitInt(5);
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
    assume $HeapSucc(old($Heap), $Heap);
}



procedure Call$$_module.StatementTwoShoes.T(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.StatementTwoShoes())
         && $IsAlloc(this, Tclass._module.StatementTwoShoes(), $Heap), 
    a#0: int);
  // user-defined preconditions
  requires a#0 != 0;
  requires Div(20, a#0) == LitInt(5);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.StatementTwoShoes.T(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.StatementTwoShoes())
         && $IsAlloc(this, Tclass._module.StatementTwoShoes(), $Heap), 
    a#0: int)
   returns ($_reverifyPost: bool);
  free requires 24 == $FunctionContextHeight;
  // user-defined preconditions
  requires a#0 != 0;
  requires Div(20, a#0) == LitInt(5);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.StatementTwoShoes.T(this: ref, a#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var k#0: int;
  var j#0: int;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var $decr$loop#00: int;
  var $PreLoopHeap$loop#1: Heap;
  var $decr_init$loop#10: int;
  var $w$loop#1: bool;
  var $decr$loop#10: int;

    // AddMethodImpl: T, Impl$$_module.StatementTwoShoes.T
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(153,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(154,11)
    assume true;
    assume true;
    k#0 := a#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(154,14)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(155,11)
    assume true;
    assume true;
    j#0 := LitInt(0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(155,14)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(156,5)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := 100 - j#0;
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
      free invariant 100 - j#0 <= $decr_init$loop#00 && (100 - j#0 == $decr_init$loop#00 ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(156,4): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assume true;
            assume false;
        }

        assert k#0 != 0;
        if (Div(20, k#0) == LitInt(5))
        {
        }

        assume true;
        if (!(Div(20, k#0) == LitInt(5) && j#0 < 100))
        {
            break;
        }

        $decr$loop#00 := 100 - j#0;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(159,9)
        assume true;
        assume true;
        j#0 := j#0 + 1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(159,16)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(156,5)
        assert 0 <= $decr$loop#00 || 100 - j#0 == $decr$loop#00;
        assert 100 - j#0 < $decr$loop#00;
    }

    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(161,7)
    assume true;
    assume true;
    j#0 := LitInt(0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(161,10)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(162,5)
    // Assume Fuel Constant
    $PreLoopHeap$loop#1 := $Heap;
    $decr_init$loop#10 := 100 - j#0;
    havoc $w$loop#1;
    while (true)
      free invariant (forall $o: ref :: 
        { $Heap[$o] } 
        $o != null && read(old($Heap), $o, alloc)
           ==> $Heap[$o] == $PreLoopHeap$loop#1[$o]);
      free invariant $HeapSucc($PreLoopHeap$loop#1, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
        { read($Heap, $o, $f) } 
        $o != null && read($PreLoopHeap$loop#1, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#1, $o, $f) || $_Frame[$o, $f]);
      free invariant 100 - j#0 <= $decr_init$loop#10 && (100 - j#0 == $decr_init$loop#10 ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(162,4): after some loop iterations"} true;
        if (!$w$loop#1)
        {
            assume true;
            assume false;
        }

        assert k#0 != 0;
        if (Div(20, k#0) == LitInt(5))
        {
        }

        assume true;
        if (!(Div(20, k#0) == LitInt(5) && j#0 < 100))
        {
            break;
        }

        $decr$loop#10 := 100 - j#0;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(165,9)
        assume true;
        havoc k#0;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(165,12)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(166,9)
        assume true;
        assume true;
        j#0 := j#0 + 1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(166,16)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(162,5)
        assert 0 <= $decr$loop#10 || 100 - j#0 == $decr$loop#10;
        assert 100 - j#0 < $decr$loop#10;
    }
}



procedure CheckWellformed$$_module.StatementTwoShoes.U(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.StatementTwoShoes())
         && $IsAlloc(this, Tclass._module.StatementTwoShoes(), $Heap));
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.StatementTwoShoes.U(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.StatementTwoShoes())
         && $IsAlloc(this, Tclass._module.StatementTwoShoes(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.StatementTwoShoes.U(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.StatementTwoShoes())
         && $IsAlloc(this, Tclass._module.StatementTwoShoes(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.StatementTwoShoes.U(this: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var i#0: int;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var ##b#0: int;
  var $decr$loop#00: int;
  var $PreLoopHeap$loop#1: Heap;
  var $decr_init$loop#10: int;
  var $w$loop#1: bool;
  var ##b#1: int;
  var $decr$loop#10: int;

    // AddMethodImpl: U, Impl$$_module.StatementTwoShoes.U
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(171,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(172,11)
    assume true;
    assume true;
    i#0 := LitInt(0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(172,14)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(173,5)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := 100 - i#0;
    havoc $w$loop#0;
    while (true)
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> i#0 <= LitInt(100);
      free invariant $w$loop#0 ==> _module.StatementTwoShoes.F#canCall($Heap, this, 123 - i#0);
      invariant $w$loop#0 ==> _module.StatementTwoShoes.F($Heap, this, 123 - i#0) == this;
      free invariant (forall $o: ref :: 
        { $Heap[$o] } 
        $o != null && read(old($Heap), $o, alloc)
           ==> $Heap[$o] == $PreLoopHeap$loop#0[$o]);
      free invariant $HeapSucc($PreLoopHeap$loop#0, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
        { read($Heap, $o, $f) } 
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
      free invariant 100 - i#0 <= $decr_init$loop#00 && (100 - i#0 == $decr_init$loop#00 ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(173,4): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assume true;
            assume i#0 <= LitInt(100);
            ##b#0 := 123 - i#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#0, TInt, $Heap);
            assert {:subsumption 0} LitInt(0) <= ##b#0;
            assume _module.StatementTwoShoes.F#canCall($Heap, this, 123 - i#0);
            assume _module.StatementTwoShoes.F#canCall($Heap, this, 123 - i#0);
            assume _module.StatementTwoShoes.F($Heap, this, 123 - i#0) == this;
            assume true;
            assume false;
        }

        assume true;
        if (100 <= i#0)
        {
            break;
        }

        $decr$loop#00 := 100 - i#0;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(177,9)
        assume true;
        assume true;
        i#0 := i#0 + 1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(177,16)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(173,5)
        assert 0 <= $decr$loop#00 || 100 - i#0 == $decr$loop#00;
        assert 100 - i#0 < $decr$loop#00;
        assume true;
        assume _module.StatementTwoShoes.F#canCall($Heap, this, 123 - i#0);
    }

    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(179,7)
    assume true;
    assume true;
    i#0 := LitInt(0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(179,10)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(180,5)
    // Assume Fuel Constant
    $PreLoopHeap$loop#1 := $Heap;
    $decr_init$loop#10 := 100 - i#0;
    havoc $w$loop#1;
    while (true)
      free invariant $w$loop#1
         ==> _module.StatementTwoShoes.F#canCall($Heap, this, (if i#0 == LitInt(77) then -3 else i#0));
      invariant $w$loop#1
         ==> _module.StatementTwoShoes.F($Heap, this, (if i#0 == LitInt(77) then -3 else i#0))
           == this;
      free invariant (forall $o: ref :: 
        { $Heap[$o] } 
        $o != null && read(old($Heap), $o, alloc)
           ==> $Heap[$o] == $PreLoopHeap$loop#1[$o]);
      free invariant $HeapSucc($PreLoopHeap$loop#1, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
        { read($Heap, $o, $f) } 
        $o != null && read($PreLoopHeap$loop#1, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#1, $o, $f) || $_Frame[$o, $f]);
      free invariant 100 - i#0 <= $decr_init$loop#10 && (100 - i#0 == $decr_init$loop#10 ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(180,4): after some loop iterations"} true;
        if (!$w$loop#1)
        {
            if (i#0 == LitInt(77))
            {
            }
            else
            {
            }

            ##b#1 := (if i#0 == LitInt(77) then -3 else i#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#1, TInt, $Heap);
            assert {:subsumption 0} LitInt(0) <= ##b#1;
            assume _module.StatementTwoShoes.F#canCall($Heap, this, (if i#0 == LitInt(77) then -3 else i#0));
            assume _module.StatementTwoShoes.F#canCall($Heap, this, (if i#0 == LitInt(77) then -3 else i#0));
            assume _module.StatementTwoShoes.F($Heap, this, (if i#0 == LitInt(77) then -3 else i#0))
               == this;
            assume true;
            assume false;
        }

        assume true;
        if (100 <= i#0)
        {
            break;
        }

        $decr$loop#10 := 100 - i#0;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(183,9)
        assume true;
        assume true;
        i#0 := i#0 + 1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(183,16)"} true;
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(184,7)
        assume true;
        if (i#0 == LitInt(77))
        {
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(184,24)
            assume true;
            assume true;
            i#0 := i#0 + 1;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(184,31)"} true;
        }
        else
        {
        }

        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(180,5)
        assert 0 <= $decr$loop#10 || 100 - i#0 == $decr$loop#10;
        assert 100 - i#0 < $decr$loop#10;
        assume _module.StatementTwoShoes.F#canCall($Heap, this, (if i#0 == LitInt(77) then -3 else i#0));
    }
}



// function declaration for _module.StatementTwoShoes.G
function _module.StatementTwoShoes.G(this: ref, w#0: int) : int;

function _module.StatementTwoShoes.G#canCall(this: ref, w#0: int) : bool;

// consequence axiom for _module.StatementTwoShoes.G
axiom 25 <= $FunctionContextHeight
   ==> (forall this: ref, w#0: int :: 
    { _module.StatementTwoShoes.G(this, w#0) } 
    _module.StatementTwoShoes.G#canCall(this, w#0)
         || (25 != $FunctionContextHeight
           && 
          this != null
           && $Is(this, Tclass._module.StatementTwoShoes()))
       ==> true);

function _module.StatementTwoShoes.G#requires(ref, int) : bool;

// #requires axiom for _module.StatementTwoShoes.G
axiom (forall this: ref, w#0: int :: 
  { _module.StatementTwoShoes.G#requires(this, w#0) } 
  this != null && $Is(this, Tclass._module.StatementTwoShoes())
     ==> _module.StatementTwoShoes.G#requires(this, w#0) == true);

// definition axiom for _module.StatementTwoShoes.G (revealed)
axiom 25 <= $FunctionContextHeight
   ==> (forall this: ref, w#0: int :: 
    { _module.StatementTwoShoes.G(this, w#0) } 
    _module.StatementTwoShoes.G#canCall(this, w#0)
         || (25 != $FunctionContextHeight
           && 
          this != null
           && $Is(this, Tclass._module.StatementTwoShoes()))
       ==> _module.StatementTwoShoes.G(this, w#0) == LitInt(5));

// definition axiom for _module.StatementTwoShoes.G for decreasing-related literals (revealed)
axiom 25 <= $FunctionContextHeight
   ==> (forall this: ref, w#0: int :: 
    {:weight 3} { _module.StatementTwoShoes.G(this, LitInt(w#0)) } 
    _module.StatementTwoShoes.G#canCall(this, LitInt(w#0))
         || (25 != $FunctionContextHeight
           && 
          this != null
           && $Is(this, Tclass._module.StatementTwoShoes()))
       ==> _module.StatementTwoShoes.G(this, LitInt(w#0)) == LitInt(5));

// definition axiom for _module.StatementTwoShoes.G for all literals (revealed)
axiom 25 <= $FunctionContextHeight
   ==> (forall this: ref, w#0: int :: 
    {:weight 3} { _module.StatementTwoShoes.G(Lit(this), LitInt(w#0)) } 
    _module.StatementTwoShoes.G#canCall(Lit(this), LitInt(w#0))
         || (25 != $FunctionContextHeight
           && 
          this != null
           && $Is(this, Tclass._module.StatementTwoShoes()))
       ==> _module.StatementTwoShoes.G(Lit(this), LitInt(w#0)) == LitInt(5));

procedure CheckWellformed$$_module.StatementTwoShoes.G(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.StatementTwoShoes())
         && $IsAlloc(this, Tclass._module.StatementTwoShoes(), $Heap), 
    w#0: int);
  free requires 25 == $FunctionContextHeight;
  modifies $Heap, $Tick;



// function declaration for _module.StatementTwoShoes.H
function _module.StatementTwoShoes.H(this: ref, x#0: int) : int;

function _module.StatementTwoShoes.H#canCall(this: ref, x#0: int) : bool;

// consequence axiom for _module.StatementTwoShoes.H
axiom 26 <= $FunctionContextHeight
   ==> (forall this: ref, x#0: int :: 
    { _module.StatementTwoShoes.H(this, x#0) } 
    _module.StatementTwoShoes.H#canCall(this, x#0)
         || (26 != $FunctionContextHeight
           && 
          this != null
           && $Is(this, Tclass._module.StatementTwoShoes()))
       ==> true);

function _module.StatementTwoShoes.H#requires(ref, int) : bool;

// #requires axiom for _module.StatementTwoShoes.H
axiom (forall this: ref, x#0: int :: 
  { _module.StatementTwoShoes.H#requires(this, x#0) } 
  this != null && $Is(this, Tclass._module.StatementTwoShoes())
     ==> _module.StatementTwoShoes.H#requires(this, x#0) == true);

// definition axiom for _module.StatementTwoShoes.H (revealed)
axiom 26 <= $FunctionContextHeight
   ==> (forall this: ref, x#0: int :: 
    { _module.StatementTwoShoes.H(this, x#0) } 
    _module.StatementTwoShoes.H#canCall(this, x#0)
         || (26 != $FunctionContextHeight
           && 
          this != null
           && $Is(this, Tclass._module.StatementTwoShoes()))
       ==> _module.StatementTwoShoes.H(this, x#0) == 0 - x#0);

// definition axiom for _module.StatementTwoShoes.H for decreasing-related literals (revealed)
axiom 26 <= $FunctionContextHeight
   ==> (forall this: ref, x#0: int :: 
    {:weight 3} { _module.StatementTwoShoes.H(this, LitInt(x#0)) } 
    _module.StatementTwoShoes.H#canCall(this, LitInt(x#0))
         || (26 != $FunctionContextHeight
           && 
          this != null
           && $Is(this, Tclass._module.StatementTwoShoes()))
       ==> _module.StatementTwoShoes.H(this, LitInt(x#0)) == LitInt(0 - x#0));

// definition axiom for _module.StatementTwoShoes.H for all literals (revealed)
axiom 26 <= $FunctionContextHeight
   ==> (forall this: ref, x#0: int :: 
    {:weight 3} { _module.StatementTwoShoes.H(Lit(this), LitInt(x#0)) } 
    _module.StatementTwoShoes.H#canCall(Lit(this), LitInt(x#0))
         || (26 != $FunctionContextHeight
           && 
          this != null
           && $Is(this, Tclass._module.StatementTwoShoes()))
       ==> _module.StatementTwoShoes.H(Lit(this), LitInt(x#0)) == LitInt(0 - x#0));

procedure CheckWellformed$$_module.StatementTwoShoes.H(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.StatementTwoShoes())
         && $IsAlloc(this, Tclass._module.StatementTwoShoes(), $Heap), 
    x#0: int);
  free requires 26 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure CheckWellformed$$_module.StatementTwoShoes.W(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.StatementTwoShoes())
         && $IsAlloc(this, Tclass._module.StatementTwoShoes(), $Heap), 
    x#0: int);
  free requires 27 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.StatementTwoShoes.W(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.StatementTwoShoes())
         && $IsAlloc(this, Tclass._module.StatementTwoShoes(), $Heap), 
    x#0: int);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.StatementTwoShoes.W(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.StatementTwoShoes())
         && $IsAlloc(this, Tclass._module.StatementTwoShoes(), $Heap), 
    x#0: int)
   returns ($_reverifyPost: bool);
  free requires 27 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.StatementTwoShoes.W(this: ref, x#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var i#0: int;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var $decr$loop#00: int;

    // AddMethodImpl: W, Impl$$_module.StatementTwoShoes.W
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(192,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(193,11)
    assume true;
    assume true;
    i#0 := LitInt(0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(193,14)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(194,5)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := 100 - i#0;
    havoc $w$loop#0;
    while (true)
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> Div(5, x#0) != Div(5, x#0);
      free invariant (forall $o: ref :: 
        { $Heap[$o] } 
        $o != null && read(old($Heap), $o, alloc)
           ==> $Heap[$o] == $PreLoopHeap$loop#0[$o]);
      free invariant $HeapSucc($PreLoopHeap$loop#0, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
        { read($Heap, $o, $f) } 
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
      free invariant 100 - i#0 <= $decr_init$loop#00 && (100 - i#0 == $decr_init$loop#00 ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(194,4): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assert {:subsumption 0} x#0 != 0;
            assert {:subsumption 0} x#0 != 0;
            assume true;
            assume Div(5, x#0) != Div(5, x#0);
            assume true;
            assume false;
        }

        assume true;
        if (100 <= i#0)
        {
            break;
        }

        $decr$loop#00 := 100 - i#0;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(198,9)
        assume true;
        assume true;
        i#0 := i#0 + 1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(198,16)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(194,5)
        assert 0 <= $decr$loop#00 || 100 - i#0 == $decr$loop#00;
        assert 100 - i#0 < $decr$loop#00;
        assume true;
    }
}



// _module.StatementTwoShoes: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.StatementTwoShoes()) } 
  $Is(c#0, Tclass._module.StatementTwoShoes())
     <==> $Is(c#0, Tclass._module.StatementTwoShoes?()) && c#0 != null);

// _module.StatementTwoShoes: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.StatementTwoShoes(), $h) } 
  $IsAlloc(c#0, Tclass._module.StatementTwoShoes(), $h)
     <==> $IsAlloc(c#0, Tclass._module.StatementTwoShoes?(), $h));

const unique class._module.Mountain?: ClassName;

function Tclass._module.Mountain?() : Ty;

const unique Tagclass._module.Mountain?: TyTag;

// Tclass._module.Mountain? Tag
axiom Tag(Tclass._module.Mountain?()) == Tagclass._module.Mountain?
   && TagFamily(Tclass._module.Mountain?()) == tytagFamily$Mountain;

// Box/unbox axiom for Tclass._module.Mountain?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Mountain?()) } 
  $IsBox(bx, Tclass._module.Mountain?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Mountain?()));

// Mountain: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.Mountain?()) } 
  $Is($o, Tclass._module.Mountain?())
     <==> $o == null || dtype($o) == Tclass._module.Mountain?());

// Mountain: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.Mountain?(), $h) } 
  $IsAlloc($o, Tclass._module.Mountain?(), $h)
     <==> $o == null || read($h, $o, alloc));

axiom FDim(_module.Mountain.x) == 0
   && FieldOfDecl(class._module.Mountain?, field$x) == _module.Mountain.x
   && !$IsGhostField(_module.Mountain.x);

const _module.Mountain.x: Field int;

// Mountain.x: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Mountain.x) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Mountain?()
     ==> $Is(read($h, $o, _module.Mountain.x), TInt));

// Mountain.x: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Mountain.x) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Mountain?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Mountain.x), TInt, $h));

function Tclass._module.Mountain() : Ty;

const unique Tagclass._module.Mountain: TyTag;

// Tclass._module.Mountain Tag
axiom Tag(Tclass._module.Mountain()) == Tagclass._module.Mountain
   && TagFamily(Tclass._module.Mountain()) == tytagFamily$Mountain;

// Box/unbox axiom for Tclass._module.Mountain
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Mountain()) } 
  $IsBox(bx, Tclass._module.Mountain())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Mountain()));

// _module.Mountain: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.Mountain()) } 
  $Is(c#0, Tclass._module.Mountain())
     <==> $Is(c#0, Tclass._module.Mountain?()) && c#0 != null);

// _module.Mountain: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.Mountain(), $h) } 
  $IsAlloc(c#0, Tclass._module.Mountain(), $h)
     <==> $IsAlloc(c#0, Tclass._module.Mountain?(), $h));

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

// function declaration for _module._default.Postie0
function _module.__default.Postie0(c#0: ref) : ref;

function _module.__default.Postie0#canCall(c#0: ref) : bool;

// consequence axiom for _module.__default.Postie0
axiom 6 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, c#0: ref :: 
    { _module.__default.Postie0(c#0), $IsGoodHeap($Heap) } 
    _module.__default.Postie0#canCall(c#0)
         || (6 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(c#0, Tclass._module.Mountain?())
           && c#0 != null)
       ==> _module.__default.Postie0(c#0) != null
         && read($Heap, _module.__default.Postie0(c#0), _module.Mountain.x)
           <= read($Heap, _module.__default.Postie0(c#0), _module.Mountain.x)
         && read($Heap, _module.__default.Postie0(c#0), _module.Mountain.x)
           == read($Heap, _module.__default.Postie0(c#0), _module.Mountain.x)
         && $Is(_module.__default.Postie0(c#0), Tclass._module.Mountain?()));

function _module.__default.Postie0#requires(ref) : bool;

// #requires axiom for _module.__default.Postie0
axiom (forall c#0: ref :: 
  { _module.__default.Postie0#requires(c#0) } 
  $Is(c#0, Tclass._module.Mountain?())
     ==> _module.__default.Postie0#requires(c#0) == (c#0 != null));

// definition axiom for _module.__default.Postie0 (revealed)
axiom 6 <= $FunctionContextHeight
   ==> (forall c#0: ref :: 
    { _module.__default.Postie0(c#0) } 
    _module.__default.Postie0#canCall(c#0)
         || (6 != $FunctionContextHeight
           && 
          $Is(c#0, Tclass._module.Mountain?())
           && c#0 != null)
       ==> _module.__default.Postie0(c#0) == c#0);

// definition axiom for _module.__default.Postie0 for all literals (revealed)
axiom 6 <= $FunctionContextHeight
   ==> (forall c#0: ref :: 
    {:weight 3} { _module.__default.Postie0(Lit(c#0)) } 
    _module.__default.Postie0#canCall(Lit(c#0))
         || (6 != $FunctionContextHeight
           && 
          $Is(c#0, Tclass._module.Mountain?())
           && c#0 != null)
       ==> _module.__default.Postie0(Lit(c#0)) == Lit(c#0));

procedure CheckWellformed$$_module.__default.Postie0(c#0: ref where $Is(c#0, Tclass._module.Mountain?()));
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures _module.__default.Postie0(c#0) != null;
  ensures read($Heap, _module.__default.Postie0(c#0), _module.Mountain.x)
     <= read($Heap, _module.__default.Postie0(c#0), _module.Mountain.x);
  ensures read($Heap, _module.__default.Postie0(c#0), _module.Mountain.x)
     == read($Heap, _module.__default.Postie0(c#0), _module.Mountain.x);



implementation CheckWellformed$$_module.__default.Postie0(c#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##c#0: ref;
  var ##c#1: ref;
  var ##c#2: ref;
  var ##c#3: ref;
  var ##c#4: ref;


    // AddWellformednessCheck for function Postie0
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(207,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume c#0 != null;
    if (*)
    {
        assume $Is(_module.__default.Postie0(c#0), Tclass._module.Mountain?());
        ##c#0 := c#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#0, Tclass._module.Mountain?(), $Heap);
        assert {:subsumption 0} ##c#0 != null;
        assume ##c#0 != null;
        assert c#0 == c#0 || (##c#0 == null && c#0 != null);
        assume c#0 == c#0 || _module.__default.Postie0#canCall(c#0);
        assume _module.__default.Postie0(c#0) != null;
        ##c#1 := c#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#1, Tclass._module.Mountain?(), $Heap);
        assert {:subsumption 0} ##c#1 != null;
        assume ##c#1 != null;
        assert c#0 == c#0 || (##c#1 == null && c#0 != null);
        assume c#0 == c#0 || _module.__default.Postie0#canCall(c#0);
        assert _module.__default.Postie0(c#0) != null;
        ##c#2 := c#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#2, Tclass._module.Mountain?(), $Heap);
        assert {:subsumption 0} ##c#2 != null;
        assume ##c#2 != null;
        assert c#0 == c#0 || (##c#2 == null && c#0 != null);
        assume c#0 == c#0 || _module.__default.Postie0#canCall(c#0);
        assert _module.__default.Postie0(c#0) != null;
        assume read($Heap, _module.__default.Postie0(c#0), _module.Mountain.x)
           <= read($Heap, _module.__default.Postie0(c#0), _module.Mountain.x);
        ##c#3 := c#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#3, Tclass._module.Mountain?(), $Heap);
        assert {:subsumption 0} ##c#3 != null;
        assume ##c#3 != null;
        assert c#0 == c#0 || (##c#3 == null && c#0 != null);
        assume c#0 == c#0 || _module.__default.Postie0#canCall(c#0);
        assert _module.__default.Postie0(c#0) != null;
        ##c#4 := c#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#4, Tclass._module.Mountain?(), $Heap);
        assert {:subsumption 0} ##c#4 != null;
        assume ##c#4 != null;
        assert c#0 == c#0 || (##c#4 == null && c#0 != null);
        assume c#0 == c#0 || _module.__default.Postie0#canCall(c#0);
        assert _module.__default.Postie0(c#0) != null;
        assume read($Heap, _module.__default.Postie0(c#0), _module.Mountain.x)
           == read($Heap, _module.__default.Postie0(c#0), _module.Mountain.x);
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        assume _module.__default.Postie0(c#0) == c#0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.Postie0(c#0), Tclass._module.Mountain?());
    }
}



// function declaration for _module._default.Postie1
function _module.__default.Postie1(c#0: ref) : ref;

function _module.__default.Postie1#canCall(c#0: ref) : bool;

// consequence axiom for _module.__default.Postie1
axiom 7 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, c#0: ref :: 
    { _module.__default.Postie1(c#0), $IsGoodHeap($Heap) } 
    _module.__default.Postie1#canCall(c#0)
         || (7 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(c#0, Tclass._module.Mountain?())
           && c#0 != null)
       ==> _module.__default.Postie1(c#0) != null
         && read($Heap, _module.__default.Postie1(c#0), _module.Mountain.x) == LitInt(5)
         && $Is(_module.__default.Postie1(c#0), Tclass._module.Mountain?()));

function _module.__default.Postie1#requires(ref) : bool;

// #requires axiom for _module.__default.Postie1
axiom (forall c#0: ref :: 
  { _module.__default.Postie1#requires(c#0) } 
  $Is(c#0, Tclass._module.Mountain?())
     ==> _module.__default.Postie1#requires(c#0) == (c#0 != null));

// definition axiom for _module.__default.Postie1 (revealed)
axiom 7 <= $FunctionContextHeight
   ==> (forall c#0: ref :: 
    { _module.__default.Postie1(c#0) } 
    _module.__default.Postie1#canCall(c#0)
         || (7 != $FunctionContextHeight
           && 
          $Is(c#0, Tclass._module.Mountain?())
           && c#0 != null)
       ==> _module.__default.Postie1(c#0) == c#0);

// definition axiom for _module.__default.Postie1 for all literals (revealed)
axiom 7 <= $FunctionContextHeight
   ==> (forall c#0: ref :: 
    {:weight 3} { _module.__default.Postie1(Lit(c#0)) } 
    _module.__default.Postie1#canCall(Lit(c#0))
         || (7 != $FunctionContextHeight
           && 
          $Is(c#0, Tclass._module.Mountain?())
           && c#0 != null)
       ==> _module.__default.Postie1(Lit(c#0)) == Lit(c#0));

procedure CheckWellformed$$_module.__default.Postie1(c#0: ref where $Is(c#0, Tclass._module.Mountain?()));
  free requires 7 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures _module.__default.Postie1(c#0) != null;
  ensures read($Heap, _module.__default.Postie1(c#0), _module.Mountain.x) == LitInt(5);



implementation CheckWellformed$$_module.__default.Postie1(c#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##c#0: ref;
  var ##c#1: ref;


    // AddWellformednessCheck for function Postie1
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(215,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume c#0 != null;
    if (*)
    {
        assume $Is(_module.__default.Postie1(c#0), Tclass._module.Mountain?());
        ##c#0 := c#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#0, Tclass._module.Mountain?(), $Heap);
        assert {:subsumption 0} ##c#0 != null;
        assume ##c#0 != null;
        assert c#0 == c#0 || (##c#0 == null && c#0 != null);
        assume c#0 == c#0 || _module.__default.Postie1#canCall(c#0);
        assume _module.__default.Postie1(c#0) != null;
        ##c#1 := c#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#1, Tclass._module.Mountain?(), $Heap);
        assert {:subsumption 0} ##c#1 != null;
        assume ##c#1 != null;
        assert c#0 == c#0 || (##c#1 == null && c#0 != null);
        assume c#0 == c#0 || _module.__default.Postie1#canCall(c#0);
        assert _module.__default.Postie1(c#0) != null;
        assume read($Heap, _module.__default.Postie1(c#0), _module.Mountain.x) == LitInt(5);
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        assume _module.__default.Postie1(c#0) == c#0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.Postie1(c#0), Tclass._module.Mountain?());
    }
}



// function declaration for _module._default.Postie2
function _module.__default.Postie2($heap: Heap, c#0: ref) : ref;

function _module.__default.Postie2#canCall($heap: Heap, c#0: ref) : bool;

// frame axiom for _module.__default.Postie2
axiom (forall $h0: Heap, $h1: Heap, c#0: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.__default.Postie2($h1, c#0) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && (_module.__default.Postie2#canCall($h0, c#0)
         || $Is(c#0, Tclass._module.Mountain?()))
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && $o == c#0 ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.__default.Postie2($h0, c#0) == _module.__default.Postie2($h1, c#0));

// consequence axiom for _module.__default.Postie2
axiom 8 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, c#0: ref :: 
    { _module.__default.Postie2($Heap, c#0) } 
    _module.__default.Postie2#canCall($Heap, c#0)
         || (8 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(c#0, Tclass._module.Mountain?())
           && 
          c#0 != null
           && read($Heap, c#0, _module.Mountain.x) == LitInt(5))
       ==> read($Heap, _module.__default.Postie2($Heap, c#0), _module.Mountain.x)
           == LitInt(5)
         && $Is(_module.__default.Postie2($Heap, c#0), Tclass._module.Mountain?()));

function _module.__default.Postie2#requires(Heap, ref) : bool;

// #requires axiom for _module.__default.Postie2
axiom (forall $Heap: Heap, c#0: ref :: 
  { _module.__default.Postie2#requires($Heap, c#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap) && $Is(c#0, Tclass._module.Mountain?())
     ==> _module.__default.Postie2#requires($Heap, c#0)
       == (c#0 != null && read($Heap, c#0, _module.Mountain.x) == LitInt(5)));

// definition axiom for _module.__default.Postie2 (revealed)
axiom 8 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, c#0: ref :: 
    { _module.__default.Postie2($Heap, c#0), $IsGoodHeap($Heap) } 
    _module.__default.Postie2#canCall($Heap, c#0)
         || (8 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(c#0, Tclass._module.Mountain?())
           && 
          c#0 != null
           && read($Heap, c#0, _module.Mountain.x) == LitInt(5))
       ==> _module.__default.Postie2($Heap, c#0) == c#0);

procedure CheckWellformed$$_module.__default.Postie2(c#0: ref where $Is(c#0, Tclass._module.Mountain?()));
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures read($Heap, _module.__default.Postie2($Heap, c#0), _module.Mountain.x)
     == LitInt(5);



implementation CheckWellformed$$_module.__default.Postie2(c#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;
  var ##c#0: ref;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function Postie2
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(222,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == c#0);
    assume c#0 != null;
    assert c#0 != null;
    b$reqreads#0 := $_Frame[c#0, _module.Mountain.x];
    assume read($Heap, c#0, _module.Mountain.x) == LitInt(5);
    assert b$reqreads#0;
    if (*)
    {
        assume $Is(_module.__default.Postie2($Heap, c#0), Tclass._module.Mountain?());
        ##c#0 := c#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#0, Tclass._module.Mountain?(), $Heap);
        assert {:subsumption 0} ##c#0 != null;
        assert {:subsumption 0} read($Heap, ##c#0, _module.Mountain.x) == LitInt(5);
        assume ##c#0 != null && read($Heap, ##c#0, _module.Mountain.x) == LitInt(5);
        assert c#0 == c#0
           || 
          (Set#Subset(Set#UnionOne(Set#Empty(): Set Box, $Box(##c#0)), 
              Set#UnionOne(Set#Empty(): Set Box, $Box(c#0)))
             && !Set#Subset(Set#UnionOne(Set#Empty(): Set Box, $Box(c#0)), 
              Set#UnionOne(Set#Empty(): Set Box, $Box(##c#0))))
           || (Set#Equal(Set#UnionOne(Set#Empty(): Set Box, $Box(##c#0)), 
              Set#UnionOne(Set#Empty(): Set Box, $Box(c#0)))
             && 
            ##c#0 == null
             && c#0 != null);
        assume c#0 == c#0 || _module.__default.Postie2#canCall($Heap, c#0);
        assert _module.__default.Postie2($Heap, c#0) != null;
        assume read($Heap, _module.__default.Postie2($Heap, c#0), _module.Mountain.x)
           == LitInt(5);
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> $o == c#0);
        assume _module.__default.Postie2($Heap, c#0) == c#0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.Postie2($Heap, c#0), Tclass._module.Mountain?());
    }
}



// function declaration for _module._default.Postie3
function _module.__default.Postie3($heap: Heap, c#0: ref) : ref;

function _module.__default.Postie3#canCall($heap: Heap, c#0: ref) : bool;

// frame axiom for _module.__default.Postie3
axiom (forall $h0: Heap, $h1: Heap, c#0: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.__default.Postie3($h1, c#0) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && (_module.__default.Postie3#canCall($h0, c#0)
         || $Is(c#0, Tclass._module.Mountain?()))
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && $o == c#0 ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.__default.Postie3($h0, c#0) == _module.__default.Postie3($h1, c#0));

// consequence axiom for _module.__default.Postie3
axiom 9 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, c#0: ref :: 
    { _module.__default.Postie3($Heap, c#0) } 
    _module.__default.Postie3#canCall($Heap, c#0)
         || (9 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(c#0, Tclass._module.Mountain?())
           && 
          c#0 != null
           && read($Heap, c#0, _module.Mountain.x) == LitInt(5))
       ==> _module.__default.Postie3($Heap, c#0) != null
         && read($Heap, _module.__default.Postie3($Heap, c#0), _module.Mountain.x) < 10
         && read($Heap, _module.__default.Postie3($Heap, c#0), _module.Mountain.x)
           == LitInt(5)
         && $Is(_module.__default.Postie3($Heap, c#0), Tclass._module.Mountain?()));

function _module.__default.Postie3#requires(Heap, ref) : bool;

// #requires axiom for _module.__default.Postie3
axiom (forall $Heap: Heap, c#0: ref :: 
  { _module.__default.Postie3#requires($Heap, c#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap) && $Is(c#0, Tclass._module.Mountain?())
     ==> _module.__default.Postie3#requires($Heap, c#0)
       == (c#0 != null && read($Heap, c#0, _module.Mountain.x) == LitInt(5)));

// definition axiom for _module.__default.Postie3 (revealed)
axiom 9 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, c#0: ref :: 
    { _module.__default.Postie3($Heap, c#0), $IsGoodHeap($Heap) } 
    _module.__default.Postie3#canCall($Heap, c#0)
         || (9 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(c#0, Tclass._module.Mountain?())
           && 
          c#0 != null
           && read($Heap, c#0, _module.Mountain.x) == LitInt(5))
       ==> _module.__default.Postie3($Heap, c#0) == c#0);

procedure CheckWellformed$$_module.__default.Postie3(c#0: ref where $Is(c#0, Tclass._module.Mountain?()));
  free requires 9 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures _module.__default.Postie3($Heap, c#0) != null;
  ensures read($Heap, _module.__default.Postie3($Heap, c#0), _module.Mountain.x) < 10;
  ensures read($Heap, _module.__default.Postie3($Heap, c#0), _module.Mountain.x)
     == LitInt(5);



implementation CheckWellformed$$_module.__default.Postie3(c#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;
  var ##c#0: ref;
  var ##c#1: ref;
  var ##c#2: ref;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function Postie3
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(229,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == c#0);
    assume c#0 != null;
    assert c#0 != null;
    b$reqreads#0 := $_Frame[c#0, _module.Mountain.x];
    assume read($Heap, c#0, _module.Mountain.x) == LitInt(5);
    assert b$reqreads#0;
    if (*)
    {
        assume $Is(_module.__default.Postie3($Heap, c#0), Tclass._module.Mountain?());
        ##c#0 := c#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#0, Tclass._module.Mountain?(), $Heap);
        assert {:subsumption 0} ##c#0 != null;
        assert {:subsumption 0} read($Heap, ##c#0, _module.Mountain.x) == LitInt(5);
        assume ##c#0 != null && read($Heap, ##c#0, _module.Mountain.x) == LitInt(5);
        assert c#0 == c#0
           || 
          (Set#Subset(Set#UnionOne(Set#Empty(): Set Box, $Box(##c#0)), 
              Set#UnionOne(Set#Empty(): Set Box, $Box(c#0)))
             && !Set#Subset(Set#UnionOne(Set#Empty(): Set Box, $Box(c#0)), 
              Set#UnionOne(Set#Empty(): Set Box, $Box(##c#0))))
           || (Set#Equal(Set#UnionOne(Set#Empty(): Set Box, $Box(##c#0)), 
              Set#UnionOne(Set#Empty(): Set Box, $Box(c#0)))
             && 
            ##c#0 == null
             && c#0 != null);
        assume c#0 == c#0 || _module.__default.Postie3#canCall($Heap, c#0);
        assume _module.__default.Postie3($Heap, c#0) != null;
        ##c#1 := c#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#1, Tclass._module.Mountain?(), $Heap);
        assert {:subsumption 0} ##c#1 != null;
        assert {:subsumption 0} read($Heap, ##c#1, _module.Mountain.x) == LitInt(5);
        assume ##c#1 != null && read($Heap, ##c#1, _module.Mountain.x) == LitInt(5);
        assert c#0 == c#0
           || 
          (Set#Subset(Set#UnionOne(Set#Empty(): Set Box, $Box(##c#1)), 
              Set#UnionOne(Set#Empty(): Set Box, $Box(c#0)))
             && !Set#Subset(Set#UnionOne(Set#Empty(): Set Box, $Box(c#0)), 
              Set#UnionOne(Set#Empty(): Set Box, $Box(##c#1))))
           || (Set#Equal(Set#UnionOne(Set#Empty(): Set Box, $Box(##c#1)), 
              Set#UnionOne(Set#Empty(): Set Box, $Box(c#0)))
             && 
            ##c#1 == null
             && c#0 != null);
        assume c#0 == c#0 || _module.__default.Postie3#canCall($Heap, c#0);
        assert _module.__default.Postie3($Heap, c#0) != null;
        assume read($Heap, _module.__default.Postie3($Heap, c#0), _module.Mountain.x) < 10;
        ##c#2 := c#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#2, Tclass._module.Mountain?(), $Heap);
        assert {:subsumption 0} ##c#2 != null;
        assert {:subsumption 0} read($Heap, ##c#2, _module.Mountain.x) == LitInt(5);
        assume ##c#2 != null && read($Heap, ##c#2, _module.Mountain.x) == LitInt(5);
        assert c#0 == c#0
           || 
          (Set#Subset(Set#UnionOne(Set#Empty(): Set Box, $Box(##c#2)), 
              Set#UnionOne(Set#Empty(): Set Box, $Box(c#0)))
             && !Set#Subset(Set#UnionOne(Set#Empty(): Set Box, $Box(c#0)), 
              Set#UnionOne(Set#Empty(): Set Box, $Box(##c#2))))
           || (Set#Equal(Set#UnionOne(Set#Empty(): Set Box, $Box(##c#2)), 
              Set#UnionOne(Set#Empty(): Set Box, $Box(c#0)))
             && 
            ##c#2 == null
             && c#0 != null);
        assume c#0 == c#0 || _module.__default.Postie3#canCall($Heap, c#0);
        assert _module.__default.Postie3($Heap, c#0) != null;
        assume read($Heap, _module.__default.Postie3($Heap, c#0), _module.Mountain.x)
           == LitInt(5);
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> $o == c#0);
        assume _module.__default.Postie3($Heap, c#0) == c#0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.Postie3($Heap, c#0), Tclass._module.Mountain?());
    }
}



// function declaration for _module._default.Postie4
function _module.__default.Postie4($heap: Heap, c#0: ref) : ref;

function _module.__default.Postie4#canCall($heap: Heap, c#0: ref) : bool;

// frame axiom for _module.__default.Postie4
axiom (forall $h0: Heap, $h1: Heap, c#0: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.__default.Postie4($h1, c#0) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && (_module.__default.Postie4#canCall($h0, c#0)
         || $Is(c#0, Tclass._module.Mountain?()))
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && $o == c#0 ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.__default.Postie4($h0, c#0) == _module.__default.Postie4($h1, c#0));

// consequence axiom for _module.__default.Postie4
axiom 10 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, c#0: ref :: 
    { _module.__default.Postie4($Heap, c#0) } 
    _module.__default.Postie4#canCall($Heap, c#0)
         || (10 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(c#0, Tclass._module.Mountain?())
           && 
          c#0 != null
           && read($Heap, c#0, _module.Mountain.x) <= LitInt(5))
       ==> _module.__default.Postie4($Heap, c#0) != null
         && read($Heap, _module.__default.Postie4($Heap, c#0), _module.Mountain.x) < 10
         && read($Heap, _module.__default.Postie4($Heap, c#0), _module.Mountain.x)
           == LitInt(5)
         && $Is(_module.__default.Postie4($Heap, c#0), Tclass._module.Mountain?()));

function _module.__default.Postie4#requires(Heap, ref) : bool;

// #requires axiom for _module.__default.Postie4
axiom (forall $Heap: Heap, c#0: ref :: 
  { _module.__default.Postie4#requires($Heap, c#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap) && $Is(c#0, Tclass._module.Mountain?())
     ==> _module.__default.Postie4#requires($Heap, c#0)
       == (c#0 != null && read($Heap, c#0, _module.Mountain.x) <= LitInt(5)));

// definition axiom for _module.__default.Postie4 (revealed)
axiom 10 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, c#0: ref :: 
    { _module.__default.Postie4($Heap, c#0), $IsGoodHeap($Heap) } 
    _module.__default.Postie4#canCall($Heap, c#0)
         || (10 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(c#0, Tclass._module.Mountain?())
           && 
          c#0 != null
           && read($Heap, c#0, _module.Mountain.x) <= LitInt(5))
       ==> _module.__default.Postie4($Heap, c#0) == c#0);

procedure CheckWellformed$$_module.__default.Postie4(c#0: ref where $Is(c#0, Tclass._module.Mountain?()));
  free requires 10 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures _module.__default.Postie4($Heap, c#0) != null;
  ensures read($Heap, _module.__default.Postie4($Heap, c#0), _module.Mountain.x) < 10;
  ensures read($Heap, _module.__default.Postie4($Heap, c#0), _module.Mountain.x)
     == LitInt(5);



implementation CheckWellformed$$_module.__default.Postie4(c#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;
  var ##c#0: ref;
  var ##c#1: ref;
  var ##c#2: ref;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function Postie4
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Definedness.dfy(237,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == c#0);
    assume c#0 != null;
    assert c#0 != null;
    b$reqreads#0 := $_Frame[c#0, _module.Mountain.x];
    assume read($Heap, c#0, _module.Mountain.x) <= LitInt(5);
    assert b$reqreads#0;
    if (*)
    {
        assume $Is(_module.__default.Postie4($Heap, c#0), Tclass._module.Mountain?());
        ##c#0 := c#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#0, Tclass._module.Mountain?(), $Heap);
        assert {:subsumption 0} ##c#0 != null;
        assert {:subsumption 0} read($Heap, ##c#0, _module.Mountain.x) <= LitInt(5);
        assume ##c#0 != null && read($Heap, ##c#0, _module.Mountain.x) <= LitInt(5);
        assert c#0 == c#0
           || 
          (Set#Subset(Set#UnionOne(Set#Empty(): Set Box, $Box(##c#0)), 
              Set#UnionOne(Set#Empty(): Set Box, $Box(c#0)))
             && !Set#Subset(Set#UnionOne(Set#Empty(): Set Box, $Box(c#0)), 
              Set#UnionOne(Set#Empty(): Set Box, $Box(##c#0))))
           || (Set#Equal(Set#UnionOne(Set#Empty(): Set Box, $Box(##c#0)), 
              Set#UnionOne(Set#Empty(): Set Box, $Box(c#0)))
             && 
            ##c#0 == null
             && c#0 != null);
        assume c#0 == c#0 || _module.__default.Postie4#canCall($Heap, c#0);
        assume _module.__default.Postie4($Heap, c#0) != null;
        ##c#1 := c#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#1, Tclass._module.Mountain?(), $Heap);
        assert {:subsumption 0} ##c#1 != null;
        assert {:subsumption 0} read($Heap, ##c#1, _module.Mountain.x) <= LitInt(5);
        assume ##c#1 != null && read($Heap, ##c#1, _module.Mountain.x) <= LitInt(5);
        assert c#0 == c#0
           || 
          (Set#Subset(Set#UnionOne(Set#Empty(): Set Box, $Box(##c#1)), 
              Set#UnionOne(Set#Empty(): Set Box, $Box(c#0)))
             && !Set#Subset(Set#UnionOne(Set#Empty(): Set Box, $Box(c#0)), 
              Set#UnionOne(Set#Empty(): Set Box, $Box(##c#1))))
           || (Set#Equal(Set#UnionOne(Set#Empty(): Set Box, $Box(##c#1)), 
              Set#UnionOne(Set#Empty(): Set Box, $Box(c#0)))
             && 
            ##c#1 == null
             && c#0 != null);
        assume c#0 == c#0 || _module.__default.Postie4#canCall($Heap, c#0);
        assert _module.__default.Postie4($Heap, c#0) != null;
        assume read($Heap, _module.__default.Postie4($Heap, c#0), _module.Mountain.x) < 10;
        ##c#2 := c#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##c#2, Tclass._module.Mountain?(), $Heap);
        assert {:subsumption 0} ##c#2 != null;
        assert {:subsumption 0} read($Heap, ##c#2, _module.Mountain.x) <= LitInt(5);
        assume ##c#2 != null && read($Heap, ##c#2, _module.Mountain.x) <= LitInt(5);
        assert c#0 == c#0
           || 
          (Set#Subset(Set#UnionOne(Set#Empty(): Set Box, $Box(##c#2)), 
              Set#UnionOne(Set#Empty(): Set Box, $Box(c#0)))
             && !Set#Subset(Set#UnionOne(Set#Empty(): Set Box, $Box(c#0)), 
              Set#UnionOne(Set#Empty(): Set Box, $Box(##c#2))))
           || (Set#Equal(Set#UnionOne(Set#Empty(): Set Box, $Box(##c#2)), 
              Set#UnionOne(Set#Empty(): Set Box, $Box(c#0)))
             && 
            ##c#2 == null
             && c#0 != null);
        assume c#0 == c#0 || _module.__default.Postie4#canCall($Heap, c#0);
        assert _module.__default.Postie4($Heap, c#0) != null;
        assume read($Heap, _module.__default.Postie4($Heap, c#0), _module.Mountain.x)
           == LitInt(5);
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> $o == c#0);
        assume _module.__default.Postie4($Heap, c#0) == c#0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.Postie4($Heap, c#0), Tclass._module.Mountain?());
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

const unique tytagFamily$_tuple#2: TyTagFamily;

const unique tytagFamily$_tuple#0: TyTagFamily;

const unique tytagFamily$SoWellformed: TyTagFamily;

const unique tytagFamily$StatementTwoShoes: TyTagFamily;

const unique tytagFamily$Mountain: TyTagFamily;

const unique tytagFamily$_default: TyTagFamily;

const unique field$xyz: NameFamily;

const unique field$next: NameFamily;

const unique field$x: NameFamily;

const unique field$s: NameFamily;
