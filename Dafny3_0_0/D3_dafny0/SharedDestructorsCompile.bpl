// Dafny 3.0.0.30204
// Command Line Options: -compile:0 -noVerify /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy -print:./SharedDestructorsCompile.bpl

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

// Box/unbox axiom for bv27
axiom (forall bx: Box :: 
  { $IsBox(bx, TBitvector(27)) } 
  $IsBox(bx, TBitvector(27))
     ==> $Box($Unbox(bx): bv27) == bx && $Is($Unbox(bx): bv27, TBitvector(27)));

axiom (forall v: bv27 :: { $Is(v, TBitvector(27)) } $Is(v, TBitvector(27)));

axiom (forall v: bv27, heap: Heap :: 
  { $IsAlloc(v, TBitvector(27), heap) } 
  $IsAlloc(v, TBitvector(27), heap));

function {:bvbuiltin "bvand"} and_bv27(bv27, bv27) : bv27;

function {:bvbuiltin "bvor"} or_bv27(bv27, bv27) : bv27;

function {:bvbuiltin "bvxor"} xor_bv27(bv27, bv27) : bv27;

function {:bvbuiltin "bvnot"} not_bv27(bv27) : bv27;

function {:bvbuiltin "bvadd"} add_bv27(bv27, bv27) : bv27;

function {:bvbuiltin "bvsub"} sub_bv27(bv27, bv27) : bv27;

function {:bvbuiltin "bvmul"} mul_bv27(bv27, bv27) : bv27;

function {:bvbuiltin "bvudiv"} div_bv27(bv27, bv27) : bv27;

function {:bvbuiltin "bvurem"} mod_bv27(bv27, bv27) : bv27;

function {:bvbuiltin "bvult"} lt_bv27(bv27, bv27) : bool;

function {:bvbuiltin "bvule"} le_bv27(bv27, bv27) : bool;

function {:bvbuiltin "bvuge"} ge_bv27(bv27, bv27) : bool;

function {:bvbuiltin "bvugt"} gt_bv27(bv27, bv27) : bool;

function {:bvbuiltin "bvshl"} LeftShift_bv27(bv27, bv27) : bv27;

function {:bvbuiltin "bvlshr"} RightShift_bv27(bv27, bv27) : bv27;

function {:bvbuiltin "ext_rotate_left"} LeftRotate_bv27(bv27, bv27) : bv27;

function {:bvbuiltin "ext_rotate_right"} RightRotate_bv27(bv27, bv27) : bv27;

function {:bvbuiltin "(_ int2bv 27)"} nat_to_bv27(int) : bv27;

function {:bvbuiltin "bv2int"} smt_nat_from_bv27(bv27) : int;

function nat_from_bv27(bv27) : int;

axiom (forall b: bv27 :: 
  { nat_from_bv27(b) } 
  0 <= nat_from_bv27(b)
     && nat_from_bv27(b) < 134217728
     && nat_from_bv27(b) == smt_nat_from_bv27(b));

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

// Constructor function declaration
function #_module.Dt.A(int, real) : DatatypeType;

const unique ##_module.Dt.A: DtCtorId;

// Constructor identifier
axiom (forall a#14#0#0: int, a#14#1#0: real :: 
  { #_module.Dt.A(a#14#0#0, a#14#1#0) } 
  DatatypeCtorId(#_module.Dt.A(a#14#0#0, a#14#1#0)) == ##_module.Dt.A);

function _module.Dt.A_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Dt.A_q(d) } 
  _module.Dt.A_q(d) <==> DatatypeCtorId(d) == ##_module.Dt.A);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Dt.A_q(d) } 
  _module.Dt.A_q(d)
     ==> (exists a#15#0#0: int, a#15#1#0: real :: d == #_module.Dt.A(a#15#0#0, a#15#1#0)));

function Tclass._module.Dt() : Ty;

const unique Tagclass._module.Dt: TyTag;

// Tclass._module.Dt Tag
axiom Tag(Tclass._module.Dt()) == Tagclass._module.Dt
   && TagFamily(Tclass._module.Dt()) == tytagFamily$Dt;

// Box/unbox axiom for Tclass._module.Dt
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Dt()) } 
  $IsBox(bx, Tclass._module.Dt())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Dt()));

// Constructor $Is
axiom (forall a#16#0#0: int, a#16#1#0: real :: 
  { $Is(#_module.Dt.A(a#16#0#0, a#16#1#0), Tclass._module.Dt()) } 
  $Is(#_module.Dt.A(a#16#0#0, a#16#1#0), Tclass._module.Dt())
     <==> $Is(a#16#0#0, TInt) && $Is(a#16#1#0, TReal));

// Constructor $IsAlloc
axiom (forall a#17#0#0: int, a#17#1#0: real, $h: Heap :: 
  { $IsAlloc(#_module.Dt.A(a#17#0#0, a#17#1#0), Tclass._module.Dt(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Dt.A(a#17#0#0, a#17#1#0), Tclass._module.Dt(), $h)
       <==> $IsAlloc(a#17#0#0, TInt, $h) && $IsAlloc(a#17#1#0, TReal, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Dt.x(d), TInt, $h) } 
  $IsGoodHeap($h) && _module.Dt.A_q(d) && $IsAlloc(d, Tclass._module.Dt(), $h)
     ==> $IsAlloc(_module.Dt.x(d), TInt, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Dt.y(d), TReal, $h) } 
  $IsGoodHeap($h) && _module.Dt.A_q(d) && $IsAlloc(d, Tclass._module.Dt(), $h)
     ==> $IsAlloc(_module.Dt.y(d), TReal, $h));

// Constructor literal
axiom (forall a#18#0#0: int, a#18#1#0: real :: 
  { #_module.Dt.A(LitInt(a#18#0#0), LitReal(a#18#1#0)) } 
  #_module.Dt.A(LitInt(a#18#0#0), LitReal(a#18#1#0))
     == Lit(#_module.Dt.A(a#18#0#0, a#18#1#0)));

function _module.Dt.x(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#19#0#0: int, a#19#1#0: real :: 
  { #_module.Dt.A(a#19#0#0, a#19#1#0) } 
  _module.Dt.x(#_module.Dt.A(a#19#0#0, a#19#1#0)) == a#19#0#0);

function _module.Dt.y(DatatypeType) : real;

// Constructor injectivity
axiom (forall a#20#0#0: int, a#20#1#0: real :: 
  { #_module.Dt.A(a#20#0#0, a#20#1#0) } 
  _module.Dt.y(#_module.Dt.A(a#20#0#0, a#20#1#0)) == a#20#1#0);

// Constructor function declaration
function #_module.Dt.B(ref, int) : DatatypeType;

const unique ##_module.Dt.B: DtCtorId;

// Constructor identifier
axiom (forall a#21#0#0: ref, a#21#1#0: int :: 
  { #_module.Dt.B(a#21#0#0, a#21#1#0) } 
  DatatypeCtorId(#_module.Dt.B(a#21#0#0, a#21#1#0)) == ##_module.Dt.B);

function _module.Dt.B_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Dt.B_q(d) } 
  _module.Dt.B_q(d) <==> DatatypeCtorId(d) == ##_module.Dt.B);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Dt.B_q(d) } 
  _module.Dt.B_q(d)
     ==> (exists a#22#0#0: ref, a#22#1#0: int :: d == #_module.Dt.B(a#22#0#0, a#22#1#0)));

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

// Constructor $Is
axiom (forall a#23#0#0: ref, a#23#1#0: int :: 
  { $Is(#_module.Dt.B(a#23#0#0, a#23#1#0), Tclass._module.Dt()) } 
  $Is(#_module.Dt.B(a#23#0#0, a#23#1#0), Tclass._module.Dt())
     <==> $Is(a#23#0#0, Tclass._module.MyClass()) && $Is(a#23#1#0, TInt));

// Constructor $IsAlloc
axiom (forall a#24#0#0: ref, a#24#1#0: int, $h: Heap :: 
  { $IsAlloc(#_module.Dt.B(a#24#0#0, a#24#1#0), Tclass._module.Dt(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Dt.B(a#24#0#0, a#24#1#0), Tclass._module.Dt(), $h)
       <==> $IsAlloc(a#24#0#0, Tclass._module.MyClass(), $h) && $IsAlloc(a#24#1#0, TInt, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Dt.h(d), Tclass._module.MyClass(), $h) } 
  $IsGoodHeap($h) && _module.Dt.B_q(d) && $IsAlloc(d, Tclass._module.Dt(), $h)
     ==> $IsAlloc(_module.Dt.h(d), Tclass._module.MyClass(), $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Dt.x(d), TInt, $h) } 
  $IsGoodHeap($h) && _module.Dt.B_q(d) && $IsAlloc(d, Tclass._module.Dt(), $h)
     ==> $IsAlloc(_module.Dt.x(d), TInt, $h));

// Constructor literal
axiom (forall a#25#0#0: ref, a#25#1#0: int :: 
  { #_module.Dt.B(Lit(a#25#0#0), LitInt(a#25#1#0)) } 
  #_module.Dt.B(Lit(a#25#0#0), LitInt(a#25#1#0))
     == Lit(#_module.Dt.B(a#25#0#0, a#25#1#0)));

function _module.Dt.h(DatatypeType) : ref;

// Constructor injectivity
axiom (forall a#26#0#0: ref, a#26#1#0: int :: 
  { #_module.Dt.B(a#26#0#0, a#26#1#0) } 
  _module.Dt.h(#_module.Dt.B(a#26#0#0, a#26#1#0)) == a#26#0#0);

// Constructor injectivity
axiom (forall a#27#0#0: ref, a#27#1#0: int :: 
  { #_module.Dt.B(a#27#0#0, a#27#1#0) } 
  _module.Dt.x(#_module.Dt.B(a#27#0#0, a#27#1#0)) == a#27#1#0);

// Constructor function declaration
function #_module.Dt.C(real) : DatatypeType;

const unique ##_module.Dt.C: DtCtorId;

// Constructor identifier
axiom (forall a#28#0#0: real :: 
  { #_module.Dt.C(a#28#0#0) } 
  DatatypeCtorId(#_module.Dt.C(a#28#0#0)) == ##_module.Dt.C);

function _module.Dt.C_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Dt.C_q(d) } 
  _module.Dt.C_q(d) <==> DatatypeCtorId(d) == ##_module.Dt.C);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Dt.C_q(d) } 
  _module.Dt.C_q(d) ==> (exists a#29#0#0: real :: d == #_module.Dt.C(a#29#0#0)));

// Constructor $Is
axiom (forall a#30#0#0: real :: 
  { $Is(#_module.Dt.C(a#30#0#0), Tclass._module.Dt()) } 
  $Is(#_module.Dt.C(a#30#0#0), Tclass._module.Dt()) <==> $Is(a#30#0#0, TReal));

// Constructor $IsAlloc
axiom (forall a#31#0#0: real, $h: Heap :: 
  { $IsAlloc(#_module.Dt.C(a#31#0#0), Tclass._module.Dt(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Dt.C(a#31#0#0), Tclass._module.Dt(), $h)
       <==> $IsAlloc(a#31#0#0, TReal, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Dt.y(d), TReal, $h) } 
  $IsGoodHeap($h) && _module.Dt.C_q(d) && $IsAlloc(d, Tclass._module.Dt(), $h)
     ==> $IsAlloc(_module.Dt.y(d), TReal, $h));

// Constructor literal
axiom (forall a#32#0#0: real :: 
  { #_module.Dt.C(LitReal(a#32#0#0)) } 
  #_module.Dt.C(LitReal(a#32#0#0)) == Lit(#_module.Dt.C(a#32#0#0)));

// Constructor injectivity
axiom (forall a#33#0#0: real :: 
  { #_module.Dt.C(a#33#0#0) } 
  _module.Dt.y(#_module.Dt.C(a#33#0#0)) == a#33#0#0);

// Depth-one case-split function
function $IsA#_module.Dt(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.Dt(d) } 
  $IsA#_module.Dt(d)
     ==> _module.Dt.A_q(d) || _module.Dt.B_q(d) || _module.Dt.C_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.Dt.C_q(d), $Is(d, Tclass._module.Dt()) } 
    { _module.Dt.B_q(d), $Is(d, Tclass._module.Dt()) } 
    { _module.Dt.A_q(d), $Is(d, Tclass._module.Dt()) } 
  $Is(d, Tclass._module.Dt())
     ==> _module.Dt.A_q(d) || _module.Dt.B_q(d) || _module.Dt.C_q(d));

// Datatype extensional equality declaration
function _module.Dt#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.Dt.A
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Dt#Equal(a, b), _module.Dt.A_q(a) } 
    { _module.Dt#Equal(a, b), _module.Dt.A_q(b) } 
  _module.Dt.A_q(a) && _module.Dt.A_q(b)
     ==> (_module.Dt#Equal(a, b)
       <==> _module.Dt.x(a) == _module.Dt.x(b) && _module.Dt.y(a) == _module.Dt.y(b)));

// Datatype extensional equality definition: #_module.Dt.B
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Dt#Equal(a, b), _module.Dt.B_q(a) } 
    { _module.Dt#Equal(a, b), _module.Dt.B_q(b) } 
  _module.Dt.B_q(a) && _module.Dt.B_q(b)
     ==> (_module.Dt#Equal(a, b)
       <==> _module.Dt.h(a) == _module.Dt.h(b) && _module.Dt.x(a) == _module.Dt.x(b)));

// Datatype extensional equality definition: #_module.Dt.C
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Dt#Equal(a, b), _module.Dt.C_q(a) } 
    { _module.Dt#Equal(a, b), _module.Dt.C_q(b) } 
  _module.Dt.C_q(a) && _module.Dt.C_q(b)
     ==> (_module.Dt#Equal(a, b) <==> _module.Dt.y(a) == _module.Dt.y(b)));

// Datatype extensionality axiom: _module.Dt
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Dt#Equal(a, b) } 
  _module.Dt#Equal(a, b) <==> a == b);

const unique class._module.Dt: ClassName;

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

// Constructor function declaration
function #_module.Klef.C0(int, int, int, int) : DatatypeType;

const unique ##_module.Klef.C0: DtCtorId;

// Constructor identifier
axiom (forall a#34#0#0: int, a#34#1#0: int, a#34#2#0: int, a#34#3#0: int :: 
  { #_module.Klef.C0(a#34#0#0, a#34#1#0, a#34#2#0, a#34#3#0) } 
  DatatypeCtorId(#_module.Klef.C0(a#34#0#0, a#34#1#0, a#34#2#0, a#34#3#0))
     == ##_module.Klef.C0);

function _module.Klef.C0_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Klef.C0_q(d) } 
  _module.Klef.C0_q(d) <==> DatatypeCtorId(d) == ##_module.Klef.C0);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Klef.C0_q(d) } 
  _module.Klef.C0_q(d)
     ==> (exists a#35#0#0: int, a#35#1#0: int, a#35#2#0: int, a#35#3#0: int :: 
      d == #_module.Klef.C0(a#35#0#0, a#35#1#0, a#35#2#0, a#35#3#0)));

function Tclass._module.Klef() : Ty;

const unique Tagclass._module.Klef: TyTag;

// Tclass._module.Klef Tag
axiom Tag(Tclass._module.Klef()) == Tagclass._module.Klef
   && TagFamily(Tclass._module.Klef()) == tytagFamily$Klef;

// Box/unbox axiom for Tclass._module.Klef
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Klef()) } 
  $IsBox(bx, Tclass._module.Klef())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Klef()));

// Constructor $Is
axiom (forall a#36#0#0: int, a#36#1#0: int, a#36#2#0: int, a#36#3#0: int :: 
  { $Is(#_module.Klef.C0(a#36#0#0, a#36#1#0, a#36#2#0, a#36#3#0), Tclass._module.Klef()) } 
  $Is(#_module.Klef.C0(a#36#0#0, a#36#1#0, a#36#2#0, a#36#3#0), Tclass._module.Klef())
     <==> $Is(a#36#0#0, TInt)
       && $Is(a#36#1#0, TInt)
       && $Is(a#36#2#0, TInt)
       && $Is(a#36#3#0, TInt));

// Constructor $IsAlloc
axiom (forall a#37#0#0: int, a#37#1#0: int, a#37#2#0: int, a#37#3#0: int, $h: Heap :: 
  { $IsAlloc(#_module.Klef.C0(a#37#0#0, a#37#1#0, a#37#2#0, a#37#3#0), 
      Tclass._module.Klef(), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Klef.C0(a#37#0#0, a#37#1#0, a#37#2#0, a#37#3#0), 
        Tclass._module.Klef(), 
        $h)
       <==> $IsAlloc(a#37#0#0, TInt, $h)
         && $IsAlloc(a#37#1#0, TInt, $h)
         && $IsAlloc(a#37#2#0, TInt, $h)
         && $IsAlloc(a#37#3#0, TInt, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Klef._0(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Klef.C0_q(d)
       && $IsAlloc(d, Tclass._module.Klef(), $h)
     ==> $IsAlloc(_module.Klef._0(d), TInt, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Klef._1(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Klef.C0_q(d)
       && $IsAlloc(d, Tclass._module.Klef(), $h)
     ==> $IsAlloc(_module.Klef._1(d), TInt, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Klef._2(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Klef.C0_q(d)
       && $IsAlloc(d, Tclass._module.Klef(), $h)
     ==> $IsAlloc(_module.Klef._2(d), TInt, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Klef.c0(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Klef.C0_q(d)
       && $IsAlloc(d, Tclass._module.Klef(), $h)
     ==> $IsAlloc(_module.Klef.c0(d), TInt, $h));

// Constructor literal
axiom (forall a#38#0#0: int, a#38#1#0: int, a#38#2#0: int, a#38#3#0: int :: 
  { #_module.Klef.C0(LitInt(a#38#0#0), LitInt(a#38#1#0), LitInt(a#38#2#0), LitInt(a#38#3#0)) } 
  #_module.Klef.C0(LitInt(a#38#0#0), LitInt(a#38#1#0), LitInt(a#38#2#0), LitInt(a#38#3#0))
     == Lit(#_module.Klef.C0(a#38#0#0, a#38#1#0, a#38#2#0, a#38#3#0)));

function _module.Klef._0(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#39#0#0: int, a#39#1#0: int, a#39#2#0: int, a#39#3#0: int :: 
  { #_module.Klef.C0(a#39#0#0, a#39#1#0, a#39#2#0, a#39#3#0) } 
  _module.Klef._0(#_module.Klef.C0(a#39#0#0, a#39#1#0, a#39#2#0, a#39#3#0))
     == a#39#0#0);

function _module.Klef._1(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#40#0#0: int, a#40#1#0: int, a#40#2#0: int, a#40#3#0: int :: 
  { #_module.Klef.C0(a#40#0#0, a#40#1#0, a#40#2#0, a#40#3#0) } 
  _module.Klef._1(#_module.Klef.C0(a#40#0#0, a#40#1#0, a#40#2#0, a#40#3#0))
     == a#40#1#0);

function _module.Klef._2(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#41#0#0: int, a#41#1#0: int, a#41#2#0: int, a#41#3#0: int :: 
  { #_module.Klef.C0(a#41#0#0, a#41#1#0, a#41#2#0, a#41#3#0) } 
  _module.Klef._2(#_module.Klef.C0(a#41#0#0, a#41#1#0, a#41#2#0, a#41#3#0))
     == a#41#2#0);

function _module.Klef.c0(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#42#0#0: int, a#42#1#0: int, a#42#2#0: int, a#42#3#0: int :: 
  { #_module.Klef.C0(a#42#0#0, a#42#1#0, a#42#2#0, a#42#3#0) } 
  _module.Klef.c0(#_module.Klef.C0(a#42#0#0, a#42#1#0, a#42#2#0, a#42#3#0))
     == a#42#3#0);

// Constructor function declaration
function #_module.Klef.C1(int, int, int, int) : DatatypeType;

const unique ##_module.Klef.C1: DtCtorId;

// Constructor identifier
axiom (forall a#43#0#0: int, a#43#1#0: int, a#43#2#0: int, a#43#3#0: int :: 
  { #_module.Klef.C1(a#43#0#0, a#43#1#0, a#43#2#0, a#43#3#0) } 
  DatatypeCtorId(#_module.Klef.C1(a#43#0#0, a#43#1#0, a#43#2#0, a#43#3#0))
     == ##_module.Klef.C1);

function _module.Klef.C1_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Klef.C1_q(d) } 
  _module.Klef.C1_q(d) <==> DatatypeCtorId(d) == ##_module.Klef.C1);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Klef.C1_q(d) } 
  _module.Klef.C1_q(d)
     ==> (exists a#44#0#0: int, a#44#1#0: int, a#44#2#0: int, a#44#3#0: int :: 
      d == #_module.Klef.C1(a#44#0#0, a#44#1#0, a#44#2#0, a#44#3#0)));

// Constructor $Is
axiom (forall a#45#0#0: int, a#45#1#0: int, a#45#2#0: int, a#45#3#0: int :: 
  { $Is(#_module.Klef.C1(a#45#0#0, a#45#1#0, a#45#2#0, a#45#3#0), Tclass._module.Klef()) } 
  $Is(#_module.Klef.C1(a#45#0#0, a#45#1#0, a#45#2#0, a#45#3#0), Tclass._module.Klef())
     <==> $Is(a#45#0#0, TInt)
       && $Is(a#45#1#0, TInt)
       && $Is(a#45#2#0, TInt)
       && $Is(a#45#3#0, TInt));

// Constructor $IsAlloc
axiom (forall a#46#0#0: int, a#46#1#0: int, a#46#2#0: int, a#46#3#0: int, $h: Heap :: 
  { $IsAlloc(#_module.Klef.C1(a#46#0#0, a#46#1#0, a#46#2#0, a#46#3#0), 
      Tclass._module.Klef(), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Klef.C1(a#46#0#0, a#46#1#0, a#46#2#0, a#46#3#0), 
        Tclass._module.Klef(), 
        $h)
       <==> $IsAlloc(a#46#0#0, TInt, $h)
         && $IsAlloc(a#46#1#0, TInt, $h)
         && $IsAlloc(a#46#2#0, TInt, $h)
         && $IsAlloc(a#46#3#0, TInt, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Klef._1(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Klef.C1_q(d)
       && $IsAlloc(d, Tclass._module.Klef(), $h)
     ==> $IsAlloc(_module.Klef._1(d), TInt, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Klef._2(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Klef.C1_q(d)
       && $IsAlloc(d, Tclass._module.Klef(), $h)
     ==> $IsAlloc(_module.Klef._2(d), TInt, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Klef._3(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Klef.C1_q(d)
       && $IsAlloc(d, Tclass._module.Klef(), $h)
     ==> $IsAlloc(_module.Klef._3(d), TInt, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Klef.c1(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Klef.C1_q(d)
       && $IsAlloc(d, Tclass._module.Klef(), $h)
     ==> $IsAlloc(_module.Klef.c1(d), TInt, $h));

// Constructor literal
axiom (forall a#47#0#0: int, a#47#1#0: int, a#47#2#0: int, a#47#3#0: int :: 
  { #_module.Klef.C1(LitInt(a#47#0#0), LitInt(a#47#1#0), LitInt(a#47#2#0), LitInt(a#47#3#0)) } 
  #_module.Klef.C1(LitInt(a#47#0#0), LitInt(a#47#1#0), LitInt(a#47#2#0), LitInt(a#47#3#0))
     == Lit(#_module.Klef.C1(a#47#0#0, a#47#1#0, a#47#2#0, a#47#3#0)));

// Constructor injectivity
axiom (forall a#48#0#0: int, a#48#1#0: int, a#48#2#0: int, a#48#3#0: int :: 
  { #_module.Klef.C1(a#48#0#0, a#48#1#0, a#48#2#0, a#48#3#0) } 
  _module.Klef._1(#_module.Klef.C1(a#48#0#0, a#48#1#0, a#48#2#0, a#48#3#0))
     == a#48#0#0);

// Constructor injectivity
axiom (forall a#49#0#0: int, a#49#1#0: int, a#49#2#0: int, a#49#3#0: int :: 
  { #_module.Klef.C1(a#49#0#0, a#49#1#0, a#49#2#0, a#49#3#0) } 
  _module.Klef._2(#_module.Klef.C1(a#49#0#0, a#49#1#0, a#49#2#0, a#49#3#0))
     == a#49#1#0);

function _module.Klef._3(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#50#0#0: int, a#50#1#0: int, a#50#2#0: int, a#50#3#0: int :: 
  { #_module.Klef.C1(a#50#0#0, a#50#1#0, a#50#2#0, a#50#3#0) } 
  _module.Klef._3(#_module.Klef.C1(a#50#0#0, a#50#1#0, a#50#2#0, a#50#3#0))
     == a#50#2#0);

function _module.Klef.c1(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#51#0#0: int, a#51#1#0: int, a#51#2#0: int, a#51#3#0: int :: 
  { #_module.Klef.C1(a#51#0#0, a#51#1#0, a#51#2#0, a#51#3#0) } 
  _module.Klef.c1(#_module.Klef.C1(a#51#0#0, a#51#1#0, a#51#2#0, a#51#3#0))
     == a#51#3#0);

// Constructor function declaration
function #_module.Klef.C2(int, int, int, int) : DatatypeType;

const unique ##_module.Klef.C2: DtCtorId;

// Constructor identifier
axiom (forall a#52#0#0: int, a#52#1#0: int, a#52#2#0: int, a#52#3#0: int :: 
  { #_module.Klef.C2(a#52#0#0, a#52#1#0, a#52#2#0, a#52#3#0) } 
  DatatypeCtorId(#_module.Klef.C2(a#52#0#0, a#52#1#0, a#52#2#0, a#52#3#0))
     == ##_module.Klef.C2);

function _module.Klef.C2_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Klef.C2_q(d) } 
  _module.Klef.C2_q(d) <==> DatatypeCtorId(d) == ##_module.Klef.C2);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Klef.C2_q(d) } 
  _module.Klef.C2_q(d)
     ==> (exists a#53#0#0: int, a#53#1#0: int, a#53#2#0: int, a#53#3#0: int :: 
      d == #_module.Klef.C2(a#53#0#0, a#53#1#0, a#53#2#0, a#53#3#0)));

// Constructor $Is
axiom (forall a#54#0#0: int, a#54#1#0: int, a#54#2#0: int, a#54#3#0: int :: 
  { $Is(#_module.Klef.C2(a#54#0#0, a#54#1#0, a#54#2#0, a#54#3#0), Tclass._module.Klef()) } 
  $Is(#_module.Klef.C2(a#54#0#0, a#54#1#0, a#54#2#0, a#54#3#0), Tclass._module.Klef())
     <==> $Is(a#54#0#0, TInt)
       && $Is(a#54#1#0, TInt)
       && $Is(a#54#2#0, TInt)
       && $Is(a#54#3#0, TInt));

// Constructor $IsAlloc
axiom (forall a#55#0#0: int, a#55#1#0: int, a#55#2#0: int, a#55#3#0: int, $h: Heap :: 
  { $IsAlloc(#_module.Klef.C2(a#55#0#0, a#55#1#0, a#55#2#0, a#55#3#0), 
      Tclass._module.Klef(), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Klef.C2(a#55#0#0, a#55#1#0, a#55#2#0, a#55#3#0), 
        Tclass._module.Klef(), 
        $h)
       <==> $IsAlloc(a#55#0#0, TInt, $h)
         && $IsAlloc(a#55#1#0, TInt, $h)
         && $IsAlloc(a#55#2#0, TInt, $h)
         && $IsAlloc(a#55#3#0, TInt, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Klef._2(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Klef.C2_q(d)
       && $IsAlloc(d, Tclass._module.Klef(), $h)
     ==> $IsAlloc(_module.Klef._2(d), TInt, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Klef._3(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Klef.C2_q(d)
       && $IsAlloc(d, Tclass._module.Klef(), $h)
     ==> $IsAlloc(_module.Klef._3(d), TInt, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Klef._0(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Klef.C2_q(d)
       && $IsAlloc(d, Tclass._module.Klef(), $h)
     ==> $IsAlloc(_module.Klef._0(d), TInt, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Klef.c2(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Klef.C2_q(d)
       && $IsAlloc(d, Tclass._module.Klef(), $h)
     ==> $IsAlloc(_module.Klef.c2(d), TInt, $h));

// Constructor literal
axiom (forall a#56#0#0: int, a#56#1#0: int, a#56#2#0: int, a#56#3#0: int :: 
  { #_module.Klef.C2(LitInt(a#56#0#0), LitInt(a#56#1#0), LitInt(a#56#2#0), LitInt(a#56#3#0)) } 
  #_module.Klef.C2(LitInt(a#56#0#0), LitInt(a#56#1#0), LitInt(a#56#2#0), LitInt(a#56#3#0))
     == Lit(#_module.Klef.C2(a#56#0#0, a#56#1#0, a#56#2#0, a#56#3#0)));

// Constructor injectivity
axiom (forall a#57#0#0: int, a#57#1#0: int, a#57#2#0: int, a#57#3#0: int :: 
  { #_module.Klef.C2(a#57#0#0, a#57#1#0, a#57#2#0, a#57#3#0) } 
  _module.Klef._2(#_module.Klef.C2(a#57#0#0, a#57#1#0, a#57#2#0, a#57#3#0))
     == a#57#0#0);

// Constructor injectivity
axiom (forall a#58#0#0: int, a#58#1#0: int, a#58#2#0: int, a#58#3#0: int :: 
  { #_module.Klef.C2(a#58#0#0, a#58#1#0, a#58#2#0, a#58#3#0) } 
  _module.Klef._3(#_module.Klef.C2(a#58#0#0, a#58#1#0, a#58#2#0, a#58#3#0))
     == a#58#1#0);

// Constructor injectivity
axiom (forall a#59#0#0: int, a#59#1#0: int, a#59#2#0: int, a#59#3#0: int :: 
  { #_module.Klef.C2(a#59#0#0, a#59#1#0, a#59#2#0, a#59#3#0) } 
  _module.Klef._0(#_module.Klef.C2(a#59#0#0, a#59#1#0, a#59#2#0, a#59#3#0))
     == a#59#2#0);

function _module.Klef.c2(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#60#0#0: int, a#60#1#0: int, a#60#2#0: int, a#60#3#0: int :: 
  { #_module.Klef.C2(a#60#0#0, a#60#1#0, a#60#2#0, a#60#3#0) } 
  _module.Klef.c2(#_module.Klef.C2(a#60#0#0, a#60#1#0, a#60#2#0, a#60#3#0))
     == a#60#3#0);

// Constructor function declaration
function #_module.Klef.C3(int, int, int, int) : DatatypeType;

const unique ##_module.Klef.C3: DtCtorId;

// Constructor identifier
axiom (forall a#61#0#0: int, a#61#1#0: int, a#61#2#0: int, a#61#3#0: int :: 
  { #_module.Klef.C3(a#61#0#0, a#61#1#0, a#61#2#0, a#61#3#0) } 
  DatatypeCtorId(#_module.Klef.C3(a#61#0#0, a#61#1#0, a#61#2#0, a#61#3#0))
     == ##_module.Klef.C3);

function _module.Klef.C3_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Klef.C3_q(d) } 
  _module.Klef.C3_q(d) <==> DatatypeCtorId(d) == ##_module.Klef.C3);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Klef.C3_q(d) } 
  _module.Klef.C3_q(d)
     ==> (exists a#62#0#0: int, a#62#1#0: int, a#62#2#0: int, a#62#3#0: int :: 
      d == #_module.Klef.C3(a#62#0#0, a#62#1#0, a#62#2#0, a#62#3#0)));

// Constructor $Is
axiom (forall a#63#0#0: int, a#63#1#0: int, a#63#2#0: int, a#63#3#0: int :: 
  { $Is(#_module.Klef.C3(a#63#0#0, a#63#1#0, a#63#2#0, a#63#3#0), Tclass._module.Klef()) } 
  $Is(#_module.Klef.C3(a#63#0#0, a#63#1#0, a#63#2#0, a#63#3#0), Tclass._module.Klef())
     <==> $Is(a#63#0#0, TInt)
       && $Is(a#63#1#0, TInt)
       && $Is(a#63#2#0, TInt)
       && $Is(a#63#3#0, TInt));

// Constructor $IsAlloc
axiom (forall a#64#0#0: int, a#64#1#0: int, a#64#2#0: int, a#64#3#0: int, $h: Heap :: 
  { $IsAlloc(#_module.Klef.C3(a#64#0#0, a#64#1#0, a#64#2#0, a#64#3#0), 
      Tclass._module.Klef(), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Klef.C3(a#64#0#0, a#64#1#0, a#64#2#0, a#64#3#0), 
        Tclass._module.Klef(), 
        $h)
       <==> $IsAlloc(a#64#0#0, TInt, $h)
         && $IsAlloc(a#64#1#0, TInt, $h)
         && $IsAlloc(a#64#2#0, TInt, $h)
         && $IsAlloc(a#64#3#0, TInt, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Klef._3(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Klef.C3_q(d)
       && $IsAlloc(d, Tclass._module.Klef(), $h)
     ==> $IsAlloc(_module.Klef._3(d), TInt, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Klef._0(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Klef.C3_q(d)
       && $IsAlloc(d, Tclass._module.Klef(), $h)
     ==> $IsAlloc(_module.Klef._0(d), TInt, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Klef._1(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Klef.C3_q(d)
       && $IsAlloc(d, Tclass._module.Klef(), $h)
     ==> $IsAlloc(_module.Klef._1(d), TInt, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Klef.c3(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Klef.C3_q(d)
       && $IsAlloc(d, Tclass._module.Klef(), $h)
     ==> $IsAlloc(_module.Klef.c3(d), TInt, $h));

// Constructor literal
axiom (forall a#65#0#0: int, a#65#1#0: int, a#65#2#0: int, a#65#3#0: int :: 
  { #_module.Klef.C3(LitInt(a#65#0#0), LitInt(a#65#1#0), LitInt(a#65#2#0), LitInt(a#65#3#0)) } 
  #_module.Klef.C3(LitInt(a#65#0#0), LitInt(a#65#1#0), LitInt(a#65#2#0), LitInt(a#65#3#0))
     == Lit(#_module.Klef.C3(a#65#0#0, a#65#1#0, a#65#2#0, a#65#3#0)));

// Constructor injectivity
axiom (forall a#66#0#0: int, a#66#1#0: int, a#66#2#0: int, a#66#3#0: int :: 
  { #_module.Klef.C3(a#66#0#0, a#66#1#0, a#66#2#0, a#66#3#0) } 
  _module.Klef._3(#_module.Klef.C3(a#66#0#0, a#66#1#0, a#66#2#0, a#66#3#0))
     == a#66#0#0);

// Constructor injectivity
axiom (forall a#67#0#0: int, a#67#1#0: int, a#67#2#0: int, a#67#3#0: int :: 
  { #_module.Klef.C3(a#67#0#0, a#67#1#0, a#67#2#0, a#67#3#0) } 
  _module.Klef._0(#_module.Klef.C3(a#67#0#0, a#67#1#0, a#67#2#0, a#67#3#0))
     == a#67#1#0);

// Constructor injectivity
axiom (forall a#68#0#0: int, a#68#1#0: int, a#68#2#0: int, a#68#3#0: int :: 
  { #_module.Klef.C3(a#68#0#0, a#68#1#0, a#68#2#0, a#68#3#0) } 
  _module.Klef._1(#_module.Klef.C3(a#68#0#0, a#68#1#0, a#68#2#0, a#68#3#0))
     == a#68#2#0);

function _module.Klef.c3(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#69#0#0: int, a#69#1#0: int, a#69#2#0: int, a#69#3#0: int :: 
  { #_module.Klef.C3(a#69#0#0, a#69#1#0, a#69#2#0, a#69#3#0) } 
  _module.Klef.c3(#_module.Klef.C3(a#69#0#0, a#69#1#0, a#69#2#0, a#69#3#0))
     == a#69#3#0);

// Depth-one case-split function
function $IsA#_module.Klef(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.Klef(d) } 
  $IsA#_module.Klef(d)
     ==> _module.Klef.C0_q(d)
       || _module.Klef.C1_q(d)
       || _module.Klef.C2_q(d)
       || _module.Klef.C3_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.Klef.C3_q(d), $Is(d, Tclass._module.Klef()) } 
    { _module.Klef.C2_q(d), $Is(d, Tclass._module.Klef()) } 
    { _module.Klef.C1_q(d), $Is(d, Tclass._module.Klef()) } 
    { _module.Klef.C0_q(d), $Is(d, Tclass._module.Klef()) } 
  $Is(d, Tclass._module.Klef())
     ==> _module.Klef.C0_q(d)
       || _module.Klef.C1_q(d)
       || _module.Klef.C2_q(d)
       || _module.Klef.C3_q(d));

// Datatype extensional equality declaration
function _module.Klef#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.Klef.C0
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Klef#Equal(a, b), _module.Klef.C0_q(a) } 
    { _module.Klef#Equal(a, b), _module.Klef.C0_q(b) } 
  _module.Klef.C0_q(a) && _module.Klef.C0_q(b)
     ==> (_module.Klef#Equal(a, b)
       <==> _module.Klef._0(a) == _module.Klef._0(b)
         && _module.Klef._1(a) == _module.Klef._1(b)
         && _module.Klef._2(a) == _module.Klef._2(b)
         && _module.Klef.c0(a) == _module.Klef.c0(b)));

// Datatype extensional equality definition: #_module.Klef.C1
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Klef#Equal(a, b), _module.Klef.C1_q(a) } 
    { _module.Klef#Equal(a, b), _module.Klef.C1_q(b) } 
  _module.Klef.C1_q(a) && _module.Klef.C1_q(b)
     ==> (_module.Klef#Equal(a, b)
       <==> _module.Klef._1(a) == _module.Klef._1(b)
         && _module.Klef._2(a) == _module.Klef._2(b)
         && _module.Klef._3(a) == _module.Klef._3(b)
         && _module.Klef.c1(a) == _module.Klef.c1(b)));

// Datatype extensional equality definition: #_module.Klef.C2
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Klef#Equal(a, b), _module.Klef.C2_q(a) } 
    { _module.Klef#Equal(a, b), _module.Klef.C2_q(b) } 
  _module.Klef.C2_q(a) && _module.Klef.C2_q(b)
     ==> (_module.Klef#Equal(a, b)
       <==> _module.Klef._2(a) == _module.Klef._2(b)
         && _module.Klef._3(a) == _module.Klef._3(b)
         && _module.Klef._0(a) == _module.Klef._0(b)
         && _module.Klef.c2(a) == _module.Klef.c2(b)));

// Datatype extensional equality definition: #_module.Klef.C3
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Klef#Equal(a, b), _module.Klef.C3_q(a) } 
    { _module.Klef#Equal(a, b), _module.Klef.C3_q(b) } 
  _module.Klef.C3_q(a) && _module.Klef.C3_q(b)
     ==> (_module.Klef#Equal(a, b)
       <==> _module.Klef._3(a) == _module.Klef._3(b)
         && _module.Klef._0(a) == _module.Klef._0(b)
         && _module.Klef._1(a) == _module.Klef._1(b)
         && _module.Klef.c3(a) == _module.Klef.c3(b)));

// Datatype extensionality axiom: _module.Klef
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Klef#Equal(a, b) } 
  _module.Klef#Equal(a, b) <==> a == b);

const unique class._module.Klef: ClassName;

// Constructor function declaration
function #_module.Datte.AA(int, int) : DatatypeType;

const unique ##_module.Datte.AA: DtCtorId;

// Constructor identifier
axiom (forall a#70#0#0: int, a#70#1#0: int :: 
  { #_module.Datte.AA(a#70#0#0, a#70#1#0) } 
  DatatypeCtorId(#_module.Datte.AA(a#70#0#0, a#70#1#0)) == ##_module.Datte.AA);

function _module.Datte.AA_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Datte.AA_q(d) } 
  _module.Datte.AA_q(d) <==> DatatypeCtorId(d) == ##_module.Datte.AA);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Datte.AA_q(d) } 
  _module.Datte.AA_q(d)
     ==> (exists a#71#0#0: int, a#71#1#0: int :: 
      d == #_module.Datte.AA(a#71#0#0, a#71#1#0)));

function Tclass._module.Datte(Ty) : Ty;

const unique Tagclass._module.Datte: TyTag;

// Tclass._module.Datte Tag
axiom (forall _module.Datte$T: Ty :: 
  { Tclass._module.Datte(_module.Datte$T) } 
  Tag(Tclass._module.Datte(_module.Datte$T)) == Tagclass._module.Datte
     && TagFamily(Tclass._module.Datte(_module.Datte$T)) == tytagFamily$Datte);

// Tclass._module.Datte injectivity 0
axiom (forall _module.Datte$T: Ty :: 
  { Tclass._module.Datte(_module.Datte$T) } 
  Tclass._module.Datte_0(Tclass._module.Datte(_module.Datte$T)) == _module.Datte$T);

function Tclass._module.Datte_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.Datte
axiom (forall _module.Datte$T: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.Datte(_module.Datte$T)) } 
  $IsBox(bx, Tclass._module.Datte(_module.Datte$T))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Datte(_module.Datte$T)));

// Constructor $Is
axiom (forall _module.Datte$T: Ty, a#72#0#0: int, a#72#1#0: int :: 
  { $Is(#_module.Datte.AA(a#72#0#0, a#72#1#0), Tclass._module.Datte(_module.Datte$T)) } 
  $Is(#_module.Datte.AA(a#72#0#0, a#72#1#0), Tclass._module.Datte(_module.Datte$T))
     <==> $Is(a#72#0#0, TInt) && $Is(a#72#1#0, TInt));

// Constructor $IsAlloc
axiom (forall _module.Datte$T: Ty, a#73#0#0: int, a#73#1#0: int, $h: Heap :: 
  { $IsAlloc(#_module.Datte.AA(a#73#0#0, a#73#1#0), Tclass._module.Datte(_module.Datte$T), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Datte.AA(a#73#0#0, a#73#1#0), Tclass._module.Datte(_module.Datte$T), $h)
       <==> $IsAlloc(a#73#0#0, TInt, $h) && $IsAlloc(a#73#1#0, TInt, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Datte.a(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Datte.AA_q(d)
       && (exists _module.Datte$T: Ty :: 
        { $IsAlloc(d, Tclass._module.Datte(_module.Datte$T), $h) } 
        $IsAlloc(d, Tclass._module.Datte(_module.Datte$T), $h))
     ==> $IsAlloc(_module.Datte.a(d), TInt, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Datte.x(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Datte.AA_q(d)
       && (exists _module.Datte$T: Ty :: 
        { $IsAlloc(d, Tclass._module.Datte(_module.Datte$T), $h) } 
        $IsAlloc(d, Tclass._module.Datte(_module.Datte$T), $h))
     ==> $IsAlloc(_module.Datte.x(d), TInt, $h));

// Constructor literal
axiom (forall a#74#0#0: int, a#74#1#0: int :: 
  { #_module.Datte.AA(LitInt(a#74#0#0), LitInt(a#74#1#0)) } 
  #_module.Datte.AA(LitInt(a#74#0#0), LitInt(a#74#1#0))
     == Lit(#_module.Datte.AA(a#74#0#0, a#74#1#0)));

function _module.Datte.a(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#75#0#0: int, a#75#1#0: int :: 
  { #_module.Datte.AA(a#75#0#0, a#75#1#0) } 
  _module.Datte.a(#_module.Datte.AA(a#75#0#0, a#75#1#0)) == a#75#0#0);

function _module.Datte.x(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#76#0#0: int, a#76#1#0: int :: 
  { #_module.Datte.AA(a#76#0#0, a#76#1#0) } 
  _module.Datte.x(#_module.Datte.AA(a#76#0#0, a#76#1#0)) == a#76#1#0);

// Constructor function declaration
function #_module.Datte.BB(bool, int) : DatatypeType;

const unique ##_module.Datte.BB: DtCtorId;

// Constructor identifier
axiom (forall a#77#0#0: bool, a#77#1#0: int :: 
  { #_module.Datte.BB(a#77#0#0, a#77#1#0) } 
  DatatypeCtorId(#_module.Datte.BB(a#77#0#0, a#77#1#0)) == ##_module.Datte.BB);

function _module.Datte.BB_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Datte.BB_q(d) } 
  _module.Datte.BB_q(d) <==> DatatypeCtorId(d) == ##_module.Datte.BB);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Datte.BB_q(d) } 
  _module.Datte.BB_q(d)
     ==> (exists a#78#0#0: bool, a#78#1#0: int :: 
      d == #_module.Datte.BB(a#78#0#0, a#78#1#0)));

// Constructor $Is
axiom (forall _module.Datte$T: Ty, a#79#0#0: bool, a#79#1#0: int :: 
  { $Is(#_module.Datte.BB(a#79#0#0, a#79#1#0), Tclass._module.Datte(_module.Datte$T)) } 
  $Is(#_module.Datte.BB(a#79#0#0, a#79#1#0), Tclass._module.Datte(_module.Datte$T))
     <==> $Is(a#79#0#0, TBool) && $Is(a#79#1#0, TInt));

// Constructor $IsAlloc
axiom (forall _module.Datte$T: Ty, a#80#0#0: bool, a#80#1#0: int, $h: Heap :: 
  { $IsAlloc(#_module.Datte.BB(a#80#0#0, a#80#1#0), Tclass._module.Datte(_module.Datte$T), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Datte.BB(a#80#0#0, a#80#1#0), Tclass._module.Datte(_module.Datte$T), $h)
       <==> $IsAlloc(a#80#0#0, TBool, $h) && $IsAlloc(a#80#1#0, TInt, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Datte.b(d), TBool, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Datte.BB_q(d)
       && (exists _module.Datte$T: Ty :: 
        { $IsAlloc(d, Tclass._module.Datte(_module.Datte$T), $h) } 
        $IsAlloc(d, Tclass._module.Datte(_module.Datte$T), $h))
     ==> $IsAlloc(_module.Datte.b(d), TBool, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Datte.x(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Datte.BB_q(d)
       && (exists _module.Datte$T: Ty :: 
        { $IsAlloc(d, Tclass._module.Datte(_module.Datte$T), $h) } 
        $IsAlloc(d, Tclass._module.Datte(_module.Datte$T), $h))
     ==> $IsAlloc(_module.Datte.x(d), TInt, $h));

// Constructor literal
axiom (forall a#81#0#0: bool, a#81#1#0: int :: 
  { #_module.Datte.BB(Lit(a#81#0#0), LitInt(a#81#1#0)) } 
  #_module.Datte.BB(Lit(a#81#0#0), LitInt(a#81#1#0))
     == Lit(#_module.Datte.BB(a#81#0#0, a#81#1#0)));

function _module.Datte.b(DatatypeType) : bool;

// Constructor injectivity
axiom (forall a#82#0#0: bool, a#82#1#0: int :: 
  { #_module.Datte.BB(a#82#0#0, a#82#1#0) } 
  _module.Datte.b(#_module.Datte.BB(a#82#0#0, a#82#1#0)) == a#82#0#0);

// Constructor injectivity
axiom (forall a#83#0#0: bool, a#83#1#0: int :: 
  { #_module.Datte.BB(a#83#0#0, a#83#1#0) } 
  _module.Datte.x(#_module.Datte.BB(a#83#0#0, a#83#1#0)) == a#83#1#0);

// Constructor function declaration
function #_module.Datte.CC(real) : DatatypeType;

const unique ##_module.Datte.CC: DtCtorId;

// Constructor identifier
axiom (forall a#84#0#0: real :: 
  { #_module.Datte.CC(a#84#0#0) } 
  DatatypeCtorId(#_module.Datte.CC(a#84#0#0)) == ##_module.Datte.CC);

function _module.Datte.CC_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Datte.CC_q(d) } 
  _module.Datte.CC_q(d) <==> DatatypeCtorId(d) == ##_module.Datte.CC);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Datte.CC_q(d) } 
  _module.Datte.CC_q(d)
     ==> (exists a#85#0#0: real :: d == #_module.Datte.CC(a#85#0#0)));

// Constructor $Is
axiom (forall _module.Datte$T: Ty, a#86#0#0: real :: 
  { $Is(#_module.Datte.CC(a#86#0#0), Tclass._module.Datte(_module.Datte$T)) } 
  $Is(#_module.Datte.CC(a#86#0#0), Tclass._module.Datte(_module.Datte$T))
     <==> $Is(a#86#0#0, TReal));

// Constructor $IsAlloc
axiom (forall _module.Datte$T: Ty, a#87#0#0: real, $h: Heap :: 
  { $IsAlloc(#_module.Datte.CC(a#87#0#0), Tclass._module.Datte(_module.Datte$T), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Datte.CC(a#87#0#0), Tclass._module.Datte(_module.Datte$T), $h)
       <==> $IsAlloc(a#87#0#0, TReal, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Datte.c(d), TReal, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Datte.CC_q(d)
       && (exists _module.Datte$T: Ty :: 
        { $IsAlloc(d, Tclass._module.Datte(_module.Datte$T), $h) } 
        $IsAlloc(d, Tclass._module.Datte(_module.Datte$T), $h))
     ==> $IsAlloc(_module.Datte.c(d), TReal, $h));

// Constructor literal
axiom (forall a#88#0#0: real :: 
  { #_module.Datte.CC(LitReal(a#88#0#0)) } 
  #_module.Datte.CC(LitReal(a#88#0#0)) == Lit(#_module.Datte.CC(a#88#0#0)));

function _module.Datte.c(DatatypeType) : real;

// Constructor injectivity
axiom (forall a#89#0#0: real :: 
  { #_module.Datte.CC(a#89#0#0) } 
  _module.Datte.c(#_module.Datte.CC(a#89#0#0)) == a#89#0#0);

// Constructor function declaration
function #_module.Datte.DD(int, Set Box, bv27, Box) : DatatypeType;

const unique ##_module.Datte.DD: DtCtorId;

// Constructor identifier
axiom (forall a#90#0#0: int, a#90#1#0: Set Box, a#90#2#0: bv27, a#90#3#0: Box :: 
  { #_module.Datte.DD(a#90#0#0, a#90#1#0, a#90#2#0, a#90#3#0) } 
  DatatypeCtorId(#_module.Datte.DD(a#90#0#0, a#90#1#0, a#90#2#0, a#90#3#0))
     == ##_module.Datte.DD);

function _module.Datte.DD_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Datte.DD_q(d) } 
  _module.Datte.DD_q(d) <==> DatatypeCtorId(d) == ##_module.Datte.DD);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Datte.DD_q(d) } 
  _module.Datte.DD_q(d)
     ==> (exists a#91#0#0: int, a#91#1#0: Set Box, a#91#2#0: bv27, a#91#3#0: Box :: 
      d == #_module.Datte.DD(a#91#0#0, a#91#1#0, a#91#2#0, a#91#3#0)));

// Constructor $Is
axiom (forall _module.Datte$T: Ty, 
    a#92#0#0: int, 
    a#92#1#0: Set Box, 
    a#92#2#0: bv27, 
    a#92#3#0: Box :: 
  { $Is(#_module.Datte.DD(a#92#0#0, a#92#1#0, a#92#2#0, a#92#3#0), 
      Tclass._module.Datte(_module.Datte$T)) } 
  $Is(#_module.Datte.DD(a#92#0#0, a#92#1#0, a#92#2#0, a#92#3#0), 
      Tclass._module.Datte(_module.Datte$T))
     <==> $Is(a#92#0#0, TInt)
       && $Is(a#92#1#0, TSet(TInt))
       && $Is(a#92#2#0, TBitvector(27))
       && $IsBox(a#92#3#0, _module.Datte$T));

// Constructor $IsAlloc
axiom (forall _module.Datte$T: Ty, 
    a#93#0#0: int, 
    a#93#1#0: Set Box, 
    a#93#2#0: bv27, 
    a#93#3#0: Box, 
    $h: Heap :: 
  { $IsAlloc(#_module.Datte.DD(a#93#0#0, a#93#1#0, a#93#2#0, a#93#3#0), 
      Tclass._module.Datte(_module.Datte$T), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Datte.DD(a#93#0#0, a#93#1#0, a#93#2#0, a#93#3#0), 
        Tclass._module.Datte(_module.Datte$T), 
        $h)
       <==> $IsAlloc(a#93#0#0, TInt, $h)
         && $IsAlloc(a#93#1#0, TSet(TInt), $h)
         && $IsAlloc(a#93#2#0, TBitvector(27), $h)
         && $IsAllocBox(a#93#3#0, _module.Datte$T, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Datte.x(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Datte.DD_q(d)
       && (exists _module.Datte$T: Ty :: 
        { $IsAlloc(d, Tclass._module.Datte(_module.Datte$T), $h) } 
        $IsAlloc(d, Tclass._module.Datte(_module.Datte$T), $h))
     ==> $IsAlloc(_module.Datte.x(d), TInt, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Datte.o(d), TSet(TInt), $h) } 
  $IsGoodHeap($h)
       && 
      _module.Datte.DD_q(d)
       && (exists _module.Datte$T: Ty :: 
        { $IsAlloc(d, Tclass._module.Datte(_module.Datte$T), $h) } 
        $IsAlloc(d, Tclass._module.Datte(_module.Datte$T), $h))
     ==> $IsAlloc(_module.Datte.o(d), TSet(TInt), $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Datte.p(d), TBitvector(27), $h) } 
  $IsGoodHeap($h)
       && 
      _module.Datte.DD_q(d)
       && (exists _module.Datte$T: Ty :: 
        { $IsAlloc(d, Tclass._module.Datte(_module.Datte$T), $h) } 
        $IsAlloc(d, Tclass._module.Datte(_module.Datte$T), $h))
     ==> $IsAlloc(_module.Datte.p(d), TBitvector(27), $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _module.Datte$T: Ty, $h: Heap :: 
  { $IsAllocBox(_module.Datte.q(d), _module.Datte$T, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Datte.DD_q(d)
       && $IsAlloc(d, Tclass._module.Datte(_module.Datte$T), $h)
     ==> $IsAllocBox(_module.Datte.q(d), _module.Datte$T, $h));

// Constructor literal
axiom (forall a#94#0#0: int, a#94#1#0: Set Box, a#94#2#0: bv27, a#94#3#0: Box :: 
  { #_module.Datte.DD(LitInt(a#94#0#0), Lit(a#94#1#0), Lit(a#94#2#0), Lit(a#94#3#0)) } 
  #_module.Datte.DD(LitInt(a#94#0#0), Lit(a#94#1#0), Lit(a#94#2#0), Lit(a#94#3#0))
     == Lit(#_module.Datte.DD(a#94#0#0, a#94#1#0, a#94#2#0, a#94#3#0)));

// Constructor injectivity
axiom (forall a#95#0#0: int, a#95#1#0: Set Box, a#95#2#0: bv27, a#95#3#0: Box :: 
  { #_module.Datte.DD(a#95#0#0, a#95#1#0, a#95#2#0, a#95#3#0) } 
  _module.Datte.x(#_module.Datte.DD(a#95#0#0, a#95#1#0, a#95#2#0, a#95#3#0))
     == a#95#0#0);

function _module.Datte.o(DatatypeType) : Set Box;

// Constructor injectivity
axiom (forall a#96#0#0: int, a#96#1#0: Set Box, a#96#2#0: bv27, a#96#3#0: Box :: 
  { #_module.Datte.DD(a#96#0#0, a#96#1#0, a#96#2#0, a#96#3#0) } 
  _module.Datte.o(#_module.Datte.DD(a#96#0#0, a#96#1#0, a#96#2#0, a#96#3#0))
     == a#96#1#0);

// Inductive set element rank
axiom (forall a#97#0#0: int, a#97#1#0: Set Box, a#97#2#0: bv27, a#97#3#0: Box, d: DatatypeType :: 
  { a#97#1#0[$Box(d)], #_module.Datte.DD(a#97#0#0, a#97#1#0, a#97#2#0, a#97#3#0) } 
  a#97#1#0[$Box(d)]
     ==> DtRank(d) < DtRank(#_module.Datte.DD(a#97#0#0, a#97#1#0, a#97#2#0, a#97#3#0)));

function _module.Datte.p(DatatypeType) : bv27;

// Constructor injectivity
axiom (forall a#98#0#0: int, a#98#1#0: Set Box, a#98#2#0: bv27, a#98#3#0: Box :: 
  { #_module.Datte.DD(a#98#0#0, a#98#1#0, a#98#2#0, a#98#3#0) } 
  _module.Datte.p(#_module.Datte.DD(a#98#0#0, a#98#1#0, a#98#2#0, a#98#3#0))
     == a#98#2#0);

function _module.Datte.q(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#99#0#0: int, a#99#1#0: Set Box, a#99#2#0: bv27, a#99#3#0: Box :: 
  { #_module.Datte.DD(a#99#0#0, a#99#1#0, a#99#2#0, a#99#3#0) } 
  _module.Datte.q(#_module.Datte.DD(a#99#0#0, a#99#1#0, a#99#2#0, a#99#3#0))
     == a#99#3#0);

// Inductive rank
axiom (forall a#100#0#0: int, a#100#1#0: Set Box, a#100#2#0: bv27, a#100#3#0: Box :: 
  { #_module.Datte.DD(a#100#0#0, a#100#1#0, a#100#2#0, a#100#3#0) } 
  BoxRank(a#100#3#0)
     < DtRank(#_module.Datte.DD(a#100#0#0, a#100#1#0, a#100#2#0, a#100#3#0)));

// Depth-one case-split function
function $IsA#_module.Datte(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.Datte(d) } 
  $IsA#_module.Datte(d)
     ==> _module.Datte.AA_q(d)
       || _module.Datte.BB_q(d)
       || _module.Datte.CC_q(d)
       || _module.Datte.DD_q(d));

// Questionmark data type disjunctivity
axiom (forall _module.Datte$T: Ty, d: DatatypeType :: 
  { _module.Datte.DD_q(d), $Is(d, Tclass._module.Datte(_module.Datte$T)) } 
    { _module.Datte.CC_q(d), $Is(d, Tclass._module.Datte(_module.Datte$T)) } 
    { _module.Datte.BB_q(d), $Is(d, Tclass._module.Datte(_module.Datte$T)) } 
    { _module.Datte.AA_q(d), $Is(d, Tclass._module.Datte(_module.Datte$T)) } 
  $Is(d, Tclass._module.Datte(_module.Datte$T))
     ==> _module.Datte.AA_q(d)
       || _module.Datte.BB_q(d)
       || _module.Datte.CC_q(d)
       || _module.Datte.DD_q(d));

// Datatype extensional equality declaration
function _module.Datte#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.Datte.AA
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Datte#Equal(a, b), _module.Datte.AA_q(a) } 
    { _module.Datte#Equal(a, b), _module.Datte.AA_q(b) } 
  _module.Datte.AA_q(a) && _module.Datte.AA_q(b)
     ==> (_module.Datte#Equal(a, b)
       <==> _module.Datte.a(a) == _module.Datte.a(b)
         && _module.Datte.x(a) == _module.Datte.x(b)));

// Datatype extensional equality definition: #_module.Datte.BB
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Datte#Equal(a, b), _module.Datte.BB_q(a) } 
    { _module.Datte#Equal(a, b), _module.Datte.BB_q(b) } 
  _module.Datte.BB_q(a) && _module.Datte.BB_q(b)
     ==> (_module.Datte#Equal(a, b)
       <==> _module.Datte.b(a) == _module.Datte.b(b)
         && _module.Datte.x(a) == _module.Datte.x(b)));

// Datatype extensional equality definition: #_module.Datte.CC
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Datte#Equal(a, b), _module.Datte.CC_q(a) } 
    { _module.Datte#Equal(a, b), _module.Datte.CC_q(b) } 
  _module.Datte.CC_q(a) && _module.Datte.CC_q(b)
     ==> (_module.Datte#Equal(a, b) <==> _module.Datte.c(a) == _module.Datte.c(b)));

// Datatype extensional equality definition: #_module.Datte.DD
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Datte#Equal(a, b), _module.Datte.DD_q(a) } 
    { _module.Datte#Equal(a, b), _module.Datte.DD_q(b) } 
  _module.Datte.DD_q(a) && _module.Datte.DD_q(b)
     ==> (_module.Datte#Equal(a, b)
       <==> _module.Datte.x(a) == _module.Datte.x(b)
         && Set#Equal(_module.Datte.o(a), _module.Datte.o(b))
         && _module.Datte.p(a) == _module.Datte.p(b)
         && _module.Datte.q(a) == _module.Datte.q(b)));

// Datatype extensionality axiom: _module.Datte
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Datte#Equal(a, b) } 
  _module.Datte#Equal(a, b) <==> a == b);

const unique class._module.Datte: ClassName;

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

procedure CheckWellformed$$_module.__default._default_Main();
  free requires 6 == $FunctionContextHeight;
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
  free requires 6 == $FunctionContextHeight;
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
  var o#0: ref
     where $Is(o#0, Tclass._module.MyClass())
       && $IsAlloc(o#0, Tclass._module.MyClass(), $Heap);
  var $nw: ref;
  var s#0: Seq Box
     where $Is(s#0, TSeq(Tclass._module.Dt()))
       && $IsAlloc(s#0, TSeq(Tclass._module.Dt()), $Heap);
  var d#0: DatatypeType
     where $Is(d#0, Tclass._module.Dt()) && $IsAlloc(d#0, Tclass._module.Dt(), $Heap);
  var i#0: int;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var $decr$loop#00: int;
  var k##0: DatatypeType;
  var d##0: DatatypeType;

    // AddMethodImpl: Main, Impl$$_module.__default._default_Main
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(12,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(13,9)
    assume true;
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._module.MyClass?();
    assume !read($Heap, $nw, alloc);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    o#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(13,22)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(14,9)
    assume true;
    assume true;
    s#0 := Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(Lit(#_module.Dt.A(LitInt(10), LitReal(12e0))))), 
        $Box(#_module.Dt.B(o#0, LitInt(6)))), 
      $Box(Lit(#_module.Dt.C(LitReal(314e-2)))));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(14,42)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(15,3)
    assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(s#0);
    assert _module.Dt.A_q($Unbox(Seq#Index(s#0, LitInt(0))): DatatypeType)
       || _module.Dt.B_q($Unbox(Seq#Index(s#0, LitInt(0))): DatatypeType);
    if (_module.Dt.x($Unbox(Seq#Index(s#0, LitInt(0))): DatatypeType) == LitInt(10))
    {
        assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(s#0);
        assert _module.Dt.A_q($Unbox(Seq#Index(s#0, LitInt(0))): DatatypeType)
           || _module.Dt.C_q($Unbox(Seq#Index(s#0, LitInt(0))): DatatypeType);
    }

    assume true;
    assert {:subsumption 0} _module.Dt.x($Unbox(Seq#Index(s#0, LitInt(0))): DatatypeType) == LitInt(10);
    assert {:subsumption 0} _module.Dt.y($Unbox(Seq#Index(s#0, LitInt(0))): DatatypeType) == LitReal(12e0);
    assume _module.Dt.x($Unbox(Seq#Index(s#0, LitInt(0))): DatatypeType) == LitInt(10)
       && _module.Dt.y($Unbox(Seq#Index(s#0, LitInt(0))): DatatypeType) == LitReal(12e0);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(16,3)
    assert {:subsumption 0} 0 <= LitInt(1) && LitInt(1) < Seq#Length(s#0);
    assert _module.Dt.B_q($Unbox(Seq#Index(s#0, LitInt(1))): DatatypeType);
    if (_module.Dt.h($Unbox(Seq#Index(s#0, LitInt(1))): DatatypeType) == o#0)
    {
        assert {:subsumption 0} 0 <= LitInt(1) && LitInt(1) < Seq#Length(s#0);
        assert _module.Dt.A_q($Unbox(Seq#Index(s#0, LitInt(1))): DatatypeType)
           || _module.Dt.B_q($Unbox(Seq#Index(s#0, LitInt(1))): DatatypeType);
    }

    assume true;
    assert {:subsumption 0} _module.Dt.h($Unbox(Seq#Index(s#0, LitInt(1))): DatatypeType) == o#0;
    assert {:subsumption 0} _module.Dt.x($Unbox(Seq#Index(s#0, LitInt(1))): DatatypeType) == LitInt(6);
    assume _module.Dt.h($Unbox(Seq#Index(s#0, LitInt(1))): DatatypeType) == o#0
       && _module.Dt.x($Unbox(Seq#Index(s#0, LitInt(1))): DatatypeType) == LitInt(6);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(17,3)
    assert {:subsumption 0} 0 <= LitInt(2) && LitInt(2) < Seq#Length(s#0);
    assert _module.Dt.A_q($Unbox(Seq#Index(s#0, LitInt(2))): DatatypeType)
       || _module.Dt.C_q($Unbox(Seq#Index(s#0, LitInt(2))): DatatypeType);
    assume true;
    assert _module.Dt.y($Unbox(Seq#Index(s#0, LitInt(2))): DatatypeType) == LitReal(314e-2);
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(19,9)
    assume true;
    assert 0 <= LitInt(0) && LitInt(0) < Seq#Length(s#0);
    assume true;
    d#0 := $Unbox(Seq#Index(s#0, LitInt(0))): DatatypeType;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(19,15)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(20,3)
    assume true;
    assume true;
    assert _module.Dt.A_q(d#0) || _module.Dt.B_q(d#0);
    assume true;
    assume true;
    assert _module.Dt.A_q(d#0) || _module.Dt.C_q(d#0);
    assume true;
    assume true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(21,5)
    assume true;
    assert 0 <= LitInt(1) && LitInt(1) < Seq#Length(s#0);
    assume true;
    d#0 := $Unbox(Seq#Index(s#0, LitInt(1))): DatatypeType;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(21,11)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(22,3)
    assume true;
    assume true;
    assert _module.Dt.B_q(d#0);
    assume true;
    assume true;
    assert _module.Dt.A_q(d#0) || _module.Dt.B_q(d#0);
    assume true;
    assume true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(23,5)
    assume true;
    assert 0 <= LitInt(2) && LitInt(2) < Seq#Length(s#0);
    assume true;
    d#0 := $Unbox(Seq#Index(s#0, LitInt(2))): DatatypeType;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(23,11)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(24,3)
    assume true;
    assume true;
    assert _module.Dt.A_q(d#0) || _module.Dt.C_q(d#0);
    assume true;
    assume true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(26,5)
    assume true;
    assume true;
    s#0 := Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(Lit(#_module.Dt.A(LitInt(71), LitReal(1e-1))))), 
      $Box(#_module.Dt.B(o#0, LitInt(71))));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(26,29)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(27,9)
    assume true;
    assume true;
    i#0 := LitInt(0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(27,12)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(28,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := Seq#Length(s#0) - i#0;
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
      free invariant Seq#Length(s#0) - i#0 <= $decr_init$loop#00
         && (Seq#Length(s#0) - i#0 == $decr_init$loop#00 ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(28,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assume true;
            assume false;
        }

        assume true;
        if (Seq#Length(s#0) <= i#0)
        {
            break;
        }

        $decr$loop#00 := Seq#Length(s#0) - i#0;
        // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(30,5)
        assume true;
        assume true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(31,7)
        assume true;
        assert 0 <= i#0 && i#0 < Seq#Length(s#0);
        assume true;
        d#0 := $Unbox(Seq#Index(s#0, i#0)): DatatypeType;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(31,13)"} true;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(32,5)
        assert _module.Dt.A_q(d#0) || _module.Dt.B_q(d#0);
        assume true;
        assert _module.Dt.x(d#0) == LitInt(71);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(33,7)
        assume true;
        assume true;
        i#0 := i#0 + 1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(33,14)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(28,3)
        assert 0 <= $decr$loop#00 || Seq#Length(s#0) - i#0 == $decr$loop#00;
        assert Seq#Length(s#0) - i#0 < $decr$loop#00;
    }

    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(36,11)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    k##0 := Lit(#_module.Klef.C3(LitInt(44), LitInt(55), LitInt(66), LitInt(77)));
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.BaseKlef(k##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(36,30)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(37,8)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    d##0 := Lit(#_module.Datte.AA(LitInt(10), LitInt(2)));
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.Matte(d##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(37,18)"} true;
}



procedure CheckWellformed$$_module.__default.BaseKlef(k#0: DatatypeType
       where $Is(k#0, Tclass._module.Klef())
         && $IsAlloc(k#0, Tclass._module.Klef(), $Heap)
         && $IsA#_module.Klef(k#0));
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.BaseKlef(k#0: DatatypeType
       where $Is(k#0, Tclass._module.Klef())
         && $IsAlloc(k#0, Tclass._module.Klef(), $Heap)
         && $IsA#_module.Klef(k#0));
  // user-defined preconditions
  requires !_module.Klef.C0_q(k#0);
  requires !_module.Klef.C2_q(k#0);
  requires !_module.Klef.C1_q(k#0);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.BaseKlef(k#0: DatatypeType
       where $Is(k#0, Tclass._module.Klef())
         && $IsAlloc(k#0, Tclass._module.Klef(), $Heap)
         && $IsA#_module.Klef(k#0))
   returns ($_reverifyPost: bool);
  free requires 3 == $FunctionContextHeight;
  // user-defined preconditions
  requires !_module.Klef.C0_q(k#0);
  requires !_module.Klef.C2_q(k#0);
  requires !_module.Klef.C1_q(k#0);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.BaseKlef(k#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var k'#0: DatatypeType
     where $Is(k'#0, Tclass._module.Klef()) && $IsAlloc(k'#0, Tclass._module.Klef(), $Heap);
  var dt_update_tmp#0#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var dt_update#c3#0#Z#0: int;
  var let#1#0#0: int;
  var dt_update#0#0#Z#0: int;
  var let#2#0#0: int;

    // AddMethodImpl: BaseKlef, Impl$$_module.__default.BaseKlef
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(48,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(49,10)
    assume true;
    assert _module.Klef.C3_q(k#0);
    havoc dt_update_tmp#0#Z#0;
    assume $Is(dt_update_tmp#0#Z#0, Tclass._module.Klef());
    assume let#0#0#0 == k#0;
    assume true;
    // CheckWellformedWithResult: any expression
    assume $Is(let#0#0#0, Tclass._module.Klef());
    assume dt_update_tmp#0#Z#0 == let#0#0#0;
    havoc dt_update#c3#0#Z#0;
    assume true;
    assume let#1#0#0 == LitInt(200);
    assume true;
    // CheckWellformedWithResult: any expression
    assume $Is(let#1#0#0, TInt);
    assume dt_update#c3#0#Z#0 == let#1#0#0;
    havoc dt_update#0#0#Z#0;
    assume true;
    assume let#2#0#0 == LitInt(100);
    assume true;
    // CheckWellformedWithResult: any expression
    assume $Is(let#2#0#0, TInt);
    assume dt_update#0#0#Z#0 == let#2#0#0;
    assert _module.Klef.C1_q(dt_update_tmp#0#Z#0)
       || _module.Klef.C2_q(dt_update_tmp#0#Z#0)
       || _module.Klef.C3_q(dt_update_tmp#0#Z#0);
    assert _module.Klef.C0_q(dt_update_tmp#0#Z#0)
       || _module.Klef.C1_q(dt_update_tmp#0#Z#0)
       || _module.Klef.C3_q(dt_update_tmp#0#Z#0);
    assume true;
    k'#0 := (var dt_update_tmp#0#0 := k#0; 
      (var dt_update#c3#0#0 := LitInt(200); 
        (var dt_update#0#0#0 := LitInt(100); 
          #_module.Klef.C3(_module.Klef._3(dt_update_tmp#0#0), 
            dt_update#0#0#0, 
            _module.Klef._1(dt_update_tmp#0#0), 
            dt_update#c3#0#0))));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(49,35)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(50,3)
    assert _module.Klef.C1_q(k#0) || _module.Klef.C2_q(k#0) || _module.Klef.C3_q(k#0);
    assert _module.Klef.C0_q(k#0) || _module.Klef.C1_q(k#0) || _module.Klef.C3_q(k#0);
    assume $IsA#_module.Klef(k'#0);
    assert _module.Klef#Equal(k'#0, 
      #_module.Klef.C3(_module.Klef._3(k#0), LitInt(100), _module.Klef._1(k#0), LitInt(200)));
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(51,3)
    assume true;
    assume true;
}



procedure CheckWellformed$$_module.__default.Matte(d#0: DatatypeType
       where $Is(d#0, Tclass._module.Datte(TReal))
         && $IsAlloc(d#0, Tclass._module.Datte(TReal), $Heap)
         && $IsA#_module.Datte(d#0));
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Matte(d#0: DatatypeType
       where $Is(d#0, Tclass._module.Datte(TReal))
         && $IsAlloc(d#0, Tclass._module.Datte(TReal), $Heap)
         && $IsA#_module.Datte(d#0));
  // user-defined preconditions
  requires !_module.Datte.CC_q(d#0);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.Matte(d#0: DatatypeType
       where $Is(d#0, Tclass._module.Datte(TReal))
         && $IsAlloc(d#0, Tclass._module.Datte(TReal), $Heap)
         && $IsA#_module.Datte(d#0))
   returns ($_reverifyPost: bool);
  free requires 5 == $FunctionContextHeight;
  // user-defined preconditions
  requires !_module.Datte.CC_q(d#0);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.Matte(d#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var d#1: DatatypeType
     where $Is(d#1, Tclass._module.Datte(TReal))
       && $IsAlloc(d#1, Tclass._module.Datte(TReal), $Heap);
  var s#0: DatatypeType
     where $Is(s#0, Tclass._module.Datte(TReal))
       && $IsAlloc(s#0, Tclass._module.Datte(TReal), $Heap);
  var dt_update_tmp#0#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var dt_update#x#0#Z#0: int;
  var let#1#0#0: int;
  var dt_update_tmp#1#Z#0: DatatypeType;
  var let#2#0#0: DatatypeType;
  var dt_update#x#1#Z#0: int;
  var let#3#0#0: int;
  var dt_update_tmp#2#Z#0: DatatypeType;
  var let#4#0#0: DatatypeType;
  var dt_update#c#0#Z#0: real;
  var let#5#0#0: real;
  var dt_update_tmp#3#Z#0: DatatypeType;
  var let#6#0#0: DatatypeType;
  var dt_update#x#2#Z#0: int;
  var let#7#0#0: int;
  var dt_update_tmp#4#Z#0: DatatypeType;
  var let#8#0#0: DatatypeType;
  var dt_update#p#0#Z#0: bv27;
  var let#9#0#0: bv27;
  var dt_update#q#0#Z#0: real;
  var let#10#0#0: real;

    // AddMethodImpl: Matte, Impl$$_module.__default.Matte
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(58,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(59,9)
    assume true;
    assume true;
    d#1 := d#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(59,12)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(61,9)
    assume true;
    assert _module.Datte.DD_q(d#1) || _module.Datte.BB_q(d#1) || _module.Datte.AA_q(d#1);
    havoc dt_update_tmp#0#Z#0;
    assume $Is(dt_update_tmp#0#Z#0, Tclass._module.Datte(TReal));
    assume let#0#0#0 == d#1;
    assume true;
    // CheckWellformedWithResult: any expression
    assume $Is(let#0#0#0, Tclass._module.Datte(TReal));
    assume dt_update_tmp#0#Z#0 == let#0#0#0;
    havoc dt_update#x#0#Z#0;
    assume true;
    assume let#1#0#0 == LitInt(5);
    assume true;
    // CheckWellformedWithResult: any expression
    assume $Is(let#1#0#0, TInt);
    assume dt_update#x#0#Z#0 == let#1#0#0;
    if (_module.Datte.AA_q(dt_update_tmp#0#Z#0))
    {
        assert _module.Datte.AA_q(dt_update_tmp#0#Z#0);
    }
    else
    {
        if (_module.Datte.BB_q(dt_update_tmp#0#Z#0))
        {
            assert _module.Datte.BB_q(dt_update_tmp#0#Z#0);
        }
        else
        {
            assert _module.Datte.DD_q(dt_update_tmp#0#Z#0);
            assert _module.Datte.DD_q(dt_update_tmp#0#Z#0);
            assert _module.Datte.DD_q(dt_update_tmp#0#Z#0);
        }
    }

    assume true;
    s#0 := (var dt_update_tmp#0#0 := d#1; 
      (var dt_update#x#0#0 := LitInt(5); 
        (if _module.Datte.AA_q(dt_update_tmp#0#0)
           then #_module.Datte.AA(_module.Datte.a(dt_update_tmp#0#0), dt_update#x#0#0)
           else (if _module.Datte.BB_q(dt_update_tmp#0#0)
             then #_module.Datte.BB(_module.Datte.b(dt_update_tmp#0#0), dt_update#x#0#0)
             else #_module.Datte.DD(dt_update#x#0#0, 
              _module.Datte.o(dt_update_tmp#0#0), 
              _module.Datte.p(dt_update_tmp#0#0), 
              _module.Datte.q(dt_update_tmp#0#0))))));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(61,21)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(62,3)
    assume true;
    assume true;
    assume true;
    assume true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(64,5)
    assume true;
    assume true;
    d#1 := Lit(#_module.Datte.BB(Lit(false), LitInt(12)));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(64,20)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(65,5)
    assume true;
    assert _module.Datte.DD_q(d#1) || _module.Datte.BB_q(d#1) || _module.Datte.AA_q(d#1);
    havoc dt_update_tmp#1#Z#0;
    assume $Is(dt_update_tmp#1#Z#0, Tclass._module.Datte(TReal));
    assume let#2#0#0 == d#1;
    assume true;
    // CheckWellformedWithResult: any expression
    assume $Is(let#2#0#0, Tclass._module.Datte(TReal));
    assume dt_update_tmp#1#Z#0 == let#2#0#0;
    havoc dt_update#x#1#Z#0;
    assume true;
    assume let#3#0#0 == LitInt(6);
    assume true;
    // CheckWellformedWithResult: any expression
    assume $Is(let#3#0#0, TInt);
    assume dt_update#x#1#Z#0 == let#3#0#0;
    if (_module.Datte.AA_q(dt_update_tmp#1#Z#0))
    {
        assert _module.Datte.AA_q(dt_update_tmp#1#Z#0);
    }
    else
    {
        if (_module.Datte.BB_q(dt_update_tmp#1#Z#0))
        {
            assert _module.Datte.BB_q(dt_update_tmp#1#Z#0);
        }
        else
        {
            assert _module.Datte.DD_q(dt_update_tmp#1#Z#0);
            assert _module.Datte.DD_q(dt_update_tmp#1#Z#0);
            assert _module.Datte.DD_q(dt_update_tmp#1#Z#0);
        }
    }

    assume true;
    s#0 := (var dt_update_tmp#1#0 := d#1; 
      (var dt_update#x#1#0 := LitInt(6); 
        (if _module.Datte.AA_q(dt_update_tmp#1#0)
           then #_module.Datte.AA(_module.Datte.a(dt_update_tmp#1#0), dt_update#x#1#0)
           else (if _module.Datte.BB_q(dt_update_tmp#1#0)
             then #_module.Datte.BB(_module.Datte.b(dt_update_tmp#1#0), dt_update#x#1#0)
             else #_module.Datte.DD(dt_update#x#1#0, 
              _module.Datte.o(dt_update_tmp#1#0), 
              _module.Datte.p(dt_update_tmp#1#0), 
              _module.Datte.q(dt_update_tmp#1#0))))));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(65,17)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(66,3)
    assume true;
    assume true;
    assume true;
    assume true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(68,5)
    assume true;
    assume true;
    d#1 := Lit(#_module.Datte.CC(LitReal(32e-1)));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(68,14)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(69,5)
    assume true;
    assert _module.Datte.CC_q(d#1);
    havoc dt_update_tmp#2#Z#0;
    assume $Is(dt_update_tmp#2#Z#0, Tclass._module.Datte(TReal));
    assume let#4#0#0 == d#1;
    assume true;
    // CheckWellformedWithResult: any expression
    assume $Is(let#4#0#0, Tclass._module.Datte(TReal));
    assume dt_update_tmp#2#Z#0 == let#4#0#0;
    havoc dt_update#c#0#Z#0;
    assume true;
    assume let#5#0#0 == LitReal(34e-1);
    assume true;
    // CheckWellformedWithResult: any expression
    assume $Is(let#5#0#0, TReal);
    assume dt_update#c#0#Z#0 == let#5#0#0;
    assume true;
    s#0 := (var dt_update_tmp#2#0 := d#1; 
      (var dt_update#c#0#0 := LitReal(34e-1); Lit(#_module.Datte.CC(dt_update#c#0#0))));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(69,19)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(70,3)
    assume true;
    assume true;
    assume true;
    assume true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(72,5)
    assume true;
    assume true;
    d#1 := Lit(#_module.Datte.DD(LitInt(100), 
        Lit(Set#UnionOne(Set#Empty(): Set Box, $Box(LitInt(7)))), 
        Lit(5bv27), 
        $Box(LitReal(9e0))));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(72,27)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(73,5)
    assume true;
    assert _module.Datte.DD_q(d#1) || _module.Datte.BB_q(d#1) || _module.Datte.AA_q(d#1);
    havoc dt_update_tmp#3#Z#0;
    assume $Is(dt_update_tmp#3#Z#0, Tclass._module.Datte(TReal));
    assume let#6#0#0 == d#1;
    assume true;
    // CheckWellformedWithResult: any expression
    assume $Is(let#6#0#0, Tclass._module.Datte(TReal));
    assume dt_update_tmp#3#Z#0 == let#6#0#0;
    havoc dt_update#x#2#Z#0;
    assume true;
    assume let#7#0#0 == LitInt(30);
    assume true;
    // CheckWellformedWithResult: any expression
    assume $Is(let#7#0#0, TInt);
    assume dt_update#x#2#Z#0 == let#7#0#0;
    if (_module.Datte.AA_q(dt_update_tmp#3#Z#0))
    {
        assert _module.Datte.AA_q(dt_update_tmp#3#Z#0);
    }
    else
    {
        if (_module.Datte.BB_q(dt_update_tmp#3#Z#0))
        {
            assert _module.Datte.BB_q(dt_update_tmp#3#Z#0);
        }
        else
        {
            assert _module.Datte.DD_q(dt_update_tmp#3#Z#0);
            assert _module.Datte.DD_q(dt_update_tmp#3#Z#0);
            assert _module.Datte.DD_q(dt_update_tmp#3#Z#0);
        }
    }

    assume true;
    s#0 := (var dt_update_tmp#3#0 := d#1; 
      (var dt_update#x#2#0 := LitInt(30); 
        (if _module.Datte.AA_q(dt_update_tmp#3#0)
           then #_module.Datte.AA(_module.Datte.a(dt_update_tmp#3#0), dt_update#x#2#0)
           else (if _module.Datte.BB_q(dt_update_tmp#3#0)
             then #_module.Datte.BB(_module.Datte.b(dt_update_tmp#3#0), dt_update#x#2#0)
             else #_module.Datte.DD(dt_update#x#2#0, 
              _module.Datte.o(dt_update_tmp#3#0), 
              _module.Datte.p(dt_update_tmp#3#0), 
              _module.Datte.q(dt_update_tmp#3#0))))));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(73,18)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(74,3)
    assume true;
    assume true;
    assume true;
    assume true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(75,5)
    assume true;
    assert _module.Datte.DD_q(s#0);
    havoc dt_update_tmp#4#Z#0;
    assume $Is(dt_update_tmp#4#Z#0, Tclass._module.Datte(TReal));
    assume let#8#0#0 == s#0;
    assume true;
    // CheckWellformedWithResult: any expression
    assume $Is(let#8#0#0, Tclass._module.Datte(TReal));
    assume dt_update_tmp#4#Z#0 == let#8#0#0;
    havoc dt_update#p#0#Z#0;
    assume true;
    assert _module.Datte.DD_q(d#1);
    assume let#9#0#0 == _module.Datte.p(d#1);
    assume true;
    // CheckWellformedWithResult: any expression
    assume $Is(let#9#0#0, TBitvector(27));
    assume dt_update#p#0#Z#0 == let#9#0#0;
    havoc dt_update#q#0#Z#0;
    assume true;
    assume let#10#0#0 == LitReal(2e0);
    assume true;
    // CheckWellformedWithResult: any expression
    assume $Is(let#10#0#0, TReal);
    assume dt_update#q#0#Z#0 == let#10#0#0;
    assert _module.Datte.AA_q(dt_update_tmp#4#Z#0)
       || _module.Datte.BB_q(dt_update_tmp#4#Z#0)
       || _module.Datte.DD_q(dt_update_tmp#4#Z#0);
    assert _module.Datte.DD_q(dt_update_tmp#4#Z#0);
    assume true;
    s#0 := (var dt_update_tmp#4#0 := s#0; 
      (var dt_update#p#0#0 := _module.Datte.p(d#1); 
        (var dt_update#q#0#0 := LitReal(2e0); 
          #_module.Datte.DD(_module.Datte.x(dt_update_tmp#4#0), 
            _module.Datte.o(dt_update_tmp#4#0), 
            dt_update#p#0#0, 
            $Box(dt_update#q#0#0)))));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(75,29)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructorsCompile.dfy(76,3)
    assume true;
    assume true;
    assume true;
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

const unique tytagFamily$Dt: TyTagFamily;

const unique tytagFamily$MyClass: TyTagFamily;

const unique tytagFamily$Klef: TyTagFamily;

const unique tytagFamily$Datte: TyTagFamily;

const unique tytagFamily$_default: TyTagFamily;