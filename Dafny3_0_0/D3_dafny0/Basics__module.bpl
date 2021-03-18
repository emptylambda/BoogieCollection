// Dafny 3.0.0.30204
// Command Line Options: -compile:0 -noVerify /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy -print:./Basics.bpl

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

const unique class._module.Global?: ClassName;

function Tclass._module.Global?() : Ty;

const unique Tagclass._module.Global?: TyTag;

// Tclass._module.Global? Tag
axiom Tag(Tclass._module.Global?()) == Tagclass._module.Global?
   && TagFamily(Tclass._module.Global?()) == tytagFamily$Global;

// Box/unbox axiom for Tclass._module.Global?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Global?()) } 
  $IsBox(bx, Tclass._module.Global?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Global?()));

// Global: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.Global?()) } 
  $Is($o, Tclass._module.Global?())
     <==> $o == null || dtype($o) == Tclass._module.Global?());

// Global: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.Global?(), $h) } 
  $IsAlloc($o, Tclass._module.Global?(), $h)
     <==> $o == null || read($h, $o, alloc));

// function declaration for _module.Global.G
function _module.Global.G(x#0: int) : int;

function _module.Global.G#canCall(x#0: int) : bool;

// consequence axiom for _module.Global.G
axiom 3 <= $FunctionContextHeight
   ==> (forall x#0: int :: 
    { _module.Global.G(x#0) } 
    _module.Global.G#canCall(x#0) || 3 != $FunctionContextHeight ==> true);

function _module.Global.G#requires(int) : bool;

// #requires axiom for _module.Global.G
axiom (forall x#0: int :: 
  { _module.Global.G#requires(x#0) } 
  _module.Global.G#requires(x#0) == true);

// definition axiom for _module.Global.G (revealed)
axiom 3 <= $FunctionContextHeight
   ==> (forall x#0: int :: 
    { _module.Global.G(x#0) } 
    _module.Global.G#canCall(x#0) || 3 != $FunctionContextHeight
       ==> _module.Global.G(x#0) == x#0 + x#0);

// definition axiom for _module.Global.G for all literals (revealed)
axiom 3 <= $FunctionContextHeight
   ==> (forall x#0: int :: 
    {:weight 3} { _module.Global.G(LitInt(x#0)) } 
    _module.Global.G#canCall(LitInt(x#0)) || 3 != $FunctionContextHeight
       ==> _module.Global.G(LitInt(x#0)) == LitInt(x#0 + x#0));

procedure CheckWellformed$$_module.Global.G(x#0: int);
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure CheckWellformed$$_module.Global.N(x#0: int) returns (r#0: int);
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Global.N(x#0: int) returns (r#0: int);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Global.G#canCall(x#0);
  ensures r#0 == _module.Global.G(x#0);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Global.N(x#0: int) returns (r#0: int, $_reverifyPost: bool);
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Global.G#canCall(x#0);
  ensures r#0 == _module.Global.G(x#0);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



function Tclass._module.Global() : Ty;

const unique Tagclass._module.Global: TyTag;

// Tclass._module.Global Tag
axiom Tag(Tclass._module.Global()) == Tagclass._module.Global
   && TagFamily(Tclass._module.Global()) == tytagFamily$Global;

// Box/unbox axiom for Tclass._module.Global
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Global()) } 
  $IsBox(bx, Tclass._module.Global())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Global()));

implementation Impl$$_module.Global.N(x#0: int) returns (r#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##x#0_0: int;
  var g#1_0: ref
     where $Is(g#1_0, Tclass._module.Global?())
       && $IsAlloc(g#1_0, Tclass._module.Global?(), $Heap);
  var ##x#1_0: int;
  var defass#g#2_0: bool;
  var g#2_0: ref
     where defass#g#2_0
       ==> $Is(g#2_0, Tclass._module.Global())
         && $IsAlloc(g#2_0, Tclass._module.Global(), $Heap);
  var ##x#2_0: int;
  var ##x#3_0: int;

    // AddMethodImpl: N, Impl$$_module.Global.N
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(8,2): initial state"} true;
    $_reverifyPost := false;
    // ----- alternative statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(9,5)
    if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(10,23)
        assume true;
        ##x#3_0 := x#0 + 0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##x#3_0, TInt, $Heap);
        assume _module.Global.G#canCall(x#0 + 0);
        assume _module.Global.G#canCall(x#0 + 0);
        r#0 := _module.Global.G(x#0 + 0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(10,31)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        havoc g#2_0 /* where defass#g#2_0
           ==> $Is(g#2_0, Tclass._module.Global())
             && $IsAlloc(g#2_0, Tclass._module.Global(), $Heap) */;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(13,11)
        assume true;
        assert defass#g#2_0;
        ##x#2_0 := x#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##x#2_0, TInt, $Heap);
        assume _module.Global.G#canCall(x#0);
        assume _module.Global.G#canCall(x#0);
        r#0 := _module.Global.G(x#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(13,19)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(15,24)
        assume true;
        assume true;
        g#1_0 := null;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(15,30)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(16,11)
        assume true;
        ##x#1_0 := x#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##x#1_0, TInt, $Heap);
        assume _module.Global.G#canCall(x#0);
        assume _module.Global.G#canCall(x#0);
        r#0 := _module.Global.G(x#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(16,19)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(18,11)
        assume true;
        ##x#0_0 := x#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##x#0_0, TInt, $Heap);
        assume _module.Global.G#canCall(x#0);
        assume _module.Global.G#canCall(x#0);
        r#0 := _module.Global.G(x#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(18,24)"} true;
    }
    else
    {
        assume true;
        assume true;
        assume true;
        assume true;
        assume !Lit(true) && !Lit(true) && !Lit(true) && !Lit(true);
        assert false;
    }
}



// _module.Global: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.Global()) } 
  $Is(c#0, Tclass._module.Global())
     <==> $Is(c#0, Tclass._module.Global?()) && c#0 != null);

// _module.Global: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.Global(), $h) } 
  $IsAlloc(c#0, Tclass._module.Global(), $h)
     <==> $IsAlloc(c#0, Tclass._module.Global?(), $h));

const unique class._module.Multi?: ClassName;

function Tclass._module.Multi?() : Ty;

const unique Tagclass._module.Multi?: TyTag;

// Tclass._module.Multi? Tag
axiom Tag(Tclass._module.Multi?()) == Tagclass._module.Multi?
   && TagFamily(Tclass._module.Multi?()) == tytagFamily$Multi;

// Box/unbox axiom for Tclass._module.Multi?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Multi?()) } 
  $IsBox(bx, Tclass._module.Multi?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Multi?()));

// Multi: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.Multi?()) } 
  $Is($o, Tclass._module.Multi?())
     <==> $o == null || dtype($o) == Tclass._module.Multi?());

// Multi: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.Multi?(), $h) } 
  $IsAlloc($o, Tclass._module.Multi?(), $h) <==> $o == null || read($h, $o, alloc));

axiom FDim(_module.Multi.x) == 0
   && FieldOfDecl(class._module.Multi?, field$x) == _module.Multi.x
   && !$IsGhostField(_module.Multi.x);

const _module.Multi.x: Field int;

// Multi.x: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Multi.x) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Multi?()
     ==> $Is(read($h, $o, _module.Multi.x), TInt));

// Multi.x: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Multi.x) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Multi?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Multi.x), TInt, $h));

axiom FDim(_module.Multi.y) == 0
   && FieldOfDecl(class._module.Multi?, field$y) == _module.Multi.y
   && !$IsGhostField(_module.Multi.y);

const _module.Multi.y: Field int;

// Multi.y: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Multi.y) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Multi?()
     ==> $Is(read($h, $o, _module.Multi.y), TInt));

// Multi.y: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Multi.y) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Multi?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Multi.y), TInt, $h));

axiom FDim(_module.Multi.next) == 0
   && FieldOfDecl(class._module.Multi?, field$next) == _module.Multi.next
   && !$IsGhostField(_module.Multi.next);

const _module.Multi.next: Field ref;

// Multi.next: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Multi.next) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Multi?()
     ==> $Is(read($h, $o, _module.Multi.next), Tclass._module.Multi?()));

// Multi.next: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Multi.next) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Multi?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Multi.next), Tclass._module.Multi?(), $h));

function Tclass._module.Multi() : Ty;

const unique Tagclass._module.Multi: TyTag;

// Tclass._module.Multi Tag
axiom Tag(Tclass._module.Multi()) == Tagclass._module.Multi
   && TagFamily(Tclass._module.Multi()) == tytagFamily$Multi;

// Box/unbox axiom for Tclass._module.Multi
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Multi()) } 
  $IsBox(bx, Tclass._module.Multi())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Multi()));

procedure CheckWellformed$$_module.Multi.Mutate(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Multi())
         && $IsAlloc(this, Tclass._module.Multi(), $Heap), 
    z#0: int)
   returns (m#0: ref
       where $Is(m#0, Tclass._module.Multi?())
         && $IsAlloc(m#0, Tclass._module.Multi?(), $Heap));
  free requires 13 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Multi.Mutate(this: ref, z#0: int) returns (m#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Mutate, CheckWellformed$$_module.Multi.Mutate
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(124,9): initial state"} true;
    assume LitInt(0) <= z#0;
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc)
         ==> $Heap[$o] == old($Heap)[$o] || $o == this);
    assume $HeapSucc(old($Heap), $Heap);
    havoc m#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(127,14): post-state"} true;
    assert $IsAlloc(this, Tclass._module.Multi(), old($Heap));
    assume read($Heap, this, _module.Multi.y) == read(old($Heap), this, _module.Multi.y);
}



procedure Call$$_module.Multi.Mutate(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Multi())
         && $IsAlloc(this, Tclass._module.Multi(), $Heap), 
    z#0: int)
   returns (m#0: ref
       where $Is(m#0, Tclass._module.Multi?())
         && $IsAlloc(m#0, Tclass._module.Multi?(), $Heap));
  // user-defined preconditions
  requires LitInt(0) <= z#0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures read($Heap, this, _module.Multi.y) == read(old($Heap), this, _module.Multi.y);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Multi.Mutate(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Multi())
         && $IsAlloc(this, Tclass._module.Multi(), $Heap), 
    z#0: int)
   returns (m#0: ref
       where $Is(m#0, Tclass._module.Multi?())
         && $IsAlloc(m#0, Tclass._module.Multi?(), $Heap), 
    $_reverifyPost: bool);
  free requires 13 == $FunctionContextHeight;
  // user-defined preconditions
  requires LitInt(0) <= z#0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures read($Heap, this, _module.Multi.y) == read(old($Heap), this, _module.Multi.y);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Multi.Mutate(this: ref, z#0: int) returns (m#0: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: int;

    // AddMethodImpl: Mutate, Impl$$_module.Multi.Mutate
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(128,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(129,7)
    assume true;
    assert $_Frame[this, _module.Multi.x];
    assume true;
    $rhs#0 := read($Heap, this, _module.Multi.x) + z#0;
    $Heap := update($Heap, this, _module.Multi.x, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(129,14)"} true;
}



procedure CheckWellformed$$_module.Multi.IncX(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Multi())
         && $IsAlloc(this, Tclass._module.Multi(), $Heap))
   returns (oldX#0: int);
  free requires 15 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Multi.IncX(this: ref) returns (oldX#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: IncX, CheckWellformed$$_module.Multi.IncX
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(131,9): initial state"} true;
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc)
         ==> $Heap[$o] == old($Heap)[$o] || $o == this);
    assume $HeapSucc(old($Heap), $Heap);
    havoc oldX#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(133,28): post-state"} true;
    assert $IsAlloc(this, Tclass._module.Multi(), old($Heap));
    assume read($Heap, this, _module.Multi.x)
       == read(old($Heap), this, _module.Multi.x) + 1;
    assert $IsAlloc(this, Tclass._module.Multi(), old($Heap));
    assume oldX#0 == read(old($Heap), this, _module.Multi.x);
}



procedure Call$$_module.Multi.IncX(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Multi())
         && $IsAlloc(this, Tclass._module.Multi(), $Heap))
   returns (oldX#0: int);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures read($Heap, this, _module.Multi.x)
     == read(old($Heap), this, _module.Multi.x) + 1;
  ensures oldX#0 == read(old($Heap), this, _module.Multi.x);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Multi.IncX(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Multi())
         && $IsAlloc(this, Tclass._module.Multi(), $Heap))
   returns (oldX#0: int, $_reverifyPost: bool);
  free requires 15 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures read($Heap, this, _module.Multi.x)
     == read(old($Heap), this, _module.Multi.x) + 1;
  ensures oldX#0 == read(old($Heap), this, _module.Multi.x);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Multi.IncX(this: ref) returns (oldX#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $obj0: ref;
  var $rhs#0: int;
  var $rhs#1: int;

    // AddMethodImpl: IncX, Impl$$_module.Multi.IncX
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(134,2): initial state"} true;
    $_reverifyPost := false;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(135,13)
    assume true;
    $obj0 := this;
    assert $_Frame[$obj0, _module.Multi.x];
    assume true;
    assume true;
    $rhs#0 := read($Heap, this, _module.Multi.x) + 1;
    assume true;
    $rhs#1 := read($Heap, this, _module.Multi.x);
    $Heap := update($Heap, $obj0, _module.Multi.x, $rhs#0);
    assume $IsGoodHeap($Heap);
    oldX#0 := $rhs#1;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(135,23)"} true;
}



// _module.Multi: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.Multi()) } 
  $Is(c#0, Tclass._module.Multi())
     <==> $Is(c#0, Tclass._module.Multi?()) && c#0 != null);

// _module.Multi: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.Multi(), $h) } 
  $IsAlloc(c#0, Tclass._module.Multi(), $h)
     <==> $IsAlloc(c#0, Tclass._module.Multi?(), $h));

const unique class._module.MyBoxyClass?: ClassName;

function Tclass._module.MyBoxyClass?(Ty) : Ty;

const unique Tagclass._module.MyBoxyClass?: TyTag;

// Tclass._module.MyBoxyClass? Tag
axiom (forall _module.MyBoxyClass$T: Ty :: 
  { Tclass._module.MyBoxyClass?(_module.MyBoxyClass$T) } 
  Tag(Tclass._module.MyBoxyClass?(_module.MyBoxyClass$T))
       == Tagclass._module.MyBoxyClass?
     && TagFamily(Tclass._module.MyBoxyClass?(_module.MyBoxyClass$T))
       == tytagFamily$MyBoxyClass);

// Tclass._module.MyBoxyClass? injectivity 0
axiom (forall _module.MyBoxyClass$T: Ty :: 
  { Tclass._module.MyBoxyClass?(_module.MyBoxyClass$T) } 
  Tclass._module.MyBoxyClass?_0(Tclass._module.MyBoxyClass?(_module.MyBoxyClass$T))
     == _module.MyBoxyClass$T);

function Tclass._module.MyBoxyClass?_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.MyBoxyClass?
axiom (forall _module.MyBoxyClass$T: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.MyBoxyClass?(_module.MyBoxyClass$T)) } 
  $IsBox(bx, Tclass._module.MyBoxyClass?(_module.MyBoxyClass$T))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.MyBoxyClass?(_module.MyBoxyClass$T)));

// MyBoxyClass: Class $Is
axiom (forall _module.MyBoxyClass$T: Ty, $o: ref :: 
  { $Is($o, Tclass._module.MyBoxyClass?(_module.MyBoxyClass$T)) } 
  $Is($o, Tclass._module.MyBoxyClass?(_module.MyBoxyClass$T))
     <==> $o == null || dtype($o) == Tclass._module.MyBoxyClass?(_module.MyBoxyClass$T));

// MyBoxyClass: Class $IsAlloc
axiom (forall _module.MyBoxyClass$T: Ty, $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.MyBoxyClass?(_module.MyBoxyClass$T), $h) } 
  $IsAlloc($o, Tclass._module.MyBoxyClass?(_module.MyBoxyClass$T), $h)
     <==> $o == null || read($h, $o, alloc));

axiom FDim(_module.MyBoxyClass.f) == 0
   && FieldOfDecl(class._module.MyBoxyClass?, field$f) == _module.MyBoxyClass.f
   && !$IsGhostField(_module.MyBoxyClass.f);

const _module.MyBoxyClass.f: Field Box;

// MyBoxyClass.f: Type axiom
axiom (forall _module.MyBoxyClass$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.MyBoxyClass.f), Tclass._module.MyBoxyClass?(_module.MyBoxyClass$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.MyBoxyClass?(_module.MyBoxyClass$T)
     ==> $IsBox(read($h, $o, _module.MyBoxyClass.f), _module.MyBoxyClass$T));

// MyBoxyClass.f: Allocation axiom
axiom (forall _module.MyBoxyClass$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.MyBoxyClass.f), Tclass._module.MyBoxyClass?(_module.MyBoxyClass$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.MyBoxyClass?(_module.MyBoxyClass$T)
       && read($h, $o, alloc)
     ==> $IsAllocBox(read($h, $o, _module.MyBoxyClass.f), _module.MyBoxyClass$T, $h));

function Tclass._module.MyBoxyClass(Ty) : Ty;

const unique Tagclass._module.MyBoxyClass: TyTag;

// Tclass._module.MyBoxyClass Tag
axiom (forall _module.MyBoxyClass$T: Ty :: 
  { Tclass._module.MyBoxyClass(_module.MyBoxyClass$T) } 
  Tag(Tclass._module.MyBoxyClass(_module.MyBoxyClass$T))
       == Tagclass._module.MyBoxyClass
     && TagFamily(Tclass._module.MyBoxyClass(_module.MyBoxyClass$T))
       == tytagFamily$MyBoxyClass);

// Tclass._module.MyBoxyClass injectivity 0
axiom (forall _module.MyBoxyClass$T: Ty :: 
  { Tclass._module.MyBoxyClass(_module.MyBoxyClass$T) } 
  Tclass._module.MyBoxyClass_0(Tclass._module.MyBoxyClass(_module.MyBoxyClass$T))
     == _module.MyBoxyClass$T);

function Tclass._module.MyBoxyClass_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.MyBoxyClass
axiom (forall _module.MyBoxyClass$T: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.MyBoxyClass(_module.MyBoxyClass$T)) } 
  $IsBox(bx, Tclass._module.MyBoxyClass(_module.MyBoxyClass$T))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.MyBoxyClass(_module.MyBoxyClass$T)));

procedure CheckWellformed$$_module.MyBoxyClass._MyBoxyClass(_module.MyBoxyClass$T: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.MyBoxyClass(_module.MyBoxyClass$T))
         && $IsAlloc(this, Tclass._module.MyBoxyClass(_module.MyBoxyClass$T), $Heap), 
    t#0: Box
       where $IsBox(t#0, _module.MyBoxyClass$T)
         && $IsAllocBox(t#0, _module.MyBoxyClass$T, $Heap));
  free requires 31 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.MyBoxyClass._MyBoxyClass(_module.MyBoxyClass$T: Ty, 
    t#0: Box
       where $IsBox(t#0, _module.MyBoxyClass$T)
         && $IsAllocBox(t#0, _module.MyBoxyClass$T, $Heap))
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass._module.MyBoxyClass(_module.MyBoxyClass$T))
         && $IsAlloc(this, Tclass._module.MyBoxyClass(_module.MyBoxyClass$T), $Heap));
  modifies $Heap, $Tick;
  // constructor allocates the object
  ensures !read(old($Heap), this, alloc);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.MyBoxyClass._MyBoxyClass(_module.MyBoxyClass$T: Ty, 
    t#0: Box
       where $IsBox(t#0, _module.MyBoxyClass$T)
         && $IsAllocBox(t#0, _module.MyBoxyClass$T, $Heap))
   returns (this: ref
       where this != null && $Is(this, Tclass._module.MyBoxyClass(_module.MyBoxyClass$T)), 
    $_reverifyPost: bool);
  free requires 31 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.MyBoxyClass._MyBoxyClass(_module.MyBoxyClass$T: Ty, t#0: Box) returns (this: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var this.f: Box;
  var defass#this.f: bool;

    // AddMethodImpl: MyBoxyClass, Impl$$_module.MyBoxyClass._MyBoxyClass
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(172,32): initial state"} true;
    $_reverifyPost := false;
    // ----- divided block before new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(172,33)
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(173,7)
    assume true;
    assume true;
    this.f := t#0;
    defass#this.f := true;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(173,10)"} true;
    // ----- new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(172,33)
    assert defass#this.f;
    assume !read($Heap, this, alloc);
    assume read($Heap, this, _module.MyBoxyClass.f) == this.f;
    $Heap := update($Heap, this, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    // ----- divided block after new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(172,33)
}



// _module.MyBoxyClass: subset type $Is
axiom (forall _module.MyBoxyClass$T: Ty, c#0: ref :: 
  { $Is(c#0, Tclass._module.MyBoxyClass(_module.MyBoxyClass$T)) } 
  $Is(c#0, Tclass._module.MyBoxyClass(_module.MyBoxyClass$T))
     <==> $Is(c#0, Tclass._module.MyBoxyClass?(_module.MyBoxyClass$T)) && c#0 != null);

// _module.MyBoxyClass: subset type $IsAlloc
axiom (forall _module.MyBoxyClass$T: Ty, c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.MyBoxyClass(_module.MyBoxyClass$T), $h) } 
  $IsAlloc(c#0, Tclass._module.MyBoxyClass(_module.MyBoxyClass$T), $h)
     <==> $IsAlloc(c#0, Tclass._module.MyBoxyClass?(_module.MyBoxyClass$T), $h));

const unique class._module.CC?: ClassName;

function Tclass._module.CC?() : Ty;

const unique Tagclass._module.CC?: TyTag;

// Tclass._module.CC? Tag
axiom Tag(Tclass._module.CC?()) == Tagclass._module.CC?
   && TagFamily(Tclass._module.CC?()) == tytagFamily$CC;

// Box/unbox axiom for Tclass._module.CC?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.CC?()) } 
  $IsBox(bx, Tclass._module.CC?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.CC?()));

// CC: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.CC?()) } 
  $Is($o, Tclass._module.CC?())
     <==> $o == null || dtype($o) == Tclass._module.CC?());

// CC: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.CC?(), $h) } 
  $IsAlloc($o, Tclass._module.CC?(), $h) <==> $o == null || read($h, $o, alloc));

axiom FDim(_module.CC.x) == 0
   && FieldOfDecl(class._module.CC?, field$x) == _module.CC.x
   && !$IsGhostField(_module.CC.x);

const _module.CC.x: Field int;

// CC.x: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.CC.x) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.CC?()
     ==> $Is(read($h, $o, _module.CC.x), TInt));

// CC.x: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.CC.x) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.CC?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.CC.x), TInt, $h));

axiom FDim(_module.CC.y) == 0
   && FieldOfDecl(class._module.CC?, field$y) == _module.CC.y
   && !$IsGhostField(_module.CC.y);

const _module.CC.y: Field int;

// CC.y: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.CC.y) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.CC?()
     ==> $Is(read($h, $o, _module.CC.y), TInt));

// CC.y: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.CC.y) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.CC?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.CC.y), TInt, $h));

function Tclass._module.CC() : Ty;

const unique Tagclass._module.CC: TyTag;

// Tclass._module.CC Tag
axiom Tag(Tclass._module.CC()) == Tagclass._module.CC
   && TagFamily(Tclass._module.CC()) == tytagFamily$CC;

// Box/unbox axiom for Tclass._module.CC
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.CC()) } 
  $IsBox(bx, Tclass._module.CC())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.CC()));

// _module.CC: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.CC()) } 
  $Is(c#0, Tclass._module.CC()) <==> $Is(c#0, Tclass._module.CC?()) && c#0 != null);

// _module.CC: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.CC(), $h) } 
  $IsAlloc(c#0, Tclass._module.CC(), $h)
     <==> $IsAlloc(c#0, Tclass._module.CC?(), $h));

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

procedure CheckWellformed$$_module.__default.TestCalls(k#0: int where LitInt(0) <= k#0);
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.TestCalls(k#0: int where LitInt(0) <= k#0);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.TestCalls(k#0: int where LitInt(0) <= k#0) returns ($_reverifyPost: bool);
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.TestCalls(k#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var g#0: ref
     where $Is(g#0, Tclass._module.Global?())
       && $IsAlloc(g#0, Tclass._module.Global?(), $Heap);
  var h#0: ref
     where $Is(h#0, Tclass._module.Global?())
       && $IsAlloc(h#0, Tclass._module.Global?(), $Heap);
  var r#0: int;
  var s#0: int;
  var ##x#0: int;
  var $rhs##0: int;
  var x##0: int;
  var $rhs##1: int;
  var x##1: int;
  var $rhs##2: int;
  var x##2: int;
  var $rhs##3: int;
  var x##3: int;
  var $rhs##4: int;
  var x##4: int;

    // AddMethodImpl: TestCalls, Impl$$_module.__default.TestCalls
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(23,25): initial state"} true;
    $_reverifyPost := false;
    havoc g#0 /* where $Is(g#0, Tclass._module.Global?())
       && $IsAlloc(g#0, Tclass._module.Global?(), $Heap) */, h#0 /* where $Is(h#0, Tclass._module.Global?())
       && $IsAlloc(h#0, Tclass._module.Global?(), $Heap) */;
    // ----- assume statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(25,3)
    assume true;
    assume g#0 != h#0;
    havoc r#0;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(27,15)
    assume true;
    ##x#0 := k#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##x#0, TInt, $Heap);
    assume _module.Global.G#canCall(k#0);
    assume _module.Global.G#canCall(k#0);
    s#0 := _module.Global.G(k#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(27,28)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(29,16)
    assume true;
    // TrCallStmt: Adding lhs with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##0 := k#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0 := Call$$_module.Global.N(x##0);
    // TrCallStmt: After ProcessCallStmt
    r#0 := $rhs##0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(29,18)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(30,3)
    assume true;
    assert r#0 == s#0;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(32,11)
    assume true;
    // TrCallStmt: Adding lhs with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##1 := k#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##1 := Call$$_module.Global.N(x##1);
    // TrCallStmt: After ProcessCallStmt
    r#0 := $rhs##1;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(32,13)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(33,3)
    assume true;
    assert r#0 == s#0;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(34,11)
    assume true;
    // TrCallStmt: Adding lhs with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##2 := k#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##2 := Call$$_module.Global.N(x##2);
    // TrCallStmt: After ProcessCallStmt
    r#0 := $rhs##2;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(34,13)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(35,3)
    assume true;
    assert r#0 == s#0;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(37,5)
    assume true;
    assume true;
    g#0 := null;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(37,11)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(38,11)
    assume true;
    // TrCallStmt: Adding lhs with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##3 := k#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##3 := Call$$_module.Global.N(x##3);
    // TrCallStmt: After ProcessCallStmt
    r#0 := $rhs##3;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(38,13)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(39,3)
    assume true;
    assert r#0 == s#0;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(41,16)
    assume true;
    // TrCallStmt: Adding lhs with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##4 := r#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##4 := Call$$_module.Global.N(x##4);
    // TrCallStmt: After ProcessCallStmt
    r#0 := $rhs##4;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(41,18)"} true;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(42,3)
    assume true;
    if (k#0 == LitInt(0))
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(43,5)
        assume true;
        assert r#0 == s#0;
    }
    else
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(45,5)
        assume true;
        assert r#0 == s#0;
    }
}



// function declaration for _module._default.UpTruth
function _module.__default.UpTruth(j#0: int, k#0: int) : bool;

function _module.__default.UpTruth#canCall(j#0: int, k#0: int) : bool;

// consequence axiom for _module.__default.UpTruth
axiom 23 <= $FunctionContextHeight
   ==> (forall j#0: int, k#0: int :: 
    { _module.__default.UpTruth(j#0, k#0) } 
    _module.__default.UpTruth#canCall(j#0, k#0)
         || (23 != $FunctionContextHeight
           && 
          LitInt(10) <= j#0
           && j#0 < 180
           && 180 < 220
           && LitInt(220) <= k#0)
       ==> true);

function _module.__default.UpTruth#requires(int, int) : bool;

// #requires axiom for _module.__default.UpTruth
axiom (forall j#0: int, k#0: int :: 
  { _module.__default.UpTruth#requires(j#0, k#0) } 
  _module.__default.UpTruth#requires(j#0, k#0)
     == (LitInt(10) <= j#0 && j#0 < 180 && 180 < 220 && LitInt(220) <= k#0));

// definition axiom for _module.__default.UpTruth (revealed)
axiom 23 <= $FunctionContextHeight
   ==> (forall j#0: int, k#0: int :: 
    { _module.__default.UpTruth(j#0, k#0) } 
    _module.__default.UpTruth#canCall(j#0, k#0)
         || (23 != $FunctionContextHeight
           && 
          LitInt(10) <= j#0
           && j#0 < 180
           && 180 < 220
           && LitInt(220) <= k#0)
       ==> _module.__default.UpTruth(j#0, k#0)
         == (
          0 < 2
           && LitInt(2) <= LitInt(2)
           && 2 < j#0
           && j#0 != 200
           && 200 < k#0
           && k#0 < k#0 + 1));

// definition axiom for _module.__default.UpTruth for all literals (revealed)
axiom 23 <= $FunctionContextHeight
   ==> (forall j#0: int, k#0: int :: 
    {:weight 3} { _module.__default.UpTruth(LitInt(j#0), LitInt(k#0)) } 
    _module.__default.UpTruth#canCall(LitInt(j#0), LitInt(k#0))
         || (23 != $FunctionContextHeight
           && 
          LitInt(10) <= LitInt(j#0)
           && j#0 < 180
           && 180 < 220
           && LitInt(220) <= LitInt(k#0))
       ==> _module.__default.UpTruth(LitInt(j#0), LitInt(k#0))
         == (
          0 < 2
           && LitInt(2) <= LitInt(2)
           && 2 < j#0
           && j#0 != 200
           && 200 < k#0
           && k#0 < k#0 + 1));

procedure CheckWellformed$$_module.__default.UpTruth(j#0: int, k#0: int);
  free requires 23 == $FunctionContextHeight;
  modifies $Heap, $Tick;



// function declaration for _module._default.DownTruth
function _module.__default.DownTruth(j#0: int, k#0: int) : bool;

function _module.__default.DownTruth#canCall(j#0: int, k#0: int) : bool;

// consequence axiom for _module.__default.DownTruth
axiom 24 <= $FunctionContextHeight
   ==> (forall j#0: int, k#0: int :: 
    { _module.__default.DownTruth(j#0, k#0) } 
    _module.__default.DownTruth#canCall(j#0, k#0)
         || (24 != $FunctionContextHeight
           && 
          k#0 >= LitInt(220)
           && 220 > 180
           && 180 > j#0
           && j#0 >= LitInt(10))
       ==> true);

function _module.__default.DownTruth#requires(int, int) : bool;

// #requires axiom for _module.__default.DownTruth
axiom (forall j#0: int, k#0: int :: 
  { _module.__default.DownTruth#requires(j#0, k#0) } 
  _module.__default.DownTruth#requires(j#0, k#0)
     == (k#0 >= LitInt(220) && 220 > 180 && 180 > j#0 && j#0 >= LitInt(10)));

// definition axiom for _module.__default.DownTruth (revealed)
axiom 24 <= $FunctionContextHeight
   ==> (forall j#0: int, k#0: int :: 
    { _module.__default.DownTruth(j#0, k#0) } 
    _module.__default.DownTruth#canCall(j#0, k#0)
         || (24 != $FunctionContextHeight
           && 
          k#0 >= LitInt(220)
           && 220 > 180
           && 180 > j#0
           && j#0 >= LitInt(10))
       ==> _module.__default.DownTruth(j#0, k#0)
         == (
          k#0 + 1 > k#0
           && k#0 > 200
           && 200 != j#0
           && j#0 > 2
           && LitInt(2) >= LitInt(2)
           && 2 > 0));

// definition axiom for _module.__default.DownTruth for all literals (revealed)
axiom 24 <= $FunctionContextHeight
   ==> (forall j#0: int, k#0: int :: 
    {:weight 3} { _module.__default.DownTruth(LitInt(j#0), LitInt(k#0)) } 
    _module.__default.DownTruth#canCall(LitInt(j#0), LitInt(k#0))
         || (24 != $FunctionContextHeight
           && 
          LitInt(k#0) >= LitInt(220)
           && 220 > 180
           && 180 > j#0
           && LitInt(j#0) >= LitInt(10))
       ==> _module.__default.DownTruth(LitInt(j#0), LitInt(k#0))
         == (
          k#0 + 1 > k#0
           && k#0 > 200
           && 200 != j#0
           && j#0 > 2
           && LitInt(2) >= LitInt(2)
           && 2 > 0));

procedure CheckWellformed$$_module.__default.DownTruth(j#0: int, k#0: int);
  free requires 24 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure CheckWellformed$$_module.__default.ChallengeTruth(j#0: int, k#0: int);
  free requires 25 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.ChallengeTruth(j#0: int, k#0: int);
  // user-defined preconditions
  requires LitInt(80) <= j#0;
  requires j#0 < 150;
  requires LitInt(250) <= k#0;
  requires k#0 < 1000;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.ChallengeTruth(j#0: int, k#0: int) returns ($_reverifyPost: bool);
  free requires 25 == $FunctionContextHeight;
  // user-defined preconditions
  requires LitInt(80) <= j#0;
  requires j#0 < 150;
  requires LitInt(250) <= k#0;
  requires k#0 < 1000;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.ChallengeTruth(j#0: int, k#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##j#0: int;
  var ##k#0: int;
  var ##j#1: int;
  var ##k#1: int;

    // AddMethodImpl: ChallengeTruth, Impl$$_module.__default.ChallengeTruth
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(65,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(66,3)
    ##j#0 := j#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##j#0, TInt, $Heap);
    ##k#0 := k#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##k#0, TInt, $Heap);
    assert {:subsumption 0} LitInt(10) <= ##j#0;
    assert {:subsumption 0} ##j#0 < 180;
    assert {:subsumption 0} 180 < 220;
    assert {:subsumption 0} LitInt(220) <= ##k#0;
    assume _module.__default.UpTruth#canCall(j#0, k#0);
    assume _module.__default.UpTruth#canCall(j#0, k#0);
    assert {:subsumption 0} _module.__default.UpTruth#canCall(j#0, k#0)
       ==> _module.__default.UpTruth(j#0, k#0) || Lit(0 < 2);
    assert {:subsumption 0} _module.__default.UpTruth#canCall(j#0, k#0)
       ==> _module.__default.UpTruth(j#0, k#0) || LitInt(2) <= LitInt(2);
    assert {:subsumption 0} _module.__default.UpTruth#canCall(j#0, k#0)
       ==> _module.__default.UpTruth(j#0, k#0) || 2 < j#0;
    assert {:subsumption 0} _module.__default.UpTruth#canCall(j#0, k#0)
       ==> _module.__default.UpTruth(j#0, k#0) || j#0 != 200;
    assert {:subsumption 0} _module.__default.UpTruth#canCall(j#0, k#0)
       ==> _module.__default.UpTruth(j#0, k#0) || 200 < k#0;
    assert {:subsumption 0} _module.__default.UpTruth#canCall(j#0, k#0)
       ==> _module.__default.UpTruth(j#0, k#0) || k#0 < k#0 + 1;
    assume _module.__default.UpTruth(j#0, k#0);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(67,3)
    ##j#1 := j#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##j#1, TInt, $Heap);
    ##k#1 := k#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##k#1, TInt, $Heap);
    assert {:subsumption 0} ##k#1 >= LitInt(220);
    assert {:subsumption 0} 220 > 180;
    assert {:subsumption 0} 180 > ##j#1;
    assert {:subsumption 0} ##j#1 >= LitInt(10);
    assume _module.__default.DownTruth#canCall(j#0, k#0);
    assume _module.__default.DownTruth#canCall(j#0, k#0);
    assert {:subsumption 0} _module.__default.DownTruth#canCall(j#0, k#0)
       ==> _module.__default.DownTruth(j#0, k#0) || k#0 + 1 > k#0;
    assert {:subsumption 0} _module.__default.DownTruth#canCall(j#0, k#0)
       ==> _module.__default.DownTruth(j#0, k#0) || k#0 > 200;
    assert {:subsumption 0} _module.__default.DownTruth#canCall(j#0, k#0)
       ==> _module.__default.DownTruth(j#0, k#0) || 200 != j#0;
    assert {:subsumption 0} _module.__default.DownTruth#canCall(j#0, k#0)
       ==> _module.__default.DownTruth(j#0, k#0) || j#0 > 2;
    assert {:subsumption 0} _module.__default.DownTruth#canCall(j#0, k#0)
       ==> _module.__default.DownTruth(j#0, k#0) || LitInt(2) >= LitInt(2);
    assert {:subsumption 0} _module.__default.DownTruth#canCall(j#0, k#0)
       ==> _module.__default.DownTruth(j#0, k#0) || Lit(2 > 0);
    assume _module.__default.DownTruth(j#0, k#0);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(69,3)
    if (j#0 <= j#0 + k#0)
    {
    }

    if (j#0 <= j#0 + k#0 && j#0 + k#0 != k#0 + j#0 + 1)
    {
    }

    if (j#0 <= j#0 + k#0
       && j#0 + k#0 != k#0 + j#0 + 1
       && k#0 + j#0 + 1 < k#0 + k#0 + j#0)
    {
    }

    if (j#0 <= j#0 + k#0
       && j#0 + k#0 != k#0 + j#0 + 1
       && k#0 + j#0 + 1 < k#0 + k#0 + j#0
       && k#0 + k#0 + j#0 <= j#0 + j#0 + k#0)
    {
    }

    if (j#0 <= j#0 + k#0
       && j#0 + k#0 != k#0 + j#0 + 1
       && k#0 + j#0 + 1 < k#0 + k#0 + j#0
       && k#0 + k#0 + j#0 <= j#0 + j#0 + k#0
       && j#0 + j#0 + k#0 < k#0 + k#0 + j#0 + j#0)
    {
    }

    if (j#0 <= j#0 + k#0
       && j#0 + k#0 != k#0 + j#0 + 1
       && k#0 + j#0 + 1 < k#0 + k#0 + j#0
       && k#0 + k#0 + j#0 <= j#0 + j#0 + k#0
       && j#0 + j#0 + k#0 < k#0 + k#0 + j#0 + j#0
       && k#0 + k#0 + j#0 + j#0 == Mul(LitInt(2), k#0) + Mul(LitInt(2), j#0))
    {
    }

    assume true;
    assert {:subsumption 0} j#0 <= j#0 + k#0;
    assert {:subsumption 0} j#0 + k#0 != k#0 + j#0 + 1;
    assert {:subsumption 0} k#0 + j#0 + 1 < k#0 + k#0 + j#0;
    assert {:subsumption 0} k#0 + k#0 + j#0 <= j#0 + j#0 + k#0;
    assert {:subsumption 0} j#0 + j#0 + k#0 < k#0 + k#0 + j#0 + j#0;
    assert {:subsumption 0} k#0 + k#0 + j#0 + j#0 == Mul(LitInt(2), k#0) + Mul(LitInt(2), j#0);
    assert {:subsumption 0} Mul(LitInt(2), k#0) + Mul(LitInt(2), j#0) == Mul(LitInt(2), k#0 + j#0);
    assume j#0 <= j#0 + k#0
       && j#0 + k#0 != k#0 + j#0 + 1
       && k#0 + j#0 + 1 < k#0 + k#0 + j#0
       && k#0 + k#0 + j#0 <= j#0 + j#0 + k#0
       && j#0 + j#0 + k#0 < k#0 + k#0 + j#0 + j#0
       && k#0 + k#0 + j#0 + j#0 == Mul(LitInt(2), k#0) + Mul(LitInt(2), j#0)
       && Mul(LitInt(2), k#0) + Mul(LitInt(2), j#0) == Mul(LitInt(2), k#0 + j#0);
}



procedure CheckWellformed$$_module.__default.Explies(s#0: Seq Box where $Is(s#0, TSeq(TInt)) && $IsAlloc(s#0, TSeq(TInt), $Heap), 
    i#0: int where LitInt(0) <= i#0);
  free requires 7 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Explies(s#0: Seq Box where $Is(s#0, TSeq(TInt)) && $IsAlloc(s#0, TSeq(TInt), $Heap), 
    i#0: int where LitInt(0) <= i#0);
  // user-defined preconditions
  requires (forall x#1: int :: 
    { Seq#Contains(s#0, $Box(x#1)) } 
    true ==> Seq#Contains(s#0, $Box(x#1)) ==> x#1 > 0);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.Explies(s#0: Seq Box where $Is(s#0, TSeq(TInt)) && $IsAlloc(s#0, TSeq(TInt), $Heap), 
    i#0: int where LitInt(0) <= i#0)
   returns ($_reverifyPost: bool);
  free requires 7 == $FunctionContextHeight;
  // user-defined preconditions
  requires (forall x#1: int :: 
    { Seq#Contains(s#0, $Box(x#1)) } 
    true ==> Seq#Contains(s#0, $Box(x#1)) ==> x#1 > 0);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.Explies(s#0: Seq Box, i#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var a#0: bool;
  var b#0: bool;
  var c#0: bool;

    // AddMethodImpl: Explies, Impl$$_module.__default.Explies
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(76,0): initial state"} true;
    $_reverifyPost := false;
    havoc a#0, b#0, c#0;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(78,3)
    if (Lit(false))
    {
        if (c#0)
        {
            if (b#0)
            {
            }
        }
    }

    assume true;
    assert {:subsumption 0} Lit(false) ==> c#0 ==> b#0 ==> a#0;
    assume false ==> c#0 ==> b#0 ==> a#0;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(79,3)
    if (i#0 < Seq#Length(s#0))
    {
        assert {:subsumption 0} 0 <= i#0 && i#0 < Seq#Length(s#0);
    }

    assume true;
    assert {:subsumption 0} i#0 < Seq#Length(s#0) ==> $Unbox(Seq#Index(s#0, i#0)): int > 0;
    assume i#0 < Seq#Length(s#0) ==> $Unbox(Seq#Index(s#0, i#0)): int > 0;
}



procedure CheckWellformed$$_module.__default.ExpliesAssociativityM(A#0: bool, B#0: bool, C#0: bool);
  free requires 32 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.ExpliesAssociativityM(A#0: bool, B#0: bool, C#0: bool);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.ExpliesAssociativityM(A#0: bool, B#0: bool, C#0: bool) returns ($_reverifyPost: bool);
  free requires 32 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.ExpliesAssociativityM(A#0: bool, B#0: bool, C#0: bool) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var x#0: bool;
  var y#0: bool;
  var z#0: bool;

    // AddMethodImpl: ExpliesAssociativityM, Impl$$_module.__default.ExpliesAssociativityM
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(82,56): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(83,9)
    assume true;
    if (A#0)
    {
    }

    assume true;
    x#0 := A#0 ==> B#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(83,18)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(84,9)
    assume true;
    if (A#0)
    {
    }

    assume true;
    y#0 := A#0 ==> B#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(84,18)"} true;
    havoc z#0;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(86,3)
    assume true;
    assert x#0 == y#0;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(88,3)
    if (*)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(89,7)
        assume true;
        if (A#0)
        {
            if (B#0)
            {
            }
        }

        assume true;
        x#0 := A#0 ==> B#0 ==> C#0;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(89,22)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(90,7)
        assume true;
        if (A#0)
        {
            if (B#0)
            {
            }
        }

        assume true;
        y#0 := A#0 ==> B#0 ==> C#0;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(90,24)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(91,7)
        assume true;
        if (A#0)
        {
        }

        if (A#0 ==> B#0)
        {
        }

        assume true;
        z#0 := (A#0 ==> B#0) ==> C#0;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(91,24)"} true;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(92,5)
        assume true;
        assert x#0 == y#0;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(93,5)
        assume true;
        assert x#0 == z#0;
    }
    else
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(95,7)
        assume true;
        if (A#0)
        {
            if (B#0)
            {
            }
        }

        assume true;
        x#0 := A#0 ==> B#0 ==> C#0;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(95,22)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(96,7)
        assume true;
        if (A#0)
        {
            if (B#0)
            {
            }
        }

        assume true;
        y#0 := A#0 ==> B#0 ==> C#0;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(96,24)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(97,7)
        assume true;
        if (A#0)
        {
        }

        if (A#0 ==> B#0)
        {
        }

        assume true;
        z#0 := (A#0 ==> B#0) ==> C#0;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(97,24)"} true;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(98,5)
        assume true;
        assert x#0 == y#0;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(99,5)
        assume true;
        assert x#0 == z#0;
    }
}



procedure CheckWellformed$$_module.__default.ExpliesShortCircuiting(_module._default.ExpliesShortCircuiting$_T0: Ty, 
    a#0: ref
       where $Is(a#0, Tclass._System.array?(_module._default.ExpliesShortCircuiting$_T0))
         && $IsAlloc(a#0, Tclass._System.array?(_module._default.ExpliesShortCircuiting$_T0), $Heap));
  free requires 33 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.ExpliesShortCircuiting(_module._default.ExpliesShortCircuiting$_T0: Ty, 
    a#0: ref
       where $Is(a#0, Tclass._System.array?(_module._default.ExpliesShortCircuiting$_T0))
         && $IsAlloc(a#0, Tclass._System.array?(_module._default.ExpliesShortCircuiting$_T0), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.ExpliesShortCircuiting(_module._default.ExpliesShortCircuiting$_T0: Ty, 
    a#0: ref
       where $Is(a#0, Tclass._System.array?(_module._default.ExpliesShortCircuiting$_T0))
         && $IsAlloc(a#0, Tclass._System.array?(_module._default.ExpliesShortCircuiting$_T0), $Heap))
   returns ($_reverifyPost: bool);
  free requires 33 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.ExpliesShortCircuiting(_module._default.ExpliesShortCircuiting$_T0: Ty, a#0: ref)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: ExpliesShortCircuiting, Impl$$_module.__default.ExpliesShortCircuiting
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(104,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(105,3)
    if (a#0 != null)
    {
        assert {:subsumption 0} a#0 != null;
    }

    assume true;
    assert a#0 == null || LitInt(0) <= _System.array.Length(a#0);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(106,3)
    if (a#0 != null)
    {
        assert {:subsumption 0} a#0 != null;
    }

    assume true;
    assert {:subsumption 0} a#0 != null ==> LitInt(0) <= _System.array.Length(a#0);
    assume a#0 != null ==> LitInt(0) <= _System.array.Length(a#0);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(107,3)
    if (a#0 != null)
    {
        assert {:subsumption 0} a#0 != null;
    }

    assume true;
    assert {:subsumption 0} a#0 != null ==> LitInt(0) <= _System.array.Length(a#0);
    assume a#0 != null ==> LitInt(0) <= _System.array.Length(a#0);
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(111,3)
    if (*)
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(112,5)
        assert {:subsumption 0} a#0 != null;
        if (_System.array.Length(a#0) < 0)
        {
        }

        assume true;
        assert {:subsumption 0} _System.array.Length(a#0) < 0 ==> a#0 == null;
        assume _System.array.Length(a#0) < 0 ==> a#0 == null;
    }
    else
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(114,5)
        assert {:subsumption 0} a#0 != null;
        if (_System.array.Length(a#0) < 0)
        {
        }

        assume true;
        assert {:subsumption 0} _System.array.Length(a#0) < 0 ==> a#0 == null;
        assume _System.array.Length(a#0) < 0 ==> a#0 == null;
    }
}



procedure CheckWellformed$$_module.__default.TestMulti(m#0: ref
       where $Is(m#0, Tclass._module.Multi()) && $IsAlloc(m#0, Tclass._module.Multi(), $Heap), 
    p#0: ref
       where $Is(p#0, Tclass._module.Multi()) && $IsAlloc(p#0, Tclass._module.Multi(), $Heap));
  free requires 10 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.TestMulti(m#0: ref
       where $Is(m#0, Tclass._module.Multi()) && $IsAlloc(m#0, Tclass._module.Multi(), $Heap), 
    p#0: ref
       where $Is(p#0, Tclass._module.Multi()) && $IsAlloc(p#0, Tclass._module.Multi(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == m#0 || $o == p#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.TestMulti(m#0: ref
       where $Is(m#0, Tclass._module.Multi()) && $IsAlloc(m#0, Tclass._module.Multi(), $Heap), 
    p#0: ref
       where $Is(p#0, Tclass._module.Multi()) && $IsAlloc(p#0, Tclass._module.Multi(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 10 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == m#0 || $o == p#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.TestMulti(m#0: ref, p#0: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: int;
  var $rhs#1: int;
  var $rhs#2: int;
  var $rhs#3: int;
  var t#0: int;
  var u#0: int;
  var $obj1: ref;
  var $rhs#4: int;
  var $rhs#5: int;
  var $rhs#6: int;
  var $rhs#7: int;
  var $rhs#8: int;
  var $rhs#9: int;
  var $rhs#10: int;
  var $obj0: ref;
  var $rhs#1_0: int;
  var $rhs#1_1: int;
  var $rhs#2_0: int;
  var $rhs#2_1: int;
  var $rhs#2_2: int;
  var $rhs#2_3: int;
  var a#0: ref
     where $Is(a#0, Tclass._System.array(TInt))
       && $IsAlloc(a#0, Tclass._System.array(TInt), $Heap);
  var b#0: ref
     where $Is(b#0, Tclass._System.array(TInt))
       && $IsAlloc(b#0, Tclass._System.array(TInt), $Heap);
  var $rhs#11: ref where $Is($rhs#11, Tclass._System.array(TInt));
  var $nw: ref;
  var $rhs#12: ref where $Is($rhs#12, Tclass._System.array(TInt));
  var $index0: Field Box;
  var $index1: Field Box;
  var $obj2: ref;
  var $index2: Field Box;
  var $obj3: ref;
  var $index3: Field Box;
  var $obj4: ref;
  var $index4: Field Box;
  var $rhs#13: int;
  var $rhs#14: int;
  var $rhs#15: int;
  var $rhs#16: int;
  var $rhs#17: int;
  var $rhs#18: int;
  var $rhs#19: int;
  var $rhs#20: int;
  var $rhs#21: int;

    // AddMethodImpl: TestMulti, Impl$$_module.__default.TestMulti
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == m#0 || $o == p#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(141,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(142,7)
    assert m#0 != null;
    assume true;
    assert $_Frame[m#0, _module.Multi.x];
    assume true;
    $rhs#0 := LitInt(10);
    $Heap := update($Heap, m#0, _module.Multi.x, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(142,11)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(143,7)
    assert m#0 != null;
    assume true;
    assert $_Frame[m#0, _module.Multi.y];
    assume true;
    $rhs#1 := LitInt(12);
    $Heap := update($Heap, m#0, _module.Multi.y, $rhs#1);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(143,11)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(144,7)
    assert p#0 != null;
    assume true;
    assert $_Frame[p#0, _module.Multi.x];
    assume true;
    $rhs#2 := LitInt(20);
    $Heap := update($Heap, p#0, _module.Multi.x, $rhs#2);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(144,11)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(145,7)
    assert p#0 != null;
    assume true;
    assert $_Frame[p#0, _module.Multi.y];
    assume true;
    $rhs#3 := LitInt(22);
    $Heap := update($Heap, p#0, _module.Multi.y, $rhs#3);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(145,11)"} true;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(146,3)
    if (*)
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(147,5)
        assert {:subsumption 0} p#0 != null;
        assume true;
        assert read($Heap, p#0, _module.Multi.x) == LitInt(20);
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(148,5)
        assert {:subsumption 0} m#0 != null;
        assume true;
        assert read($Heap, m#0, _module.Multi.x) == LitInt(10);
    }
    else
    {
    }

    havoc t#0, u#0;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(151,13)
    assume true;
    assert m#0 != null;
    assume true;
    $obj1 := m#0;
    assert $_Frame[$obj1, _module.Multi.x];
    assume true;
    assume true;
    $rhs#4 := LitInt(100);
    assert m#0 != null;
    assume true;
    $rhs#5 := u#0 + t#0 + read($Heap, m#0, _module.Multi.x);
    assume true;
    $rhs#6 := LitInt(200);
    u#0 := $rhs#4;
    $Heap := update($Heap, $obj1, _module.Multi.x, $rhs#5);
    assume $IsGoodHeap($Heap);
    t#0 := $rhs#6;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(151,36)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(152,7)
    assert m#0 != null;
    assume true;
    assert $_Frame[m#0, _module.Multi.x];
    assume true;
    $rhs#7 := LitInt(0);
    $Heap := update($Heap, m#0, _module.Multi.x, $rhs#7);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(152,10)"} true;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(153,13)
    assume true;
    assert m#0 != null;
    assume true;
    $obj1 := m#0;
    assert $_Frame[$obj1, _module.Multi.x];
    assume true;
    assume true;
    $rhs#8 := LitInt(200);
    assert m#0 != null;
    assume true;
    $rhs#9 := u#0 + t#0 + read($Heap, m#0, _module.Multi.x);
    assume true;
    $rhs#10 := LitInt(400);
    u#0 := $rhs#8;
    $Heap := update($Heap, $obj1, _module.Multi.x, $rhs#9);
    assume $IsGoodHeap($Heap);
    t#0 := $rhs#10;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(153,36)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(154,3)
    assert {:subsumption 0} m#0 != null;
    assume true;
    assert read($Heap, m#0, _module.Multi.x) == LitInt(300);
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(155,3)
    assert p#0 != null;
    assume true;
    if (read($Heap, p#0, _module.Multi.x) != 300)
    {
        // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(156,14)
        assert p#0 != null;
        assume true;
        $obj0 := p#0;
        assert $_Frame[$obj0, _module.Multi.x];
        assert m#0 != null;
        assume true;
        $obj1 := m#0;
        assert $_Frame[$obj1, _module.Multi.x];
        assert m#0 != null;
        assume true;
        $rhs#1_0 := read($Heap, m#0, _module.Multi.x);
        assert p#0 != null;
        assume true;
        $rhs#1_1 := read($Heap, p#0, _module.Multi.x);
        assert m#0 != p#0 || $rhs#1_1 == $rhs#1_0;
        $Heap := update($Heap, $obj0, _module.Multi.x, $rhs#1_0);
        assume $IsGoodHeap($Heap);
        $Heap := update($Heap, $obj1, _module.Multi.x, $rhs#1_1);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(156,24)"} true;
    }
    else
    {
    }

    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(158,3)
    assert {:subsumption 0} p#0 != null;
    assume true;
    assert read($Heap, p#0, _module.Multi.x) == LitInt(300);
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(159,3)
    if (*)
    {
        // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(160,14)
        assert p#0 != null;
        assume true;
        $obj0 := p#0;
        assert $_Frame[$obj0, _module.Multi.x];
        assert m#0 != null;
        assume true;
        $obj1 := m#0;
        assert $_Frame[$obj1, _module.Multi.y];
        assume true;
        $rhs#2_0 := LitInt(10);
        assume true;
        $rhs#2_1 := LitInt(10);
        $Heap := update($Heap, $obj0, _module.Multi.x, $rhs#2_0);
        assume $IsGoodHeap($Heap);
        $Heap := update($Heap, $obj1, _module.Multi.y, $rhs#2_1);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(160,22)"} true;
        // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(161,14)
        assert p#0 != null;
        assume true;
        $obj0 := p#0;
        assert $_Frame[$obj0, _module.Multi.x];
        assert m#0 != null;
        assume true;
        $obj1 := m#0;
        assert $_Frame[$obj1, _module.Multi.x];
        assume true;
        $rhs#2_2 := LitInt(8);
        assume true;
        $rhs#2_3 := LitInt(8);
        assert m#0 != p#0 || $rhs#2_3 == $rhs#2_2;
        $Heap := update($Heap, $obj0, _module.Multi.x, $rhs#2_2);
        assume $IsGoodHeap($Heap);
        $Heap := update($Heap, $obj1, _module.Multi.x, $rhs#2_3);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(161,20)"} true;
    }
    else
    {
    }

    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(164,12)
    assume true;
    assume true;
    assert 0 <= LitInt(20);
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._System.array?(TInt);
    assume !read($Heap, $nw, alloc);
    assume _System.array.Length($nw) == LitInt(20);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    $rhs#11 := $nw;
    assert 0 <= LitInt(30);
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._System.array?(TInt);
    assume !read($Heap, $nw, alloc);
    assume _System.array.Length($nw) == LitInt(30);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    $rhs#12 := $nw;
    a#0 := $rhs#11;
    b#0 := $rhs#12;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(164,38)"} true;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(165,34)
    assert a#0 != null;
    assert 0 <= LitInt(4) && LitInt(4) < _System.array.Length(a#0);
    assume true;
    $obj0 := a#0;
    $index0 := IndexField(LitInt(4));
    assert $_Frame[$obj0, $index0];
    assert b#0 != null;
    assert 0 <= LitInt(10) && LitInt(10) < _System.array.Length(b#0);
    assume true;
    $obj1 := b#0;
    $index1 := IndexField(LitInt(10));
    assert $_Frame[$obj1, $index1];
    assert a#0 != null;
    assert 0 <= LitInt(0) && LitInt(0) < _System.array.Length(a#0);
    assume true;
    $obj2 := a#0;
    $index2 := IndexField(LitInt(0));
    assert $_Frame[$obj2, $index2];
    assert a#0 != null;
    assert 0 <= LitInt(3) && LitInt(3) < _System.array.Length(a#0);
    assume true;
    $obj3 := a#0;
    $index3 := IndexField(LitInt(3));
    assert $_Frame[$obj3, $index3];
    assert b#0 != null;
    assert 0 <= LitInt(18) && LitInt(18) < _System.array.Length(b#0);
    assume true;
    $obj4 := b#0;
    $index4 := IndexField(LitInt(18));
    assert $_Frame[$obj4, $index4];
    assume true;
    $rhs#13 := LitInt(0);
    assume true;
    $rhs#14 := LitInt(1);
    assume true;
    $rhs#15 := LitInt(2);
    assume true;
    $rhs#16 := LitInt(3);
    assume true;
    $rhs#17 := LitInt(4);
    assert b#0 != a#0 || LitInt(10) != LitInt(4) || $Box($rhs#14) == $Box($rhs#13);
    assert a#0 != a#0 || LitInt(0) != LitInt(4) || $Box($rhs#15) == $Box($rhs#13);
    assert a#0 != b#0 || LitInt(0) != LitInt(10) || $Box($rhs#15) == $Box($rhs#14);
    assert a#0 != a#0 || LitInt(3) != LitInt(4) || $Box($rhs#16) == $Box($rhs#13);
    assert a#0 != b#0 || LitInt(3) != LitInt(10) || $Box($rhs#16) == $Box($rhs#14);
    assert a#0 != a#0 || LitInt(3) != LitInt(0) || $Box($rhs#16) == $Box($rhs#15);
    assert b#0 != a#0 || LitInt(18) != LitInt(4) || $Box($rhs#17) == $Box($rhs#13);
    assert b#0 != b#0 || LitInt(18) != LitInt(10) || $Box($rhs#17) == $Box($rhs#14);
    assert b#0 != a#0 || LitInt(18) != LitInt(0) || $Box($rhs#17) == $Box($rhs#15);
    assert b#0 != a#0 || LitInt(18) != LitInt(3) || $Box($rhs#17) == $Box($rhs#16);
    $Heap := update($Heap, $obj0, $index0, $Box($rhs#13));
    assume $IsGoodHeap($Heap);
    $Heap := update($Heap, $obj1, $index1, $Box($rhs#14));
    assume $IsGoodHeap($Heap);
    $Heap := update($Heap, $obj2, $index2, $Box($rhs#15));
    assume $IsGoodHeap($Heap);
    $Heap := update($Heap, $obj3, $index3, $Box($rhs#16));
    assume $IsGoodHeap($Heap);
    $Heap := update($Heap, $obj4, $index4, $Box($rhs#17));
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(165,49)"} true;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(166,18)
    assert a#0 != null;
    assert 0 <= LitInt(4) && LitInt(4) < _System.array.Length(a#0);
    assume true;
    $obj0 := a#0;
    $index0 := IndexField(LitInt(4));
    assert $_Frame[$obj0, $index0];
    assert b#0 != null;
    assert b#0 != null;
    assert 0 <= LitInt(18) && LitInt(18) < _System.array.Length(b#0);
    assert 0 <= $Unbox(read($Heap, b#0, IndexField(LitInt(18)))): int
       && $Unbox(read($Heap, b#0, IndexField(LitInt(18)))): int
         < _System.array.Length(b#0);
    assume true;
    $obj1 := b#0;
    $index1 := IndexField($Unbox(read($Heap, b#0, IndexField(LitInt(18)))): int);
    assert $_Frame[$obj1, $index1];
    assume true;
    $rhs#18 := LitInt(271);
    assume true;
    $rhs#19 := LitInt(272);
    assert b#0 != a#0
       || $Unbox(read($Heap, b#0, IndexField(LitInt(18)))): int != LitInt(4)
       || $Box($rhs#19) == $Box($rhs#18);
    $Heap := update($Heap, $obj0, $index0, $Box($rhs#18));
    assume $IsGoodHeap($Heap);
    $Heap := update($Heap, $obj1, $index1, $Box($rhs#19));
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(166,28)"} true;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(167,18)
    assert a#0 != null;
    assert 0 <= LitInt(4) && LitInt(4) < _System.array.Length(a#0);
    assume true;
    $obj0 := a#0;
    $index0 := IndexField(LitInt(4));
    assert $_Frame[$obj0, $index0];
    assert a#0 != null;
    assert b#0 != null;
    assert 0 <= LitInt(18) && LitInt(18) < _System.array.Length(b#0);
    assert 0 <= $Unbox(read($Heap, b#0, IndexField(LitInt(18)))): int
       && $Unbox(read($Heap, b#0, IndexField(LitInt(18)))): int
         < _System.array.Length(a#0);
    assume true;
    $obj1 := a#0;
    $index1 := IndexField($Unbox(read($Heap, b#0, IndexField(LitInt(18)))): int);
    assert $_Frame[$obj1, $index1];
    assume true;
    $rhs#20 := LitInt(273);
    assume true;
    $rhs#21 := LitInt(274);
    assert a#0 != a#0
       || $Unbox(read($Heap, b#0, IndexField(LitInt(18)))): int != LitInt(4)
       || $Box($rhs#21) == $Box($rhs#20);
    $Heap := update($Heap, $obj0, $index0, $Box($rhs#20));
    assume $IsGoodHeap($Heap);
    $Heap := update($Heap, $obj1, $index1, $Box($rhs#21));
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(167,28)"} true;
}



procedure CheckWellformed$$_module.__default.TestBoxAssignment(_module._default.TestBoxAssignment$T: Ty, 
    x#0: ref
       where $Is(x#0, Tclass._module.MyBoxyClass(TInt))
         && $IsAlloc(x#0, Tclass._module.MyBoxyClass(TInt), $Heap), 
    y#0: ref
       where $Is(y#0, Tclass._module.MyBoxyClass(_module._default.TestBoxAssignment$T))
         && $IsAlloc(y#0, Tclass._module.MyBoxyClass(_module._default.TestBoxAssignment$T), $Heap), 
    t#0: Box
       where $IsBox(t#0, _module._default.TestBoxAssignment$T)
         && $IsAllocBox(t#0, _module._default.TestBoxAssignment$T, $Heap));
  free requires 12 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.TestBoxAssignment(_module._default.TestBoxAssignment$T: Ty, 
    x#0: ref
       where $Is(x#0, Tclass._module.MyBoxyClass(TInt))
         && $IsAlloc(x#0, Tclass._module.MyBoxyClass(TInt), $Heap), 
    y#0: ref
       where $Is(y#0, Tclass._module.MyBoxyClass(_module._default.TestBoxAssignment$T))
         && $IsAlloc(y#0, Tclass._module.MyBoxyClass(_module._default.TestBoxAssignment$T), $Heap), 
    t#0: Box
       where $IsBox(t#0, _module._default.TestBoxAssignment$T)
         && $IsAllocBox(t#0, _module._default.TestBoxAssignment$T, $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == x#0 || $o == y#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.TestBoxAssignment(_module._default.TestBoxAssignment$T: Ty, 
    x#0: ref
       where $Is(x#0, Tclass._module.MyBoxyClass(TInt))
         && $IsAlloc(x#0, Tclass._module.MyBoxyClass(TInt), $Heap), 
    y#0: ref
       where $Is(y#0, Tclass._module.MyBoxyClass(_module._default.TestBoxAssignment$T))
         && $IsAlloc(y#0, Tclass._module.MyBoxyClass(_module._default.TestBoxAssignment$T), $Heap), 
    t#0: Box
       where $IsBox(t#0, _module._default.TestBoxAssignment$T)
         && $IsAllocBox(t#0, _module._default.TestBoxAssignment$T, $Heap))
   returns ($_reverifyPost: bool);
  free requires 12 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == x#0 || $o == y#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.TestBoxAssignment(_module._default.TestBoxAssignment$T: Ty, x#0: ref, y#0: ref, t#0: Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: Box where $IsBox($rhs#0, _module._default.TestBoxAssignment$T);
  var $rhs#1: int;
  var $obj0: ref;
  var $obj1: ref;
  var $rhs#2: Box where $IsBox($rhs#2, _module._default.TestBoxAssignment$T);
  var $rhs#3: int;
  var k#0: int;

    // AddMethodImpl: TestBoxAssignment, Impl$$_module.__default.TestBoxAssignment
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == x#0 || $o == y#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(179,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(180,7)
    assert y#0 != null;
    assume true;
    assert $_Frame[y#0, _module.MyBoxyClass.f];
    assume true;
    $rhs#0 := t#0;
    $Heap := update($Heap, y#0, _module.MyBoxyClass.f, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(180,10)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(181,7)
    assert x#0 != null;
    assume true;
    assert $_Frame[x#0, _module.MyBoxyClass.f];
    assume true;
    $rhs#1 := LitInt(15);
    $Heap := update($Heap, x#0, _module.MyBoxyClass.f, $Box($rhs#1));
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(181,11)"} true;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(183,12)
    assert y#0 != null;
    assume true;
    $obj0 := y#0;
    assert $_Frame[$obj0, _module.MyBoxyClass.f];
    assert x#0 != null;
    assume true;
    $obj1 := x#0;
    assert $_Frame[$obj1, _module.MyBoxyClass.f];
    assume true;
    $rhs#2 := t#0;
    assume true;
    $rhs#3 := LitInt(15);
    assert x#0 != y#0 || $Box($rhs#3) == $rhs#2;
    $Heap := update($Heap, $obj0, _module.MyBoxyClass.f, $rhs#2);
    assume $IsGoodHeap($Heap);
    $Heap := update($Heap, $obj1, _module.MyBoxyClass.f, $Box($rhs#3));
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(183,19)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(184,14)
    assume true;
    assert x#0 != null;
    assume true;
    k#0 := $Unbox(read($Heap, x#0, _module.MyBoxyClass.f)): int;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(184,19)"} true;
}



procedure CheckWellformed$$_module.__default.TestCallsWithFancyLhss(m#0: ref
       where $Is(m#0, Tclass._module.Multi()) && $IsAlloc(m#0, Tclass._module.Multi(), $Heap));
  free requires 16 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.TestCallsWithFancyLhss(m#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: TestCallsWithFancyLhss, CheckWellformed$$_module.__default.TestCallsWithFancyLhss
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> $o == m#0 || $o == read($Heap, m#0, _module.Multi.next));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(187,7): initial state"} true;
    assert m#0 != null;
    assume read($Heap, m#0, _module.Multi.next) != null;
    assert m#0 != null;
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc)
         ==> $Heap[$o] == old($Heap)[$o]
           || 
          $o == m#0
           || $o == read(old($Heap), m#0, _module.Multi.next));
    assume $HeapSucc(old($Heap), $Heap);
}



procedure Call$$_module.__default.TestCallsWithFancyLhss(m#0: ref
       where $Is(m#0, Tclass._module.Multi()) && $IsAlloc(m#0, Tclass._module.Multi(), $Heap));
  // user-defined preconditions
  requires read($Heap, m#0, _module.Multi.next) != null;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || 
        $o == m#0
         || $o == read(old($Heap), m#0, _module.Multi.next));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.TestCallsWithFancyLhss(m#0: ref
       where $Is(m#0, Tclass._module.Multi()) && $IsAlloc(m#0, Tclass._module.Multi(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 16 == $FunctionContextHeight;
  // user-defined preconditions
  requires read($Heap, m#0, _module.Multi.next) != null;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || 
        $o == m#0
         || $o == read(old($Heap), m#0, _module.Multi.next));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.TestCallsWithFancyLhss(m#0: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: int;
  var p#0: ref
     where $Is(p#0, Tclass._module.Multi?())
       && $IsAlloc(p#0, Tclass._module.Multi?(), $Heap);
  var $obj0: ref;
  var $rhs##0: ref
     where $Is($rhs##0, Tclass._module.Multi?())
       && $IsAlloc($rhs##0, Tclass._module.Multi?(), $Heap);
  var z##0: int;
  var $rhs##1: ref
     where $Is($rhs##1, Tclass._module.Multi?())
       && $IsAlloc($rhs##1, Tclass._module.Multi?(), $Heap);
  var z##1: int;
  var $obj1: ref;
  var $rhs#1: int;
  var $rhs#2: ref where $Is($rhs#2, Tclass._module.Multi?());
  var $rhs##2: int;
  var $rhs##3: int;
  var a##0: int;
  var b##0: int;
  var $rhs##1_0: int;
  var $rhs##1_1: int;
  var a##1_0: int;
  var b##1_0: int;
  var $rhs#3: int;
  var xx#0: int;
  var $rhs##4: int;
  var $rhs##5: int;
  var $rhs##6: int;
  var $rhs##7: int;

    // AddMethodImpl: TestCallsWithFancyLhss, Impl$$_module.__default.TestCallsWithFancyLhss
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> $o == m#0 || $o == read($Heap, m#0, _module.Multi.next));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(190,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(191,7)
    assert m#0 != null;
    assume true;
    assert $_Frame[m#0, _module.Multi.x];
    assume true;
    $rhs#0 := LitInt(10);
    $Heap := update($Heap, m#0, _module.Multi.x, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(191,11)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(192,9)
    assume true;
    assert m#0 != null;
    assume true;
    p#0 := read($Heap, m#0, _module.Multi.next);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(192,17)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(193,26)
    assert m#0 != null;
    assert read($Heap, m#0, _module.Multi.next) != null;
    assume true;
    $obj0 := read($Heap, m#0, _module.Multi.next);
    assert $_Frame[$obj0, _module.Multi.next];
    // TrCallStmt: Adding lhs with type Multi?
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert m#0 != null;
    assert m#0 != null;
    assume true;
    // ProcessCallStmt: CheckSubrange
    z##0 := read($Heap, m#0, _module.Multi.x);
    assert (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) && $o == m#0 ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0 := Call$$_module.Multi.Mutate(m#0, z##0);
    // TrCallStmt: After ProcessCallStmt
    $Heap := update($Heap, $obj0, _module.Multi.next, $rhs##0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(193,30)"} true;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(194,3)
    if (*)
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(195,5)
        assert {:subsumption 0} m#0 != null;
        assert {:subsumption 0} m#0 != null;
        assert $IsAlloc(m#0, Tclass._module.Multi(), old($Heap));
        assume true;
        assert read($Heap, m#0, _module.Multi.next)
           == read(old($Heap), m#0, _module.Multi.next);
    }
    else
    {
    }

    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(197,26)
    assert m#0 != null;
    assert read($Heap, m#0, _module.Multi.next) != null;
    assume true;
    $obj0 := read($Heap, m#0, _module.Multi.next);
    assert $_Frame[$obj0, _module.Multi.next];
    // TrCallStmt: Adding lhs with type Multi?
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert m#0 != null;
    assume true;
    // ProcessCallStmt: CheckSubrange
    z##1 := LitInt(20);
    assert (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) && $o == m#0 ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##1 := Call$$_module.Multi.Mutate(m#0, z##1);
    // TrCallStmt: After ProcessCallStmt
    $Heap := update($Heap, $obj0, _module.Multi.next, $rhs##1);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(197,29)"} true;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(198,15)
    assert m#0 != null;
    assume true;
    $obj0 := m#0;
    assert $_Frame[$obj0, _module.Multi.x];
    assert m#0 != null;
    assume true;
    $obj1 := m#0;
    assert $_Frame[$obj1, _module.Multi.next];
    assume true;
    $rhs#1 := LitInt(12);
    assume true;
    $rhs#2 := p#0;
    $Heap := update($Heap, $obj0, _module.Multi.x, $rhs#1);
    assume $IsGoodHeap($Heap);
    $Heap := update($Heap, $obj1, _module.Multi.next, $rhs#2);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(198,22)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(199,21)
    assert m#0 != null;
    assume true;
    $obj0 := m#0;
    assert $_Frame[$obj0, _module.Multi.x];
    assert m#0 != null;
    assume true;
    $obj1 := m#0;
    assert $_Frame[$obj1, _module.Multi.y];
    // TrCallStmt: Adding lhs with type int
    // TrCallStmt: Adding lhs with type int
    // TrCallStmt: Before ProcessCallStmt
    assert m#0 != null;
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##0 := read($Heap, m#0, _module.Multi.x);
    assert m#0 != null;
    assume true;
    // ProcessCallStmt: CheckSubrange
    b##0 := read($Heap, m#0, _module.Multi.y);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##2, $rhs##3 := Call$$_module.__default.SwapEm(a##0, b##0);
    // TrCallStmt: After ProcessCallStmt
    $Heap := update($Heap, $obj0, _module.Multi.x, $rhs##2);
    assume $IsGoodHeap($Heap);
    $Heap := update($Heap, $obj1, _module.Multi.y, $rhs##3);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(199,30)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(200,3)
    assert {:subsumption 0} m#0 != null;
    assume true;
    assert read($Heap, m#0, _module.Multi.y) == LitInt(12);
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(201,3)
    if (*)
    {
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(202,23)
        assert m#0 != m#0;
        assert m#0 != null;
        assume true;
        $obj0 := m#0;
        assert $_Frame[$obj0, _module.Multi.x];
        assert m#0 != null;
        assume true;
        $obj1 := m#0;
        assert $_Frame[$obj1, _module.Multi.x];
        // TrCallStmt: Adding lhs with type int
        // TrCallStmt: Adding lhs with type int
        // TrCallStmt: Before ProcessCallStmt
        assert m#0 != null;
        assume true;
        // ProcessCallStmt: CheckSubrange
        a##1_0 := read($Heap, m#0, _module.Multi.x);
        assert m#0 != null;
        assume true;
        // ProcessCallStmt: CheckSubrange
        b##1_0 := read($Heap, m#0, _module.Multi.y);
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call $rhs##1_0, $rhs##1_1 := Call$$_module.__default.SwapEm(a##1_0, b##1_0);
        // TrCallStmt: After ProcessCallStmt
        $Heap := update($Heap, $obj0, _module.Multi.x, $rhs##1_0);
        assume $IsGoodHeap($Heap);
        $Heap := update($Heap, $obj1, _module.Multi.x, $rhs##1_1);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(202,32)"} true;
    }
    else
    {
    }

    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(204,7)
    assert m#0 != null;
    assume true;
    assert $_Frame[m#0, _module.Multi.x];
    assume true;
    $rhs#3 := LitInt(30);
    $Heap := update($Heap, m#0, _module.Multi.x, $rhs#3);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(204,11)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(205,19)
    assume true;
    // TrCallStmt: Adding lhs with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert m#0 != null;
    assert (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) && $o == m#0 ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##4 := Call$$_module.Multi.IncX(m#0);
    // TrCallStmt: After ProcessCallStmt
    xx#0 := $rhs##4;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(205,20)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(206,3)
    assume true;
    assert xx#0 == LitInt(30);
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(207,16)
    assert m#0 != null;
    assume true;
    $obj0 := m#0;
    assert $_Frame[$obj0, _module.Multi.y];
    // TrCallStmt: Adding lhs with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert m#0 != null;
    assert (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) && $o == m#0 ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##5 := Call$$_module.Multi.IncX(m#0);
    // TrCallStmt: After ProcessCallStmt
    $Heap := update($Heap, $obj0, _module.Multi.y, $rhs##5);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(207,17)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(208,3)
    assert {:subsumption 0} m#0 != null;
    if (read($Heap, m#0, _module.Multi.y) == LitInt(31))
    {
        assert {:subsumption 0} m#0 != null;
    }

    assume true;
    assert {:subsumption 0} read($Heap, m#0, _module.Multi.y) == LitInt(31);
    assert {:subsumption 0} read($Heap, m#0, _module.Multi.x) == LitInt(32);
    assume read($Heap, m#0, _module.Multi.y) == LitInt(31)
       && read($Heap, m#0, _module.Multi.x) == LitInt(32);
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(209,16)
    assert m#0 != null;
    assume true;
    $obj0 := m#0;
    assert $_Frame[$obj0, _module.Multi.x];
    // TrCallStmt: Adding lhs with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert m#0 != null;
    assert (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) && $o == m#0 ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##6 := Call$$_module.Multi.IncX(m#0);
    // TrCallStmt: After ProcessCallStmt
    $Heap := update($Heap, $obj0, _module.Multi.x, $rhs##6);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(209,17)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(210,3)
    assert {:subsumption 0} m#0 != null;
    assume true;
    assert read($Heap, m#0, _module.Multi.x) == LitInt(32);
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(211,15)
    assume true;
    // TrCallStmt: Adding lhs with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert m#0 != null;
    assert (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) && $o == m#0 ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##7 := Call$$_module.Multi.IncX(m#0);
    // TrCallStmt: After ProcessCallStmt
    xx#0 := $rhs##7;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(211,16)"} true;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(212,3)
    if (*)
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(213,5)
        assume true;
        assert xx#0 == LitInt(33);
    }
    else
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(215,5)
        assume true;
        assert xx#0 == LitInt(32);
    }
}



procedure CheckWellformed$$_module.__default.SwapEm(a#0: int, b#0: int) returns (x#0: int, y#0: int);
  free requires 14 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.SwapEm(a#0: int, b#0: int) returns (x#0: int, y#0: int);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures x#0 == b#0;
  ensures y#0 == a#0;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.SwapEm(a#0: int, b#0: int) returns (x#0: int, y#0: int, $_reverifyPost: bool);
  free requires 14 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures x#0 == b#0;
  ensures y#0 == a#0;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.SwapEm(a#0: int, b#0: int) returns (x#0: int, y#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: int;
  var $rhs#1: int;

    // AddMethodImpl: SwapEm, Impl$$_module.__default.SwapEm
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(221,0): initial state"} true;
    $_reverifyPost := false;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(222,8)
    assume true;
    assume true;
    assume true;
    $rhs#0 := b#0;
    assume true;
    $rhs#1 := a#0;
    x#0 := $rhs#0;
    y#0 := $rhs#1;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(222,14)"} true;
}



// function declaration for _module._default.abs
function _module.__default.abs(a#0: int) : int;

function _module.__default.abs#canCall(a#0: int) : bool;

// consequence axiom for _module.__default.abs
axiom 26 <= $FunctionContextHeight
   ==> (forall a#0: int :: 
    { _module.__default.abs(a#0) } 
    _module.__default.abs#canCall(a#0) || 26 != $FunctionContextHeight ==> true);

function _module.__default.abs#requires(int) : bool;

// #requires axiom for _module.__default.abs
axiom (forall a#0: int :: 
  { _module.__default.abs#requires(a#0) } 
  _module.__default.abs#requires(a#0) == true);

// definition axiom for _module.__default.abs (revealed)
axiom 26 <= $FunctionContextHeight
   ==> (forall a#0: int :: 
    { _module.__default.abs(a#0) } 
    _module.__default.abs#canCall(a#0) || 26 != $FunctionContextHeight
       ==> _module.__default.abs(a#0) == (if a#0 <= LitInt(0) then 0 - a#0 else a#0));

// definition axiom for _module.__default.abs for all literals (revealed)
axiom 26 <= $FunctionContextHeight
   ==> (forall a#0: int :: 
    {:weight 3} { _module.__default.abs(LitInt(a#0)) } 
    _module.__default.abs#canCall(LitInt(a#0)) || 26 != $FunctionContextHeight
       ==> _module.__default.abs(LitInt(a#0))
         == (if LitInt(a#0) <= LitInt(0) then 0 - a#0 else a#0));

procedure CheckWellformed$$_module.__default.abs(a#0: int);
  free requires 26 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure CheckWellformed$$_module.__default.EuclideanTest(a#0: int, b#0: int);
  free requires 27 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.EuclideanTest(a#0: int, b#0: int);
  // user-defined preconditions
  requires b#0 != 0;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.EuclideanTest(a#0: int, b#0: int) returns ($_reverifyPost: bool);
  free requires 27 == $FunctionContextHeight;
  // user-defined preconditions
  requires b#0 != 0;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.EuclideanTest(a#0: int, b#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var q#0: int;
  var r#0: int;
  var $rhs#0: int;
  var $rhs#1: int;
  var ##a#0: int;

    // AddMethodImpl: EuclideanTest, Impl$$_module.__default.EuclideanTest
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(232,0): initial state"} true;
    $_reverifyPost := false;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(233,13)
    assume true;
    assume true;
    assert b#0 != 0;
    assume true;
    $rhs#0 := Div(a#0, b#0);
    assert b#0 != 0;
    assume true;
    $rhs#1 := Mod(a#0, b#0);
    q#0 := $rhs#0;
    r#0 := $rhs#1;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(233,27)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(234,4)
    if (LitInt(0) <= r#0)
    {
        ##a#0 := b#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##a#0, TInt, $Heap);
        assume _module.__default.abs#canCall(b#0);
    }

    assume LitInt(0) <= r#0 ==> _module.__default.abs#canCall(b#0);
    assert {:subsumption 0} LitInt(0) <= r#0;
    assert {:subsumption 0} r#0 < _module.__default.abs(b#0);
    assume LitInt(0) <= r#0 && r#0 < _module.__default.abs(b#0);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(235,4)
    assume true;
    assert a#0 == Mul(b#0, q#0) + r#0;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(236,4)
    assert {:subsumption 0} b#0 != 0;
    assert {:subsumption 0} b#0 != 0;
    assume true;
    assert Mul(Div(a#0, b#0), b#0) + Mod(a#0, b#0) == a#0;
}



procedure CheckWellformed$$_module.__default.havocInMultiassignment();
  free requires 28 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.havocInMultiassignment();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.havocInMultiassignment() returns ($_reverifyPost: bool);
  free requires 28 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.havocInMultiassignment() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var i#0: int where LitInt(0) <= i#0;
  var j#0: int where LitInt(0) <= j#0;
  var $rhs#0: int where LitInt(0) <= $rhs#0;
  var $rhs#1: int where LitInt(0) <= $rhs#1;

    // AddMethodImpl: havocInMultiassignment, Impl$$_module.__default.havocInMultiassignment
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(240,0): initial state"} true;
    $_reverifyPost := false;
    havoc i#0 /* where LitInt(0) <= i#0 */, j#0 /* where LitInt(0) <= j#0 */;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(242,9)
    assume true;
    assume true;
    havoc $rhs#0 /* where LitInt(0) <= $rhs#0 */;
    assume true;
    assert $Is(LitInt(3), Tclass._System.nat());
    $rhs#1 := LitInt(3);
    i#0 := $rhs#0;
    j#0 := $rhs#1;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(242,15)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(243,4)
    assume true;
    assert LitInt(0) <= i#0;
}



procedure CheckWellformed$$_module.__default.m();
  free requires 34 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.m();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.m() returns ($_reverifyPost: bool);
  free requires 34 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure CheckWellformed$$_module.__default.swap(a#0: ref
       where $Is(a#0, Tclass._System.array(TInt))
         && $IsAlloc(a#0, Tclass._System.array(TInt), $Heap), 
    i#0: int where LitInt(0) <= i#0, 
    j#0: int where LitInt(0) <= j#0);
  free requires 17 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.swap(a#0: ref, i#0: int, j#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: swap, CheckWellformed$$_module.__default.swap
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == a#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(252,7): initial state"} true;
    if (LitInt(0) <= i#0)
    {
        assert a#0 != null;
    }

    assume LitInt(0) <= i#0 && i#0 < _System.array.Length(a#0);
    if (LitInt(0) <= j#0)
    {
        assert a#0 != null;
    }

    assume LitInt(0) <= j#0 && j#0 < _System.array.Length(a#0);
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc)
         ==> $Heap[$o] == old($Heap)[$o] || $o == a#0);
    assume $HeapSucc(old($Heap), $Heap);
}



procedure Call$$_module.__default.swap(a#0: ref
       where $Is(a#0, Tclass._System.array(TInt))
         && $IsAlloc(a#0, Tclass._System.array(TInt), $Heap), 
    i#0: int where LitInt(0) <= i#0, 
    j#0: int where LitInt(0) <= j#0);
  // user-defined preconditions
  requires LitInt(0) <= i#0;
  requires i#0 < _System.array.Length(a#0);
  requires LitInt(0) <= j#0;
  requires j#0 < _System.array.Length(a#0);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == a#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.swap(a#0: ref
       where $Is(a#0, Tclass._System.array(TInt))
         && $IsAlloc(a#0, Tclass._System.array(TInt), $Heap), 
    i#0: int where LitInt(0) <= i#0, 
    j#0: int where LitInt(0) <= j#0)
   returns ($_reverifyPost: bool);
  free requires 17 == $FunctionContextHeight;
  // user-defined preconditions
  requires LitInt(0) <= i#0;
  requires i#0 < _System.array.Length(a#0);
  requires LitInt(0) <= j#0;
  requires j#0 < _System.array.Length(a#0);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == a#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.swap(a#0: ref, i#0: int, j#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $obj0: ref;
  var $index0: Field Box;
  var $obj1: ref;
  var $index1: Field Box;
  var $rhs#0: int;
  var $rhs#1: int;

    // AddMethodImpl: swap, Impl$$_module.__default.swap
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == a#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(255,0): initial state"} true;
    $_reverifyPost := false;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(256,14)
    assert a#0 != null;
    assert 0 <= i#0 && i#0 < _System.array.Length(a#0);
    assume true;
    $obj0 := a#0;
    $index0 := IndexField(i#0);
    assert $_Frame[$obj0, $index0];
    assert a#0 != null;
    assert 0 <= j#0 && j#0 < _System.array.Length(a#0);
    assume true;
    $obj1 := a#0;
    $index1 := IndexField(j#0);
    assert $_Frame[$obj1, $index1];
    assert a#0 != null;
    assert 0 <= j#0 && j#0 < _System.array.Length(a#0);
    assume true;
    $rhs#0 := $Unbox(read($Heap, a#0, IndexField(j#0))): int;
    assert a#0 != null;
    assert 0 <= i#0 && i#0 < _System.array.Length(a#0);
    assume true;
    $rhs#1 := $Unbox(read($Heap, a#0, IndexField(i#0))): int;
    assert a#0 != a#0 || j#0 != i#0 || $Box($rhs#1) == $Box($rhs#0);
    $Heap := update($Heap, $obj0, $index0, $Box($rhs#0));
    assume $IsGoodHeap($Heap);
    $Heap := update($Heap, $obj1, $index1, $Box($rhs#1));
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(256,26)"} true;
}



procedure CheckWellformed$$_module.__default.notQuiteSwap(c#0: ref
       where $Is(c#0, Tclass._module.CC()) && $IsAlloc(c#0, Tclass._module.CC(), $Heap), 
    d#0: ref
       where $Is(d#0, Tclass._module.CC()) && $IsAlloc(d#0, Tclass._module.CC(), $Heap));
  free requires 19 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.notQuiteSwap(c#0: ref
       where $Is(c#0, Tclass._module.CC()) && $IsAlloc(c#0, Tclass._module.CC(), $Heap), 
    d#0: ref
       where $Is(d#0, Tclass._module.CC()) && $IsAlloc(d#0, Tclass._module.CC(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == c#0 || $o == d#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.notQuiteSwap(c#0: ref
       where $Is(c#0, Tclass._module.CC()) && $IsAlloc(c#0, Tclass._module.CC(), $Heap), 
    d#0: ref
       where $Is(d#0, Tclass._module.CC()) && $IsAlloc(d#0, Tclass._module.CC(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 19 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == c#0 || $o == d#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.notQuiteSwap(c#0: ref, d#0: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $obj0: ref;
  var $obj1: ref;
  var $rhs#0: int;
  var $rhs#1: int;

    // AddMethodImpl: notQuiteSwap, Impl$$_module.__default.notQuiteSwap
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == c#0 || $o == d#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(266,0): initial state"} true;
    $_reverifyPost := false;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(267,12)
    assert c#0 != null;
    assume true;
    $obj0 := c#0;
    assert $_Frame[$obj0, _module.CC.x];
    assert d#0 != null;
    assume true;
    $obj1 := d#0;
    assert $_Frame[$obj1, _module.CC.x];
    assert c#0 != null;
    assume true;
    $rhs#0 := read($Heap, c#0, _module.CC.x);
    assert c#0 != null;
    assume true;
    $rhs#1 := read($Heap, c#0, _module.CC.x);
    assert d#0 != c#0 || $rhs#1 == $rhs#0;
    $Heap := update($Heap, $obj0, _module.CC.x, $rhs#0);
    assume $IsGoodHeap($Heap);
    $Heap := update($Heap, $obj1, _module.CC.x, $rhs#1);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(267,22)"} true;
}



procedure CheckWellformed$$_module.__default.notQuiteSwap2(c#0: ref
       where $Is(c#0, Tclass._module.CC()) && $IsAlloc(c#0, Tclass._module.CC(), $Heap), 
    d#0: ref
       where $Is(d#0, Tclass._module.CC()) && $IsAlloc(d#0, Tclass._module.CC(), $Heap));
  free requires 20 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.notQuiteSwap2(c#0: ref
       where $Is(c#0, Tclass._module.CC()) && $IsAlloc(c#0, Tclass._module.CC(), $Heap), 
    d#0: ref
       where $Is(d#0, Tclass._module.CC()) && $IsAlloc(d#0, Tclass._module.CC(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == c#0 || $o == d#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.notQuiteSwap2(c#0: ref
       where $Is(c#0, Tclass._module.CC()) && $IsAlloc(c#0, Tclass._module.CC(), $Heap), 
    d#0: ref
       where $Is(d#0, Tclass._module.CC()) && $IsAlloc(d#0, Tclass._module.CC(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 20 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == c#0 || $o == d#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.notQuiteSwap2(c#0: ref, d#0: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $obj0: ref;
  var $obj1: ref;
  var $rhs#0: int;
  var $rhs#1: int;

    // AddMethodImpl: notQuiteSwap2, Impl$$_module.__default.notQuiteSwap2
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == c#0 || $o == d#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(272,0): initial state"} true;
    $_reverifyPost := false;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(273,12)
    assert c#0 != null;
    assume true;
    $obj0 := c#0;
    assert $_Frame[$obj0, _module.CC.x];
    assert d#0 != null;
    assume true;
    $obj1 := d#0;
    assert $_Frame[$obj1, _module.CC.x];
    assert d#0 != null;
    assume true;
    $rhs#0 := read($Heap, d#0, _module.CC.x);
    assert c#0 != null;
    assume true;
    $rhs#1 := read($Heap, c#0, _module.CC.y);
    assert d#0 != c#0 || $rhs#1 == $rhs#0;
    $Heap := update($Heap, $obj0, _module.CC.x, $rhs#0);
    assume $IsGoodHeap($Heap);
    $Heap := update($Heap, $obj1, _module.CC.x, $rhs#1);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(273,22)"} true;
}



procedure CheckWellformed$$_module.__default.OKNowIt_ksSwapAgain(c#0: ref
       where $Is(c#0, Tclass._module.CC()) && $IsAlloc(c#0, Tclass._module.CC(), $Heap), 
    d#0: ref
       where $Is(d#0, Tclass._module.CC()) && $IsAlloc(d#0, Tclass._module.CC(), $Heap));
  free requires 21 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.OKNowIt_ksSwapAgain(c#0: ref
       where $Is(c#0, Tclass._module.CC()) && $IsAlloc(c#0, Tclass._module.CC(), $Heap), 
    d#0: ref
       where $Is(d#0, Tclass._module.CC()) && $IsAlloc(d#0, Tclass._module.CC(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == c#0 || $o == d#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.OKNowIt_ksSwapAgain(c#0: ref
       where $Is(c#0, Tclass._module.CC()) && $IsAlloc(c#0, Tclass._module.CC(), $Heap), 
    d#0: ref
       where $Is(d#0, Tclass._module.CC()) && $IsAlloc(d#0, Tclass._module.CC(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 21 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == c#0 || $o == d#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.OKNowIt_ksSwapAgain(c#0: ref, d#0: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $obj0: ref;
  var $obj1: ref;
  var $rhs#0: int;
  var $rhs#1: int;

    // AddMethodImpl: OKNowIt'sSwapAgain, Impl$$_module.__default.OKNowIt_ksSwapAgain
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == c#0 || $o == d#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(278,0): initial state"} true;
    $_reverifyPost := false;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(279,12)
    assert c#0 != null;
    assume true;
    $obj0 := c#0;
    assert $_Frame[$obj0, _module.CC.x];
    assert d#0 != null;
    assume true;
    $obj1 := d#0;
    assert $_Frame[$obj1, _module.CC.x];
    assert d#0 != null;
    assume true;
    $rhs#0 := read($Heap, d#0, _module.CC.x);
    assert c#0 != null;
    assume true;
    $rhs#1 := read($Heap, c#0, _module.CC.x);
    assert d#0 != c#0 || $rhs#1 == $rhs#0;
    $Heap := update($Heap, $obj0, _module.CC.x, $rhs#0);
    assume $IsGoodHeap($Heap);
    $Heap := update($Heap, $obj1, _module.CC.x, $rhs#1);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(279,22)"} true;
}



procedure CheckWellformed$$_module.__default.notQuiteSwap3(c#0: ref
       where $Is(c#0, Tclass._module.CC()) && $IsAlloc(c#0, Tclass._module.CC(), $Heap), 
    d#0: ref
       where $Is(d#0, Tclass._module.CC()) && $IsAlloc(d#0, Tclass._module.CC(), $Heap));
  free requires 22 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.notQuiteSwap3(c#0: ref
       where $Is(c#0, Tclass._module.CC()) && $IsAlloc(c#0, Tclass._module.CC(), $Heap), 
    d#0: ref
       where $Is(d#0, Tclass._module.CC()) && $IsAlloc(d#0, Tclass._module.CC(), $Heap));
  // user-defined preconditions
  requires c#0 != d#0;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == c#0 || $o == d#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.notQuiteSwap3(c#0: ref
       where $Is(c#0, Tclass._module.CC()) && $IsAlloc(c#0, Tclass._module.CC(), $Heap), 
    d#0: ref
       where $Is(d#0, Tclass._module.CC()) && $IsAlloc(d#0, Tclass._module.CC(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 22 == $FunctionContextHeight;
  // user-defined preconditions
  requires c#0 != d#0;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == c#0 || $o == d#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.notQuiteSwap3(c#0: ref, d#0: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $obj0: ref;
  var $obj1: ref;
  var $rhs#0: int;
  var $rhs#1: int;
  var $rhs#2: int;
  var $rhs#3: int;

    // AddMethodImpl: notQuiteSwap3, Impl$$_module.__default.notQuiteSwap3
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == c#0 || $o == d#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(285,0): initial state"} true;
    $_reverifyPost := false;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(286,12)
    assert c#0 != null;
    assume true;
    $obj0 := c#0;
    assert $_Frame[$obj0, _module.CC.x];
    assert d#0 != null;
    assume true;
    $obj1 := d#0;
    assert $_Frame[$obj1, _module.CC.x];
    assume true;
    $rhs#0 := LitInt(4);
    assert c#0 != null;
    assume true;
    $rhs#1 := read($Heap, c#0, _module.CC.y);
    assert d#0 != c#0 || $rhs#1 == $rhs#0;
    $Heap := update($Heap, $obj0, _module.CC.x, $rhs#0);
    assume $IsGoodHeap($Heap);
    $Heap := update($Heap, $obj1, _module.CC.x, $rhs#1);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(286,20)"} true;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(287,12)
    assert c#0 != null;
    assume true;
    $obj0 := c#0;
    assert $_Frame[$obj0, _module.CC.x];
    assert c#0 != null;
    assume true;
    $obj1 := c#0;
    assert $_Frame[$obj1, _module.CC.y];
    assume true;
    $rhs#2 := LitInt(3);
    assert c#0 != null;
    assume true;
    $rhs#3 := read($Heap, c#0, _module.CC.y);
    $Heap := update($Heap, $obj0, _module.CC.x, $rhs#2);
    assume $IsGoodHeap($Heap);
    $Heap := update($Heap, $obj1, _module.CC.y, $rhs#3);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(287,20)"} true;
}



procedure CheckWellformed$$_module.__default.InlineMultisetFormingExpr(s#0: Seq Box where $Is(s#0, TSeq(TInt)) && $IsAlloc(s#0, TSeq(TInt), $Heap));
  free requires 30 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.InlineMultisetFormingExpr(s#0: Seq Box where $Is(s#0, TSeq(TInt)) && $IsAlloc(s#0, TSeq(TInt), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.MSFE#canCall(s#0);
  free ensures _module.__default.MSFE#canCall(s#0)
     && 
    _module.__default.MSFE(s#0)
     && MultiSet#Equal(MultiSet#FromSeq(s#0), MultiSet#FromSeq(s#0));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



// function declaration for _module._default.MSFE
function _module.__default.MSFE(s#0: Seq Box) : bool;

function _module.__default.MSFE#canCall(s#0: Seq Box) : bool;

// consequence axiom for _module.__default.MSFE
axiom 29 <= $FunctionContextHeight
   ==> (forall s#0: Seq Box :: 
    { _module.__default.MSFE(s#0) } 
    _module.__default.MSFE#canCall(s#0)
         || (29 != $FunctionContextHeight && $Is(s#0, TSeq(TInt)))
       ==> true);

function _module.__default.MSFE#requires(Seq Box) : bool;

// #requires axiom for _module.__default.MSFE
axiom (forall s#0: Seq Box :: 
  { _module.__default.MSFE#requires(s#0) } 
  $Is(s#0, TSeq(TInt)) ==> _module.__default.MSFE#requires(s#0) == true);

// definition axiom for _module.__default.MSFE (revealed)
axiom 29 <= $FunctionContextHeight
   ==> (forall s#0: Seq Box :: 
    { _module.__default.MSFE(s#0) } 
    _module.__default.MSFE#canCall(s#0)
         || (29 != $FunctionContextHeight && $Is(s#0, TSeq(TInt)))
       ==> _module.__default.MSFE(s#0)
         == MultiSet#Equal(MultiSet#FromSeq(s#0), MultiSet#FromSeq(s#0)));

// definition axiom for _module.__default.MSFE for all literals (revealed)
axiom 29 <= $FunctionContextHeight
   ==> (forall s#0: Seq Box :: 
    {:weight 3} { _module.__default.MSFE(Lit(s#0)) } 
    _module.__default.MSFE#canCall(Lit(s#0))
         || (29 != $FunctionContextHeight && $Is(s#0, TSeq(TInt)))
       ==> _module.__default.MSFE(Lit(s#0))
         == MultiSet#Equal(MultiSet#FromSeq(Lit(s#0)), MultiSet#FromSeq(Lit(s#0))));

procedure CheckWellformed$$_module.__default.MSFE(s#0: Seq Box where $Is(s#0, TSeq(TInt)));
  free requires 29 == $FunctionContextHeight;
  modifies $Heap, $Tick;



// function declaration for _module._default.CoPredTypeCheck
function _module.__default.CoPredTypeCheck(n#0: int) : bool;

function _module.__default.CoPredTypeCheck#canCall(n#0: int) : bool;

// consequence axiom for _module.__default.CoPredTypeCheck
axiom 0 <= $FunctionContextHeight
   ==> (forall n#0: int :: 
    { _module.__default.CoPredTypeCheck(n#0) } 
    _module.__default.CoPredTypeCheck#canCall(n#0)
         || (0 != $FunctionContextHeight && n#0 != 0)
       ==> true);

function _module.__default.CoPredTypeCheck#requires(int) : bool;

// #requires axiom for _module.__default.CoPredTypeCheck
axiom (forall n#0: int :: 
  { _module.__default.CoPredTypeCheck#requires(n#0) } 
  _module.__default.CoPredTypeCheck#requires(n#0) == (n#0 != 0));

// 1st prefix predicate axiom for _module.__default.CoPredTypeCheck_h
axiom 1 <= $FunctionContextHeight
   ==> (forall n#0: int :: 
    { _module.__default.CoPredTypeCheck(n#0) } 
    _module.__default.CoPredTypeCheck(n#0)
       ==> (forall _k#0: Box :: 
        { _module.__default.CoPredTypeCheck_h(_k#0, n#0) } 
        _module.__default.CoPredTypeCheck_h(_k#0, n#0)));

// 2nd prefix predicate axiom
axiom 1 <= $FunctionContextHeight
   ==> (forall n#0: int :: 
    { _module.__default.CoPredTypeCheck(n#0) } 
    (forall _k#0: Box :: 
        { _module.__default.CoPredTypeCheck_h(_k#0, n#0) } 
        _module.__default.CoPredTypeCheck_h(_k#0, n#0))
       ==> _module.__default.CoPredTypeCheck(n#0));

// 3rd prefix predicate axiom
axiom 1 <= $FunctionContextHeight
   ==> (forall n#0: int, _k#0: Box :: 
    { _module.__default.CoPredTypeCheck_h(_k#0, n#0) } 
    _k#0 == ORD#FromNat(0) ==> _module.__default.CoPredTypeCheck_h(_k#0, n#0));

procedure CheckWellformed$$_module.__default.CoPredTypeCheck(n#0: int);
  free requires 0 == $FunctionContextHeight;
  modifies $Heap, $Tick;



// function declaration for _module._default.CoPredTypeCheck#
function _module.__default.CoPredTypeCheck_h(_k#0: Box, n#0: int) : bool;

function _module.__default.CoPredTypeCheck_h#canCall(_k#0: Box, n#0: int) : bool;

// consequence axiom for _module.__default.CoPredTypeCheck_h
axiom 1 <= $FunctionContextHeight
   ==> (forall _k#0: Box, n#0: int :: 
    { _module.__default.CoPredTypeCheck_h(_k#0, n#0) } 
    _module.__default.CoPredTypeCheck_h#canCall(_k#0, n#0)
         || (1 != $FunctionContextHeight && n#0 != 0)
       ==> true);

function _module.__default.CoPredTypeCheck_h#requires(Box, int) : bool;

// #requires axiom for _module.__default.CoPredTypeCheck_h
axiom (forall _k#0: Box, n#0: int :: 
  { _module.__default.CoPredTypeCheck_h#requires(_k#0, n#0) } 
  _module.__default.CoPredTypeCheck_h#requires(_k#0, n#0) == (n#0 != 0));

procedure CheckWellformed$$_module.__default.HexTest();
  free requires 35 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.HexTest();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.HexTest() returns ($_reverifyPost: bool);
  free requires 35 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.HexTest() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var first16lower#0: Seq Box
     where $Is(first16lower#0, TSeq(TInt)) && $IsAlloc(first16lower#0, TSeq(TInt), $Heap);
  var first16upper#0: Seq Box
     where $Is(first16upper#0, TSeq(TInt)) && $IsAlloc(first16upper#0, TSeq(TInt), $Heap);
  var i#0: int;
  var i#2: int;
  var randomHex#0: Seq Box
     where $Is(randomHex#0, TSeq(TInt)) && $IsAlloc(randomHex#0, TSeq(TInt), $Heap);
  var randomDec#0: Seq Box
     where $Is(randomDec#0, TSeq(TInt)) && $IsAlloc(randomDec#0, TSeq(TInt), $Heap);
  var i#4: int;

    // AddMethodImpl: HexTest, Impl$$_module.__default.HexTest
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(421,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(422,20)
    assume true;
    assume true;
    first16lower#0 := Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0))), $Box(LitInt(1))), 
                                  $Box(LitInt(2))), 
                                $Box(LitInt(3))), 
                              $Box(LitInt(4))), 
                            $Box(LitInt(5))), 
                          $Box(LitInt(6))), 
                        $Box(LitInt(7))), 
                      $Box(LitInt(8))), 
                    $Box(LitInt(9))), 
                  $Box(LitInt(10))), 
                $Box(LitInt(11))), 
              $Box(LitInt(12))), 
            $Box(LitInt(13))), 
          $Box(LitInt(14))), 
        $Box(LitInt(15))));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(422,104)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(423,20)
    assume true;
    assume true;
    first16upper#0 := Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0))), $Box(LitInt(1))), 
                                  $Box(LitInt(2))), 
                                $Box(LitInt(3))), 
                              $Box(LitInt(4))), 
                            $Box(LitInt(5))), 
                          $Box(LitInt(6))), 
                        $Box(LitInt(7))), 
                      $Box(LitInt(8))), 
                    $Box(LitInt(9))), 
                  $Box(LitInt(10))), 
                $Box(LitInt(11))), 
              $Box(LitInt(12))), 
            $Box(LitInt(13))), 
          $Box(LitInt(14))), 
        $Box(LitInt(15))));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(423,104)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(424,3)
    // Begin Comprehension WF check
    havoc i#0;
    if (true)
    {
        if (LitInt(0) <= i#0)
        {
        }

        if (LitInt(0) <= i#0 && i#0 < Seq#Length(first16lower#0))
        {
            assert {:subsumption 0} 0 <= i#0 && i#0 < Seq#Length(first16lower#0);
        }
    }

    // End Comprehension WF check
    assume true;
    assert (forall i#1: int :: 
      { $Unbox(Seq#Index(first16lower#0, i#1)): int } 
      true
         ==> 
        LitInt(0) <= i#1 && i#1 < Seq#Length(first16lower#0)
         ==> $Unbox(Seq#Index(first16lower#0, i#1)): int == i#1);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(425,3)
    // Begin Comprehension WF check
    havoc i#2;
    if (true)
    {
        if (LitInt(0) <= i#2)
        {
        }

        if (LitInt(0) <= i#2 && i#2 < Seq#Length(first16upper#0))
        {
            assert {:subsumption 0} 0 <= i#2 && i#2 < Seq#Length(first16upper#0);
        }
    }

    // End Comprehension WF check
    assume true;
    assert (forall i#3: int :: 
      { $Unbox(Seq#Index(first16upper#0, i#3)): int } 
      true
         ==> 
        LitInt(0) <= i#3 && i#3 < Seq#Length(first16upper#0)
         ==> $Unbox(Seq#Index(first16upper#0, i#3)): int == i#3);
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(427,17)
    assume true;
    assume true;
    randomHex#0 := Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(3477362930))), 
                                                                                                                                                                                                            $Box(LitInt(2589744047))), 
                                                                                                                                                                                                          $Box(LitInt(648457174))), 
                                                                                                                                                                                                        $Box(LitInt(15415603))), 
                                                                                                                                                                                                      $Box(LitInt(2435044047))), 
                                                                                                                                                                                                    $Box(LitInt(3187933185))), 
                                                                                                                                                                                                  $Box(LitInt(1523595514))), 
                                                                                                                                                                                                $Box(LitInt(3344275366))), 
                                                                                                                                                                                              $Box(LitInt(2096636327))), 
                                                                                                                                                                                            $Box(LitInt(3455038999))), 
                                                                                                                                                                                          $Box(LitInt(1216993640))), 
                                                                                                                                                                                        $Box(LitInt(2959051114))), 
                                                                                                                                                                                      $Box(LitInt(1974570418))), 
                                                                                                                                                                                    $Box(LitInt(3403117488))), 
                                                                                                                                                                                  $Box(LitInt(3632553720))), 
                                                                                                                                                                                $Box(LitInt(2398769469))), 
                                                                                                                                                                              $Box(LitInt(2394608417))), 
                                                                                                                                                                            $Box(LitInt(2621464030))), 
                                                                                                                                                                          $Box(LitInt(246013718))), 
                                                                                                                                                                        $Box(LitInt(3444056938))), 
                                                                                                                                                                      $Box(LitInt(2322109135))), 
                                                                                                                                                                    $Box(LitInt(2579433337))), 
                                                                                                                                                                  $Box(LitInt(3931300104))), 
                                                                                                                                                                $Box(LitInt(58310470))), 
                                                                                                                                                              $Box(LitInt(1628242745))), 
                                                                                                                                                            $Box(LitInt(3678616519))), 
                                                                                                                                                          $Box(LitInt(3914072686))), 
                                                                                                                                                        $Box(LitInt(4229460828))), 
                                                                                                                                                      $Box(LitInt(1784659379))), 
                                                                                                                                                    $Box(LitInt(4255523577))), 
                                                                                                                                                  $Box(LitInt(1644485497))), 
                                                                                                                                                $Box(LitInt(1376063380))), 
                                                                                                                                              $Box(LitInt(1522390013))), 
                                                                                                                                            $Box(LitInt(2132606175))), 
                                                                                                                                          $Box(LitInt(3967586431))), 
                                                                                                                                        $Box(LitInt(4198605885))), 
                                                                                                                                      $Box(LitInt(50066004))), 
                                                                                                                                    $Box(LitInt(2658563354))), 
                                                                                                                                  $Box(LitInt(4149411884))), 
                                                                                                                                $Box(LitInt(2520109921))), 
                                                                                                                              $Box(LitInt(3123451110))), 
                                                                                                                            $Box(LitInt(1096590075))), 
                                                                                                                          $Box(LitInt(2759389036))), 
                                                                                                                        $Box(LitInt(2139150316))), 
                                                                                                                      $Box(LitInt(3034416536))), 
                                                                                                                    $Box(LitInt(113569056))), 
                                                                                                                  $Box(LitInt(3217684480))), 
                                                                                                                $Box(LitInt(1777952605))), 
                                                                                                              $Box(LitInt(1930266087))), 
                                                                                                            $Box(LitInt(806691985))), 
                                                                                                          $Box(LitInt(36091805))), 
                                                                                                        $Box(LitInt(1820297564))), 
                                                                                                      $Box(LitInt(1330016162))), 
                                                                                                    $Box(LitInt(776406857))), 
                                                                                                  $Box(LitInt(2897015342))), 
                                                                                                $Box(LitInt(1163573365))), 
                                                                                              $Box(LitInt(2693955015))), 
                                                                                            $Box(LitInt(3799815127))), 
                                                                                          $Box(LitInt(1326665135))), 
                                                                                        $Box(LitInt(3536241040))), 
                                                                                      $Box(LitInt(3378447726))), 
                                                                                    $Box(LitInt(1163165151))), 
                                                                                  $Box(LitInt(1784424295))), 
                                                                                $Box(LitInt(2915391749))), 
                                                                              $Box(LitInt(3319144829))), 
                                                                            $Box(LitInt(1256473918))), 
                                                                          $Box(LitInt(3188839385))), 
                                                                        $Box(LitInt(865831700))), 
                                                                      $Box(LitInt(3868161393))), 
                                                                    $Box(LitInt(4113045917))), 
                                                                  $Box(LitInt(241438432))), 
                                                                $Box(LitInt(2675007811))), 
                                                              $Box(LitInt(354465647))), 
                                                            $Box(LitInt(2080258281))), 
                                                          $Box(LitInt(2351471473))), 
                                                        $Box(LitInt(1736439093))), 
                                                      $Box(LitInt(196693838))), 
                                                    $Box(LitInt(4215372800))), 
                                                  $Box(LitInt(2714419258))), 
                                                $Box(LitInt(1581046514))), 
                                              $Box(LitInt(1981216564))), 
                                            $Box(LitInt(3042395387))), 
                                          $Box(LitInt(660877099))), 
                                        $Box(LitInt(2707539070))), 
                                      $Box(LitInt(3217899519))), 
                                    $Box(LitInt(2788029817))), 
                                  $Box(LitInt(1050875824))), 
                                $Box(LitInt(3362808767))), 
                              $Box(LitInt(3721613))), 
                            $Box(LitInt(2510678132))), 
                          $Box(LitInt(1993876726))), 
                        $Box(LitInt(409501246))), 
                      $Box(LitInt(1273417770))), 
                    $Box(LitInt(741130572))), 
                  $Box(LitInt(1855051115))), 
                $Box(LitInt(1994570544))), 
              $Box(LitInt(3448107468))), 
            $Box(LitInt(1645859758))), 
          $Box(LitInt(3193559252))), 
        $Box(LitInt(3636919031))));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(435,69)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(436,17)
    assume true;
    assume true;
    randomDec#0 := Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(3477362930))), 
                                                                                                                                                                                                            $Box(LitInt(2589744047))), 
                                                                                                                                                                                                          $Box(LitInt(648457174))), 
                                                                                                                                                                                                        $Box(LitInt(15415603))), 
                                                                                                                                                                                                      $Box(LitInt(2435044047))), 
                                                                                                                                                                                                    $Box(LitInt(3187933185))), 
                                                                                                                                                                                                  $Box(LitInt(1523595514))), 
                                                                                                                                                                                                $Box(LitInt(3344275366))), 
                                                                                                                                                                                              $Box(LitInt(2096636327))), 
                                                                                                                                                                                            $Box(LitInt(3455038999))), 
                                                                                                                                                                                          $Box(LitInt(1216993640))), 
                                                                                                                                                                                        $Box(LitInt(2959051114))), 
                                                                                                                                                                                      $Box(LitInt(1974570418))), 
                                                                                                                                                                                    $Box(LitInt(3403117488))), 
                                                                                                                                                                                  $Box(LitInt(3632553720))), 
                                                                                                                                                                                $Box(LitInt(2398769469))), 
                                                                                                                                                                              $Box(LitInt(2394608417))), 
                                                                                                                                                                            $Box(LitInt(2621464030))), 
                                                                                                                                                                          $Box(LitInt(246013718))), 
                                                                                                                                                                        $Box(LitInt(3444056938))), 
                                                                                                                                                                      $Box(LitInt(2322109135))), 
                                                                                                                                                                    $Box(LitInt(2579433337))), 
                                                                                                                                                                  $Box(LitInt(3931300104))), 
                                                                                                                                                                $Box(LitInt(58310470))), 
                                                                                                                                                              $Box(LitInt(1628242745))), 
                                                                                                                                                            $Box(LitInt(3678616519))), 
                                                                                                                                                          $Box(LitInt(3914072686))), 
                                                                                                                                                        $Box(LitInt(4229460828))), 
                                                                                                                                                      $Box(LitInt(1784659379))), 
                                                                                                                                                    $Box(LitInt(4255523577))), 
                                                                                                                                                  $Box(LitInt(1644485497))), 
                                                                                                                                                $Box(LitInt(1376063380))), 
                                                                                                                                              $Box(LitInt(1522390013))), 
                                                                                                                                            $Box(LitInt(2132606175))), 
                                                                                                                                          $Box(LitInt(3967586431))), 
                                                                                                                                        $Box(LitInt(4198605885))), 
                                                                                                                                      $Box(LitInt(50066004))), 
                                                                                                                                    $Box(LitInt(2658563354))), 
                                                                                                                                  $Box(LitInt(4149411884))), 
                                                                                                                                $Box(LitInt(2520109921))), 
                                                                                                                              $Box(LitInt(3123451110))), 
                                                                                                                            $Box(LitInt(1096590075))), 
                                                                                                                          $Box(LitInt(2759389036))), 
                                                                                                                        $Box(LitInt(2139150316))), 
                                                                                                                      $Box(LitInt(3034416536))), 
                                                                                                                    $Box(LitInt(113569056))), 
                                                                                                                  $Box(LitInt(3217684480))), 
                                                                                                                $Box(LitInt(1777952605))), 
                                                                                                              $Box(LitInt(1930266087))), 
                                                                                                            $Box(LitInt(806691985))), 
                                                                                                          $Box(LitInt(36091805))), 
                                                                                                        $Box(LitInt(1820297564))), 
                                                                                                      $Box(LitInt(1330016162))), 
                                                                                                    $Box(LitInt(776406857))), 
                                                                                                  $Box(LitInt(2897015342))), 
                                                                                                $Box(LitInt(1163573365))), 
                                                                                              $Box(LitInt(2693955015))), 
                                                                                            $Box(LitInt(3799815127))), 
                                                                                          $Box(LitInt(1326665135))), 
                                                                                        $Box(LitInt(3536241040))), 
                                                                                      $Box(LitInt(3378447726))), 
                                                                                    $Box(LitInt(1163165151))), 
                                                                                  $Box(LitInt(1784424295))), 
                                                                                $Box(LitInt(2915391749))), 
                                                                              $Box(LitInt(3319144829))), 
                                                                            $Box(LitInt(1256473918))), 
                                                                          $Box(LitInt(3188839385))), 
                                                                        $Box(LitInt(865831700))), 
                                                                      $Box(LitInt(3868161393))), 
                                                                    $Box(LitInt(4113045917))), 
                                                                  $Box(LitInt(241438432))), 
                                                                $Box(LitInt(2675007811))), 
                                                              $Box(LitInt(354465647))), 
                                                            $Box(LitInt(2080258281))), 
                                                          $Box(LitInt(2351471473))), 
                                                        $Box(LitInt(1736439093))), 
                                                      $Box(LitInt(196693838))), 
                                                    $Box(LitInt(4215372800))), 
                                                  $Box(LitInt(2714419258))), 
                                                $Box(LitInt(1581046514))), 
                                              $Box(LitInt(1981216564))), 
                                            $Box(LitInt(3042395387))), 
                                          $Box(LitInt(660877099))), 
                                        $Box(LitInt(2707539070))), 
                                      $Box(LitInt(3217899519))), 
                                    $Box(LitInt(2788029817))), 
                                  $Box(LitInt(1050875824))), 
                                $Box(LitInt(3362808767))), 
                              $Box(LitInt(3721613))), 
                            $Box(LitInt(2510678132))), 
                          $Box(LitInt(1993876726))), 
                        $Box(LitInt(409501246))), 
                      $Box(LitInt(1273417770))), 
                    $Box(LitInt(741130572))), 
                  $Box(LitInt(1855051115))), 
                $Box(LitInt(1994570544))), 
              $Box(LitInt(3448107468))), 
            $Box(LitInt(1645859758))), 
          $Box(LitInt(3193559252))), 
        $Box(LitInt(3636919031))));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(444,70)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(445,3)
    // Begin Comprehension WF check
    havoc i#4;
    if (true)
    {
        if (LitInt(0) <= i#4)
        {
        }

        if (LitInt(0) <= i#4 && i#4 < Seq#Length(randomHex#0))
        {
            assert {:subsumption 0} 0 <= i#4 && i#4 < Seq#Length(randomHex#0);
            assert {:subsumption 0} 0 <= i#4 && i#4 < Seq#Length(randomDec#0);
        }
    }

    // End Comprehension WF check
    assume true;
    assert (forall i#5: int :: 
      { $Unbox(Seq#Index(randomDec#0, i#5)): int } 
        { $Unbox(Seq#Index(randomHex#0, i#5)): int } 
      true
         ==> 
        LitInt(0) <= i#5 && i#5 < Seq#Length(randomHex#0)
         ==> $Unbox(Seq#Index(randomHex#0, i#5)): int
           == $Unbox(Seq#Index(randomDec#0, i#5)): int);
}



procedure {:selective_checking} CheckWellformed$$_module.__default.MySelectiveChecking0(x#0: int, y#0: int, z#0: int);
  free requires 36 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:selective_checking} Call$$_module.__default.MySelectiveChecking0(x#0: int, y#0: int, z#0: int);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure {:selective_checking} Impl$$_module.__default.MySelectiveChecking0(x#0: int, y#0: int, z#0: int) returns ($_reverifyPost: bool);
  free requires 36 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation {:selective_checking} Impl$$_module.__default.MySelectiveChecking0(x#0: int, y#0: int, z#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: MySelectiveChecking0, Impl$$_module.__default.MySelectiveChecking0
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(453,0): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(454,3)
    if (*)
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(456,5)
        assume true;
        assert y#0 + 129 == z#0;
    }
    else
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(458,5)
        assume true;
        assert x#0 < y#0;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(459,5)
        assume true;
        assert y#0 < z#0;
        // ----- assume statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(460,5)
        assume true;
        assume {:start_checking_here} true;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(461,5)
        assume true;
        assert x#0 < z#0;
    }

    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(463,3)
    assume true;
    assert x#0 < z#0;
}



procedure {:selective_checking} CheckWellformed$$_module.__default.MySelectiveChecking1(x#0: int, y#0: int, z#0: int);
  free requires 37 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:selective_checking} Call$$_module.__default.MySelectiveChecking1(x#0: int, y#0: int, z#0: int);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure {:selective_checking} Impl$$_module.__default.MySelectiveChecking1(x#0: int, y#0: int, z#0: int) returns ($_reverifyPost: bool);
  free requires 37 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation {:selective_checking} Impl$$_module.__default.MySelectiveChecking1(x#0: int, y#0: int, z#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: MySelectiveChecking1, Impl$$_module.__default.MySelectiveChecking1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(466,0): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(467,3)
    if (*)
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(469,5)
        assume true;
        assert y#0 + 129 == z#0;
    }
    else
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(471,5)
        assume true;
        assert x#0 < y#0;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(472,5)
        assume true;
        assert y#0 < z#0;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(473,5)
        assume true;
        assert {:start_checking_here} true;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(474,5)
        assume true;
        assert x#0 + 10 < z#0;
    }

    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Basics.dfy(476,3)
    assume true;
    assert x#0 < z#0;
}



const unique class.SetCardinality.__default: ClassName;

function Tclass.SetCardinality.__default() : Ty;

const unique Tagclass.SetCardinality.__default: TyTag;

// Tclass.SetCardinality.__default Tag
axiom Tag(Tclass.SetCardinality.__default()) == Tagclass.SetCardinality.__default
   && TagFamily(Tclass.SetCardinality.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.SetCardinality.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.SetCardinality.__default()) } 
  $IsBox(bx, Tclass.SetCardinality.__default())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.SetCardinality.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.SetCardinality.__default()) } 
  $Is($o, Tclass.SetCardinality.__default())
     <==> $o == null || dtype($o) == Tclass.SetCardinality.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.SetCardinality.__default(), $h) } 
  $IsAlloc($o, Tclass.SetCardinality.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

const unique class.AssumeTypeAssumptions.IntCell?: ClassName;

function Tclass.AssumeTypeAssumptions.IntCell?() : Ty;

const unique Tagclass.AssumeTypeAssumptions.IntCell?: TyTag;

// Tclass.AssumeTypeAssumptions.IntCell? Tag
axiom Tag(Tclass.AssumeTypeAssumptions.IntCell?())
     == Tagclass.AssumeTypeAssumptions.IntCell?
   && TagFamily(Tclass.AssumeTypeAssumptions.IntCell?()) == tytagFamily$IntCell;

// Box/unbox axiom for Tclass.AssumeTypeAssumptions.IntCell?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.AssumeTypeAssumptions.IntCell?()) } 
  $IsBox(bx, Tclass.AssumeTypeAssumptions.IntCell?())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.AssumeTypeAssumptions.IntCell?()));

// IntCell: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.AssumeTypeAssumptions.IntCell?()) } 
  $Is($o, Tclass.AssumeTypeAssumptions.IntCell?())
     <==> $o == null || dtype($o) == Tclass.AssumeTypeAssumptions.IntCell?());

// IntCell: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.AssumeTypeAssumptions.IntCell?(), $h) } 
  $IsAlloc($o, Tclass.AssumeTypeAssumptions.IntCell?(), $h)
     <==> $o == null || read($h, $o, alloc));

axiom FDim(AssumeTypeAssumptions.IntCell.data) == 0
   && FieldOfDecl(class.AssumeTypeAssumptions.IntCell?, field$data)
     == AssumeTypeAssumptions.IntCell.data
   && !$IsGhostField(AssumeTypeAssumptions.IntCell.data);

const AssumeTypeAssumptions.IntCell.data: Field int;

// IntCell.data: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, AssumeTypeAssumptions.IntCell.data) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.AssumeTypeAssumptions.IntCell?()
     ==> $Is(read($h, $o, AssumeTypeAssumptions.IntCell.data), TInt));

// IntCell.data: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, AssumeTypeAssumptions.IntCell.data) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.AssumeTypeAssumptions.IntCell?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, AssumeTypeAssumptions.IntCell.data), TInt, $h));

function Tclass.AssumeTypeAssumptions.IntCell() : Ty;

const unique Tagclass.AssumeTypeAssumptions.IntCell: TyTag;

// Tclass.AssumeTypeAssumptions.IntCell Tag
axiom Tag(Tclass.AssumeTypeAssumptions.IntCell())
     == Tagclass.AssumeTypeAssumptions.IntCell
   && TagFamily(Tclass.AssumeTypeAssumptions.IntCell()) == tytagFamily$IntCell;

// Box/unbox axiom for Tclass.AssumeTypeAssumptions.IntCell
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.AssumeTypeAssumptions.IntCell()) } 
  $IsBox(bx, Tclass.AssumeTypeAssumptions.IntCell())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.AssumeTypeAssumptions.IntCell()));

// AssumeTypeAssumptions.IntCell: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass.AssumeTypeAssumptions.IntCell()) } 
  $Is(c#0, Tclass.AssumeTypeAssumptions.IntCell())
     <==> $Is(c#0, Tclass.AssumeTypeAssumptions.IntCell?()) && c#0 != null);

// AssumeTypeAssumptions.IntCell: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass.AssumeTypeAssumptions.IntCell(), $h) } 
  $IsAlloc(c#0, Tclass.AssumeTypeAssumptions.IntCell(), $h)
     <==> $IsAlloc(c#0, Tclass.AssumeTypeAssumptions.IntCell?(), $h));

const unique class.AssumeTypeAssumptions.Cell?: ClassName;

function Tclass.AssumeTypeAssumptions.Cell?(Ty) : Ty;

const unique Tagclass.AssumeTypeAssumptions.Cell?: TyTag;

// Tclass.AssumeTypeAssumptions.Cell? Tag
axiom (forall AssumeTypeAssumptions.Cell$T: Ty :: 
  { Tclass.AssumeTypeAssumptions.Cell?(AssumeTypeAssumptions.Cell$T) } 
  Tag(Tclass.AssumeTypeAssumptions.Cell?(AssumeTypeAssumptions.Cell$T))
       == Tagclass.AssumeTypeAssumptions.Cell?
     && TagFamily(Tclass.AssumeTypeAssumptions.Cell?(AssumeTypeAssumptions.Cell$T))
       == tytagFamily$Cell);

// Tclass.AssumeTypeAssumptions.Cell? injectivity 0
axiom (forall AssumeTypeAssumptions.Cell$T: Ty :: 
  { Tclass.AssumeTypeAssumptions.Cell?(AssumeTypeAssumptions.Cell$T) } 
  Tclass.AssumeTypeAssumptions.Cell?_0(Tclass.AssumeTypeAssumptions.Cell?(AssumeTypeAssumptions.Cell$T))
     == AssumeTypeAssumptions.Cell$T);

function Tclass.AssumeTypeAssumptions.Cell?_0(Ty) : Ty;

// Box/unbox axiom for Tclass.AssumeTypeAssumptions.Cell?
axiom (forall AssumeTypeAssumptions.Cell$T: Ty, bx: Box :: 
  { $IsBox(bx, Tclass.AssumeTypeAssumptions.Cell?(AssumeTypeAssumptions.Cell$T)) } 
  $IsBox(bx, Tclass.AssumeTypeAssumptions.Cell?(AssumeTypeAssumptions.Cell$T))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, 
        Tclass.AssumeTypeAssumptions.Cell?(AssumeTypeAssumptions.Cell$T)));

// Cell: Class $Is
axiom (forall AssumeTypeAssumptions.Cell$T: Ty, $o: ref :: 
  { $Is($o, Tclass.AssumeTypeAssumptions.Cell?(AssumeTypeAssumptions.Cell$T)) } 
  $Is($o, Tclass.AssumeTypeAssumptions.Cell?(AssumeTypeAssumptions.Cell$T))
     <==> $o == null
       || dtype($o) == Tclass.AssumeTypeAssumptions.Cell?(AssumeTypeAssumptions.Cell$T));

// Cell: Class $IsAlloc
axiom (forall AssumeTypeAssumptions.Cell$T: Ty, $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.AssumeTypeAssumptions.Cell?(AssumeTypeAssumptions.Cell$T), $h) } 
  $IsAlloc($o, Tclass.AssumeTypeAssumptions.Cell?(AssumeTypeAssumptions.Cell$T), $h)
     <==> $o == null || read($h, $o, alloc));

axiom FDim(AssumeTypeAssumptions.Cell.data) == 0
   && FieldOfDecl(class.AssumeTypeAssumptions.Cell?, field$data)
     == AssumeTypeAssumptions.Cell.data
   && !$IsGhostField(AssumeTypeAssumptions.Cell.data);

const AssumeTypeAssumptions.Cell.data: Field Box;

// Cell.data: Type axiom
axiom (forall AssumeTypeAssumptions.Cell$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, AssumeTypeAssumptions.Cell.data), Tclass.AssumeTypeAssumptions.Cell?(AssumeTypeAssumptions.Cell$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.AssumeTypeAssumptions.Cell?(AssumeTypeAssumptions.Cell$T)
     ==> $IsBox(read($h, $o, AssumeTypeAssumptions.Cell.data), AssumeTypeAssumptions.Cell$T));

// Cell.data: Allocation axiom
axiom (forall AssumeTypeAssumptions.Cell$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, AssumeTypeAssumptions.Cell.data), Tclass.AssumeTypeAssumptions.Cell?(AssumeTypeAssumptions.Cell$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.AssumeTypeAssumptions.Cell?(AssumeTypeAssumptions.Cell$T)
       && read($h, $o, alloc)
     ==> $IsAllocBox(read($h, $o, AssumeTypeAssumptions.Cell.data), AssumeTypeAssumptions.Cell$T, $h));

function Tclass.AssumeTypeAssumptions.Cell(Ty) : Ty;

const unique Tagclass.AssumeTypeAssumptions.Cell: TyTag;

// Tclass.AssumeTypeAssumptions.Cell Tag
axiom (forall AssumeTypeAssumptions.Cell$T: Ty :: 
  { Tclass.AssumeTypeAssumptions.Cell(AssumeTypeAssumptions.Cell$T) } 
  Tag(Tclass.AssumeTypeAssumptions.Cell(AssumeTypeAssumptions.Cell$T))
       == Tagclass.AssumeTypeAssumptions.Cell
     && TagFamily(Tclass.AssumeTypeAssumptions.Cell(AssumeTypeAssumptions.Cell$T))
       == tytagFamily$Cell);

// Tclass.AssumeTypeAssumptions.Cell injectivity 0
axiom (forall AssumeTypeAssumptions.Cell$T: Ty :: 
  { Tclass.AssumeTypeAssumptions.Cell(AssumeTypeAssumptions.Cell$T) } 
  Tclass.AssumeTypeAssumptions.Cell_0(Tclass.AssumeTypeAssumptions.Cell(AssumeTypeAssumptions.Cell$T))
     == AssumeTypeAssumptions.Cell$T);

function Tclass.AssumeTypeAssumptions.Cell_0(Ty) : Ty;

// Box/unbox axiom for Tclass.AssumeTypeAssumptions.Cell
axiom (forall AssumeTypeAssumptions.Cell$T: Ty, bx: Box :: 
  { $IsBox(bx, Tclass.AssumeTypeAssumptions.Cell(AssumeTypeAssumptions.Cell$T)) } 
  $IsBox(bx, Tclass.AssumeTypeAssumptions.Cell(AssumeTypeAssumptions.Cell$T))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.AssumeTypeAssumptions.Cell(AssumeTypeAssumptions.Cell$T)));

// AssumeTypeAssumptions.Cell: subset type $Is
axiom (forall AssumeTypeAssumptions.Cell$T: Ty, c#0: ref :: 
  { $Is(c#0, Tclass.AssumeTypeAssumptions.Cell(AssumeTypeAssumptions.Cell$T)) } 
  $Is(c#0, Tclass.AssumeTypeAssumptions.Cell(AssumeTypeAssumptions.Cell$T))
     <==> $Is(c#0, Tclass.AssumeTypeAssumptions.Cell?(AssumeTypeAssumptions.Cell$T))
       && c#0 != null);

// AssumeTypeAssumptions.Cell: subset type $IsAlloc
axiom (forall AssumeTypeAssumptions.Cell$T: Ty, c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass.AssumeTypeAssumptions.Cell(AssumeTypeAssumptions.Cell$T), $h) } 
  $IsAlloc(c#0, Tclass.AssumeTypeAssumptions.Cell(AssumeTypeAssumptions.Cell$T), $h)
     <==> $IsAlloc(c#0, Tclass.AssumeTypeAssumptions.Cell?(AssumeTypeAssumptions.Cell$T), $h));

const unique class.AssumeTypeAssumptions.__default: ClassName;

function Tclass.AssumeTypeAssumptions.__default() : Ty;

const unique Tagclass.AssumeTypeAssumptions.__default: TyTag;

// Tclass.AssumeTypeAssumptions.__default Tag
axiom Tag(Tclass.AssumeTypeAssumptions.__default())
     == Tagclass.AssumeTypeAssumptions.__default
   && TagFamily(Tclass.AssumeTypeAssumptions.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.AssumeTypeAssumptions.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.AssumeTypeAssumptions.__default()) } 
  $IsBox(bx, Tclass.AssumeTypeAssumptions.__default())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.AssumeTypeAssumptions.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.AssumeTypeAssumptions.__default()) } 
  $Is($o, Tclass.AssumeTypeAssumptions.__default())
     <==> $o == null || dtype($o) == Tclass.AssumeTypeAssumptions.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.AssumeTypeAssumptions.__default(), $h) } 
  $IsAlloc($o, Tclass.AssumeTypeAssumptions.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

// function declaration for AssumeTypeAssumptions._default.f
function AssumeTypeAssumptions.__default.f(p#0: Seq Box) : bool;

function AssumeTypeAssumptions.__default.f#canCall(p#0: Seq Box) : bool;

// consequence axiom for AssumeTypeAssumptions.__default.f
axiom true
   ==> (forall p#0: Seq Box :: 
    { AssumeTypeAssumptions.__default.f(p#0) } 
    AssumeTypeAssumptions.__default.f#canCall(p#0) || $Is(p#0, TSeq(TInt)) ==> true);

function AssumeTypeAssumptions.__default.f#requires(Seq Box) : bool;

// #requires axiom for AssumeTypeAssumptions.__default.f
axiom (forall p#0: Seq Box :: 
  { AssumeTypeAssumptions.__default.f#requires(p#0) } 
  $Is(p#0, TSeq(TInt)) ==> AssumeTypeAssumptions.__default.f#requires(p#0) == true);

const unique class.LetStmtHasMutableVariables.__default: ClassName;

function Tclass.LetStmtHasMutableVariables.__default() : Ty;

const unique Tagclass.LetStmtHasMutableVariables.__default: TyTag;

// Tclass.LetStmtHasMutableVariables.__default Tag
axiom Tag(Tclass.LetStmtHasMutableVariables.__default())
     == Tagclass.LetStmtHasMutableVariables.__default
   && TagFamily(Tclass.LetStmtHasMutableVariables.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.LetStmtHasMutableVariables.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.LetStmtHasMutableVariables.__default()) } 
  $IsBox(bx, Tclass.LetStmtHasMutableVariables.__default())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.LetStmtHasMutableVariables.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.LetStmtHasMutableVariables.__default()) } 
  $Is($o, Tclass.LetStmtHasMutableVariables.__default())
     <==> $o == null || dtype($o) == Tclass.LetStmtHasMutableVariables.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.LetStmtHasMutableVariables.__default(), $h) } 
  $IsAlloc($o, Tclass.LetStmtHasMutableVariables.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

function Tclass.DivModBounded.int8() : Ty;

const unique Tagclass.DivModBounded.int8: TyTag;

// Tclass.DivModBounded.int8 Tag
axiom Tag(Tclass.DivModBounded.int8()) == Tagclass.DivModBounded.int8
   && TagFamily(Tclass.DivModBounded.int8()) == tytagFamily$int8;

// Box/unbox axiom for Tclass.DivModBounded.int8
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.DivModBounded.int8()) } 
  $IsBox(bx, Tclass.DivModBounded.int8())
     ==> $Box($Unbox(bx): int) == bx && $Is($Unbox(bx): int, Tclass.DivModBounded.int8()));

// DivModBounded.int8: newtype $Is
axiom (forall x#0: int :: 
  { $Is(x#0, Tclass.DivModBounded.int8()) } 
  $Is(x#0, Tclass.DivModBounded.int8()) <==> LitInt(-128) <= x#0 && x#0 < 128);

// DivModBounded.int8: newtype $IsAlloc
axiom (forall x#0: int, $h: Heap :: 
  { $IsAlloc(x#0, Tclass.DivModBounded.int8(), $h) } 
  $IsAlloc(x#0, Tclass.DivModBounded.int8(), $h));

const unique class.DivModBounded.int8: ClassName;

const unique class.DivModBounded.__default: ClassName;

function Tclass.DivModBounded.__default() : Ty;

const unique Tagclass.DivModBounded.__default: TyTag;

// Tclass.DivModBounded.__default Tag
axiom Tag(Tclass.DivModBounded.__default()) == Tagclass.DivModBounded.__default
   && TagFamily(Tclass.DivModBounded.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.DivModBounded.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.DivModBounded.__default()) } 
  $IsBox(bx, Tclass.DivModBounded.__default())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.DivModBounded.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.DivModBounded.__default()) } 
  $Is($o, Tclass.DivModBounded.__default())
     <==> $o == null || dtype($o) == Tclass.DivModBounded.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.DivModBounded.__default(), $h) } 
  $IsAlloc($o, Tclass.DivModBounded.__default(), $h)
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

const unique tytagFamily$_tuple#2: TyTagFamily;

const unique tytagFamily$_tuple#0: TyTagFamily;

const unique tytagFamily$Global: TyTagFamily;

const unique tytagFamily$Multi: TyTagFamily;

const unique tytagFamily$MyBoxyClass: TyTagFamily;

const unique tytagFamily$CC: TyTagFamily;

const unique tytagFamily$_default: TyTagFamily;

const unique tytagFamily$IntCell: TyTagFamily;

const unique tytagFamily$Cell: TyTagFamily;

const unique tytagFamily$int8: TyTagFamily;

const unique field$x: NameFamily;

const unique field$y: NameFamily;

const unique field$next: NameFamily;

const unique field$f: NameFamily;

const unique field$data: NameFamily;
