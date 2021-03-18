// Dafny 3.0.0.30204
// Command Line Options: -compile:0 -noVerify /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy -print:./SharedDestructors.bpl

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

// Constructor function declaration
function #_module.Dt.D(int, real, bool) : DatatypeType;

const unique ##_module.Dt.D: DtCtorId;

// Constructor identifier
axiom (forall a#34#0#0: int, a#34#1#0: real, a#34#2#0: bool :: 
  { #_module.Dt.D(a#34#0#0, a#34#1#0, a#34#2#0) } 
  DatatypeCtorId(#_module.Dt.D(a#34#0#0, a#34#1#0, a#34#2#0)) == ##_module.Dt.D);

function _module.Dt.D_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Dt.D_q(d) } 
  _module.Dt.D_q(d) <==> DatatypeCtorId(d) == ##_module.Dt.D);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Dt.D_q(d) } 
  _module.Dt.D_q(d)
     ==> (exists a#35#0#0: int, a#35#1#0: real, a#35#2#0: bool :: 
      d == #_module.Dt.D(a#35#0#0, a#35#1#0, a#35#2#0)));

// Constructor $Is
axiom (forall a#36#0#0: int, a#36#1#0: real, a#36#2#0: bool :: 
  { $Is(#_module.Dt.D(a#36#0#0, a#36#1#0, a#36#2#0), Tclass._module.Dt()) } 
  $Is(#_module.Dt.D(a#36#0#0, a#36#1#0, a#36#2#0), Tclass._module.Dt())
     <==> $Is(a#36#0#0, TInt) && $Is(a#36#1#0, TReal) && $Is(a#36#2#0, TBool));

// Constructor $IsAlloc
axiom (forall a#37#0#0: int, a#37#1#0: real, a#37#2#0: bool, $h: Heap :: 
  { $IsAlloc(#_module.Dt.D(a#37#0#0, a#37#1#0, a#37#2#0), Tclass._module.Dt(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Dt.D(a#37#0#0, a#37#1#0, a#37#2#0), Tclass._module.Dt(), $h)
       <==> $IsAlloc(a#37#0#0, TInt, $h)
         && $IsAlloc(a#37#1#0, TReal, $h)
         && $IsAlloc(a#37#2#0, TBool, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Dt.u(d), TInt, $h) } 
  $IsGoodHeap($h) && _module.Dt.D_q(d) && $IsAlloc(d, Tclass._module.Dt(), $h)
     ==> $IsAlloc(_module.Dt.u(d), TInt, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Dt.y(d), TReal, $h) } 
  $IsGoodHeap($h) && _module.Dt.D_q(d) && $IsAlloc(d, Tclass._module.Dt(), $h)
     ==> $IsAlloc(_module.Dt.y(d), TReal, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Dt.v(d), TBool, $h) } 
  $IsGoodHeap($h) && _module.Dt.D_q(d) && $IsAlloc(d, Tclass._module.Dt(), $h)
     ==> $IsAlloc(_module.Dt.v(d), TBool, $h));

// Constructor literal
axiom (forall a#38#0#0: int, a#38#1#0: real, a#38#2#0: bool :: 
  { #_module.Dt.D(LitInt(a#38#0#0), LitReal(a#38#1#0), Lit(a#38#2#0)) } 
  #_module.Dt.D(LitInt(a#38#0#0), LitReal(a#38#1#0), Lit(a#38#2#0))
     == Lit(#_module.Dt.D(a#38#0#0, a#38#1#0, a#38#2#0)));

function _module.Dt.u(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#39#0#0: int, a#39#1#0: real, a#39#2#0: bool :: 
  { #_module.Dt.D(a#39#0#0, a#39#1#0, a#39#2#0) } 
  _module.Dt.u(#_module.Dt.D(a#39#0#0, a#39#1#0, a#39#2#0)) == a#39#0#0);

// Constructor injectivity
axiom (forall a#40#0#0: int, a#40#1#0: real, a#40#2#0: bool :: 
  { #_module.Dt.D(a#40#0#0, a#40#1#0, a#40#2#0) } 
  _module.Dt.y(#_module.Dt.D(a#40#0#0, a#40#1#0, a#40#2#0)) == a#40#1#0);

function _module.Dt.v(DatatypeType) : bool;

// Constructor injectivity
axiom (forall a#41#0#0: int, a#41#1#0: real, a#41#2#0: bool :: 
  { #_module.Dt.D(a#41#0#0, a#41#1#0, a#41#2#0) } 
  _module.Dt.v(#_module.Dt.D(a#41#0#0, a#41#1#0, a#41#2#0)) == a#41#2#0);

// Depth-one case-split function
function $IsA#_module.Dt(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.Dt(d) } 
  $IsA#_module.Dt(d)
     ==> _module.Dt.A_q(d) || _module.Dt.B_q(d) || _module.Dt.C_q(d) || _module.Dt.D_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.Dt.D_q(d), $Is(d, Tclass._module.Dt()) } 
    { _module.Dt.C_q(d), $Is(d, Tclass._module.Dt()) } 
    { _module.Dt.B_q(d), $Is(d, Tclass._module.Dt()) } 
    { _module.Dt.A_q(d), $Is(d, Tclass._module.Dt()) } 
  $Is(d, Tclass._module.Dt())
     ==> _module.Dt.A_q(d) || _module.Dt.B_q(d) || _module.Dt.C_q(d) || _module.Dt.D_q(d));

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

// Datatype extensional equality definition: #_module.Dt.D
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Dt#Equal(a, b), _module.Dt.D_q(a) } 
    { _module.Dt#Equal(a, b), _module.Dt.D_q(b) } 
  _module.Dt.D_q(a) && _module.Dt.D_q(b)
     ==> (_module.Dt#Equal(a, b)
       <==> _module.Dt.u(a) == _module.Dt.u(b)
         && _module.Dt.y(a) == _module.Dt.y(b)
         && _module.Dt.v(a) == _module.Dt.v(b)));

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
function #_module.Record.Record(int) : DatatypeType;

const unique ##_module.Record.Record: DtCtorId;

// Constructor identifier
axiom (forall a#42#0#0: int :: 
  { #_module.Record.Record(a#42#0#0) } 
  DatatypeCtorId(#_module.Record.Record(a#42#0#0)) == ##_module.Record.Record);

function _module.Record.Record_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Record.Record_q(d) } 
  _module.Record.Record_q(d) <==> DatatypeCtorId(d) == ##_module.Record.Record);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Record.Record_q(d) } 
  _module.Record.Record_q(d)
     ==> (exists a#43#0#0: int :: d == #_module.Record.Record(a#43#0#0)));

function Tclass._module.Record() : Ty;

const unique Tagclass._module.Record: TyTag;

// Tclass._module.Record Tag
axiom Tag(Tclass._module.Record()) == Tagclass._module.Record
   && TagFamily(Tclass._module.Record()) == tytagFamily$Record;

// Box/unbox axiom for Tclass._module.Record
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Record()) } 
  $IsBox(bx, Tclass._module.Record())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Record()));

// Constructor $Is
axiom (forall a#44#0#0: int :: 
  { $Is(#_module.Record.Record(a#44#0#0), Tclass._module.Record()) } 
  $Is(#_module.Record.Record(a#44#0#0), Tclass._module.Record())
     <==> $Is(a#44#0#0, TInt));

// Constructor $IsAlloc
axiom (forall a#45#0#0: int, $h: Heap :: 
  { $IsAlloc(#_module.Record.Record(a#45#0#0), Tclass._module.Record(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Record.Record(a#45#0#0), Tclass._module.Record(), $h)
       <==> $IsAlloc(a#45#0#0, TInt, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Record.t(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Record.Record_q(d)
       && $IsAlloc(d, Tclass._module.Record(), $h)
     ==> $IsAlloc(_module.Record.t(d), TInt, $h));

// Constructor literal
axiom (forall a#46#0#0: int :: 
  { #_module.Record.Record(LitInt(a#46#0#0)) } 
  #_module.Record.Record(LitInt(a#46#0#0))
     == Lit(#_module.Record.Record(a#46#0#0)));

function _module.Record.t(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#47#0#0: int :: 
  { #_module.Record.Record(a#47#0#0) } 
  _module.Record.t(#_module.Record.Record(a#47#0#0)) == a#47#0#0);

// Depth-one case-split function
function $IsA#_module.Record(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.Record(d) } 
  $IsA#_module.Record(d) ==> _module.Record.Record_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.Record.Record_q(d), $Is(d, Tclass._module.Record()) } 
  $Is(d, Tclass._module.Record()) ==> _module.Record.Record_q(d));

// Datatype extensional equality declaration
function _module.Record#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.Record.Record
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Record#Equal(a, b) } 
  true
     ==> (_module.Record#Equal(a, b) <==> _module.Record.t(a) == _module.Record.t(b)));

// Datatype extensionality axiom: _module.Record
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Record#Equal(a, b) } 
  _module.Record#Equal(a, b) <==> a == b);

const unique class._module.Record: ClassName;

// Constructor function declaration
function #_module.Shared.AA(int, real, real) : DatatypeType;

const unique ##_module.Shared.AA: DtCtorId;

// Constructor identifier
axiom (forall a#48#0#0: int, a#48#1#0: real, a#48#2#0: real :: 
  { #_module.Shared.AA(a#48#0#0, a#48#1#0, a#48#2#0) } 
  DatatypeCtorId(#_module.Shared.AA(a#48#0#0, a#48#1#0, a#48#2#0))
     == ##_module.Shared.AA);

function _module.Shared.AA_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Shared.AA_q(d) } 
  _module.Shared.AA_q(d) <==> DatatypeCtorId(d) == ##_module.Shared.AA);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Shared.AA_q(d) } 
  _module.Shared.AA_q(d)
     ==> (exists a#49#0#0: int, a#49#1#0: real, a#49#2#0: real :: 
      d == #_module.Shared.AA(a#49#0#0, a#49#1#0, a#49#2#0)));

function Tclass._module.Shared() : Ty;

const unique Tagclass._module.Shared: TyTag;

// Tclass._module.Shared Tag
axiom Tag(Tclass._module.Shared()) == Tagclass._module.Shared
   && TagFamily(Tclass._module.Shared()) == tytagFamily$Shared;

// Box/unbox axiom for Tclass._module.Shared
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Shared()) } 
  $IsBox(bx, Tclass._module.Shared())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Shared()));

// Constructor $Is
axiom (forall a#50#0#0: int, a#50#1#0: real, a#50#2#0: real :: 
  { $Is(#_module.Shared.AA(a#50#0#0, a#50#1#0, a#50#2#0), Tclass._module.Shared()) } 
  $Is(#_module.Shared.AA(a#50#0#0, a#50#1#0, a#50#2#0), Tclass._module.Shared())
     <==> $Is(a#50#0#0, TInt) && $Is(a#50#1#0, TReal) && $Is(a#50#2#0, TReal));

// Constructor $IsAlloc
axiom (forall a#51#0#0: int, a#51#1#0: real, a#51#2#0: real, $h: Heap :: 
  { $IsAlloc(#_module.Shared.AA(a#51#0#0, a#51#1#0, a#51#2#0), Tclass._module.Shared(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Shared.AA(a#51#0#0, a#51#1#0, a#51#2#0), Tclass._module.Shared(), $h)
       <==> $IsAlloc(a#51#0#0, TInt, $h)
         && $IsAlloc(a#51#1#0, TReal, $h)
         && $IsAlloc(a#51#2#0, TReal, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Shared.id(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Shared.AA_q(d)
       && $IsAlloc(d, Tclass._module.Shared(), $h)
     ==> $IsAlloc(_module.Shared.id(d), TInt, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Shared.a(d), TReal, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Shared.AA_q(d)
       && $IsAlloc(d, Tclass._module.Shared(), $h)
     ==> $IsAlloc(_module.Shared.a(d), TReal, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Shared.c(d), TReal, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Shared.AA_q(d)
       && $IsAlloc(d, Tclass._module.Shared(), $h)
     ==> $IsAlloc(_module.Shared.c(d), TReal, $h));

// Constructor literal
axiom (forall a#52#0#0: int, a#52#1#0: real, a#52#2#0: real :: 
  { #_module.Shared.AA(LitInt(a#52#0#0), LitReal(a#52#1#0), LitReal(a#52#2#0)) } 
  #_module.Shared.AA(LitInt(a#52#0#0), LitReal(a#52#1#0), LitReal(a#52#2#0))
     == Lit(#_module.Shared.AA(a#52#0#0, a#52#1#0, a#52#2#0)));

function _module.Shared.id(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#53#0#0: int, a#53#1#0: real, a#53#2#0: real :: 
  { #_module.Shared.AA(a#53#0#0, a#53#1#0, a#53#2#0) } 
  _module.Shared.id(#_module.Shared.AA(a#53#0#0, a#53#1#0, a#53#2#0)) == a#53#0#0);

function _module.Shared.a(DatatypeType) : real;

// Constructor injectivity
axiom (forall a#54#0#0: int, a#54#1#0: real, a#54#2#0: real :: 
  { #_module.Shared.AA(a#54#0#0, a#54#1#0, a#54#2#0) } 
  _module.Shared.a(#_module.Shared.AA(a#54#0#0, a#54#1#0, a#54#2#0)) == a#54#1#0);

function _module.Shared.c(DatatypeType) : real;

// Constructor injectivity
axiom (forall a#55#0#0: int, a#55#1#0: real, a#55#2#0: real :: 
  { #_module.Shared.AA(a#55#0#0, a#55#1#0, a#55#2#0) } 
  _module.Shared.c(#_module.Shared.AA(a#55#0#0, a#55#1#0, a#55#2#0)) == a#55#2#0);

// Constructor function declaration
function #_module.Shared.BB(int, real) : DatatypeType;

const unique ##_module.Shared.BB: DtCtorId;

// Constructor identifier
axiom (forall a#56#0#0: int, a#56#1#0: real :: 
  { #_module.Shared.BB(a#56#0#0, a#56#1#0) } 
  DatatypeCtorId(#_module.Shared.BB(a#56#0#0, a#56#1#0)) == ##_module.Shared.BB);

function _module.Shared.BB_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Shared.BB_q(d) } 
  _module.Shared.BB_q(d) <==> DatatypeCtorId(d) == ##_module.Shared.BB);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Shared.BB_q(d) } 
  _module.Shared.BB_q(d)
     ==> (exists a#57#0#0: int, a#57#1#0: real :: 
      d == #_module.Shared.BB(a#57#0#0, a#57#1#0)));

// Constructor $Is
axiom (forall a#58#0#0: int, a#58#1#0: real :: 
  { $Is(#_module.Shared.BB(a#58#0#0, a#58#1#0), Tclass._module.Shared()) } 
  $Is(#_module.Shared.BB(a#58#0#0, a#58#1#0), Tclass._module.Shared())
     <==> $Is(a#58#0#0, TInt) && $Is(a#58#1#0, TReal));

// Constructor $IsAlloc
axiom (forall a#59#0#0: int, a#59#1#0: real, $h: Heap :: 
  { $IsAlloc(#_module.Shared.BB(a#59#0#0, a#59#1#0), Tclass._module.Shared(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Shared.BB(a#59#0#0, a#59#1#0), Tclass._module.Shared(), $h)
       <==> $IsAlloc(a#59#0#0, TInt, $h) && $IsAlloc(a#59#1#0, TReal, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Shared.id(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Shared.BB_q(d)
       && $IsAlloc(d, Tclass._module.Shared(), $h)
     ==> $IsAlloc(_module.Shared.id(d), TInt, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Shared.b(d), TReal, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Shared.BB_q(d)
       && $IsAlloc(d, Tclass._module.Shared(), $h)
     ==> $IsAlloc(_module.Shared.b(d), TReal, $h));

// Constructor literal
axiom (forall a#60#0#0: int, a#60#1#0: real :: 
  { #_module.Shared.BB(LitInt(a#60#0#0), LitReal(a#60#1#0)) } 
  #_module.Shared.BB(LitInt(a#60#0#0), LitReal(a#60#1#0))
     == Lit(#_module.Shared.BB(a#60#0#0, a#60#1#0)));

// Constructor injectivity
axiom (forall a#61#0#0: int, a#61#1#0: real :: 
  { #_module.Shared.BB(a#61#0#0, a#61#1#0) } 
  _module.Shared.id(#_module.Shared.BB(a#61#0#0, a#61#1#0)) == a#61#0#0);

function _module.Shared.b(DatatypeType) : real;

// Constructor injectivity
axiom (forall a#62#0#0: int, a#62#1#0: real :: 
  { #_module.Shared.BB(a#62#0#0, a#62#1#0) } 
  _module.Shared.b(#_module.Shared.BB(a#62#0#0, a#62#1#0)) == a#62#1#0);

// Depth-one case-split function
function $IsA#_module.Shared(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.Shared(d) } 
  $IsA#_module.Shared(d) ==> _module.Shared.AA_q(d) || _module.Shared.BB_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.Shared.BB_q(d), $Is(d, Tclass._module.Shared()) } 
    { _module.Shared.AA_q(d), $Is(d, Tclass._module.Shared()) } 
  $Is(d, Tclass._module.Shared())
     ==> _module.Shared.AA_q(d) || _module.Shared.BB_q(d));

// Datatype extensional equality declaration
function _module.Shared#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.Shared.AA
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Shared#Equal(a, b), _module.Shared.AA_q(a) } 
    { _module.Shared#Equal(a, b), _module.Shared.AA_q(b) } 
  _module.Shared.AA_q(a) && _module.Shared.AA_q(b)
     ==> (_module.Shared#Equal(a, b)
       <==> _module.Shared.id(a) == _module.Shared.id(b)
         && _module.Shared.a(a) == _module.Shared.a(b)
         && _module.Shared.c(a) == _module.Shared.c(b)));

// Datatype extensional equality definition: #_module.Shared.BB
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Shared#Equal(a, b), _module.Shared.BB_q(a) } 
    { _module.Shared#Equal(a, b), _module.Shared.BB_q(b) } 
  _module.Shared.BB_q(a) && _module.Shared.BB_q(b)
     ==> (_module.Shared#Equal(a, b)
       <==> _module.Shared.id(a) == _module.Shared.id(b)
         && _module.Shared.b(a) == _module.Shared.b(b)));

// Datatype extensionality axiom: _module.Shared
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Shared#Equal(a, b) } 
  _module.Shared#Equal(a, b) <==> a == b);

const unique class._module.Shared: ClassName;

// Constructor function declaration
function #_module.Quirky.PP(int, int) : DatatypeType;

const unique ##_module.Quirky.PP: DtCtorId;

// Constructor identifier
axiom (forall a#63#0#0: int, a#63#1#0: int :: 
  { #_module.Quirky.PP(a#63#0#0, a#63#1#0) } 
  DatatypeCtorId(#_module.Quirky.PP(a#63#0#0, a#63#1#0)) == ##_module.Quirky.PP);

function _module.Quirky.PP_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Quirky.PP_q(d) } 
  _module.Quirky.PP_q(d) <==> DatatypeCtorId(d) == ##_module.Quirky.PP);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Quirky.PP_q(d) } 
  _module.Quirky.PP_q(d)
     ==> (exists a#64#0#0: int, a#64#1#0: int :: 
      d == #_module.Quirky.PP(a#64#0#0, a#64#1#0)));

function Tclass._module.Quirky() : Ty;

const unique Tagclass._module.Quirky: TyTag;

// Tclass._module.Quirky Tag
axiom Tag(Tclass._module.Quirky()) == Tagclass._module.Quirky
   && TagFamily(Tclass._module.Quirky()) == tytagFamily$Quirky;

// Box/unbox axiom for Tclass._module.Quirky
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Quirky()) } 
  $IsBox(bx, Tclass._module.Quirky())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Quirky()));

// Constructor $Is
axiom (forall a#65#0#0: int, a#65#1#0: int :: 
  { $Is(#_module.Quirky.PP(a#65#0#0, a#65#1#0), Tclass._module.Quirky()) } 
  $Is(#_module.Quirky.PP(a#65#0#0, a#65#1#0), Tclass._module.Quirky())
     <==> $Is(a#65#0#0, TInt) && $Is(a#65#1#0, TInt));

// Constructor $IsAlloc
axiom (forall a#66#0#0: int, a#66#1#0: int, $h: Heap :: 
  { $IsAlloc(#_module.Quirky.PP(a#66#0#0, a#66#1#0), Tclass._module.Quirky(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Quirky.PP(a#66#0#0, a#66#1#0), Tclass._module.Quirky(), $h)
       <==> $IsAlloc(a#66#0#0, TInt, $h) && $IsAlloc(a#66#1#0, TInt, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Quirky.id(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Quirky.PP_q(d)
       && $IsAlloc(d, Tclass._module.Quirky(), $h)
     ==> $IsAlloc(_module.Quirky.id(d), TInt, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Quirky.a(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Quirky.PP_q(d)
       && $IsAlloc(d, Tclass._module.Quirky(), $h)
     ==> $IsAlloc(_module.Quirky.a(d), TInt, $h));

// Constructor literal
axiom (forall a#67#0#0: int, a#67#1#0: int :: 
  { #_module.Quirky.PP(LitInt(a#67#0#0), LitInt(a#67#1#0)) } 
  #_module.Quirky.PP(LitInt(a#67#0#0), LitInt(a#67#1#0))
     == Lit(#_module.Quirky.PP(a#67#0#0, a#67#1#0)));

function _module.Quirky.id(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#68#0#0: int, a#68#1#0: int :: 
  { #_module.Quirky.PP(a#68#0#0, a#68#1#0) } 
  _module.Quirky.id(#_module.Quirky.PP(a#68#0#0, a#68#1#0)) == a#68#0#0);

function _module.Quirky.a(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#69#0#0: int, a#69#1#0: int :: 
  { #_module.Quirky.PP(a#69#0#0, a#69#1#0) } 
  _module.Quirky.a(#_module.Quirky.PP(a#69#0#0, a#69#1#0)) == a#69#1#0);

// Constructor function declaration
function #_module.Quirky.QQ(int, int) : DatatypeType;

const unique ##_module.Quirky.QQ: DtCtorId;

// Constructor identifier
axiom (forall a#70#0#0: int, a#70#1#0: int :: 
  { #_module.Quirky.QQ(a#70#0#0, a#70#1#0) } 
  DatatypeCtorId(#_module.Quirky.QQ(a#70#0#0, a#70#1#0)) == ##_module.Quirky.QQ);

function _module.Quirky.QQ_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Quirky.QQ_q(d) } 
  _module.Quirky.QQ_q(d) <==> DatatypeCtorId(d) == ##_module.Quirky.QQ);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Quirky.QQ_q(d) } 
  _module.Quirky.QQ_q(d)
     ==> (exists a#71#0#0: int, a#71#1#0: int :: 
      d == #_module.Quirky.QQ(a#71#0#0, a#71#1#0)));

// Constructor $Is
axiom (forall a#72#0#0: int, a#72#1#0: int :: 
  { $Is(#_module.Quirky.QQ(a#72#0#0, a#72#1#0), Tclass._module.Quirky()) } 
  $Is(#_module.Quirky.QQ(a#72#0#0, a#72#1#0), Tclass._module.Quirky())
     <==> $Is(a#72#0#0, TInt) && $Is(a#72#1#0, TInt));

// Constructor $IsAlloc
axiom (forall a#73#0#0: int, a#73#1#0: int, $h: Heap :: 
  { $IsAlloc(#_module.Quirky.QQ(a#73#0#0, a#73#1#0), Tclass._module.Quirky(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Quirky.QQ(a#73#0#0, a#73#1#0), Tclass._module.Quirky(), $h)
       <==> $IsAlloc(a#73#0#0, TInt, $h) && $IsAlloc(a#73#1#0, TInt, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Quirky.b(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Quirky.QQ_q(d)
       && $IsAlloc(d, Tclass._module.Quirky(), $h)
     ==> $IsAlloc(_module.Quirky.b(d), TInt, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Quirky.id(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Quirky.QQ_q(d)
       && $IsAlloc(d, Tclass._module.Quirky(), $h)
     ==> $IsAlloc(_module.Quirky.id(d), TInt, $h));

// Constructor literal
axiom (forall a#74#0#0: int, a#74#1#0: int :: 
  { #_module.Quirky.QQ(LitInt(a#74#0#0), LitInt(a#74#1#0)) } 
  #_module.Quirky.QQ(LitInt(a#74#0#0), LitInt(a#74#1#0))
     == Lit(#_module.Quirky.QQ(a#74#0#0, a#74#1#0)));

function _module.Quirky.b(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#75#0#0: int, a#75#1#0: int :: 
  { #_module.Quirky.QQ(a#75#0#0, a#75#1#0) } 
  _module.Quirky.b(#_module.Quirky.QQ(a#75#0#0, a#75#1#0)) == a#75#0#0);

// Constructor injectivity
axiom (forall a#76#0#0: int, a#76#1#0: int :: 
  { #_module.Quirky.QQ(a#76#0#0, a#76#1#0) } 
  _module.Quirky.id(#_module.Quirky.QQ(a#76#0#0, a#76#1#0)) == a#76#1#0);

// Constructor function declaration
function #_module.Quirky.RR(int, int, int) : DatatypeType;

const unique ##_module.Quirky.RR: DtCtorId;

// Constructor identifier
axiom (forall a#77#0#0: int, a#77#1#0: int, a#77#2#0: int :: 
  { #_module.Quirky.RR(a#77#0#0, a#77#1#0, a#77#2#0) } 
  DatatypeCtorId(#_module.Quirky.RR(a#77#0#0, a#77#1#0, a#77#2#0))
     == ##_module.Quirky.RR);

function _module.Quirky.RR_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Quirky.RR_q(d) } 
  _module.Quirky.RR_q(d) <==> DatatypeCtorId(d) == ##_module.Quirky.RR);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Quirky.RR_q(d) } 
  _module.Quirky.RR_q(d)
     ==> (exists a#78#0#0: int, a#78#1#0: int, a#78#2#0: int :: 
      d == #_module.Quirky.RR(a#78#0#0, a#78#1#0, a#78#2#0)));

// Constructor $Is
axiom (forall a#79#0#0: int, a#79#1#0: int, a#79#2#0: int :: 
  { $Is(#_module.Quirky.RR(a#79#0#0, a#79#1#0, a#79#2#0), Tclass._module.Quirky()) } 
  $Is(#_module.Quirky.RR(a#79#0#0, a#79#1#0, a#79#2#0), Tclass._module.Quirky())
     <==> $Is(a#79#0#0, TInt) && $Is(a#79#1#0, TInt) && $Is(a#79#2#0, TInt));

// Constructor $IsAlloc
axiom (forall a#80#0#0: int, a#80#1#0: int, a#80#2#0: int, $h: Heap :: 
  { $IsAlloc(#_module.Quirky.RR(a#80#0#0, a#80#1#0, a#80#2#0), Tclass._module.Quirky(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Quirky.RR(a#80#0#0, a#80#1#0, a#80#2#0), Tclass._module.Quirky(), $h)
       <==> $IsAlloc(a#80#0#0, TInt, $h)
         && $IsAlloc(a#80#1#0, TInt, $h)
         && $IsAlloc(a#80#2#0, TInt, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Quirky.id(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Quirky.RR_q(d)
       && $IsAlloc(d, Tclass._module.Quirky(), $h)
     ==> $IsAlloc(_module.Quirky.id(d), TInt, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Quirky.c(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Quirky.RR_q(d)
       && $IsAlloc(d, Tclass._module.Quirky(), $h)
     ==> $IsAlloc(_module.Quirky.c(d), TInt, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Quirky.d(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Quirky.RR_q(d)
       && $IsAlloc(d, Tclass._module.Quirky(), $h)
     ==> $IsAlloc(_module.Quirky.d(d), TInt, $h));

// Constructor literal
axiom (forall a#81#0#0: int, a#81#1#0: int, a#81#2#0: int :: 
  { #_module.Quirky.RR(LitInt(a#81#0#0), LitInt(a#81#1#0), LitInt(a#81#2#0)) } 
  #_module.Quirky.RR(LitInt(a#81#0#0), LitInt(a#81#1#0), LitInt(a#81#2#0))
     == Lit(#_module.Quirky.RR(a#81#0#0, a#81#1#0, a#81#2#0)));

// Constructor injectivity
axiom (forall a#82#0#0: int, a#82#1#0: int, a#82#2#0: int :: 
  { #_module.Quirky.RR(a#82#0#0, a#82#1#0, a#82#2#0) } 
  _module.Quirky.id(#_module.Quirky.RR(a#82#0#0, a#82#1#0, a#82#2#0)) == a#82#0#0);

function _module.Quirky.c(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#83#0#0: int, a#83#1#0: int, a#83#2#0: int :: 
  { #_module.Quirky.RR(a#83#0#0, a#83#1#0, a#83#2#0) } 
  _module.Quirky.c(#_module.Quirky.RR(a#83#0#0, a#83#1#0, a#83#2#0)) == a#83#1#0);

function _module.Quirky.d(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#84#0#0: int, a#84#1#0: int, a#84#2#0: int :: 
  { #_module.Quirky.RR(a#84#0#0, a#84#1#0, a#84#2#0) } 
  _module.Quirky.d(#_module.Quirky.RR(a#84#0#0, a#84#1#0, a#84#2#0)) == a#84#2#0);

// Depth-one case-split function
function $IsA#_module.Quirky(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.Quirky(d) } 
  $IsA#_module.Quirky(d)
     ==> _module.Quirky.PP_q(d) || _module.Quirky.QQ_q(d) || _module.Quirky.RR_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.Quirky.RR_q(d), $Is(d, Tclass._module.Quirky()) } 
    { _module.Quirky.QQ_q(d), $Is(d, Tclass._module.Quirky()) } 
    { _module.Quirky.PP_q(d), $Is(d, Tclass._module.Quirky()) } 
  $Is(d, Tclass._module.Quirky())
     ==> _module.Quirky.PP_q(d) || _module.Quirky.QQ_q(d) || _module.Quirky.RR_q(d));

// Datatype extensional equality declaration
function _module.Quirky#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.Quirky.PP
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Quirky#Equal(a, b), _module.Quirky.PP_q(a) } 
    { _module.Quirky#Equal(a, b), _module.Quirky.PP_q(b) } 
  _module.Quirky.PP_q(a) && _module.Quirky.PP_q(b)
     ==> (_module.Quirky#Equal(a, b)
       <==> _module.Quirky.id(a) == _module.Quirky.id(b)
         && _module.Quirky.a(a) == _module.Quirky.a(b)));

// Datatype extensional equality definition: #_module.Quirky.QQ
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Quirky#Equal(a, b), _module.Quirky.QQ_q(a) } 
    { _module.Quirky#Equal(a, b), _module.Quirky.QQ_q(b) } 
  _module.Quirky.QQ_q(a) && _module.Quirky.QQ_q(b)
     ==> (_module.Quirky#Equal(a, b)
       <==> _module.Quirky.b(a) == _module.Quirky.b(b)
         && _module.Quirky.id(a) == _module.Quirky.id(b)));

// Datatype extensional equality definition: #_module.Quirky.RR
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Quirky#Equal(a, b), _module.Quirky.RR_q(a) } 
    { _module.Quirky#Equal(a, b), _module.Quirky.RR_q(b) } 
  _module.Quirky.RR_q(a) && _module.Quirky.RR_q(b)
     ==> (_module.Quirky#Equal(a, b)
       <==> _module.Quirky.id(a) == _module.Quirky.id(b)
         && _module.Quirky.c(a) == _module.Quirky.c(b)
         && _module.Quirky.d(a) == _module.Quirky.d(b)));

// Datatype extensionality axiom: _module.Quirky
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Quirky#Equal(a, b) } 
  _module.Quirky#Equal(a, b) <==> a == b);

const unique class._module.Quirky: ClassName;

// Constructor function declaration
function #_module.Klef.C0(int, int, int, int) : DatatypeType;

const unique ##_module.Klef.C0: DtCtorId;

// Constructor identifier
axiom (forall a#85#0#0: int, a#85#1#0: int, a#85#2#0: int, a#85#3#0: int :: 
  { #_module.Klef.C0(a#85#0#0, a#85#1#0, a#85#2#0, a#85#3#0) } 
  DatatypeCtorId(#_module.Klef.C0(a#85#0#0, a#85#1#0, a#85#2#0, a#85#3#0))
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
     ==> (exists a#86#0#0: int, a#86#1#0: int, a#86#2#0: int, a#86#3#0: int :: 
      d == #_module.Klef.C0(a#86#0#0, a#86#1#0, a#86#2#0, a#86#3#0)));

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
axiom (forall a#87#0#0: int, a#87#1#0: int, a#87#2#0: int, a#87#3#0: int :: 
  { $Is(#_module.Klef.C0(a#87#0#0, a#87#1#0, a#87#2#0, a#87#3#0), Tclass._module.Klef()) } 
  $Is(#_module.Klef.C0(a#87#0#0, a#87#1#0, a#87#2#0, a#87#3#0), Tclass._module.Klef())
     <==> $Is(a#87#0#0, TInt)
       && $Is(a#87#1#0, TInt)
       && $Is(a#87#2#0, TInt)
       && $Is(a#87#3#0, TInt));

// Constructor $IsAlloc
axiom (forall a#88#0#0: int, a#88#1#0: int, a#88#2#0: int, a#88#3#0: int, $h: Heap :: 
  { $IsAlloc(#_module.Klef.C0(a#88#0#0, a#88#1#0, a#88#2#0, a#88#3#0), 
      Tclass._module.Klef(), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Klef.C0(a#88#0#0, a#88#1#0, a#88#2#0, a#88#3#0), 
        Tclass._module.Klef(), 
        $h)
       <==> $IsAlloc(a#88#0#0, TInt, $h)
         && $IsAlloc(a#88#1#0, TInt, $h)
         && $IsAlloc(a#88#2#0, TInt, $h)
         && $IsAlloc(a#88#3#0, TInt, $h)));

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
axiom (forall a#89#0#0: int, a#89#1#0: int, a#89#2#0: int, a#89#3#0: int :: 
  { #_module.Klef.C0(LitInt(a#89#0#0), LitInt(a#89#1#0), LitInt(a#89#2#0), LitInt(a#89#3#0)) } 
  #_module.Klef.C0(LitInt(a#89#0#0), LitInt(a#89#1#0), LitInt(a#89#2#0), LitInt(a#89#3#0))
     == Lit(#_module.Klef.C0(a#89#0#0, a#89#1#0, a#89#2#0, a#89#3#0)));

function _module.Klef._0(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#90#0#0: int, a#90#1#0: int, a#90#2#0: int, a#90#3#0: int :: 
  { #_module.Klef.C0(a#90#0#0, a#90#1#0, a#90#2#0, a#90#3#0) } 
  _module.Klef._0(#_module.Klef.C0(a#90#0#0, a#90#1#0, a#90#2#0, a#90#3#0))
     == a#90#0#0);

function _module.Klef._1(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#91#0#0: int, a#91#1#0: int, a#91#2#0: int, a#91#3#0: int :: 
  { #_module.Klef.C0(a#91#0#0, a#91#1#0, a#91#2#0, a#91#3#0) } 
  _module.Klef._1(#_module.Klef.C0(a#91#0#0, a#91#1#0, a#91#2#0, a#91#3#0))
     == a#91#1#0);

function _module.Klef._2(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#92#0#0: int, a#92#1#0: int, a#92#2#0: int, a#92#3#0: int :: 
  { #_module.Klef.C0(a#92#0#0, a#92#1#0, a#92#2#0, a#92#3#0) } 
  _module.Klef._2(#_module.Klef.C0(a#92#0#0, a#92#1#0, a#92#2#0, a#92#3#0))
     == a#92#2#0);

function _module.Klef.c0(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#93#0#0: int, a#93#1#0: int, a#93#2#0: int, a#93#3#0: int :: 
  { #_module.Klef.C0(a#93#0#0, a#93#1#0, a#93#2#0, a#93#3#0) } 
  _module.Klef.c0(#_module.Klef.C0(a#93#0#0, a#93#1#0, a#93#2#0, a#93#3#0))
     == a#93#3#0);

// Constructor function declaration
function #_module.Klef.C1(int, int, int, int) : DatatypeType;

const unique ##_module.Klef.C1: DtCtorId;

// Constructor identifier
axiom (forall a#94#0#0: int, a#94#1#0: int, a#94#2#0: int, a#94#3#0: int :: 
  { #_module.Klef.C1(a#94#0#0, a#94#1#0, a#94#2#0, a#94#3#0) } 
  DatatypeCtorId(#_module.Klef.C1(a#94#0#0, a#94#1#0, a#94#2#0, a#94#3#0))
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
     ==> (exists a#95#0#0: int, a#95#1#0: int, a#95#2#0: int, a#95#3#0: int :: 
      d == #_module.Klef.C1(a#95#0#0, a#95#1#0, a#95#2#0, a#95#3#0)));

// Constructor $Is
axiom (forall a#96#0#0: int, a#96#1#0: int, a#96#2#0: int, a#96#3#0: int :: 
  { $Is(#_module.Klef.C1(a#96#0#0, a#96#1#0, a#96#2#0, a#96#3#0), Tclass._module.Klef()) } 
  $Is(#_module.Klef.C1(a#96#0#0, a#96#1#0, a#96#2#0, a#96#3#0), Tclass._module.Klef())
     <==> $Is(a#96#0#0, TInt)
       && $Is(a#96#1#0, TInt)
       && $Is(a#96#2#0, TInt)
       && $Is(a#96#3#0, TInt));

// Constructor $IsAlloc
axiom (forall a#97#0#0: int, a#97#1#0: int, a#97#2#0: int, a#97#3#0: int, $h: Heap :: 
  { $IsAlloc(#_module.Klef.C1(a#97#0#0, a#97#1#0, a#97#2#0, a#97#3#0), 
      Tclass._module.Klef(), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Klef.C1(a#97#0#0, a#97#1#0, a#97#2#0, a#97#3#0), 
        Tclass._module.Klef(), 
        $h)
       <==> $IsAlloc(a#97#0#0, TInt, $h)
         && $IsAlloc(a#97#1#0, TInt, $h)
         && $IsAlloc(a#97#2#0, TInt, $h)
         && $IsAlloc(a#97#3#0, TInt, $h)));

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
axiom (forall a#98#0#0: int, a#98#1#0: int, a#98#2#0: int, a#98#3#0: int :: 
  { #_module.Klef.C1(LitInt(a#98#0#0), LitInt(a#98#1#0), LitInt(a#98#2#0), LitInt(a#98#3#0)) } 
  #_module.Klef.C1(LitInt(a#98#0#0), LitInt(a#98#1#0), LitInt(a#98#2#0), LitInt(a#98#3#0))
     == Lit(#_module.Klef.C1(a#98#0#0, a#98#1#0, a#98#2#0, a#98#3#0)));

// Constructor injectivity
axiom (forall a#99#0#0: int, a#99#1#0: int, a#99#2#0: int, a#99#3#0: int :: 
  { #_module.Klef.C1(a#99#0#0, a#99#1#0, a#99#2#0, a#99#3#0) } 
  _module.Klef._1(#_module.Klef.C1(a#99#0#0, a#99#1#0, a#99#2#0, a#99#3#0))
     == a#99#0#0);

// Constructor injectivity
axiom (forall a#100#0#0: int, a#100#1#0: int, a#100#2#0: int, a#100#3#0: int :: 
  { #_module.Klef.C1(a#100#0#0, a#100#1#0, a#100#2#0, a#100#3#0) } 
  _module.Klef._2(#_module.Klef.C1(a#100#0#0, a#100#1#0, a#100#2#0, a#100#3#0))
     == a#100#1#0);

function _module.Klef._3(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#101#0#0: int, a#101#1#0: int, a#101#2#0: int, a#101#3#0: int :: 
  { #_module.Klef.C1(a#101#0#0, a#101#1#0, a#101#2#0, a#101#3#0) } 
  _module.Klef._3(#_module.Klef.C1(a#101#0#0, a#101#1#0, a#101#2#0, a#101#3#0))
     == a#101#2#0);

function _module.Klef.c1(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#102#0#0: int, a#102#1#0: int, a#102#2#0: int, a#102#3#0: int :: 
  { #_module.Klef.C1(a#102#0#0, a#102#1#0, a#102#2#0, a#102#3#0) } 
  _module.Klef.c1(#_module.Klef.C1(a#102#0#0, a#102#1#0, a#102#2#0, a#102#3#0))
     == a#102#3#0);

// Constructor function declaration
function #_module.Klef.C2(int, int, int, int) : DatatypeType;

const unique ##_module.Klef.C2: DtCtorId;

// Constructor identifier
axiom (forall a#103#0#0: int, a#103#1#0: int, a#103#2#0: int, a#103#3#0: int :: 
  { #_module.Klef.C2(a#103#0#0, a#103#1#0, a#103#2#0, a#103#3#0) } 
  DatatypeCtorId(#_module.Klef.C2(a#103#0#0, a#103#1#0, a#103#2#0, a#103#3#0))
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
     ==> (exists a#104#0#0: int, a#104#1#0: int, a#104#2#0: int, a#104#3#0: int :: 
      d == #_module.Klef.C2(a#104#0#0, a#104#1#0, a#104#2#0, a#104#3#0)));

// Constructor $Is
axiom (forall a#105#0#0: int, a#105#1#0: int, a#105#2#0: int, a#105#3#0: int :: 
  { $Is(#_module.Klef.C2(a#105#0#0, a#105#1#0, a#105#2#0, a#105#3#0), 
      Tclass._module.Klef()) } 
  $Is(#_module.Klef.C2(a#105#0#0, a#105#1#0, a#105#2#0, a#105#3#0), 
      Tclass._module.Klef())
     <==> $Is(a#105#0#0, TInt)
       && $Is(a#105#1#0, TInt)
       && $Is(a#105#2#0, TInt)
       && $Is(a#105#3#0, TInt));

// Constructor $IsAlloc
axiom (forall a#106#0#0: int, a#106#1#0: int, a#106#2#0: int, a#106#3#0: int, $h: Heap :: 
  { $IsAlloc(#_module.Klef.C2(a#106#0#0, a#106#1#0, a#106#2#0, a#106#3#0), 
      Tclass._module.Klef(), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Klef.C2(a#106#0#0, a#106#1#0, a#106#2#0, a#106#3#0), 
        Tclass._module.Klef(), 
        $h)
       <==> $IsAlloc(a#106#0#0, TInt, $h)
         && $IsAlloc(a#106#1#0, TInt, $h)
         && $IsAlloc(a#106#2#0, TInt, $h)
         && $IsAlloc(a#106#3#0, TInt, $h)));

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
axiom (forall a#107#0#0: int, a#107#1#0: int, a#107#2#0: int, a#107#3#0: int :: 
  { #_module.Klef.C2(LitInt(a#107#0#0), LitInt(a#107#1#0), LitInt(a#107#2#0), LitInt(a#107#3#0)) } 
  #_module.Klef.C2(LitInt(a#107#0#0), LitInt(a#107#1#0), LitInt(a#107#2#0), LitInt(a#107#3#0))
     == Lit(#_module.Klef.C2(a#107#0#0, a#107#1#0, a#107#2#0, a#107#3#0)));

// Constructor injectivity
axiom (forall a#108#0#0: int, a#108#1#0: int, a#108#2#0: int, a#108#3#0: int :: 
  { #_module.Klef.C2(a#108#0#0, a#108#1#0, a#108#2#0, a#108#3#0) } 
  _module.Klef._2(#_module.Klef.C2(a#108#0#0, a#108#1#0, a#108#2#0, a#108#3#0))
     == a#108#0#0);

// Constructor injectivity
axiom (forall a#109#0#0: int, a#109#1#0: int, a#109#2#0: int, a#109#3#0: int :: 
  { #_module.Klef.C2(a#109#0#0, a#109#1#0, a#109#2#0, a#109#3#0) } 
  _module.Klef._3(#_module.Klef.C2(a#109#0#0, a#109#1#0, a#109#2#0, a#109#3#0))
     == a#109#1#0);

// Constructor injectivity
axiom (forall a#110#0#0: int, a#110#1#0: int, a#110#2#0: int, a#110#3#0: int :: 
  { #_module.Klef.C2(a#110#0#0, a#110#1#0, a#110#2#0, a#110#3#0) } 
  _module.Klef._0(#_module.Klef.C2(a#110#0#0, a#110#1#0, a#110#2#0, a#110#3#0))
     == a#110#2#0);

function _module.Klef.c2(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#111#0#0: int, a#111#1#0: int, a#111#2#0: int, a#111#3#0: int :: 
  { #_module.Klef.C2(a#111#0#0, a#111#1#0, a#111#2#0, a#111#3#0) } 
  _module.Klef.c2(#_module.Klef.C2(a#111#0#0, a#111#1#0, a#111#2#0, a#111#3#0))
     == a#111#3#0);

// Constructor function declaration
function #_module.Klef.C3(int, int, int, int) : DatatypeType;

const unique ##_module.Klef.C3: DtCtorId;

// Constructor identifier
axiom (forall a#112#0#0: int, a#112#1#0: int, a#112#2#0: int, a#112#3#0: int :: 
  { #_module.Klef.C3(a#112#0#0, a#112#1#0, a#112#2#0, a#112#3#0) } 
  DatatypeCtorId(#_module.Klef.C3(a#112#0#0, a#112#1#0, a#112#2#0, a#112#3#0))
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
     ==> (exists a#113#0#0: int, a#113#1#0: int, a#113#2#0: int, a#113#3#0: int :: 
      d == #_module.Klef.C3(a#113#0#0, a#113#1#0, a#113#2#0, a#113#3#0)));

// Constructor $Is
axiom (forall a#114#0#0: int, a#114#1#0: int, a#114#2#0: int, a#114#3#0: int :: 
  { $Is(#_module.Klef.C3(a#114#0#0, a#114#1#0, a#114#2#0, a#114#3#0), 
      Tclass._module.Klef()) } 
  $Is(#_module.Klef.C3(a#114#0#0, a#114#1#0, a#114#2#0, a#114#3#0), 
      Tclass._module.Klef())
     <==> $Is(a#114#0#0, TInt)
       && $Is(a#114#1#0, TInt)
       && $Is(a#114#2#0, TInt)
       && $Is(a#114#3#0, TInt));

// Constructor $IsAlloc
axiom (forall a#115#0#0: int, a#115#1#0: int, a#115#2#0: int, a#115#3#0: int, $h: Heap :: 
  { $IsAlloc(#_module.Klef.C3(a#115#0#0, a#115#1#0, a#115#2#0, a#115#3#0), 
      Tclass._module.Klef(), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Klef.C3(a#115#0#0, a#115#1#0, a#115#2#0, a#115#3#0), 
        Tclass._module.Klef(), 
        $h)
       <==> $IsAlloc(a#115#0#0, TInt, $h)
         && $IsAlloc(a#115#1#0, TInt, $h)
         && $IsAlloc(a#115#2#0, TInt, $h)
         && $IsAlloc(a#115#3#0, TInt, $h)));

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
axiom (forall a#116#0#0: int, a#116#1#0: int, a#116#2#0: int, a#116#3#0: int :: 
  { #_module.Klef.C3(LitInt(a#116#0#0), LitInt(a#116#1#0), LitInt(a#116#2#0), LitInt(a#116#3#0)) } 
  #_module.Klef.C3(LitInt(a#116#0#0), LitInt(a#116#1#0), LitInt(a#116#2#0), LitInt(a#116#3#0))
     == Lit(#_module.Klef.C3(a#116#0#0, a#116#1#0, a#116#2#0, a#116#3#0)));

// Constructor injectivity
axiom (forall a#117#0#0: int, a#117#1#0: int, a#117#2#0: int, a#117#3#0: int :: 
  { #_module.Klef.C3(a#117#0#0, a#117#1#0, a#117#2#0, a#117#3#0) } 
  _module.Klef._3(#_module.Klef.C3(a#117#0#0, a#117#1#0, a#117#2#0, a#117#3#0))
     == a#117#0#0);

// Constructor injectivity
axiom (forall a#118#0#0: int, a#118#1#0: int, a#118#2#0: int, a#118#3#0: int :: 
  { #_module.Klef.C3(a#118#0#0, a#118#1#0, a#118#2#0, a#118#3#0) } 
  _module.Klef._0(#_module.Klef.C3(a#118#0#0, a#118#1#0, a#118#2#0, a#118#3#0))
     == a#118#1#0);

// Constructor injectivity
axiom (forall a#119#0#0: int, a#119#1#0: int, a#119#2#0: int, a#119#3#0: int :: 
  { #_module.Klef.C3(a#119#0#0, a#119#1#0, a#119#2#0, a#119#3#0) } 
  _module.Klef._1(#_module.Klef.C3(a#119#0#0, a#119#1#0, a#119#2#0, a#119#3#0))
     == a#119#2#0);

function _module.Klef.c3(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#120#0#0: int, a#120#1#0: int, a#120#2#0: int, a#120#3#0: int :: 
  { #_module.Klef.C3(a#120#0#0, a#120#1#0, a#120#2#0, a#120#3#0) } 
  _module.Klef.c3(#_module.Klef.C3(a#120#0#0, a#120#1#0, a#120#2#0, a#120#3#0))
     == a#120#3#0);

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
function #_module.Many.Ma0(int) : DatatypeType;

const unique ##_module.Many.Ma0: DtCtorId;

// Constructor identifier
axiom (forall a#121#0#0: int :: 
  { #_module.Many.Ma0(a#121#0#0) } 
  DatatypeCtorId(#_module.Many.Ma0(a#121#0#0)) == ##_module.Many.Ma0);

function _module.Many.Ma0_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Many.Ma0_q(d) } 
  _module.Many.Ma0_q(d) <==> DatatypeCtorId(d) == ##_module.Many.Ma0);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Many.Ma0_q(d) } 
  _module.Many.Ma0_q(d)
     ==> (exists a#122#0#0: int :: d == #_module.Many.Ma0(a#122#0#0)));

function Tclass._module.Many() : Ty;

const unique Tagclass._module.Many: TyTag;

// Tclass._module.Many Tag
axiom Tag(Tclass._module.Many()) == Tagclass._module.Many
   && TagFamily(Tclass._module.Many()) == tytagFamily$Many;

// Box/unbox axiom for Tclass._module.Many
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Many()) } 
  $IsBox(bx, Tclass._module.Many())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Many()));

// Constructor $Is
axiom (forall a#123#0#0: int :: 
  { $Is(#_module.Many.Ma0(a#123#0#0), Tclass._module.Many()) } 
  $Is(#_module.Many.Ma0(a#123#0#0), Tclass._module.Many())
     <==> $Is(a#123#0#0, TInt));

// Constructor $IsAlloc
axiom (forall a#124#0#0: int, $h: Heap :: 
  { $IsAlloc(#_module.Many.Ma0(a#124#0#0), Tclass._module.Many(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Many.Ma0(a#124#0#0), Tclass._module.Many(), $h)
       <==> $IsAlloc(a#124#0#0, TInt, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Many.x(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Many.Ma0_q(d)
       && $IsAlloc(d, Tclass._module.Many(), $h)
     ==> $IsAlloc(_module.Many.x(d), TInt, $h));

// Constructor literal
axiom (forall a#125#0#0: int :: 
  { #_module.Many.Ma0(LitInt(a#125#0#0)) } 
  #_module.Many.Ma0(LitInt(a#125#0#0)) == Lit(#_module.Many.Ma0(a#125#0#0)));

function _module.Many.x(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#126#0#0: int :: 
  { #_module.Many.Ma0(a#126#0#0) } 
  _module.Many.x(#_module.Many.Ma0(a#126#0#0)) == a#126#0#0);

// Constructor function declaration
function #_module.Many.Ma1(int, int) : DatatypeType;

const unique ##_module.Many.Ma1: DtCtorId;

// Constructor identifier
axiom (forall a#127#0#0: int, a#127#1#0: int :: 
  { #_module.Many.Ma1(a#127#0#0, a#127#1#0) } 
  DatatypeCtorId(#_module.Many.Ma1(a#127#0#0, a#127#1#0)) == ##_module.Many.Ma1);

function _module.Many.Ma1_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Many.Ma1_q(d) } 
  _module.Many.Ma1_q(d) <==> DatatypeCtorId(d) == ##_module.Many.Ma1);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Many.Ma1_q(d) } 
  _module.Many.Ma1_q(d)
     ==> (exists a#128#0#0: int, a#128#1#0: int :: 
      d == #_module.Many.Ma1(a#128#0#0, a#128#1#0)));

// Constructor $Is
axiom (forall a#129#0#0: int, a#129#1#0: int :: 
  { $Is(#_module.Many.Ma1(a#129#0#0, a#129#1#0), Tclass._module.Many()) } 
  $Is(#_module.Many.Ma1(a#129#0#0, a#129#1#0), Tclass._module.Many())
     <==> $Is(a#129#0#0, TInt) && $Is(a#129#1#0, TInt));

// Constructor $IsAlloc
axiom (forall a#130#0#0: int, a#130#1#0: int, $h: Heap :: 
  { $IsAlloc(#_module.Many.Ma1(a#130#0#0, a#130#1#0), Tclass._module.Many(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Many.Ma1(a#130#0#0, a#130#1#0), Tclass._module.Many(), $h)
       <==> $IsAlloc(a#130#0#0, TInt, $h) && $IsAlloc(a#130#1#0, TInt, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Many.u(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Many.Ma1_q(d)
       && $IsAlloc(d, Tclass._module.Many(), $h)
     ==> $IsAlloc(_module.Many.u(d), TInt, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Many.fj(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Many.Ma1_q(d)
       && $IsAlloc(d, Tclass._module.Many(), $h)
     ==> $IsAlloc(_module.Many.fj(d), TInt, $h));

// Constructor literal
axiom (forall a#131#0#0: int, a#131#1#0: int :: 
  { #_module.Many.Ma1(LitInt(a#131#0#0), LitInt(a#131#1#0)) } 
  #_module.Many.Ma1(LitInt(a#131#0#0), LitInt(a#131#1#0))
     == Lit(#_module.Many.Ma1(a#131#0#0, a#131#1#0)));

function _module.Many.u(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#132#0#0: int, a#132#1#0: int :: 
  { #_module.Many.Ma1(a#132#0#0, a#132#1#0) } 
  _module.Many.u(#_module.Many.Ma1(a#132#0#0, a#132#1#0)) == a#132#0#0);

function _module.Many.fj(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#133#0#0: int, a#133#1#0: int :: 
  { #_module.Many.Ma1(a#133#0#0, a#133#1#0) } 
  _module.Many.fj(#_module.Many.Ma1(a#133#0#0, a#133#1#0)) == a#133#1#0);

// Constructor function declaration
function #_module.Many.Ma2(int, int) : DatatypeType;

const unique ##_module.Many.Ma2: DtCtorId;

// Constructor identifier
axiom (forall a#134#0#0: int, a#134#1#0: int :: 
  { #_module.Many.Ma2(a#134#0#0, a#134#1#0) } 
  DatatypeCtorId(#_module.Many.Ma2(a#134#0#0, a#134#1#0)) == ##_module.Many.Ma2);

function _module.Many.Ma2_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Many.Ma2_q(d) } 
  _module.Many.Ma2_q(d) <==> DatatypeCtorId(d) == ##_module.Many.Ma2);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Many.Ma2_q(d) } 
  _module.Many.Ma2_q(d)
     ==> (exists a#135#0#0: int, a#135#1#0: int :: 
      d == #_module.Many.Ma2(a#135#0#0, a#135#1#0)));

// Constructor $Is
axiom (forall a#136#0#0: int, a#136#1#0: int :: 
  { $Is(#_module.Many.Ma2(a#136#0#0, a#136#1#0), Tclass._module.Many()) } 
  $Is(#_module.Many.Ma2(a#136#0#0, a#136#1#0), Tclass._module.Many())
     <==> $Is(a#136#0#0, TInt) && $Is(a#136#1#0, TInt));

// Constructor $IsAlloc
axiom (forall a#137#0#0: int, a#137#1#0: int, $h: Heap :: 
  { $IsAlloc(#_module.Many.Ma2(a#137#0#0, a#137#1#0), Tclass._module.Many(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Many.Ma2(a#137#0#0, a#137#1#0), Tclass._module.Many(), $h)
       <==> $IsAlloc(a#137#0#0, TInt, $h) && $IsAlloc(a#137#1#0, TInt, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Many.x(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Many.Ma2_q(d)
       && $IsAlloc(d, Tclass._module.Many(), $h)
     ==> $IsAlloc(_module.Many.x(d), TInt, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Many.y(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Many.Ma2_q(d)
       && $IsAlloc(d, Tclass._module.Many(), $h)
     ==> $IsAlloc(_module.Many.y(d), TInt, $h));

// Constructor literal
axiom (forall a#138#0#0: int, a#138#1#0: int :: 
  { #_module.Many.Ma2(LitInt(a#138#0#0), LitInt(a#138#1#0)) } 
  #_module.Many.Ma2(LitInt(a#138#0#0), LitInt(a#138#1#0))
     == Lit(#_module.Many.Ma2(a#138#0#0, a#138#1#0)));

// Constructor injectivity
axiom (forall a#139#0#0: int, a#139#1#0: int :: 
  { #_module.Many.Ma2(a#139#0#0, a#139#1#0) } 
  _module.Many.x(#_module.Many.Ma2(a#139#0#0, a#139#1#0)) == a#139#0#0);

function _module.Many.y(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#140#0#0: int, a#140#1#0: int :: 
  { #_module.Many.Ma2(a#140#0#0, a#140#1#0) } 
  _module.Many.y(#_module.Many.Ma2(a#140#0#0, a#140#1#0)) == a#140#1#0);

// Constructor function declaration
function #_module.Many.Ma3(int, int) : DatatypeType;

const unique ##_module.Many.Ma3: DtCtorId;

// Constructor identifier
axiom (forall a#141#0#0: int, a#141#1#0: int :: 
  { #_module.Many.Ma3(a#141#0#0, a#141#1#0) } 
  DatatypeCtorId(#_module.Many.Ma3(a#141#0#0, a#141#1#0)) == ##_module.Many.Ma3);

function _module.Many.Ma3_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Many.Ma3_q(d) } 
  _module.Many.Ma3_q(d) <==> DatatypeCtorId(d) == ##_module.Many.Ma3);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Many.Ma3_q(d) } 
  _module.Many.Ma3_q(d)
     ==> (exists a#142#0#0: int, a#142#1#0: int :: 
      d == #_module.Many.Ma3(a#142#0#0, a#142#1#0)));

// Constructor $Is
axiom (forall a#143#0#0: int, a#143#1#0: int :: 
  { $Is(#_module.Many.Ma3(a#143#0#0, a#143#1#0), Tclass._module.Many()) } 
  $Is(#_module.Many.Ma3(a#143#0#0, a#143#1#0), Tclass._module.Many())
     <==> $Is(a#143#0#0, TInt) && $Is(a#143#1#0, TInt));

// Constructor $IsAlloc
axiom (forall a#144#0#0: int, a#144#1#0: int, $h: Heap :: 
  { $IsAlloc(#_module.Many.Ma3(a#144#0#0, a#144#1#0), Tclass._module.Many(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Many.Ma3(a#144#0#0, a#144#1#0), Tclass._module.Many(), $h)
       <==> $IsAlloc(a#144#0#0, TInt, $h) && $IsAlloc(a#144#1#0, TInt, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Many.x(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Many.Ma3_q(d)
       && $IsAlloc(d, Tclass._module.Many(), $h)
     ==> $IsAlloc(_module.Many.x(d), TInt, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Many.z(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Many.Ma3_q(d)
       && $IsAlloc(d, Tclass._module.Many(), $h)
     ==> $IsAlloc(_module.Many.z(d), TInt, $h));

// Constructor literal
axiom (forall a#145#0#0: int, a#145#1#0: int :: 
  { #_module.Many.Ma3(LitInt(a#145#0#0), LitInt(a#145#1#0)) } 
  #_module.Many.Ma3(LitInt(a#145#0#0), LitInt(a#145#1#0))
     == Lit(#_module.Many.Ma3(a#145#0#0, a#145#1#0)));

// Constructor injectivity
axiom (forall a#146#0#0: int, a#146#1#0: int :: 
  { #_module.Many.Ma3(a#146#0#0, a#146#1#0) } 
  _module.Many.x(#_module.Many.Ma3(a#146#0#0, a#146#1#0)) == a#146#0#0);

function _module.Many.z(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#147#0#0: int, a#147#1#0: int :: 
  { #_module.Many.Ma3(a#147#0#0, a#147#1#0) } 
  _module.Many.z(#_module.Many.Ma3(a#147#0#0, a#147#1#0)) == a#147#1#0);

// Constructor function declaration
function #_module.Many.Ma4(int, int) : DatatypeType;

const unique ##_module.Many.Ma4: DtCtorId;

// Constructor identifier
axiom (forall a#148#0#0: int, a#148#1#0: int :: 
  { #_module.Many.Ma4(a#148#0#0, a#148#1#0) } 
  DatatypeCtorId(#_module.Many.Ma4(a#148#0#0, a#148#1#0)) == ##_module.Many.Ma4);

function _module.Many.Ma4_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Many.Ma4_q(d) } 
  _module.Many.Ma4_q(d) <==> DatatypeCtorId(d) == ##_module.Many.Ma4);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Many.Ma4_q(d) } 
  _module.Many.Ma4_q(d)
     ==> (exists a#149#0#0: int, a#149#1#0: int :: 
      d == #_module.Many.Ma4(a#149#0#0, a#149#1#0)));

// Constructor $Is
axiom (forall a#150#0#0: int, a#150#1#0: int :: 
  { $Is(#_module.Many.Ma4(a#150#0#0, a#150#1#0), Tclass._module.Many()) } 
  $Is(#_module.Many.Ma4(a#150#0#0, a#150#1#0), Tclass._module.Many())
     <==> $Is(a#150#0#0, TInt) && $Is(a#150#1#0, TInt));

// Constructor $IsAlloc
axiom (forall a#151#0#0: int, a#151#1#0: int, $h: Heap :: 
  { $IsAlloc(#_module.Many.Ma4(a#151#0#0, a#151#1#0), Tclass._module.Many(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Many.Ma4(a#151#0#0, a#151#1#0), Tclass._module.Many(), $h)
       <==> $IsAlloc(a#151#0#0, TInt, $h) && $IsAlloc(a#151#1#0, TInt, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Many.x(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Many.Ma4_q(d)
       && $IsAlloc(d, Tclass._module.Many(), $h)
     ==> $IsAlloc(_module.Many.x(d), TInt, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Many.u(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Many.Ma4_q(d)
       && $IsAlloc(d, Tclass._module.Many(), $h)
     ==> $IsAlloc(_module.Many.u(d), TInt, $h));

// Constructor literal
axiom (forall a#152#0#0: int, a#152#1#0: int :: 
  { #_module.Many.Ma4(LitInt(a#152#0#0), LitInt(a#152#1#0)) } 
  #_module.Many.Ma4(LitInt(a#152#0#0), LitInt(a#152#1#0))
     == Lit(#_module.Many.Ma4(a#152#0#0, a#152#1#0)));

// Constructor injectivity
axiom (forall a#153#0#0: int, a#153#1#0: int :: 
  { #_module.Many.Ma4(a#153#0#0, a#153#1#0) } 
  _module.Many.x(#_module.Many.Ma4(a#153#0#0, a#153#1#0)) == a#153#0#0);

// Constructor injectivity
axiom (forall a#154#0#0: int, a#154#1#0: int :: 
  { #_module.Many.Ma4(a#154#0#0, a#154#1#0) } 
  _module.Many.u(#_module.Many.Ma4(a#154#0#0, a#154#1#0)) == a#154#1#0);

// Constructor function declaration
function #_module.Many.Ma5(int, int) : DatatypeType;

const unique ##_module.Many.Ma5: DtCtorId;

// Constructor identifier
axiom (forall a#155#0#0: int, a#155#1#0: int :: 
  { #_module.Many.Ma5(a#155#0#0, a#155#1#0) } 
  DatatypeCtorId(#_module.Many.Ma5(a#155#0#0, a#155#1#0)) == ##_module.Many.Ma5);

function _module.Many.Ma5_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Many.Ma5_q(d) } 
  _module.Many.Ma5_q(d) <==> DatatypeCtorId(d) == ##_module.Many.Ma5);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Many.Ma5_q(d) } 
  _module.Many.Ma5_q(d)
     ==> (exists a#156#0#0: int, a#156#1#0: int :: 
      d == #_module.Many.Ma5(a#156#0#0, a#156#1#0)));

// Constructor $Is
axiom (forall a#157#0#0: int, a#157#1#0: int :: 
  { $Is(#_module.Many.Ma5(a#157#0#0, a#157#1#0), Tclass._module.Many()) } 
  $Is(#_module.Many.Ma5(a#157#0#0, a#157#1#0), Tclass._module.Many())
     <==> $Is(a#157#0#0, TInt) && $Is(a#157#1#0, TInt));

// Constructor $IsAlloc
axiom (forall a#158#0#0: int, a#158#1#0: int, $h: Heap :: 
  { $IsAlloc(#_module.Many.Ma5(a#158#0#0, a#158#1#0), Tclass._module.Many(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Many.Ma5(a#158#0#0, a#158#1#0), Tclass._module.Many(), $h)
       <==> $IsAlloc(a#158#0#0, TInt, $h) && $IsAlloc(a#158#1#0, TInt, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Many.x(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Many.Ma5_q(d)
       && $IsAlloc(d, Tclass._module.Many(), $h)
     ==> $IsAlloc(_module.Many.x(d), TInt, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Many.y(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Many.Ma5_q(d)
       && $IsAlloc(d, Tclass._module.Many(), $h)
     ==> $IsAlloc(_module.Many.y(d), TInt, $h));

// Constructor literal
axiom (forall a#159#0#0: int, a#159#1#0: int :: 
  { #_module.Many.Ma5(LitInt(a#159#0#0), LitInt(a#159#1#0)) } 
  #_module.Many.Ma5(LitInt(a#159#0#0), LitInt(a#159#1#0))
     == Lit(#_module.Many.Ma5(a#159#0#0, a#159#1#0)));

// Constructor injectivity
axiom (forall a#160#0#0: int, a#160#1#0: int :: 
  { #_module.Many.Ma5(a#160#0#0, a#160#1#0) } 
  _module.Many.x(#_module.Many.Ma5(a#160#0#0, a#160#1#0)) == a#160#0#0);

// Constructor injectivity
axiom (forall a#161#0#0: int, a#161#1#0: int :: 
  { #_module.Many.Ma5(a#161#0#0, a#161#1#0) } 
  _module.Many.y(#_module.Many.Ma5(a#161#0#0, a#161#1#0)) == a#161#1#0);

// Depth-one case-split function
function $IsA#_module.Many(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.Many(d) } 
  $IsA#_module.Many(d)
     ==> _module.Many.Ma0_q(d)
       || _module.Many.Ma1_q(d)
       || _module.Many.Ma2_q(d)
       || _module.Many.Ma3_q(d)
       || _module.Many.Ma4_q(d)
       || _module.Many.Ma5_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.Many.Ma5_q(d), $Is(d, Tclass._module.Many()) } 
    { _module.Many.Ma4_q(d), $Is(d, Tclass._module.Many()) } 
    { _module.Many.Ma3_q(d), $Is(d, Tclass._module.Many()) } 
    { _module.Many.Ma2_q(d), $Is(d, Tclass._module.Many()) } 
    { _module.Many.Ma1_q(d), $Is(d, Tclass._module.Many()) } 
    { _module.Many.Ma0_q(d), $Is(d, Tclass._module.Many()) } 
  $Is(d, Tclass._module.Many())
     ==> _module.Many.Ma0_q(d)
       || _module.Many.Ma1_q(d)
       || _module.Many.Ma2_q(d)
       || _module.Many.Ma3_q(d)
       || _module.Many.Ma4_q(d)
       || _module.Many.Ma5_q(d));

// Datatype extensional equality declaration
function _module.Many#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.Many.Ma0
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Many#Equal(a, b), _module.Many.Ma0_q(a) } 
    { _module.Many#Equal(a, b), _module.Many.Ma0_q(b) } 
  _module.Many.Ma0_q(a) && _module.Many.Ma0_q(b)
     ==> (_module.Many#Equal(a, b) <==> _module.Many.x(a) == _module.Many.x(b)));

// Datatype extensional equality definition: #_module.Many.Ma1
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Many#Equal(a, b), _module.Many.Ma1_q(a) } 
    { _module.Many#Equal(a, b), _module.Many.Ma1_q(b) } 
  _module.Many.Ma1_q(a) && _module.Many.Ma1_q(b)
     ==> (_module.Many#Equal(a, b)
       <==> _module.Many.u(a) == _module.Many.u(b)
         && _module.Many.fj(a) == _module.Many.fj(b)));

// Datatype extensional equality definition: #_module.Many.Ma2
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Many#Equal(a, b), _module.Many.Ma2_q(a) } 
    { _module.Many#Equal(a, b), _module.Many.Ma2_q(b) } 
  _module.Many.Ma2_q(a) && _module.Many.Ma2_q(b)
     ==> (_module.Many#Equal(a, b)
       <==> _module.Many.x(a) == _module.Many.x(b) && _module.Many.y(a) == _module.Many.y(b)));

// Datatype extensional equality definition: #_module.Many.Ma3
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Many#Equal(a, b), _module.Many.Ma3_q(a) } 
    { _module.Many#Equal(a, b), _module.Many.Ma3_q(b) } 
  _module.Many.Ma3_q(a) && _module.Many.Ma3_q(b)
     ==> (_module.Many#Equal(a, b)
       <==> _module.Many.x(a) == _module.Many.x(b) && _module.Many.z(a) == _module.Many.z(b)));

// Datatype extensional equality definition: #_module.Many.Ma4
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Many#Equal(a, b), _module.Many.Ma4_q(a) } 
    { _module.Many#Equal(a, b), _module.Many.Ma4_q(b) } 
  _module.Many.Ma4_q(a) && _module.Many.Ma4_q(b)
     ==> (_module.Many#Equal(a, b)
       <==> _module.Many.x(a) == _module.Many.x(b) && _module.Many.u(a) == _module.Many.u(b)));

// Datatype extensional equality definition: #_module.Many.Ma5
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Many#Equal(a, b), _module.Many.Ma5_q(a) } 
    { _module.Many#Equal(a, b), _module.Many.Ma5_q(b) } 
  _module.Many.Ma5_q(a) && _module.Many.Ma5_q(b)
     ==> (_module.Many#Equal(a, b)
       <==> _module.Many.x(a) == _module.Many.x(b) && _module.Many.y(a) == _module.Many.y(b)));

// Datatype extensionality axiom: _module.Many
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Many#Equal(a, b) } 
  _module.Many#Equal(a, b) <==> a == b);

const unique class._module.Many: ClassName;

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

procedure CheckWellformed$$_module.__default.M(d#0: DatatypeType
       where $Is(d#0, Tclass._module.Dt())
         && $IsAlloc(d#0, Tclass._module.Dt(), $Heap)
         && $IsA#_module.Dt(d#0))
   returns (r#0: int, s#0: real);
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.M(d#0: DatatypeType
       where $Is(d#0, Tclass._module.Dt())
         && $IsAlloc(d#0, Tclass._module.Dt(), $Heap)
         && $IsA#_module.Dt(d#0))
   returns (r#0: int, s#0: real);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.M(d#0: DatatypeType
       where $Is(d#0, Tclass._module.Dt())
         && $IsAlloc(d#0, Tclass._module.Dt(), $Heap)
         && $IsA#_module.Dt(d#0))
   returns (r#0: int, s#0: real, $_reverifyPost: bool);
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.M(d#0: DatatypeType) returns (r#0: int, s#0: real, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var n#0_0: DatatypeType
     where $Is(n#0_0, Tclass._module.Dt()) && $IsAlloc(n#0_0, Tclass._module.Dt(), $Heap);
  var dt_update_tmp#0#Z#0_0: DatatypeType;
  var let#0_0#0#0: DatatypeType;
  var dt_update#x#0#Z#0_0: int;
  var let#0_1#0#0: int;
  var dt_update#y#0#Z#0_0: real;
  var let#0_2#0#0: real;
  var h#1_0: ref
     where $Is(h#1_0, Tclass._module.MyClass())
       && $IsAlloc(h#1_0, Tclass._module.MyClass(), $Heap);
  var h#2_0: ref
     where $Is(h#2_0, Tclass._module.MyClass())
       && $IsAlloc(h#2_0, Tclass._module.MyClass(), $Heap);

    // AddMethodImpl: M, Impl$$_module.__default.M
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(13,0): initial state"} true;
    $_reverifyPost := false;
    // ----- alternative statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(14,3)
    if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(16,7)
        assume true;
        assert _module.Dt.A_q(d#0) || _module.Dt.B_q(d#0);
        assume true;
        r#0 := _module.Dt.x(d#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(16,12)"} true;
    }
    else if (*)
    {
        assume true;
        assume _module.Dt.A_q(d#0);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(18,7)
        assume true;
        assert _module.Dt.A_q(d#0) || _module.Dt.B_q(d#0);
        assume true;
        r#0 := _module.Dt.x(d#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(18,12)"} true;
    }
    else if (*)
    {
        assume true;
        assume _module.Dt.B_q(d#0);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(20,7)
        assume true;
        assert _module.Dt.A_q(d#0) || _module.Dt.B_q(d#0);
        assume true;
        r#0 := _module.Dt.x(d#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(20,12)"} true;
    }
    else if (*)
    {
        assume true;
        assume _module.Dt.C_q(d#0);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(22,7)
        assume true;
        assert _module.Dt.A_q(d#0) || _module.Dt.B_q(d#0);
        assume true;
        r#0 := _module.Dt.x(d#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(22,12)"} true;
    }
    else if (*)
    {
        assume true;
        assume _module.Dt.B_q(d#0);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(24,7)
        assume true;
        assert _module.Dt.A_q(d#0) || _module.Dt.C_q(d#0) || _module.Dt.D_q(d#0);
        assume true;
        s#0 := _module.Dt.y(d#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(24,12)"} true;
    }
    else if (*)
    {
        assume true;
        assume !_module.Dt.B_q(d#0);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(26,7)
        assume true;
        assert _module.Dt.A_q(d#0) || _module.Dt.C_q(d#0) || _module.Dt.D_q(d#0);
        assume true;
        s#0 := _module.Dt.y(d#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(26,12)"} true;
    }
    else if (*)
    {
        if (!_module.Dt.D_q(d#0))
        {
        }

        assume true;
        assume _module.Dt.D_q(d#0) || _module.Dt.C_q(d#0);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(28,7)
        assume true;
        assert _module.Dt.A_q(d#0) || _module.Dt.C_q(d#0) || _module.Dt.D_q(d#0);
        assume true;
        s#0 := _module.Dt.y(d#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(28,12)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(30,11)
        assume true;
        assert _module.Dt.B_q(d#0);
        assume true;
        h#2_0 := _module.Dt.h(d#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(30,16)"} true;
    }
    else if (*)
    {
        assume true;
        assume _module.Dt.B_q(d#0);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(32,11)
        assume true;
        assert _module.Dt.B_q(d#0);
        assume true;
        h#1_0 := _module.Dt.h(d#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(32,16)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(34,11)
        assume true;
        assert _module.Dt.A_q(d#0);
        havoc dt_update_tmp#0#Z#0_0;
        assume $Is(dt_update_tmp#0#Z#0_0, Tclass._module.Dt());
        assume let#0_0#0#0 == d#0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_0#0#0, Tclass._module.Dt());
        assume dt_update_tmp#0#Z#0_0 == let#0_0#0#0;
        havoc dt_update#x#0#Z#0_0;
        assume true;
        assume let#0_1#0#0 == LitInt(3);
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_1#0#0, TInt);
        assume dt_update#x#0#Z#0_0 == let#0_1#0#0;
        havoc dt_update#y#0#Z#0_0;
        assume true;
        assume let#0_2#0#0 == LitReal(27e-1);
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_2#0#0, TReal);
        assume dt_update#y#0#Z#0_0 == let#0_2#0#0;
        assume true;
        n#0_0 := (var dt_update_tmp#0#0_0 := d#0; 
          (var dt_update#x#0#0_0 := LitInt(3); 
            (var dt_update#y#0#0_0 := LitReal(27e-1); 
              Lit(#_module.Dt.A(dt_update#x#0#0_0, dt_update#y#0#0_0)))));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(34,33)"} true;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(35,5)
        assume true;
        assert _module.Dt.A_q(n#0_0);
    }
    else
    {
        assume true;
        assume true;
        assume true;
        assume true;
        assume true;
        assume true;
        assume true;
        assume true;
        assume true;
        assume true;
        assume !Lit(true)
           && !_module.Dt.A_q(d#0)
           && !_module.Dt.B_q(d#0)
           && !_module.Dt.C_q(d#0)
           && !_module.Dt.B_q(d#0)
           && _module.Dt.B_q(d#0)
           && !(_module.Dt.D_q(d#0) || _module.Dt.C_q(d#0))
           && !Lit(true)
           && !_module.Dt.B_q(d#0)
           && !Lit(true);
        assert false;
    }
}



procedure CheckWellformed$$_module.__default.N(r#0: DatatypeType
       where $Is(r#0, Tclass._module.Record())
         && $IsAlloc(r#0, Tclass._module.Record(), $Heap)
         && $IsA#_module.Record(r#0), 
    sh#0: DatatypeType
       where $Is(sh#0, Tclass._module.Shared())
         && $IsAlloc(sh#0, Tclass._module.Shared(), $Heap)
         && $IsA#_module.Shared(sh#0), 
    bb#0: DatatypeType
       where $Is(bb#0, Tclass._module.Shared())
         && $IsAlloc(bb#0, Tclass._module.Shared(), $Heap)
         && $IsA#_module.Shared(bb#0))
   returns (r'#0: DatatypeType
       where $Is(r'#0, Tclass._module.Record())
         && $IsAlloc(r'#0, Tclass._module.Record(), $Heap), 
    f#0: real, 
    sh'#0: DatatypeType
       where $Is(sh'#0, Tclass._module.Shared())
         && $IsAlloc(sh'#0, Tclass._module.Shared(), $Heap));
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.N(r#0: DatatypeType
       where $Is(r#0, Tclass._module.Record())
         && $IsAlloc(r#0, Tclass._module.Record(), $Heap)
         && $IsA#_module.Record(r#0), 
    sh#0: DatatypeType
       where $Is(sh#0, Tclass._module.Shared())
         && $IsAlloc(sh#0, Tclass._module.Shared(), $Heap)
         && $IsA#_module.Shared(sh#0), 
    bb#0: DatatypeType
       where $Is(bb#0, Tclass._module.Shared())
         && $IsAlloc(bb#0, Tclass._module.Shared(), $Heap)
         && $IsA#_module.Shared(bb#0))
   returns (r'#0: DatatypeType
       where $Is(r'#0, Tclass._module.Record())
         && $IsAlloc(r'#0, Tclass._module.Record(), $Heap), 
    f#0: real, 
    sh'#0: DatatypeType
       where $Is(sh'#0, Tclass._module.Shared())
         && $IsAlloc(sh'#0, Tclass._module.Shared(), $Heap));
  // user-defined preconditions
  requires _module.Shared.BB_q(bb#0);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.N(r#0: DatatypeType
       where $Is(r#0, Tclass._module.Record())
         && $IsAlloc(r#0, Tclass._module.Record(), $Heap)
         && $IsA#_module.Record(r#0), 
    sh#0: DatatypeType
       where $Is(sh#0, Tclass._module.Shared())
         && $IsAlloc(sh#0, Tclass._module.Shared(), $Heap)
         && $IsA#_module.Shared(sh#0), 
    bb#0: DatatypeType
       where $Is(bb#0, Tclass._module.Shared())
         && $IsAlloc(bb#0, Tclass._module.Shared(), $Heap)
         && $IsA#_module.Shared(bb#0))
   returns (r'#0: DatatypeType
       where $Is(r'#0, Tclass._module.Record())
         && $IsAlloc(r'#0, Tclass._module.Record(), $Heap), 
    f#0: real, 
    sh'#0: DatatypeType
       where $Is(sh'#0, Tclass._module.Shared())
         && $IsAlloc(sh'#0, Tclass._module.Shared(), $Heap), 
    $_reverifyPost: bool);
  free requires 5 == $FunctionContextHeight;
  // user-defined preconditions
  requires _module.Shared.BB_q(bb#0);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.N(r#0: DatatypeType, sh#0: DatatypeType, bb#0: DatatypeType)
   returns (r'#0: DatatypeType, f#0: real, sh'#0: DatatypeType, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var dt_update_tmp#0#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var dt_update#t#0#Z#0: int;
  var let#1#0#0: int;
  var dt_update_tmp#1#Z#0_0: DatatypeType;
  var let#0_0#0#0: DatatypeType;
  var dt_update#a#0#Z#0_0: real;
  var let#0_1#0#0: real;
  var dt_update_tmp#2#Z#2_0: DatatypeType;
  var let#2_0#0#0: DatatypeType;
  var dt_update#a#1#Z#2_0: real;
  var let#2_1#0#0: real;
  var dt_update_tmp#3#Z#0: DatatypeType;
  var let#2#0#0: DatatypeType;
  var dt_update#a#2#Z#0: real;
  var let#3#0#0: real;

    // AddMethodImpl: N, Impl$$_module.__default.N
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(43,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(44,6)
    assume true;
    havoc dt_update_tmp#0#Z#0;
    assume $Is(dt_update_tmp#0#Z#0, Tclass._module.Record());
    assume let#0#0#0 == r#0;
    assume true;
    // CheckWellformedWithResult: any expression
    assume $Is(let#0#0#0, Tclass._module.Record());
    assume dt_update_tmp#0#Z#0 == let#0#0#0;
    havoc dt_update#t#0#Z#0;
    assume true;
    assume _module.Record.Record_q(r#0);
    assume _module.Shared.AA_q(sh#0) || _module.Shared.BB_q(sh#0);
    assume let#1#0#0 == _module.Record.t(r#0) + _module.Shared.id(sh#0);
    assume _module.Record.Record_q(r#0)
       && (_module.Shared.AA_q(sh#0) || _module.Shared.BB_q(sh#0));
    // CheckWellformedWithResult: any expression
    assume $Is(let#1#0#0, TInt);
    assume dt_update#t#0#Z#0 == let#1#0#0;
    assume _module.Record.Record_q(r#0)
       && (_module.Shared.AA_q(sh#0) || _module.Shared.BB_q(sh#0));
    r'#0 := (var dt_update_tmp#0#0 := r#0; 
      (var dt_update#t#0#0 := _module.Record.t(r#0) + _module.Shared.id(sh#0); 
        #_module.Record.Record(dt_update#t#0#0)));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(44,28)"} true;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(45,3)
    assume true;
    if (_module.Shared.AA_q(sh#0))
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(46,7)
        assume true;
        assert _module.Shared.AA_q(sh#0);
        assume true;
        f#0 := _module.Shared.a(sh#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(46,13)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(47,9)
        assume true;
        assert _module.Shared.AA_q(sh#0);
        havoc dt_update_tmp#1#Z#0_0;
        assume $Is(dt_update_tmp#1#Z#0_0, Tclass._module.Shared());
        assume let#0_0#0#0 == sh#0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_0#0#0, Tclass._module.Shared());
        assume dt_update_tmp#1#Z#0_0 == let#0_0#0#0;
        havoc dt_update#a#0#Z#0_0;
        assume true;
        assert _module.Shared.BB_q(bb#0);
        assume let#0_1#0#0 == _module.Shared.b(bb#0) + 1002e-1;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_1#0#0, TReal);
        assume dt_update#a#0#Z#0_0 == let#0_1#0#0;
        assume _module.Shared.AA_q(dt_update_tmp#1#Z#0_0)
           || _module.Shared.BB_q(dt_update_tmp#1#Z#0_0);
        assert _module.Shared.AA_q(dt_update_tmp#1#Z#0_0);
        assume (var dt_update_tmp#1#0_0 := sh#0; 
          _module.Shared.AA_q(dt_update_tmp#1#0_0)
             || _module.Shared.BB_q(dt_update_tmp#1#0_0));
        sh'#0 := (var dt_update_tmp#1#0_0 := sh#0; 
          (var dt_update#a#0#0_0 := _module.Shared.b(bb#0) + 1002e-1; 
            #_module.Shared.AA(_module.Shared.id(dt_update_tmp#1#0_0), 
              dt_update#a#0#0_0, 
              _module.Shared.c(dt_update_tmp#1#0_0))));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(47,33)"} true;
    }
    else
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(49,9)
        assume true;
        assume _module.Record.Record_q(r#0);
        assume _module.Record.Record_q(r#0);
        assume _module.Record.Record_q(r#0) && _module.Record.Record_q(r#0);
        sh'#0 := #_module.Shared.AA(_module.Record.t(r#0), Real(_module.Record.t(r#0)), LitReal(0e0));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(49,36)"} true;
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(50,5)
        if (*)
        {
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(51,9)
            assume true;
            assert _module.Shared.AA_q(sh#0);
            assume true;
            f#0 := _module.Shared.a(sh#0);
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(51,15)"} true;
        }
        else
        {
        }
    }

    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(54,3)
    if (*)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(55,9)
        assume true;
        assert _module.Shared.AA_q(sh'#0);
        havoc dt_update_tmp#2#Z#2_0;
        assume $Is(dt_update_tmp#2#Z#2_0, Tclass._module.Shared());
        assume let#2_0#0#0 == sh'#0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#2_0#0#0, Tclass._module.Shared());
        assume dt_update_tmp#2#Z#2_0 == let#2_0#0#0;
        havoc dt_update#a#1#Z#2_0;
        assume true;
        assert _module.Shared.BB_q(bb#0);
        assume let#2_1#0#0 == _module.Shared.b(bb#0);
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#2_1#0#0, TReal);
        assume dt_update#a#1#Z#2_0 == let#2_1#0#0;
        assume _module.Shared.AA_q(dt_update_tmp#2#Z#2_0)
           || _module.Shared.BB_q(dt_update_tmp#2#Z#2_0);
        assert _module.Shared.AA_q(dt_update_tmp#2#Z#2_0);
        assume (var dt_update_tmp#2#2_0 := sh'#0; 
          _module.Shared.AA_q(dt_update_tmp#2#2_0)
             || _module.Shared.BB_q(dt_update_tmp#2#2_0));
        sh'#0 := (var dt_update_tmp#2#2_0 := sh'#0; 
          (var dt_update#a#1#2_0 := _module.Shared.b(bb#0); 
            #_module.Shared.AA(_module.Shared.id(dt_update_tmp#2#2_0), 
              dt_update#a#1#2_0, 
              _module.Shared.c(dt_update_tmp#2#2_0))));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(55,26)"} true;
    }
    else
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(57,9)
        assume true;
        assert _module.Shared.AA_q(sh#0);
        havoc dt_update_tmp#3#Z#0;
        assume $Is(dt_update_tmp#3#Z#0, Tclass._module.Shared());
        assume let#2#0#0 == sh#0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#2#0#0, Tclass._module.Shared());
        assume dt_update_tmp#3#Z#0 == let#2#0#0;
        havoc dt_update#a#2#Z#0;
        assume true;
        assert _module.Shared.BB_q(bb#0);
        assume let#3#0#0 == _module.Shared.b(bb#0);
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#3#0#0, TReal);
        assume dt_update#a#2#Z#0 == let#3#0#0;
        assume _module.Shared.AA_q(dt_update_tmp#3#Z#0)
           || _module.Shared.BB_q(dt_update_tmp#3#Z#0);
        assert _module.Shared.AA_q(dt_update_tmp#3#Z#0);
        assume (var dt_update_tmp#3#0 := sh#0; 
          _module.Shared.AA_q(dt_update_tmp#3#0) || _module.Shared.BB_q(dt_update_tmp#3#0));
        sh'#0 := (var dt_update_tmp#3#0 := sh#0; 
          (var dt_update#a#2#0 := _module.Shared.b(bb#0); 
            #_module.Shared.AA(_module.Shared.id(dt_update_tmp#3#0), 
              dt_update#a#2#0, 
              _module.Shared.c(dt_update_tmp#3#0))));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(57,25)"} true;
    }
}



procedure CheckWellformed$$_module.__default.UpdateA(y#0: DatatypeType
       where $Is(y#0, Tclass._module.Quirky())
         && $IsAlloc(y#0, Tclass._module.Quirky(), $Heap)
         && $IsA#_module.Quirky(y#0))
   returns (y'#0: DatatypeType
       where $Is(y'#0, Tclass._module.Quirky())
         && $IsAlloc(y'#0, Tclass._module.Quirky(), $Heap));
  free requires 7 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.UpdateA(y#0: DatatypeType
       where $Is(y#0, Tclass._module.Quirky())
         && $IsAlloc(y#0, Tclass._module.Quirky(), $Heap)
         && $IsA#_module.Quirky(y#0))
   returns (y'#0: DatatypeType
       where $Is(y'#0, Tclass._module.Quirky())
         && $IsAlloc(y'#0, Tclass._module.Quirky(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.UpdateA(y#0: DatatypeType
       where $Is(y#0, Tclass._module.Quirky())
         && $IsAlloc(y#0, Tclass._module.Quirky(), $Heap)
         && $IsA#_module.Quirky(y#0))
   returns (y'#0: DatatypeType
       where $Is(y'#0, Tclass._module.Quirky())
         && $IsAlloc(y'#0, Tclass._module.Quirky(), $Heap), 
    $_reverifyPost: bool);
  free requires 7 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.UpdateA(y#0: DatatypeType) returns (y'#0: DatatypeType, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var dt_update_tmp#4#Z#0_0: DatatypeType;
  var let#0_0#0#0: DatatypeType;
  var dt_update#c#2#Z#0_0: int;
  var let#0_1#0#0: int;
  var dt_update_tmp#3#Z#1_0: DatatypeType;
  var let#1_0#0#0: DatatypeType;
  var dt_update#c#1#Z#1_0: int;
  var let#1_1#0#0: int;
  var dt_update_tmp#2#Z#2_0: DatatypeType;
  var let#2_0#0#0: DatatypeType;
  var dt_update#d#0#Z#2_0: int;
  var let#2_1#0#0: int;
  var dt_update#c#0#Z#2_0: int;
  var let#2_2#0#0: int;
  var dt_update_tmp#1#Z#3_0: DatatypeType;
  var let#3_0#0#0: DatatypeType;
  var dt_update#b#0#Z#3_0: int;
  var let#3_1#0#0: int;
  var dt_update_tmp#0#Z#4_0: DatatypeType;
  var let#4_0#0#0: DatatypeType;
  var dt_update#a#0#Z#4_0: int;
  var let#4_1#0#0: int;

    // AddMethodImpl: UpdateA, Impl$$_module.__default.UpdateA
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(64,0): initial state"} true;
    $_reverifyPost := false;
    // ----- alternative statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(92,3)
    if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(95,8)
        assume true;
        assert _module.Quirky.PP_q(y#0);
        havoc dt_update_tmp#0#Z#4_0;
        assume $Is(dt_update_tmp#0#Z#4_0, Tclass._module.Quirky());
        assume let#4_0#0#0 == y#0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#4_0#0#0, Tclass._module.Quirky());
        assume dt_update_tmp#0#Z#4_0 == let#4_0#0#0;
        havoc dt_update#a#0#Z#4_0;
        assume true;
        assume let#4_1#0#0 == LitInt(10);
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#4_1#0#0, TInt);
        assume dt_update#a#0#Z#4_0 == let#4_1#0#0;
        assume _module.Quirky.PP_q(dt_update_tmp#0#Z#4_0)
           || _module.Quirky.QQ_q(dt_update_tmp#0#Z#4_0)
           || _module.Quirky.RR_q(dt_update_tmp#0#Z#4_0);
        assume (var dt_update_tmp#0#4_0 := y#0; 
          _module.Quirky.PP_q(dt_update_tmp#0#4_0)
             || _module.Quirky.QQ_q(dt_update_tmp#0#4_0)
             || _module.Quirky.RR_q(dt_update_tmp#0#4_0));
        y'#0 := (var dt_update_tmp#0#4_0 := y#0; 
          (var dt_update#a#0#4_0 := LitInt(10); 
            #_module.Quirky.PP(_module.Quirky.id(dt_update_tmp#0#4_0), dt_update#a#0#4_0)));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(95,21)"} true;
    }
    else if (*)
    {
        assume true;
        assume _module.Quirky.QQ_q(y#0);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(98,8)
        assume true;
        assert _module.Quirky.QQ_q(y#0);
        havoc dt_update_tmp#1#Z#3_0;
        assume $Is(dt_update_tmp#1#Z#3_0, Tclass._module.Quirky());
        assume let#3_0#0#0 == y#0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#3_0#0#0, Tclass._module.Quirky());
        assume dt_update_tmp#1#Z#3_0 == let#3_0#0#0;
        havoc dt_update#b#0#Z#3_0;
        assume true;
        assume let#3_1#0#0 == LitInt(10);
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#3_1#0#0, TInt);
        assume dt_update#b#0#Z#3_0 == let#3_1#0#0;
        assume _module.Quirky.PP_q(dt_update_tmp#1#Z#3_0)
           || _module.Quirky.QQ_q(dt_update_tmp#1#Z#3_0)
           || _module.Quirky.RR_q(dt_update_tmp#1#Z#3_0);
        assume (var dt_update_tmp#1#3_0 := y#0; 
          _module.Quirky.PP_q(dt_update_tmp#1#3_0)
             || _module.Quirky.QQ_q(dt_update_tmp#1#3_0)
             || _module.Quirky.RR_q(dt_update_tmp#1#3_0));
        y'#0 := (var dt_update_tmp#1#3_0 := y#0; 
          (var dt_update#b#0#3_0 := LitInt(10); 
            #_module.Quirky.QQ(dt_update#b#0#3_0, _module.Quirky.id(dt_update_tmp#1#3_0))));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(98,21)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(101,8)
        assume true;
        assert _module.Quirky.RR_q(y#0);
        havoc dt_update_tmp#2#Z#2_0;
        assume $Is(dt_update_tmp#2#Z#2_0, Tclass._module.Quirky());
        assume let#2_0#0#0 == y#0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#2_0#0#0, Tclass._module.Quirky());
        assume dt_update_tmp#2#Z#2_0 == let#2_0#0#0;
        havoc dt_update#d#0#Z#2_0;
        assume true;
        assume let#2_1#0#0 == LitInt(20);
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#2_1#0#0, TInt);
        assume dt_update#d#0#Z#2_0 == let#2_1#0#0;
        havoc dt_update#c#0#Z#2_0;
        assume true;
        assume let#2_2#0#0 == LitInt(10);
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#2_2#0#0, TInt);
        assume dt_update#c#0#Z#2_0 == let#2_2#0#0;
        assume _module.Quirky.PP_q(dt_update_tmp#2#Z#2_0)
           || _module.Quirky.QQ_q(dt_update_tmp#2#Z#2_0)
           || _module.Quirky.RR_q(dt_update_tmp#2#Z#2_0);
        assume (var dt_update_tmp#2#2_0 := y#0; 
          _module.Quirky.PP_q(dt_update_tmp#2#2_0)
             || _module.Quirky.QQ_q(dt_update_tmp#2#2_0)
             || _module.Quirky.RR_q(dt_update_tmp#2#2_0));
        y'#0 := (var dt_update_tmp#2#2_0 := y#0; 
          (var dt_update#d#0#2_0 := LitInt(20); 
            (var dt_update#c#0#2_0 := LitInt(10); 
              #_module.Quirky.RR(_module.Quirky.id(dt_update_tmp#2#2_0), dt_update#c#0#2_0, dt_update#d#0#2_0))));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(101,30)"} true;
    }
    else if (*)
    {
        assume true;
        assume _module.Quirky.RR_q(y#0);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(104,8)
        assume true;
        assert _module.Quirky.RR_q(y#0);
        havoc dt_update_tmp#3#Z#1_0;
        assume $Is(dt_update_tmp#3#Z#1_0, Tclass._module.Quirky());
        assume let#1_0#0#0 == y#0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#1_0#0#0, Tclass._module.Quirky());
        assume dt_update_tmp#3#Z#1_0 == let#1_0#0#0;
        havoc dt_update#c#1#Z#1_0;
        assume true;
        assume let#1_1#0#0 == LitInt(10);
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#1_1#0#0, TInt);
        assume dt_update#c#1#Z#1_0 == let#1_1#0#0;
        assume _module.Quirky.PP_q(dt_update_tmp#3#Z#1_0)
           || _module.Quirky.QQ_q(dt_update_tmp#3#Z#1_0)
           || _module.Quirky.RR_q(dt_update_tmp#3#Z#1_0);
        assert _module.Quirky.RR_q(dt_update_tmp#3#Z#1_0);
        assume (var dt_update_tmp#3#1_0 := y#0; 
          _module.Quirky.PP_q(dt_update_tmp#3#1_0)
             || _module.Quirky.QQ_q(dt_update_tmp#3#1_0)
             || _module.Quirky.RR_q(dt_update_tmp#3#1_0));
        y'#0 := (var dt_update_tmp#3#1_0 := y#0; 
          (var dt_update#c#1#1_0 := LitInt(10); 
            #_module.Quirky.RR(_module.Quirky.id(dt_update_tmp#3#1_0), 
              dt_update#c#1#1_0, 
              _module.Quirky.d(dt_update_tmp#3#1_0))));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(104,21)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(107,8)
        assume true;
        assert _module.Quirky.RR_q(y#0);
        havoc dt_update_tmp#4#Z#0_0;
        assume $Is(dt_update_tmp#4#Z#0_0, Tclass._module.Quirky());
        assume let#0_0#0#0 == y#0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_0#0#0, Tclass._module.Quirky());
        assume dt_update_tmp#4#Z#0_0 == let#0_0#0#0;
        havoc dt_update#c#2#Z#0_0;
        assume true;
        assume let#0_1#0#0 == LitInt(10);
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_1#0#0, TInt);
        assume dt_update#c#2#Z#0_0 == let#0_1#0#0;
        assume _module.Quirky.PP_q(dt_update_tmp#4#Z#0_0)
           || _module.Quirky.QQ_q(dt_update_tmp#4#Z#0_0)
           || _module.Quirky.RR_q(dt_update_tmp#4#Z#0_0);
        assert _module.Quirky.RR_q(dt_update_tmp#4#Z#0_0);
        assume (var dt_update_tmp#4#0_0 := y#0; 
          _module.Quirky.PP_q(dt_update_tmp#4#0_0)
             || _module.Quirky.QQ_q(dt_update_tmp#4#0_0)
             || _module.Quirky.RR_q(dt_update_tmp#4#0_0));
        y'#0 := (var dt_update_tmp#4#0_0 := y#0; 
          (var dt_update#c#2#0_0 := LitInt(10); 
            #_module.Quirky.RR(_module.Quirky.id(dt_update_tmp#4#0_0), 
              dt_update#c#2#0_0, 
              _module.Quirky.d(dt_update_tmp#4#0_0))));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(107,21)"} true;
    }
    else
    {
        assume true;
        assume true;
        assume true;
        assume true;
        assume true;
        assume !Lit(true)
           && !_module.Quirky.QQ_q(y#0)
           && !Lit(true)
           && !_module.Quirky.RR_q(y#0)
           && !Lit(true);
        assert false;
    }
}



procedure CheckWellformed$$_module.__default.TroubleKlef(k#0: DatatypeType
       where $Is(k#0, Tclass._module.Klef())
         && $IsAlloc(k#0, Tclass._module.Klef(), $Heap)
         && $IsA#_module.Klef(k#0))
   returns (k'#0: DatatypeType
       where $Is(k'#0, Tclass._module.Klef()) && $IsAlloc(k'#0, Tclass._module.Klef(), $Heap));
  free requires 9 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.TroubleKlef(k#0: DatatypeType
       where $Is(k#0, Tclass._module.Klef())
         && $IsAlloc(k#0, Tclass._module.Klef(), $Heap)
         && $IsA#_module.Klef(k#0))
   returns (k'#0: DatatypeType
       where $Is(k'#0, Tclass._module.Klef()) && $IsAlloc(k'#0, Tclass._module.Klef(), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures _module.Klef.C3_q(k'#0);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.TroubleKlef(k#0: DatatypeType
       where $Is(k#0, Tclass._module.Klef())
         && $IsAlloc(k#0, Tclass._module.Klef(), $Heap)
         && $IsA#_module.Klef(k#0))
   returns (k'#0: DatatypeType
       where $Is(k'#0, Tclass._module.Klef()) && $IsAlloc(k'#0, Tclass._module.Klef(), $Heap), 
    $_reverifyPost: bool);
  free requires 9 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures _module.Klef.C3_q(k'#0);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.TroubleKlef(k#0: DatatypeType) returns (k'#0: DatatypeType, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var dt_update_tmp#1#Z#0_0: DatatypeType;
  var let#0_0#0#0: DatatypeType;
  var dt_update#c3#1#Z#0_0: int;
  var let#0_1#0#0: int;
  var dt_update#0#1#Z#0_0: int;
  var let#0_2#0#0: int;
  var dt_update_tmp#0#Z#1_0: DatatypeType;
  var let#1_0#0#0: DatatypeType;
  var dt_update#c3#0#Z#1_0: int;
  var let#1_1#0#0: int;
  var dt_update#0#0#Z#1_0: int;
  var let#1_2#0#0: int;

    // AddMethodImpl: TroubleKlef, Impl$$_module.__default.TroubleKlef
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(118,0): initial state"} true;
    $_reverifyPost := false;
    // ----- alternative statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(119,3)
    if (*)
    {
        assume true;
        assume _module.Klef.C3_q(k#0);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(121,8)
        assume true;
        assert _module.Klef.C3_q(k#0);
        havoc dt_update_tmp#0#Z#1_0;
        assume $Is(dt_update_tmp#0#Z#1_0, Tclass._module.Klef());
        assume let#1_0#0#0 == k#0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#1_0#0#0, Tclass._module.Klef());
        assume dt_update_tmp#0#Z#1_0 == let#1_0#0#0;
        havoc dt_update#c3#0#Z#1_0;
        assume true;
        assume let#1_1#0#0 == LitInt(200);
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#1_1#0#0, TInt);
        assume dt_update#c3#0#Z#1_0 == let#1_1#0#0;
        havoc dt_update#0#0#Z#1_0;
        assume true;
        assume let#1_2#0#0 == LitInt(100);
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#1_2#0#0, TInt);
        assume dt_update#0#0#Z#1_0 == let#1_2#0#0;
        assert _module.Klef.C1_q(dt_update_tmp#0#Z#1_0)
           || _module.Klef.C2_q(dt_update_tmp#0#Z#1_0)
           || _module.Klef.C3_q(dt_update_tmp#0#Z#1_0);
        assert _module.Klef.C0_q(dt_update_tmp#0#Z#1_0)
           || _module.Klef.C1_q(dt_update_tmp#0#Z#1_0)
           || _module.Klef.C3_q(dt_update_tmp#0#Z#1_0);
        assume true;
        k'#0 := (var dt_update_tmp#0#1_0 := k#0; 
          (var dt_update#c3#0#1_0 := LitInt(200); 
            (var dt_update#0#0#1_0 := LitInt(100); 
              #_module.Klef.C3(_module.Klef._3(dt_update_tmp#0#1_0), 
                dt_update#0#0#1_0, 
                _module.Klef._1(dt_update_tmp#0#1_0), 
                dt_update#c3#0#1_0))));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(121,33)"} true;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(122,5)
        assert _module.Klef.C1_q(k#0) || _module.Klef.C2_q(k#0) || _module.Klef.C3_q(k#0);
        assert _module.Klef.C0_q(k#0) || _module.Klef.C1_q(k#0) || _module.Klef.C3_q(k#0);
        assume $IsA#_module.Klef(k'#0);
        assert _module.Klef#Equal(k'#0, 
          #_module.Klef.C3(_module.Klef._3(k#0), LitInt(100), _module.Klef._1(k#0), LitInt(200)));
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(124,8)
        assume true;
        assert _module.Klef.C3_q(k#0);
        havoc dt_update_tmp#1#Z#0_0;
        assume $Is(dt_update_tmp#1#Z#0_0, Tclass._module.Klef());
        assume let#0_0#0#0 == k#0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_0#0#0, Tclass._module.Klef());
        assume dt_update_tmp#1#Z#0_0 == let#0_0#0#0;
        havoc dt_update#c3#1#Z#0_0;
        assume true;
        assume let#0_1#0#0 == LitInt(200);
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_1#0#0, TInt);
        assume dt_update#c3#1#Z#0_0 == let#0_1#0#0;
        havoc dt_update#0#1#Z#0_0;
        assume true;
        assume let#0_2#0#0 == LitInt(100);
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_2#0#0, TInt);
        assume dt_update#0#1#Z#0_0 == let#0_2#0#0;
        assert _module.Klef.C1_q(dt_update_tmp#1#Z#0_0)
           || _module.Klef.C2_q(dt_update_tmp#1#Z#0_0)
           || _module.Klef.C3_q(dt_update_tmp#1#Z#0_0);
        assert _module.Klef.C0_q(dt_update_tmp#1#Z#0_0)
           || _module.Klef.C1_q(dt_update_tmp#1#Z#0_0)
           || _module.Klef.C3_q(dt_update_tmp#1#Z#0_0);
        assume true;
        k'#0 := (var dt_update_tmp#1#0_0 := k#0; 
          (var dt_update#c3#1#0_0 := LitInt(200); 
            (var dt_update#0#1#0_0 := LitInt(100); 
              #_module.Klef.C3(_module.Klef._3(dt_update_tmp#1#0_0), 
                dt_update#0#1#0_0, 
                _module.Klef._1(dt_update_tmp#1#0_0), 
                dt_update#c3#1#0_0))));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(124,33)"} true;
    }
    else
    {
        assume true;
        assume true;
        assume !_module.Klef.C3_q(k#0) && !Lit(true);
        assert false;
    }
}



procedure CheckWellformed$$_module.__default.TestMany(m#0: DatatypeType
       where $Is(m#0, Tclass._module.Many())
         && $IsAlloc(m#0, Tclass._module.Many(), $Heap)
         && $IsA#_module.Many(m#0))
   returns (r#0: DatatypeType
       where $Is(r#0, Tclass._module.Many()) && $IsAlloc(r#0, Tclass._module.Many(), $Heap));
  free requires 11 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.TestMany(m#0: DatatypeType
       where $Is(m#0, Tclass._module.Many())
         && $IsAlloc(m#0, Tclass._module.Many(), $Heap)
         && $IsA#_module.Many(m#0))
   returns (r#0: DatatypeType
       where $Is(r#0, Tclass._module.Many()) && $IsAlloc(r#0, Tclass._module.Many(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.TestMany(m#0: DatatypeType
       where $Is(m#0, Tclass._module.Many())
         && $IsAlloc(m#0, Tclass._module.Many(), $Heap)
         && $IsA#_module.Many(m#0))
   returns (r#0: DatatypeType
       where $Is(r#0, Tclass._module.Many()) && $IsAlloc(r#0, Tclass._module.Many(), $Heap), 
    $_reverifyPost: bool);
  free requires 11 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.TestMany(m#0: DatatypeType) returns (r#0: DatatypeType, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var dt_update_tmp#3#Z#0_0: DatatypeType;
  var let#0_0#0#0: DatatypeType;
  var dt_update#x#2#Z#0_0: int;
  var let#0_1#0#0: int;
  var dt_update_tmp#2#Z#1_0: DatatypeType;
  var let#1_0#0#0: DatatypeType;
  var dt_update#u#0#Z#1_0: int;
  var let#1_1#0#0: int;
  var dt_update_tmp#1#Z#2_0: DatatypeType;
  var let#2_0#0#0: DatatypeType;
  var dt_update#y#1#Z#2_0: int;
  var let#2_1#0#0: int;
  var dt_update#x#1#Z#2_0: int;
  var let#2_2#0#0: int;
  var dt_update_tmp#0#Z#3_0: DatatypeType;
  var let#3_0#0#0: DatatypeType;
  var dt_update#y#0#Z#3_0: int;
  var let#3_1#0#0: int;
  var dt_update#x#0#Z#3_0: int;
  var let#3_2#0#0: int;

    // AddMethodImpl: TestMany, Impl$$_module.__default.TestMany
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(136,0): initial state"} true;
    $_reverifyPost := false;
    // ----- alternative statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(137,3)
    if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(139,7)
        assume true;
        assert _module.Many.Ma5_q(m#0) || _module.Many.Ma2_q(m#0);
        havoc dt_update_tmp#0#Z#3_0;
        assume $Is(dt_update_tmp#0#Z#3_0, Tclass._module.Many());
        assume let#3_0#0#0 == m#0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#3_0#0#0, Tclass._module.Many());
        assume dt_update_tmp#0#Z#3_0 == let#3_0#0#0;
        havoc dt_update#y#0#Z#3_0;
        assume true;
        assume let#3_1#0#0 == LitInt(4);
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#3_1#0#0, TInt);
        assume dt_update#y#0#Z#3_0 == let#3_1#0#0;
        havoc dt_update#x#0#Z#3_0;
        assume true;
        assume let#3_2#0#0 == LitInt(3);
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#3_2#0#0, TInt);
        assume dt_update#x#0#Z#3_0 == let#3_2#0#0;
        if (_module.Many.Ma2_q(dt_update_tmp#0#Z#3_0))
        {
        }
        else
        {
        }

        assume true;
        r#0 := (var dt_update_tmp#0#3_0 := m#0; 
          (var dt_update#y#0#3_0 := LitInt(4); 
            (var dt_update#x#0#3_0 := LitInt(3); 
              (if _module.Many.Ma2_q(dt_update_tmp#0#3_0)
                 then #_module.Many.Ma2(dt_update#x#0#3_0, dt_update#y#0#3_0)
                 else #_module.Many.Ma5(dt_update#x#0#3_0, dt_update#y#0#3_0)))));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(139,27)"} true;
    }
    else if (*)
    {
        if (!_module.Many.Ma2_q(m#0))
        {
        }

        assume true;
        assume _module.Many.Ma2_q(m#0) || _module.Many.Ma5_q(m#0);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(141,7)
        assume true;
        assert _module.Many.Ma5_q(m#0) || _module.Many.Ma2_q(m#0);
        havoc dt_update_tmp#1#Z#2_0;
        assume $Is(dt_update_tmp#1#Z#2_0, Tclass._module.Many());
        assume let#2_0#0#0 == m#0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#2_0#0#0, Tclass._module.Many());
        assume dt_update_tmp#1#Z#2_0 == let#2_0#0#0;
        havoc dt_update#y#1#Z#2_0;
        assume true;
        assume let#2_1#0#0 == LitInt(4);
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#2_1#0#0, TInt);
        assume dt_update#y#1#Z#2_0 == let#2_1#0#0;
        havoc dt_update#x#1#Z#2_0;
        assume true;
        assume let#2_2#0#0 == LitInt(3);
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#2_2#0#0, TInt);
        assume dt_update#x#1#Z#2_0 == let#2_2#0#0;
        if (_module.Many.Ma2_q(dt_update_tmp#1#Z#2_0))
        {
        }
        else
        {
        }

        assume true;
        r#0 := (var dt_update_tmp#1#2_0 := m#0; 
          (var dt_update#y#1#2_0 := LitInt(4); 
            (var dt_update#x#1#2_0 := LitInt(3); 
              (if _module.Many.Ma2_q(dt_update_tmp#1#2_0)
                 then #_module.Many.Ma2(dt_update#x#1#2_0, dt_update#y#1#2_0)
                 else #_module.Many.Ma5(dt_update#x#1#2_0, dt_update#y#1#2_0)))));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(141,27)"} true;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(142,5)
        assert _module.Many.Ma0_q(r#0)
           || _module.Many.Ma2_q(r#0)
           || _module.Many.Ma3_q(r#0)
           || _module.Many.Ma4_q(r#0)
           || _module.Many.Ma5_q(r#0);
        assume true;
        assert _module.Many.x(r#0) == LitInt(3);
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(143,5)
        assert _module.Many.Ma2_q(r#0) || _module.Many.Ma5_q(r#0);
        assume true;
        assert _module.Many.y(r#0) == LitInt(4);
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(144,5)
        if (!_module.Many.Ma2_q(r#0))
        {
        }

        assume true;
        assert _module.Many.Ma2_q(r#0) || _module.Many.Ma5_q(r#0);
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(145,5)
        assume true;
        assert _module.Many.Ma2_q(r#0);
    }
    else if (*)
    {
        assume true;
        assume _module.Many.Ma4_q(m#0);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(147,7)
        assume true;
        assert _module.Many.Ma4_q(m#0) || _module.Many.Ma1_q(m#0);
        havoc dt_update_tmp#2#Z#1_0;
        assume $Is(dt_update_tmp#2#Z#1_0, Tclass._module.Many());
        assume let#1_0#0#0 == m#0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#1_0#0#0, Tclass._module.Many());
        assume dt_update_tmp#2#Z#1_0 == let#1_0#0#0;
        havoc dt_update#u#0#Z#1_0;
        assume true;
        assume let#1_1#0#0 == LitInt(8);
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#1_1#0#0, TInt);
        assume dt_update#u#0#Z#1_0 == let#1_1#0#0;
        if (_module.Many.Ma1_q(dt_update_tmp#2#Z#1_0))
        {
            assert _module.Many.Ma1_q(dt_update_tmp#2#Z#1_0);
        }
        else
        {
            assert _module.Many.Ma0_q(dt_update_tmp#2#Z#1_0)
               || _module.Many.Ma2_q(dt_update_tmp#2#Z#1_0)
               || _module.Many.Ma3_q(dt_update_tmp#2#Z#1_0)
               || _module.Many.Ma4_q(dt_update_tmp#2#Z#1_0)
               || _module.Many.Ma5_q(dt_update_tmp#2#Z#1_0);
        }

        assume true;
        r#0 := (var dt_update_tmp#2#1_0 := m#0; 
          (var dt_update#u#0#1_0 := LitInt(8); 
            (if _module.Many.Ma1_q(dt_update_tmp#2#1_0)
               then #_module.Many.Ma1(dt_update#u#0#1_0, _module.Many.fj(dt_update_tmp#2#1_0))
               else #_module.Many.Ma4(_module.Many.x(dt_update_tmp#2#1_0), dt_update#u#0#1_0))));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(147,19)"} true;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(148,5)
        assume true;
        assert _module.Many.Ma4_q(m#0);
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(149,5)
        assert _module.Many.Ma0_q(r#0)
           || _module.Many.Ma2_q(r#0)
           || _module.Many.Ma3_q(r#0)
           || _module.Many.Ma4_q(r#0)
           || _module.Many.Ma5_q(r#0);
        assert _module.Many.Ma0_q(m#0)
           || _module.Many.Ma2_q(m#0)
           || _module.Many.Ma3_q(m#0)
           || _module.Many.Ma4_q(m#0)
           || _module.Many.Ma5_q(m#0);
        assume true;
        assert _module.Many.x(r#0) == _module.Many.x(m#0);
    }
    else if (*)
    {
        assume true;
        assume !_module.Many.Ma1_q(m#0);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(151,7)
        assume true;
        assert _module.Many.Ma5_q(m#0)
           || _module.Many.Ma4_q(m#0)
           || _module.Many.Ma3_q(m#0)
           || _module.Many.Ma2_q(m#0)
           || _module.Many.Ma0_q(m#0);
        havoc dt_update_tmp#3#Z#0_0;
        assume $Is(dt_update_tmp#3#Z#0_0, Tclass._module.Many());
        assume let#0_0#0#0 == m#0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_0#0#0, Tclass._module.Many());
        assume dt_update_tmp#3#Z#0_0 == let#0_0#0#0;
        havoc dt_update#x#2#Z#0_0;
        assume true;
        assume let#0_1#0#0 == LitInt(5);
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_1#0#0, TInt);
        assume dt_update#x#2#Z#0_0 == let#0_1#0#0;
        if (_module.Many.Ma0_q(dt_update_tmp#3#Z#0_0))
        {
        }
        else
        {
            if (_module.Many.Ma2_q(dt_update_tmp#3#Z#0_0))
            {
                assert _module.Many.Ma2_q(dt_update_tmp#3#Z#0_0)
                   || _module.Many.Ma5_q(dt_update_tmp#3#Z#0_0);
            }
            else
            {
                if (_module.Many.Ma3_q(dt_update_tmp#3#Z#0_0))
                {
                    assert _module.Many.Ma3_q(dt_update_tmp#3#Z#0_0);
                }
                else
                {
                    if (_module.Many.Ma4_q(dt_update_tmp#3#Z#0_0))
                    {
                        assert _module.Many.Ma1_q(dt_update_tmp#3#Z#0_0)
                           || _module.Many.Ma4_q(dt_update_tmp#3#Z#0_0);
                    }
                    else
                    {
                        assert _module.Many.Ma2_q(dt_update_tmp#3#Z#0_0)
                           || _module.Many.Ma5_q(dt_update_tmp#3#Z#0_0);
                    }
                }
            }
        }

        assume true;
        r#0 := (var dt_update_tmp#3#0_0 := m#0; 
          (var dt_update#x#2#0_0 := LitInt(5); 
            (if _module.Many.Ma0_q(dt_update_tmp#3#0_0)
               then #_module.Many.Ma0(dt_update#x#2#0_0)
               else (if _module.Many.Ma2_q(dt_update_tmp#3#0_0)
                 then #_module.Many.Ma2(dt_update#x#2#0_0, _module.Many.y(dt_update_tmp#3#0_0))
                 else (if _module.Many.Ma3_q(dt_update_tmp#3#0_0)
                   then #_module.Many.Ma3(dt_update#x#2#0_0, _module.Many.z(dt_update_tmp#3#0_0))
                   else (if _module.Many.Ma4_q(dt_update_tmp#3#0_0)
                     then #_module.Many.Ma4(dt_update#x#2#0_0, _module.Many.u(dt_update_tmp#3#0_0))
                     else #_module.Many.Ma5(dt_update#x#2#0_0, _module.Many.y(dt_update_tmp#3#0_0))))))));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(151,19)"} true;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(152,5)
        assume true;
        assert !_module.Many.Ma1_q(r#0);
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SharedDestructors.dfy(153,5)
        if (_module.Many.Ma4_q(m#0))
        {
        }

        assume true;
        assert {:subsumption 0} _module.Many.Ma4_q(m#0) ==> _module.Many.Ma4_q(r#0);
        assume _module.Many.Ma4_q(m#0) ==> _module.Many.Ma4_q(r#0);
    }
    else
    {
        assume true;
        assume true;
        assume true;
        assume true;
        assume !Lit(true)
           && !(_module.Many.Ma2_q(m#0) || _module.Many.Ma5_q(m#0))
           && !_module.Many.Ma4_q(m#0)
           && _module.Many.Ma1_q(m#0);
        assert false;
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

const unique tytagFamily$Dt: TyTagFamily;

const unique tytagFamily$MyClass: TyTagFamily;

const unique tytagFamily$Record: TyTagFamily;

const unique tytagFamily$Shared: TyTagFamily;

const unique tytagFamily$Quirky: TyTagFamily;

const unique tytagFamily$Klef: TyTagFamily;

const unique tytagFamily$Many: TyTagFamily;

const unique tytagFamily$_default: TyTagFamily;
