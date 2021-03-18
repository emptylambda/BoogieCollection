// Dafny 3.0.0.30204
// Command Line Options: -compile:0 -noVerify /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy -print:./BinaryTree.bpl

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

const unique class._module.IntSet?: ClassName;

function Tclass._module.IntSet?() : Ty;

const unique Tagclass._module.IntSet?: TyTag;

// Tclass._module.IntSet? Tag
axiom Tag(Tclass._module.IntSet?()) == Tagclass._module.IntSet?
   && TagFamily(Tclass._module.IntSet?()) == tytagFamily$IntSet;

// Box/unbox axiom for Tclass._module.IntSet?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.IntSet?()) } 
  $IsBox(bx, Tclass._module.IntSet?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.IntSet?()));

// IntSet: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.IntSet?()) } 
  $Is($o, Tclass._module.IntSet?())
     <==> $o == null || dtype($o) == Tclass._module.IntSet?());

// IntSet: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.IntSet?(), $h) } 
  $IsAlloc($o, Tclass._module.IntSet?(), $h)
     <==> $o == null || read($h, $o, alloc));

axiom FDim(_module.IntSet.Contents) == 0
   && FieldOfDecl(class._module.IntSet?, field$Contents) == _module.IntSet.Contents
   && $IsGhostField(_module.IntSet.Contents);

const _module.IntSet.Contents: Field (Set Box);

// IntSet.Contents: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.IntSet.Contents) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.IntSet?()
     ==> $Is(read($h, $o, _module.IntSet.Contents), TSet(TInt)));

// IntSet.Contents: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.IntSet.Contents) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.IntSet?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.IntSet.Contents), TSet(TInt), $h));

axiom FDim(_module.IntSet.Repr) == 0
   && FieldOfDecl(class._module.IntSet?, field$Repr) == _module.IntSet.Repr
   && $IsGhostField(_module.IntSet.Repr);

const _module.IntSet.Repr: Field (Set Box);

// IntSet.Repr: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.IntSet.Repr) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.IntSet?()
     ==> $Is(read($h, $o, _module.IntSet.Repr), TSet(Tclass._System.object())));

// IntSet.Repr: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.IntSet.Repr) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.IntSet?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.IntSet.Repr), TSet(Tclass._System.object()), $h));

axiom FDim(_module.IntSet.root) == 0
   && FieldOfDecl(class._module.IntSet?, field$root) == _module.IntSet.root
   && !$IsGhostField(_module.IntSet.root);

const _module.IntSet.root: Field ref;

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

// IntSet.root: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.IntSet.root) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.IntSet?()
     ==> $Is(read($h, $o, _module.IntSet.root), Tclass._module.Node?()));

// IntSet.root: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.IntSet.root) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.IntSet?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.IntSet.root), Tclass._module.Node?(), $h));

// function declaration for _module.IntSet.Valid
function _module.IntSet.Valid($heap: Heap, this: ref) : bool;

function _module.IntSet.Valid#canCall($heap: Heap, this: ref) : bool;

function Tclass._module.IntSet() : Ty;

const unique Tagclass._module.IntSet: TyTag;

// Tclass._module.IntSet Tag
axiom Tag(Tclass._module.IntSet()) == Tagclass._module.IntSet
   && TagFamily(Tclass._module.IntSet()) == tytagFamily$IntSet;

// Box/unbox axiom for Tclass._module.IntSet
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.IntSet()) } 
  $IsBox(bx, Tclass._module.IntSet())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.IntSet()));

// frame axiom for _module.IntSet.Valid
axiom (forall $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.IntSet.Valid($h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.IntSet())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && ($o == this || read($h0, this, _module.IntSet.Repr)[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.IntSet.Valid($h0, this) == _module.IntSet.Valid($h1, this));

// consequence axiom for _module.IntSet.Valid
axiom 5 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref :: 
    { _module.IntSet.Valid($Heap, this) } 
    _module.IntSet.Valid#canCall($Heap, this)
         || (5 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.IntSet())
           && $IsAlloc(this, Tclass._module.IntSet(), $Heap))
       ==> 
      _module.IntSet.Valid($Heap, this)
       ==> read($Heap, this, _module.IntSet.Repr)[$Box(this)]);

function _module.IntSet.Valid#requires(Heap, ref) : bool;

// #requires axiom for _module.IntSet.Valid
axiom (forall $Heap: Heap, this: ref :: 
  { _module.IntSet.Valid#requires($Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.IntSet())
       && $IsAlloc(this, Tclass._module.IntSet(), $Heap)
     ==> _module.IntSet.Valid#requires($Heap, this) == true);

axiom FDim(_module.Node.Repr) == 0
   && FieldOfDecl(class._module.Node?, field$Repr) == _module.Node.Repr
   && $IsGhostField(_module.Node.Repr);

axiom FDim(_module.Node.Contents) == 0
   && FieldOfDecl(class._module.Node?, field$Contents) == _module.Node.Contents
   && $IsGhostField(_module.Node.Contents);

// definition axiom for _module.IntSet.Valid (revealed)
axiom 5 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref :: 
    { _module.IntSet.Valid($Heap, this), $IsGoodHeap($Heap) } 
    _module.IntSet.Valid#canCall($Heap, this)
         || (5 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.IntSet())
           && $IsAlloc(this, Tclass._module.IntSet(), $Heap))
       ==> (read($Heap, this, _module.IntSet.Repr)[$Box(this)]
           ==> 
          (read($Heap, this, _module.IntSet.root) == null
           ==> Set#Equal(read($Heap, this, _module.IntSet.Contents), Set#Empty(): Set Box))
           ==> 
          read($Heap, this, _module.IntSet.root) != null
           ==> 
          read($Heap, this, _module.IntSet.Repr)[$Box(read($Heap, this, _module.IntSet.root))]
           ==> 
          Set#Subset(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr), 
            read($Heap, this, _module.IntSet.Repr))
           ==> 
          !read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr)[$Box(this)]
           ==> _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root)))
         && _module.IntSet.Valid($Heap, this)
           == (
            read($Heap, this, _module.IntSet.Repr)[$Box(this)]
             && (read($Heap, this, _module.IntSet.root) == null
               ==> Set#Equal(read($Heap, this, _module.IntSet.Contents), Set#Empty(): Set Box))
             && (read($Heap, this, _module.IntSet.root) != null
               ==> read($Heap, this, _module.IntSet.Repr)[$Box(read($Heap, this, _module.IntSet.root))]
                 && Set#Subset(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr), 
                  read($Heap, this, _module.IntSet.Repr))
                 && !read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr)[$Box(this)]
                 && _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
                 && Set#Equal(read($Heap, this, _module.IntSet.Contents), 
                  read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Contents)))));

procedure CheckWellformed$$_module.IntSet.Valid(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.IntSet())
         && $IsAlloc(this, Tclass._module.IntSet(), $Heap));
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures _module.IntSet.Valid($Heap, this)
     ==> read($Heap, this, _module.IntSet.Repr)[$Box(this)];



implementation CheckWellformed$$_module.IntSet.Valid(this: ref)
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

    // AddWellformednessCheck for function Valid
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(10,12): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> $o == this || read($Heap, this, _module.IntSet.Repr)[$Box($o)]);
    b$reqreads#0 := $_Frame[this, _module.IntSet.Repr];
    assert b$reqreads#0;
    if (*)
    {
        if (*)
        {
            assert this == this
               || (Set#Subset(Set#Union(read($Heap, this, _module.IntSet.Repr), 
                    Set#UnionOne(Set#Empty(): Set Box, $Box(this))), 
                  Set#Union(read($Heap, this, _module.IntSet.Repr), 
                    Set#UnionOne(Set#Empty(): Set Box, $Box(this))))
                 && !Set#Subset(Set#Union(read($Heap, this, _module.IntSet.Repr), 
                    Set#UnionOne(Set#Empty(): Set Box, $Box(this))), 
                  Set#Union(read($Heap, this, _module.IntSet.Repr), 
                    Set#UnionOne(Set#Empty(): Set Box, $Box(this)))));
            assume this == this || _module.IntSet.Valid#canCall($Heap, this);
            assume _module.IntSet.Valid($Heap, this);
            assume read($Heap, this, _module.IntSet.Repr)[$Box(this)];
        }
        else
        {
            assume _module.IntSet.Valid($Heap, this)
               ==> read($Heap, this, _module.IntSet.Repr)[$Box(this)];
        }

        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc)
             ==> $o == this || read($Heap, this, _module.IntSet.Repr)[$Box($o)]);
        b$reqreads#1 := $_Frame[this, _module.IntSet.Repr];
        if (read($Heap, this, _module.IntSet.Repr)[$Box(this)])
        {
            b$reqreads#2 := $_Frame[this, _module.IntSet.root];
            if (read($Heap, this, _module.IntSet.root) == null)
            {
                b$reqreads#3 := $_Frame[this, _module.IntSet.Contents];
            }
        }

        if (read($Heap, this, _module.IntSet.Repr)[$Box(this)]
           && (read($Heap, this, _module.IntSet.root) == null
             ==> Set#Equal(read($Heap, this, _module.IntSet.Contents), Set#Empty(): Set Box)))
        {
            b$reqreads#4 := $_Frame[this, _module.IntSet.root];
            if (read($Heap, this, _module.IntSet.root) != null)
            {
                b$reqreads#5 := $_Frame[this, _module.IntSet.root];
                b$reqreads#6 := $_Frame[this, _module.IntSet.Repr];
                if (read($Heap, this, _module.IntSet.Repr)[$Box(read($Heap, this, _module.IntSet.root))])
                {
                    b$reqreads#7 := $_Frame[this, _module.IntSet.root];
                    assert read($Heap, this, _module.IntSet.root) != null;
                    b$reqreads#8 := $_Frame[read($Heap, this, _module.IntSet.root), _module.Node.Repr];
                    b$reqreads#9 := $_Frame[this, _module.IntSet.Repr];
                }

                if (read($Heap, this, _module.IntSet.Repr)[$Box(read($Heap, this, _module.IntSet.root))]
                   && Set#Subset(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr), 
                    read($Heap, this, _module.IntSet.Repr)))
                {
                    b$reqreads#10 := $_Frame[this, _module.IntSet.root];
                    assert read($Heap, this, _module.IntSet.root) != null;
                    b$reqreads#11 := $_Frame[read($Heap, this, _module.IntSet.root), _module.Node.Repr];
                }

                if (read($Heap, this, _module.IntSet.Repr)[$Box(read($Heap, this, _module.IntSet.root))]
                   && Set#Subset(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr), 
                    read($Heap, this, _module.IntSet.Repr))
                   && !read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr)[$Box(this)])
                {
                    b$reqreads#12 := $_Frame[this, _module.IntSet.root];
                    assert read($Heap, this, _module.IntSet.root) != null;
                    b$reqreads#13 := (forall<alpha> $o: ref, $f: Field alpha :: 
                      $o != null
                           && read($Heap, $o, alloc)
                           && ($o == read($Heap, this, _module.IntSet.root)
                             || read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr)[$Box($o)])
                         ==> $_Frame[$o, $f]);
                    assume _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root));
                }

                if (read($Heap, this, _module.IntSet.Repr)[$Box(read($Heap, this, _module.IntSet.root))]
                   && Set#Subset(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr), 
                    read($Heap, this, _module.IntSet.Repr))
                   && !read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr)[$Box(this)]
                   && _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root)))
                {
                    b$reqreads#14 := $_Frame[this, _module.IntSet.Contents];
                    b$reqreads#15 := $_Frame[this, _module.IntSet.root];
                    assert read($Heap, this, _module.IntSet.root) != null;
                    b$reqreads#16 := $_Frame[read($Heap, this, _module.IntSet.root), _module.Node.Contents];
                }
            }
        }

        assume _module.IntSet.Valid($Heap, this)
           == (
            read($Heap, this, _module.IntSet.Repr)[$Box(this)]
             && (read($Heap, this, _module.IntSet.root) == null
               ==> Set#Equal(read($Heap, this, _module.IntSet.Contents), Set#Empty(): Set Box))
             && (read($Heap, this, _module.IntSet.root) != null
               ==> read($Heap, this, _module.IntSet.Repr)[$Box(read($Heap, this, _module.IntSet.root))]
                 && Set#Subset(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr), 
                  read($Heap, this, _module.IntSet.Repr))
                 && !read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr)[$Box(this)]
                 && _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
                 && Set#Equal(read($Heap, this, _module.IntSet.Contents), 
                  read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Contents))));
        assume read($Heap, this, _module.IntSet.Repr)[$Box(this)]
           ==> 
          (read($Heap, this, _module.IntSet.root) == null
           ==> Set#Equal(read($Heap, this, _module.IntSet.Contents), Set#Empty(): Set Box))
           ==> 
          read($Heap, this, _module.IntSet.root) != null
           ==> 
          read($Heap, this, _module.IntSet.Repr)[$Box(read($Heap, this, _module.IntSet.root))]
           ==> 
          Set#Subset(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr), 
            read($Heap, this, _module.IntSet.Repr))
           ==> 
          !read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr)[$Box(this)]
           ==> _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.IntSet.Valid($Heap, this), TBool);
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
    }
}



procedure CheckWellformed$$_module.IntSet.Init(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.IntSet())
         && $IsAlloc(this, Tclass._module.IntSet(), $Heap));
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;



axiom FDim(_module.Node.left) == 0
   && FieldOfDecl(class._module.Node?, field$left) == _module.Node.left
   && !$IsGhostField(_module.Node.left);

axiom FDim(_module.Node.data) == 0
   && FieldOfDecl(class._module.Node?, field$data) == _module.Node.data
   && !$IsGhostField(_module.Node.data);

axiom FDim(_module.Node.right) == 0
   && FieldOfDecl(class._module.Node?, field$right) == _module.Node.right
   && !$IsGhostField(_module.Node.right);

procedure Call$$_module.IntSet.Init()
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass._module.IntSet())
         && $IsAlloc(this, Tclass._module.IntSet(), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.IntSet.Valid#canCall($Heap, this);
  free ensures _module.IntSet.Valid#canCall($Heap, this)
     && 
    _module.IntSet.Valid($Heap, this)
     && 
    read($Heap, this, _module.IntSet.Repr)[$Box(this)]
     && (read($Heap, this, _module.IntSet.root) == null
       ==> Set#Equal(read($Heap, this, _module.IntSet.Contents), Set#Empty(): Set Box))
     && (read($Heap, this, _module.IntSet.root) != null
       ==> read($Heap, this, _module.IntSet.Repr)[$Box(read($Heap, this, _module.IntSet.root))]
         && Set#Subset(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr), 
          read($Heap, this, _module.IntSet.Repr))
         && !read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr)[$Box(this)]
         && _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
         && Set#Equal(read($Heap, this, _module.IntSet.Contents), 
          read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Contents)));
  ensures (forall $o: ref :: 
    { read($Heap, this, _module.IntSet.Repr)[$Box($o)] } 
    read($Heap, this, _module.IntSet.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures Set#Equal(read($Heap, this, _module.IntSet.Contents), Set#Empty(): Set Box);
  // constructor allocates the object
  ensures !read(old($Heap), this, alloc);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.IntSet.Init()
   returns (this: ref where this != null && $Is(this, Tclass._module.IntSet()), 
    $_reverifyPost: bool);
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.IntSet.Valid#canCall($Heap, this);
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || read($Heap, this, _module.IntSet.Repr)[$Box(this)];
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) == null
         ==> Set#Equal(read($Heap, this, _module.IntSet.Contents), Set#Empty(): Set Box));
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> read($Heap, this, _module.IntSet.Repr)[$Box(read($Heap, this, _module.IntSet.root))]);
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> Set#Subset(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr), 
          read($Heap, this, _module.IntSet.Repr)));
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> !read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr)[$Box(this)]);
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr)[$Box(read($Heap, this, _module.IntSet.root))]);
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
             ==> read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr)[$Box(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left))]));
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
             ==> Set#Subset(read($Heap, 
                read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left), 
                _module.Node.Repr), 
              read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr))));
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
             ==> !read($Heap, 
              read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left), 
              _module.Node.Repr)[$Box(read($Heap, this, _module.IntSet.root))]));
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
             ==> _module.Node.Valid($LS($LS($LZ)), 
              $Heap, 
              read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left))));
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
             ==> (forall y#2: int :: 
              { read($Heap, 
                  read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left), 
                  _module.Node.Contents)[$Box(y#2)] } 
              true
                 ==> 
                read($Heap, 
                  read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left), 
                  _module.Node.Contents)[$Box(y#2)]
                 ==> y#2 < read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.data))));
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
             ==> read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr)[$Box(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right))]));
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
             ==> Set#Subset(read($Heap, 
                read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right), 
                _module.Node.Repr), 
              read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr))));
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
             ==> !read($Heap, 
              read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right), 
              _module.Node.Repr)[$Box(read($Heap, this, _module.IntSet.root))]));
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
             ==> _module.Node.Valid($LS($LS($LZ)), 
              $Heap, 
              read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right))));
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
             ==> (forall y#3: int :: 
              { read($Heap, 
                  read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right), 
                  _module.Node.Contents)[$Box(y#3)] } 
              true
                 ==> 
                read($Heap, 
                  read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right), 
                  _module.Node.Contents)[$Box(y#3)]
                 ==> read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.data) < y#3)));
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) == null
               && read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) == null
             ==> Set#Equal(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Contents), 
              Set#UnionOne(Set#Empty(): Set Box, 
                $Box(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.data))))));
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
               && read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) == null
             ==> Set#Equal(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Contents), 
              Set#Union(read($Heap, 
                  read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left), 
                  _module.Node.Contents), 
                Set#UnionOne(Set#Empty(): Set Box, 
                  $Box(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.data)))))));
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) == null
               && read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
             ==> Set#Equal(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Contents), 
              Set#Union(Set#UnionOne(Set#Empty(): Set Box, 
                  $Box(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.data))), 
                read($Heap, 
                  read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right), 
                  _module.Node.Contents)))));
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
               && read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
             ==> Set#Disjoint(read($Heap, 
                read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left), 
                _module.Node.Repr), 
              read($Heap, 
                read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right), 
                _module.Node.Repr))));
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
               && read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
             ==> Set#Equal(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Contents), 
              Set#Union(Set#Union(read($Heap, 
                    read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left), 
                    _module.Node.Contents), 
                  Set#UnionOne(Set#Empty(): Set Box, 
                    $Box(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.data)))), 
                read($Heap, 
                  read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right), 
                  _module.Node.Contents)))));
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> Set#Equal(read($Heap, this, _module.IntSet.Contents), 
          read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Contents)));
  ensures (forall $o: ref :: 
    { read($Heap, this, _module.IntSet.Repr)[$Box($o)] } 
    read($Heap, this, _module.IntSet.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures Set#Equal(read($Heap, this, _module.IntSet.Contents), Set#Empty(): Set Box);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.IntSet.Init() returns (this: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var this.Contents: Set Box;
  var this.Repr: Set Box;
  var this.root: ref;

    // AddMethodImpl: Init, Impl$$_module.IntSet.Init
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(25,2): initial state"} true;
    $_reverifyPost := false;
    // ----- divided block before new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(25,3)
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(26,10)
    assume true;
    assume true;
    this.root := null;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(26,16)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(27,10)
    assume true;
    assume true;
    assert $Is(Set#UnionOne(Set#Empty(): Set Box, $Box(this)), TSet(Tclass._System.object()));
    this.Repr := Set#UnionOne(Set#Empty(): Set Box, $Box(this));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(27,18)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(28,14)
    assume true;
    assume true;
    this.Contents := Lit(Set#Empty(): Set Box);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(28,18)"} true;
    // ----- new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(25,3)
    assume !read($Heap, this, alloc);
    assume read($Heap, this, _module.IntSet.Contents) == this.Contents;
    assume read($Heap, this, _module.IntSet.Repr) == this.Repr;
    assume read($Heap, this, _module.IntSet.root) == this.root;
    $Heap := update($Heap, this, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    // ----- divided block after new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(25,3)
}



// function declaration for _module.IntSet.Find
function _module.IntSet.Find($heap: Heap, this: ref, x#0: int) : bool;

function _module.IntSet.Find#canCall($heap: Heap, this: ref, x#0: int) : bool;

// frame axiom for _module.IntSet.Find
axiom (forall $h0: Heap, $h1: Heap, this: ref, x#0: int :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.IntSet.Find($h1, this, x#0) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.IntSet())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($h0, this, _module.IntSet.Repr)[$Box($o)]
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.IntSet.Find($h0, this, x#0) == _module.IntSet.Find($h1, this, x#0));

// consequence axiom for _module.IntSet.Find
axiom 10 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref, x#0: int :: 
    { _module.IntSet.Find($Heap, this, x#0) } 
    _module.IntSet.Find#canCall($Heap, this, x#0)
         || (10 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.IntSet())
           && $IsAlloc(this, Tclass._module.IntSet(), $Heap)
           && _module.IntSet.Valid($Heap, this))
       ==> (_module.IntSet.Find($Heap, this, x#0)
         <==> read($Heap, this, _module.IntSet.Contents)[$Box(x#0)]));

function _module.IntSet.Find#requires(Heap, ref, int) : bool;

// #requires axiom for _module.IntSet.Find
axiom (forall $Heap: Heap, this: ref, x#0: int :: 
  { _module.IntSet.Find#requires($Heap, this, x#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.IntSet())
       && $IsAlloc(this, Tclass._module.IntSet(), $Heap)
     ==> _module.IntSet.Find#requires($Heap, this, x#0)
       == _module.IntSet.Valid($Heap, this));

// definition axiom for _module.IntSet.Find (revealed)
axiom 10 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref, x#0: int :: 
    { _module.IntSet.Find($Heap, this, x#0), $IsGoodHeap($Heap) } 
    _module.IntSet.Find#canCall($Heap, this, x#0)
         || (10 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.IntSet())
           && $IsAlloc(this, Tclass._module.IntSet(), $Heap)
           && _module.IntSet.Valid($Heap, this))
       ==> (read($Heap, this, _module.IntSet.root) != null
           ==> _module.Node.Find#canCall($Heap, read($Heap, this, _module.IntSet.root), x#0))
         && _module.IntSet.Find($Heap, this, x#0)
           == (read($Heap, this, _module.IntSet.root) != null
             && _module.Node.Find($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root), x#0)));

procedure CheckWellformed$$_module.IntSet.Find(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.IntSet())
         && $IsAlloc(this, Tclass._module.IntSet(), $Heap), 
    x#0: int);
  free requires 10 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures _module.IntSet.Find($Heap, this, x#0)
     <==> read($Heap, this, _module.IntSet.Contents)[$Box(x#0)];



implementation CheckWellformed$$_module.IntSet.Find(this: ref, x#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;
  var ##x#0: int;
  var ##x#1: int;
  var b$reqreads#2: bool;
  var b$reqreads#3: bool;
  var b$reqreads#4: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;
    b$reqreads#3 := true;
    b$reqreads#4 := true;

    // AddWellformednessCheck for function Find
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(31,18): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.IntSet.Repr)[$Box($o)]);
    b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && read($Heap, $o, alloc)
           && ($o == this || read($Heap, this, _module.IntSet.Repr)[$Box($o)])
         ==> $_Frame[$o, $f]);
    assume _module.IntSet.Valid#canCall($Heap, this);
    assume _module.IntSet.Valid($Heap, this);
    assert b$reqreads#0;
    b$reqreads#1 := $_Frame[this, _module.IntSet.Repr];
    assert b$reqreads#1;
    if (*)
    {
        ##x#0 := x#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##x#0, TInt, $Heap);
        assert {:subsumption 0} _module.IntSet.Valid#canCall($Heap, this)
           ==> _module.IntSet.Valid($Heap, this)
             || read($Heap, this, _module.IntSet.Repr)[$Box(this)];
        assert {:subsumption 0} _module.IntSet.Valid#canCall($Heap, this)
           ==> _module.IntSet.Valid($Heap, this)
             || (read($Heap, this, _module.IntSet.root) == null
               ==> Set#Equal(read($Heap, this, _module.IntSet.Contents), Set#Empty(): Set Box));
        assert {:subsumption 0} _module.IntSet.Valid#canCall($Heap, this)
           ==> _module.IntSet.Valid($Heap, this)
             || (read($Heap, this, _module.IntSet.root) != null
               ==> read($Heap, this, _module.IntSet.Repr)[$Box(read($Heap, this, _module.IntSet.root))]);
        assert {:subsumption 0} _module.IntSet.Valid#canCall($Heap, this)
           ==> _module.IntSet.Valid($Heap, this)
             || (read($Heap, this, _module.IntSet.root) != null
               ==> Set#Subset(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr), 
                read($Heap, this, _module.IntSet.Repr)));
        assert {:subsumption 0} _module.IntSet.Valid#canCall($Heap, this)
           ==> _module.IntSet.Valid($Heap, this)
             || (read($Heap, this, _module.IntSet.root) != null
               ==> !read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr)[$Box(this)]);
        assert {:subsumption 0} _module.IntSet.Valid#canCall($Heap, this)
           ==> _module.IntSet.Valid($Heap, this)
             || (read($Heap, this, _module.IntSet.root) != null
               ==> 
              _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
               ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
                 || read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr)[$Box(read($Heap, this, _module.IntSet.root))]);
        assert {:subsumption 0} _module.IntSet.Valid#canCall($Heap, this)
           ==> _module.IntSet.Valid($Heap, this)
             || (read($Heap, this, _module.IntSet.root) != null
               ==> 
              _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
               ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
                 || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
                   ==> read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr)[$Box(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left))]));
        assert {:subsumption 0} _module.IntSet.Valid#canCall($Heap, this)
           ==> _module.IntSet.Valid($Heap, this)
             || (read($Heap, this, _module.IntSet.root) != null
               ==> 
              _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
               ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
                 || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
                   ==> Set#Subset(read($Heap, 
                      read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left), 
                      _module.Node.Repr), 
                    read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr))));
        assert {:subsumption 0} _module.IntSet.Valid#canCall($Heap, this)
           ==> _module.IntSet.Valid($Heap, this)
             || (read($Heap, this, _module.IntSet.root) != null
               ==> 
              _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
               ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
                 || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
                   ==> !read($Heap, 
                    read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left), 
                    _module.Node.Repr)[$Box(read($Heap, this, _module.IntSet.root))]));
        assert {:subsumption 0} _module.IntSet.Valid#canCall($Heap, this)
           ==> _module.IntSet.Valid($Heap, this)
             || (read($Heap, this, _module.IntSet.root) != null
               ==> 
              _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
               ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
                 || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
                   ==> _module.Node.Valid($LS($LS($LZ)), 
                    $Heap, 
                    read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left))));
        assert {:subsumption 0} _module.IntSet.Valid#canCall($Heap, this)
           ==> _module.IntSet.Valid($Heap, this)
             || (read($Heap, this, _module.IntSet.root) != null
               ==> 
              _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
               ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
                 || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
                   ==> (forall y#0: int :: 
                    { read($Heap, 
                        read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left), 
                        _module.Node.Contents)[$Box(y#0)] } 
                    true
                       ==> 
                      read($Heap, 
                        read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left), 
                        _module.Node.Contents)[$Box(y#0)]
                       ==> y#0 < read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.data))));
        assert {:subsumption 0} _module.IntSet.Valid#canCall($Heap, this)
           ==> _module.IntSet.Valid($Heap, this)
             || (read($Heap, this, _module.IntSet.root) != null
               ==> 
              _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
               ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
                 || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
                   ==> read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr)[$Box(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right))]));
        assert {:subsumption 0} _module.IntSet.Valid#canCall($Heap, this)
           ==> _module.IntSet.Valid($Heap, this)
             || (read($Heap, this, _module.IntSet.root) != null
               ==> 
              _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
               ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
                 || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
                   ==> Set#Subset(read($Heap, 
                      read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right), 
                      _module.Node.Repr), 
                    read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr))));
        assert {:subsumption 0} _module.IntSet.Valid#canCall($Heap, this)
           ==> _module.IntSet.Valid($Heap, this)
             || (read($Heap, this, _module.IntSet.root) != null
               ==> 
              _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
               ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
                 || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
                   ==> !read($Heap, 
                    read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right), 
                    _module.Node.Repr)[$Box(read($Heap, this, _module.IntSet.root))]));
        assert {:subsumption 0} _module.IntSet.Valid#canCall($Heap, this)
           ==> _module.IntSet.Valid($Heap, this)
             || (read($Heap, this, _module.IntSet.root) != null
               ==> 
              _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
               ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
                 || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
                   ==> _module.Node.Valid($LS($LS($LZ)), 
                    $Heap, 
                    read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right))));
        assert {:subsumption 0} _module.IntSet.Valid#canCall($Heap, this)
           ==> _module.IntSet.Valid($Heap, this)
             || (read($Heap, this, _module.IntSet.root) != null
               ==> 
              _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
               ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
                 || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
                   ==> (forall y#1: int :: 
                    { read($Heap, 
                        read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right), 
                        _module.Node.Contents)[$Box(y#1)] } 
                    true
                       ==> 
                      read($Heap, 
                        read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right), 
                        _module.Node.Contents)[$Box(y#1)]
                       ==> read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.data) < y#1)));
        assert {:subsumption 0} _module.IntSet.Valid#canCall($Heap, this)
           ==> _module.IntSet.Valid($Heap, this)
             || (read($Heap, this, _module.IntSet.root) != null
               ==> 
              _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
               ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
                 || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) == null
                     && read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) == null
                   ==> Set#Equal(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Contents), 
                    Set#UnionOne(Set#Empty(): Set Box, 
                      $Box(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.data))))));
        assert {:subsumption 0} _module.IntSet.Valid#canCall($Heap, this)
           ==> _module.IntSet.Valid($Heap, this)
             || (read($Heap, this, _module.IntSet.root) != null
               ==> 
              _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
               ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
                 || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
                     && read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) == null
                   ==> Set#Equal(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Contents), 
                    Set#Union(read($Heap, 
                        read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left), 
                        _module.Node.Contents), 
                      Set#UnionOne(Set#Empty(): Set Box, 
                        $Box(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.data)))))));
        assert {:subsumption 0} _module.IntSet.Valid#canCall($Heap, this)
           ==> _module.IntSet.Valid($Heap, this)
             || (read($Heap, this, _module.IntSet.root) != null
               ==> 
              _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
               ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
                 || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) == null
                     && read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
                   ==> Set#Equal(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Contents), 
                    Set#Union(Set#UnionOne(Set#Empty(): Set Box, 
                        $Box(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.data))), 
                      read($Heap, 
                        read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right), 
                        _module.Node.Contents)))));
        assert {:subsumption 0} _module.IntSet.Valid#canCall($Heap, this)
           ==> _module.IntSet.Valid($Heap, this)
             || (read($Heap, this, _module.IntSet.root) != null
               ==> 
              _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
               ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
                 || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
                     && read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
                   ==> Set#Disjoint(read($Heap, 
                      read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left), 
                      _module.Node.Repr), 
                    read($Heap, 
                      read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right), 
                      _module.Node.Repr))));
        assert {:subsumption 0} _module.IntSet.Valid#canCall($Heap, this)
           ==> _module.IntSet.Valid($Heap, this)
             || (read($Heap, this, _module.IntSet.root) != null
               ==> 
              _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
               ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
                 || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
                     && read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
                   ==> Set#Equal(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Contents), 
                    Set#Union(Set#Union(read($Heap, 
                          read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left), 
                          _module.Node.Contents), 
                        Set#UnionOne(Set#Empty(): Set Box, 
                          $Box(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.data)))), 
                      read($Heap, 
                        read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right), 
                        _module.Node.Contents)))));
        assert {:subsumption 0} _module.IntSet.Valid#canCall($Heap, this)
           ==> _module.IntSet.Valid($Heap, this)
             || (read($Heap, this, _module.IntSet.root) != null
               ==> Set#Equal(read($Heap, this, _module.IntSet.Contents), 
                read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Contents)));
        assume _module.IntSet.Valid($Heap, this);
        assert 0 <= x#0
           || (Set#Subset(read($Heap, this, _module.IntSet.Repr), read($Heap, this, _module.IntSet.Repr))
             && !Set#Subset(read($Heap, this, _module.IntSet.Repr), read($Heap, this, _module.IntSet.Repr)))
           || ##x#0 == x#0;
        assert (this == this && x#0 == x#0)
           || 
          (Set#Subset(read($Heap, this, _module.IntSet.Repr), read($Heap, this, _module.IntSet.Repr))
             && !Set#Subset(read($Heap, this, _module.IntSet.Repr), read($Heap, this, _module.IntSet.Repr)))
           || (Set#Equal(read($Heap, this, _module.IntSet.Repr), read($Heap, this, _module.IntSet.Repr))
             && ##x#0 < x#0);
        assume (this == this && x#0 == x#0) || _module.IntSet.Find#canCall($Heap, this, x#0);
        assume _module.IntSet.Find($Heap, this, x#0)
           <==> read($Heap, this, _module.IntSet.Contents)[$Box(x#0)];
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc)
             ==> read($Heap, this, _module.IntSet.Repr)[$Box($o)]);
        b$reqreads#2 := $_Frame[this, _module.IntSet.root];
        if (read($Heap, this, _module.IntSet.root) != null)
        {
            b$reqreads#3 := $_Frame[this, _module.IntSet.root];
            assert read($Heap, this, _module.IntSet.root) != null;
            ##x#1 := x#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##x#1, TInt, $Heap);
            assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
               ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
                 || read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr)[$Box(read($Heap, this, _module.IntSet.root))];
            assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
               ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
                 || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
                   ==> read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr)[$Box(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left))]);
            assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
               ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
                 || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
                   ==> Set#Subset(read($Heap, 
                      read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left), 
                      _module.Node.Repr), 
                    read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr)));
            assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
               ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
                 || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
                   ==> !read($Heap, 
                    read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left), 
                    _module.Node.Repr)[$Box(read($Heap, this, _module.IntSet.root))]);
            assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
               ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
                 || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
                   ==> _module.Node.Valid($LS($LS($LZ)), 
                    $Heap, 
                    read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left)));
            assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
               ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
                 || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
                   ==> (forall y#2: int :: 
                    { read($Heap, 
                        read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left), 
                        _module.Node.Contents)[$Box(y#2)] } 
                    true
                       ==> 
                      read($Heap, 
                        read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left), 
                        _module.Node.Contents)[$Box(y#2)]
                       ==> y#2 < read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.data)));
            assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
               ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
                 || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
                   ==> read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr)[$Box(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right))]);
            assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
               ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
                 || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
                   ==> Set#Subset(read($Heap, 
                      read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right), 
                      _module.Node.Repr), 
                    read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr)));
            assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
               ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
                 || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
                   ==> !read($Heap, 
                    read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right), 
                    _module.Node.Repr)[$Box(read($Heap, this, _module.IntSet.root))]);
            assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
               ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
                 || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
                   ==> _module.Node.Valid($LS($LS($LZ)), 
                    $Heap, 
                    read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right)));
            assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
               ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
                 || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
                   ==> (forall y#3: int :: 
                    { read($Heap, 
                        read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right), 
                        _module.Node.Contents)[$Box(y#3)] } 
                    true
                       ==> 
                      read($Heap, 
                        read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right), 
                        _module.Node.Contents)[$Box(y#3)]
                       ==> read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.data) < y#3));
            assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
               ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
                 || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) == null
                     && read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) == null
                   ==> Set#Equal(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Contents), 
                    Set#UnionOne(Set#Empty(): Set Box, 
                      $Box(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.data)))));
            assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
               ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
                 || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
                     && read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) == null
                   ==> Set#Equal(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Contents), 
                    Set#Union(read($Heap, 
                        read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left), 
                        _module.Node.Contents), 
                      Set#UnionOne(Set#Empty(): Set Box, 
                        $Box(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.data))))));
            assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
               ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
                 || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) == null
                     && read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
                   ==> Set#Equal(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Contents), 
                    Set#Union(Set#UnionOne(Set#Empty(): Set Box, 
                        $Box(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.data))), 
                      read($Heap, 
                        read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right), 
                        _module.Node.Contents))));
            assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
               ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
                 || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
                     && read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
                   ==> Set#Disjoint(read($Heap, 
                      read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left), 
                      _module.Node.Repr), 
                    read($Heap, 
                      read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right), 
                      _module.Node.Repr)));
            assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
               ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
                 || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
                     && read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
                   ==> Set#Equal(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Contents), 
                    Set#Union(Set#Union(read($Heap, 
                          read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left), 
                          _module.Node.Contents), 
                        Set#UnionOne(Set#Empty(): Set Box, 
                          $Box(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.data)))), 
                      read($Heap, 
                        read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right), 
                        _module.Node.Contents))));
            assume _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root));
            b$reqreads#4 := (forall<alpha> $o: ref, $f: Field alpha :: 
              $o != null
                   && read($Heap, $o, alloc)
                   && read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr)[$Box($o)]
                 ==> $_Frame[$o, $f]);
            assume _module.Node.Find#canCall($Heap, read($Heap, this, _module.IntSet.root), x#0);
        }

        assume _module.IntSet.Find($Heap, this, x#0)
           == (read($Heap, this, _module.IntSet.root) != null
             && _module.Node.Find($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root), x#0));
        assume read($Heap, this, _module.IntSet.root) != null
           ==> _module.Node.Find#canCall($Heap, read($Heap, this, _module.IntSet.root), x#0);
        // CheckWellformedWithResult: any expression
        assume $Is(_module.IntSet.Find($Heap, this, x#0), TBool);
        assert b$reqreads#2;
        assert b$reqreads#3;
        assert b$reqreads#4;
    }
}



procedure CheckWellformed$$_module.IntSet.Insert(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.IntSet())
         && $IsAlloc(this, Tclass._module.IntSet(), $Heap), 
    x#0: int);
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.IntSet.Insert(this: ref, x#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Insert, CheckWellformed$$_module.IntSet.Insert
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.IntSet.Repr)[$Box($o)]);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(39,9): initial state"} true;
    assume _module.IntSet.Valid#canCall($Heap, this);
    assume _module.IntSet.Valid($Heap, this);
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc)
         ==> $Heap[$o] == old($Heap)[$o]
           || read(old($Heap), this, _module.IntSet.Repr)[$Box($o)]);
    assume $HeapSucc(old($Heap), $Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(42,20): post-state"} true;
    assume _module.IntSet.Valid#canCall($Heap, this);
    assume _module.IntSet.Valid($Heap, this);
    assert $IsAlloc(this, Tclass._module.IntSet(), old($Heap));
    assume (forall $o: ref :: 
      { read(old($Heap), $o, alloc) } 
      read($Heap, this, _module.IntSet.Repr)[$Box($o)]
           && !read(old($Heap), this, _module.IntSet.Repr)[$Box($o)]
         ==> $o != null && !read(old($Heap), $o, alloc));
    assert $IsAlloc(this, Tclass._module.IntSet(), old($Heap));
    assume Set#Equal(read($Heap, this, _module.IntSet.Contents), 
      Set#Union(read(old($Heap), this, _module.IntSet.Contents), 
        Set#UnionOne(Set#Empty(): Set Box, $Box(x#0))));
}



procedure Call$$_module.IntSet.Insert(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.IntSet())
         && $IsAlloc(this, Tclass._module.IntSet(), $Heap), 
    x#0: int);
  // user-defined preconditions
  requires _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || read($Heap, this, _module.IntSet.Repr)[$Box(this)];
  requires _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) == null
         ==> Set#Equal(read($Heap, this, _module.IntSet.Contents), Set#Empty(): Set Box));
  requires _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> read($Heap, this, _module.IntSet.Repr)[$Box(read($Heap, this, _module.IntSet.root))]);
  requires _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> Set#Subset(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr), 
          read($Heap, this, _module.IntSet.Repr)));
  requires _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> !read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr)[$Box(this)]);
  requires _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr)[$Box(read($Heap, this, _module.IntSet.root))]);
  requires _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
             ==> read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr)[$Box(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left))]));
  requires _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
             ==> Set#Subset(read($Heap, 
                read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left), 
                _module.Node.Repr), 
              read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr))));
  requires _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
             ==> !read($Heap, 
              read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left), 
              _module.Node.Repr)[$Box(read($Heap, this, _module.IntSet.root))]));
  requires _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
             ==> _module.Node.Valid($LS($LS($LZ)), 
              $Heap, 
              read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left))));
  requires _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
             ==> (forall y#0: int :: 
              { read($Heap, 
                  read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left), 
                  _module.Node.Contents)[$Box(y#0)] } 
              true
                 ==> 
                read($Heap, 
                  read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left), 
                  _module.Node.Contents)[$Box(y#0)]
                 ==> y#0 < read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.data))));
  requires _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
             ==> read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr)[$Box(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right))]));
  requires _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
             ==> Set#Subset(read($Heap, 
                read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right), 
                _module.Node.Repr), 
              read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr))));
  requires _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
             ==> !read($Heap, 
              read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right), 
              _module.Node.Repr)[$Box(read($Heap, this, _module.IntSet.root))]));
  requires _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
             ==> _module.Node.Valid($LS($LS($LZ)), 
              $Heap, 
              read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right))));
  requires _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
             ==> (forall y#1: int :: 
              { read($Heap, 
                  read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right), 
                  _module.Node.Contents)[$Box(y#1)] } 
              true
                 ==> 
                read($Heap, 
                  read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right), 
                  _module.Node.Contents)[$Box(y#1)]
                 ==> read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.data) < y#1)));
  requires _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) == null
               && read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) == null
             ==> Set#Equal(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Contents), 
              Set#UnionOne(Set#Empty(): Set Box, 
                $Box(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.data))))));
  requires _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
               && read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) == null
             ==> Set#Equal(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Contents), 
              Set#Union(read($Heap, 
                  read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left), 
                  _module.Node.Contents), 
                Set#UnionOne(Set#Empty(): Set Box, 
                  $Box(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.data)))))));
  requires _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) == null
               && read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
             ==> Set#Equal(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Contents), 
              Set#Union(Set#UnionOne(Set#Empty(): Set Box, 
                  $Box(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.data))), 
                read($Heap, 
                  read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right), 
                  _module.Node.Contents)))));
  requires _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
               && read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
             ==> Set#Disjoint(read($Heap, 
                read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left), 
                _module.Node.Repr), 
              read($Heap, 
                read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right), 
                _module.Node.Repr))));
  requires _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
               && read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
             ==> Set#Equal(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Contents), 
              Set#Union(Set#Union(read($Heap, 
                    read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left), 
                    _module.Node.Contents), 
                  Set#UnionOne(Set#Empty(): Set Box, 
                    $Box(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.data)))), 
                read($Heap, 
                  read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right), 
                  _module.Node.Contents)))));
  requires _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> Set#Equal(read($Heap, this, _module.IntSet.Contents), 
          read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Contents)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.IntSet.Valid#canCall($Heap, this);
  free ensures _module.IntSet.Valid#canCall($Heap, this)
     && 
    _module.IntSet.Valid($Heap, this)
     && 
    read($Heap, this, _module.IntSet.Repr)[$Box(this)]
     && (read($Heap, this, _module.IntSet.root) == null
       ==> Set#Equal(read($Heap, this, _module.IntSet.Contents), Set#Empty(): Set Box))
     && (read($Heap, this, _module.IntSet.root) != null
       ==> read($Heap, this, _module.IntSet.Repr)[$Box(read($Heap, this, _module.IntSet.root))]
         && Set#Subset(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr), 
          read($Heap, this, _module.IntSet.Repr))
         && !read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr)[$Box(this)]
         && _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
         && Set#Equal(read($Heap, this, _module.IntSet.Contents), 
          read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Contents)));
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    read($Heap, this, _module.IntSet.Repr)[$Box($o)]
         && !read(old($Heap), this, _module.IntSet.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures Set#Equal(read($Heap, this, _module.IntSet.Contents), 
    Set#Union(read(old($Heap), this, _module.IntSet.Contents), 
      Set#UnionOne(Set#Empty(): Set Box, $Box(x#0))));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || read(old($Heap), this, _module.IntSet.Repr)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.IntSet.Insert(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.IntSet())
         && $IsAlloc(this, Tclass._module.IntSet(), $Heap), 
    x#0: int)
   returns ($_reverifyPost: bool);
  free requires 6 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.IntSet.Valid#canCall($Heap, this)
     && 
    _module.IntSet.Valid($Heap, this)
     && 
    read($Heap, this, _module.IntSet.Repr)[$Box(this)]
     && (read($Heap, this, _module.IntSet.root) == null
       ==> Set#Equal(read($Heap, this, _module.IntSet.Contents), Set#Empty(): Set Box))
     && (read($Heap, this, _module.IntSet.root) != null
       ==> read($Heap, this, _module.IntSet.Repr)[$Box(read($Heap, this, _module.IntSet.root))]
         && Set#Subset(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr), 
          read($Heap, this, _module.IntSet.Repr))
         && !read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr)[$Box(this)]
         && _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
         && Set#Equal(read($Heap, this, _module.IntSet.Contents), 
          read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Contents)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.IntSet.Valid#canCall($Heap, this);
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || read($Heap, this, _module.IntSet.Repr)[$Box(this)];
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) == null
         ==> Set#Equal(read($Heap, this, _module.IntSet.Contents), Set#Empty(): Set Box));
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> read($Heap, this, _module.IntSet.Repr)[$Box(read($Heap, this, _module.IntSet.root))]);
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> Set#Subset(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr), 
          read($Heap, this, _module.IntSet.Repr)));
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> !read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr)[$Box(this)]);
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr)[$Box(read($Heap, this, _module.IntSet.root))]);
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
             ==> read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr)[$Box(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left))]));
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
             ==> Set#Subset(read($Heap, 
                read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left), 
                _module.Node.Repr), 
              read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr))));
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
             ==> !read($Heap, 
              read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left), 
              _module.Node.Repr)[$Box(read($Heap, this, _module.IntSet.root))]));
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
             ==> _module.Node.Valid($LS($LS($LZ)), 
              $Heap, 
              read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left))));
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
             ==> (forall y#6: int :: 
              { read($Heap, 
                  read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left), 
                  _module.Node.Contents)[$Box(y#6)] } 
              true
                 ==> 
                read($Heap, 
                  read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left), 
                  _module.Node.Contents)[$Box(y#6)]
                 ==> y#6 < read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.data))));
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
             ==> read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr)[$Box(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right))]));
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
             ==> Set#Subset(read($Heap, 
                read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right), 
                _module.Node.Repr), 
              read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr))));
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
             ==> !read($Heap, 
              read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right), 
              _module.Node.Repr)[$Box(read($Heap, this, _module.IntSet.root))]));
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
             ==> _module.Node.Valid($LS($LS($LZ)), 
              $Heap, 
              read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right))));
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
             ==> (forall y#7: int :: 
              { read($Heap, 
                  read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right), 
                  _module.Node.Contents)[$Box(y#7)] } 
              true
                 ==> 
                read($Heap, 
                  read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right), 
                  _module.Node.Contents)[$Box(y#7)]
                 ==> read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.data) < y#7)));
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) == null
               && read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) == null
             ==> Set#Equal(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Contents), 
              Set#UnionOne(Set#Empty(): Set Box, 
                $Box(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.data))))));
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
               && read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) == null
             ==> Set#Equal(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Contents), 
              Set#Union(read($Heap, 
                  read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left), 
                  _module.Node.Contents), 
                Set#UnionOne(Set#Empty(): Set Box, 
                  $Box(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.data)))))));
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) == null
               && read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
             ==> Set#Equal(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Contents), 
              Set#Union(Set#UnionOne(Set#Empty(): Set Box, 
                  $Box(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.data))), 
                read($Heap, 
                  read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right), 
                  _module.Node.Contents)))));
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
               && read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
             ==> Set#Disjoint(read($Heap, 
                read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left), 
                _module.Node.Repr), 
              read($Heap, 
                read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right), 
                _module.Node.Repr))));
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
               && read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
             ==> Set#Equal(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Contents), 
              Set#Union(Set#Union(read($Heap, 
                    read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left), 
                    _module.Node.Contents), 
                  Set#UnionOne(Set#Empty(): Set Box, 
                    $Box(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.data)))), 
                read($Heap, 
                  read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right), 
                  _module.Node.Contents)))));
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> Set#Equal(read($Heap, this, _module.IntSet.Contents), 
          read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Contents)));
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    read($Heap, this, _module.IntSet.Repr)[$Box($o)]
         && !read(old($Heap), this, _module.IntSet.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures Set#Equal(read($Heap, this, _module.IntSet.Contents), 
    Set#Union(read(old($Heap), this, _module.IntSet.Contents), 
      Set#UnionOne(Set#Empty(): Set Box, $Box(x#0))));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || read(old($Heap), this, _module.IntSet.Repr)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



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

implementation Impl$$_module.IntSet.Insert(this: ref, x#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var t#0: ref
     where $Is(t#0, Tclass._module.Node()) && $IsAlloc(t#0, Tclass._module.Node(), $Heap);
  var $rhs##0: ref
     where $Is($rhs##0, Tclass._module.Node())
       && $IsAlloc($rhs##0, Tclass._module.Node(), $Heap);
  var x##0: int;
  var n##0: ref;
  var $rhs#0: ref where $Is($rhs#0, Tclass._module.Node?());
  var $rhs#1: Set Box where $Is($rhs#1, TSet(TInt));
  var $rhs#2: Set Box where $Is($rhs#2, TSet(Tclass._System.object()));

    // AddMethodImpl: Insert, Impl$$_module.IntSet.Insert
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.IntSet.Repr)[$Box($o)]);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(44,2): initial state"} true;
    $_reverifyPost := false;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(45,26)
    assume true;
    // TrCallStmt: Adding lhs with type Node
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##0 := x#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    n##0 := read($Heap, this, _module.IntSet.root);
    assert (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && read($Heap, $o, alloc)
           && (if n##0 != null
             then read($Heap, n##0, _module.Node.Repr)
             else Set#Empty(): Set Box)[$Box($o)]
         ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0 := Call$$_module.IntSet.InsertHelper(x##0, n##0);
    // TrCallStmt: After ProcessCallStmt
    t#0 := $rhs##0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(45,34)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(46,10)
    assume true;
    assert $_Frame[this, _module.IntSet.root];
    assume true;
    $rhs#0 := t#0;
    $Heap := update($Heap, this, _module.IntSet.root, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(46,13)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(47,14)
    assume true;
    assert $_Frame[this, _module.IntSet.Contents];
    assert read($Heap, this, _module.IntSet.root) != null;
    assume true;
    $rhs#1 := read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Contents);
    $Heap := update($Heap, this, _module.IntSet.Contents, $rhs#1);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(47,29)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(48,10)
    assume true;
    assert $_Frame[this, _module.IntSet.Repr];
    assert read($Heap, this, _module.IntSet.root) != null;
    assume true;
    $rhs#2 := Set#Union(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr), 
      Set#UnionOne(Set#Empty(): Set Box, $Box(this)));
    $Heap := update($Heap, this, _module.IntSet.Repr, $rhs#2);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(48,30)"} true;
}



procedure CheckWellformed$$_module.IntSet.InsertHelper(x#0: int, 
    n#0: ref
       where $Is(n#0, Tclass._module.Node?()) && $IsAlloc(n#0, Tclass._module.Node?(), $Heap))
   returns (m#0: ref
       where $Is(m#0, Tclass._module.Node()) && $IsAlloc(m#0, Tclass._module.Node(), $Heap));
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.IntSet.InsertHelper(x#0: int, n#0: ref) returns (m#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: InsertHelper, CheckWellformed$$_module.IntSet.InsertHelper
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> (if n#0 != null
           then read($Heap, n#0, _module.Node.Repr)
           else Set#Empty(): Set Box)[$Box($o)]);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(51,16): initial state"} true;
    if (*)
    {
        assume n#0 == null;
    }
    else
    {
        assume n#0 != null;
        assert n#0 != null;
        assume _module.Node.Valid#canCall($Heap, n#0);
        assume _module.Node.Valid($LS($LZ), $Heap, n#0);
    }

    if (n#0 != null)
    {
        assert n#0 != null;
    }
    else
    {
    }

    if (n#0 == null)
    {
    }
    else
    {
        assert n#0 != null;
    }

    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc)
         ==> $Heap[$o] == old($Heap)[$o]
           || (if n#0 != null
             then read(old($Heap), n#0, _module.Node.Repr)
             else Set#Empty(): Set Box)[$Box($o)]);
    assume $HeapSucc(old($Heap), $Heap);
    havoc m#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(54,19): post-state"} true;
    assert m#0 != null;
    assume _module.Node.Valid#canCall($Heap, m#0);
    assume _module.Node.Valid($LS($LZ), $Heap, m#0);
    if (*)
    {
        assume n#0 == null;
        assert m#0 != null;
        assume (forall $o: ref :: 
          { read($Heap, m#0, _module.Node.Repr)[$Box($o)] } 
          read($Heap, m#0, _module.Node.Repr)[$Box($o)]
             ==> $o != null && !read(old($Heap), $o, alloc));
        assert m#0 != null;
        assume Set#Equal(read($Heap, m#0, _module.Node.Contents), 
          Set#UnionOne(Set#Empty(): Set Box, $Box(x#0)));
    }
    else
    {
        assume n#0 == null
           ==> (forall $o: ref :: 
              { read($Heap, m#0, _module.Node.Repr)[$Box($o)] } 
              read($Heap, m#0, _module.Node.Repr)[$Box($o)]
                 ==> $o != null && !read(old($Heap), $o, alloc))
             && Set#Equal(read($Heap, m#0, _module.Node.Contents), 
              Set#UnionOne(Set#Empty(): Set Box, $Box(x#0)));
    }

    if (*)
    {
        assume n#0 != null;
        assume m#0 == n#0;
        assert n#0 != null;
        assert n#0 != null;
        assert $IsAlloc(n#0, Tclass._module.Node?(), old($Heap));
        assume Set#Equal(read($Heap, n#0, _module.Node.Contents), 
          Set#Union(read(old($Heap), n#0, _module.Node.Contents), 
            Set#UnionOne(Set#Empty(): Set Box, $Box(x#0))));
    }
    else
    {
        assume n#0 != null
           ==> m#0 == n#0
             && Set#Equal(read($Heap, n#0, _module.Node.Contents), 
              Set#Union(read(old($Heap), n#0, _module.Node.Contents), 
                Set#UnionOne(Set#Empty(): Set Box, $Box(x#0))));
    }

    if (*)
    {
        assume n#0 != null;
        assert n#0 != null;
        assert n#0 != null;
        assert $IsAlloc(n#0, Tclass._module.Node?(), old($Heap));
        assume (forall $o: ref :: 
          { read(old($Heap), $o, alloc) } 
          read($Heap, n#0, _module.Node.Repr)[$Box($o)]
               && !read(old($Heap), n#0, _module.Node.Repr)[$Box($o)]
             ==> $o != null && !read(old($Heap), $o, alloc));
    }
    else
    {
        assume n#0 != null
           ==> (forall $o: ref :: 
            { read(old($Heap), $o, alloc) } 
            read($Heap, n#0, _module.Node.Repr)[$Box($o)]
                 && !read(old($Heap), n#0, _module.Node.Repr)[$Box($o)]
               ==> $o != null && !read(old($Heap), $o, alloc));
    }
}



procedure Call$$_module.IntSet.InsertHelper(x#0: int, 
    n#0: ref
       where $Is(n#0, Tclass._module.Node?()) && $IsAlloc(n#0, Tclass._module.Node?(), $Heap))
   returns (m#0: ref
       where $Is(m#0, Tclass._module.Node()) && $IsAlloc(m#0, Tclass._module.Node(), $Heap));
  // user-defined preconditions
  requires n#0 == null || _module.Node.Valid($LS($LS($LZ)), $Heap, n#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Node.Valid#canCall($Heap, m#0);
  free ensures _module.Node.Valid#canCall($Heap, m#0)
     && 
    _module.Node.Valid($LS($LZ), $Heap, m#0)
     && 
    read($Heap, m#0, _module.Node.Repr)[$Box(m#0)]
     && (read($Heap, m#0, _module.Node.left) != null
       ==> read($Heap, m#0, _module.Node.Repr)[$Box(read($Heap, m#0, _module.Node.left))]
         && Set#Subset(read($Heap, read($Heap, m#0, _module.Node.left), _module.Node.Repr), 
          read($Heap, m#0, _module.Node.Repr))
         && !read($Heap, read($Heap, m#0, _module.Node.left), _module.Node.Repr)[$Box(m#0)]
         && _module.Node.Valid($LS($LZ), $Heap, read($Heap, m#0, _module.Node.left))
         && (forall y#0: int :: 
          { read($Heap, read($Heap, m#0, _module.Node.left), _module.Node.Contents)[$Box(y#0)] } 
          true
             ==> 
            read($Heap, read($Heap, m#0, _module.Node.left), _module.Node.Contents)[$Box(y#0)]
             ==> y#0 < read($Heap, m#0, _module.Node.data)))
     && (read($Heap, m#0, _module.Node.right) != null
       ==> read($Heap, m#0, _module.Node.Repr)[$Box(read($Heap, m#0, _module.Node.right))]
         && Set#Subset(read($Heap, read($Heap, m#0, _module.Node.right), _module.Node.Repr), 
          read($Heap, m#0, _module.Node.Repr))
         && !read($Heap, read($Heap, m#0, _module.Node.right), _module.Node.Repr)[$Box(m#0)]
         && _module.Node.Valid($LS($LZ), $Heap, read($Heap, m#0, _module.Node.right))
         && (forall y#1: int :: 
          { read($Heap, read($Heap, m#0, _module.Node.right), _module.Node.Contents)[$Box(y#1)] } 
          true
             ==> 
            read($Heap, read($Heap, m#0, _module.Node.right), _module.Node.Contents)[$Box(y#1)]
             ==> read($Heap, m#0, _module.Node.data) < y#1))
     && (read($Heap, m#0, _module.Node.left) == null
         && read($Heap, m#0, _module.Node.right) == null
       ==> Set#Equal(read($Heap, m#0, _module.Node.Contents), 
        Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, m#0, _module.Node.data)))))
     && (read($Heap, m#0, _module.Node.left) != null
         && read($Heap, m#0, _module.Node.right) == null
       ==> Set#Equal(read($Heap, m#0, _module.Node.Contents), 
        Set#Union(read($Heap, read($Heap, m#0, _module.Node.left), _module.Node.Contents), 
          Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, m#0, _module.Node.data))))))
     && (read($Heap, m#0, _module.Node.left) == null
         && read($Heap, m#0, _module.Node.right) != null
       ==> Set#Equal(read($Heap, m#0, _module.Node.Contents), 
        Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, m#0, _module.Node.data))), 
          read($Heap, read($Heap, m#0, _module.Node.right), _module.Node.Contents))))
     && (read($Heap, m#0, _module.Node.left) != null
         && read($Heap, m#0, _module.Node.right) != null
       ==> Set#Disjoint(read($Heap, read($Heap, m#0, _module.Node.left), _module.Node.Repr), 
          read($Heap, read($Heap, m#0, _module.Node.right), _module.Node.Repr))
         && Set#Equal(read($Heap, m#0, _module.Node.Contents), 
          Set#Union(Set#Union(read($Heap, read($Heap, m#0, _module.Node.left), _module.Node.Contents), 
              Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, m#0, _module.Node.data)))), 
            read($Heap, read($Heap, m#0, _module.Node.right), _module.Node.Contents))));
  free ensures true;
  ensures n#0 == null
     ==> (forall $o: ref :: 
      { read($Heap, m#0, _module.Node.Repr)[$Box($o)] } 
      read($Heap, m#0, _module.Node.Repr)[$Box($o)]
         ==> $o != null && !read(old($Heap), $o, alloc));
  ensures n#0 == null
     ==> Set#Equal(read($Heap, m#0, _module.Node.Contents), 
      Set#UnionOne(Set#Empty(): Set Box, $Box(x#0)));
  free ensures true;
  ensures n#0 != null ==> m#0 == n#0;
  ensures n#0 != null
     ==> Set#Equal(read($Heap, n#0, _module.Node.Contents), 
      Set#Union(read(old($Heap), n#0, _module.Node.Contents), 
        Set#UnionOne(Set#Empty(): Set Box, $Box(x#0))));
  free ensures true;
  ensures n#0 != null
     ==> (forall $o: ref :: 
      { read(old($Heap), $o, alloc) } 
      read($Heap, n#0, _module.Node.Repr)[$Box($o)]
           && !read(old($Heap), n#0, _module.Node.Repr)[$Box($o)]
         ==> $o != null && !read(old($Heap), $o, alloc));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || (if n#0 != null
           then read(old($Heap), n#0, _module.Node.Repr)
           else Set#Empty(): Set Box)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.IntSet.InsertHelper(x#0: int, 
    n#0: ref
       where $Is(n#0, Tclass._module.Node?()) && $IsAlloc(n#0, Tclass._module.Node?(), $Heap))
   returns (defass#m#0: bool, 
    m#0: ref
       where defass#m#0
         ==> $Is(m#0, Tclass._module.Node()) && $IsAlloc(m#0, Tclass._module.Node(), $Heap), 
    $_reverifyPost: bool);
  free requires 3 == $FunctionContextHeight;
  // user-defined preconditions
  requires n#0 == null || _module.Node.Valid($LS($LS($LZ)), $Heap, n#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Node.Valid#canCall($Heap, m#0);
  ensures _module.Node.Valid#canCall($Heap, m#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, m#0)
       || read($Heap, m#0, _module.Node.Repr)[$Box(m#0)];
  ensures _module.Node.Valid#canCall($Heap, m#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, m#0)
       || (read($Heap, m#0, _module.Node.left) != null
         ==> read($Heap, m#0, _module.Node.Repr)[$Box(read($Heap, m#0, _module.Node.left))]);
  ensures _module.Node.Valid#canCall($Heap, m#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, m#0)
       || (read($Heap, m#0, _module.Node.left) != null
         ==> Set#Subset(read($Heap, read($Heap, m#0, _module.Node.left), _module.Node.Repr), 
          read($Heap, m#0, _module.Node.Repr)));
  ensures _module.Node.Valid#canCall($Heap, m#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, m#0)
       || (read($Heap, m#0, _module.Node.left) != null
         ==> !read($Heap, read($Heap, m#0, _module.Node.left), _module.Node.Repr)[$Box(m#0)]);
  ensures _module.Node.Valid#canCall($Heap, m#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, m#0)
       || (read($Heap, m#0, _module.Node.left) != null
         ==> _module.Node.Valid($LS($LS($LZ)), $Heap, read($Heap, m#0, _module.Node.left)));
  ensures _module.Node.Valid#canCall($Heap, m#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, m#0)
       || (read($Heap, m#0, _module.Node.left) != null
         ==> (forall y#2: int :: 
          { read($Heap, read($Heap, m#0, _module.Node.left), _module.Node.Contents)[$Box(y#2)] } 
          true
             ==> 
            read($Heap, read($Heap, m#0, _module.Node.left), _module.Node.Contents)[$Box(y#2)]
             ==> y#2 < read($Heap, m#0, _module.Node.data)));
  ensures _module.Node.Valid#canCall($Heap, m#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, m#0)
       || (read($Heap, m#0, _module.Node.right) != null
         ==> read($Heap, m#0, _module.Node.Repr)[$Box(read($Heap, m#0, _module.Node.right))]);
  ensures _module.Node.Valid#canCall($Heap, m#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, m#0)
       || (read($Heap, m#0, _module.Node.right) != null
         ==> Set#Subset(read($Heap, read($Heap, m#0, _module.Node.right), _module.Node.Repr), 
          read($Heap, m#0, _module.Node.Repr)));
  ensures _module.Node.Valid#canCall($Heap, m#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, m#0)
       || (read($Heap, m#0, _module.Node.right) != null
         ==> !read($Heap, read($Heap, m#0, _module.Node.right), _module.Node.Repr)[$Box(m#0)]);
  ensures _module.Node.Valid#canCall($Heap, m#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, m#0)
       || (read($Heap, m#0, _module.Node.right) != null
         ==> _module.Node.Valid($LS($LS($LZ)), $Heap, read($Heap, m#0, _module.Node.right)));
  ensures _module.Node.Valid#canCall($Heap, m#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, m#0)
       || (read($Heap, m#0, _module.Node.right) != null
         ==> (forall y#3: int :: 
          { read($Heap, read($Heap, m#0, _module.Node.right), _module.Node.Contents)[$Box(y#3)] } 
          true
             ==> 
            read($Heap, read($Heap, m#0, _module.Node.right), _module.Node.Contents)[$Box(y#3)]
             ==> read($Heap, m#0, _module.Node.data) < y#3));
  ensures _module.Node.Valid#canCall($Heap, m#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, m#0)
       || (read($Heap, m#0, _module.Node.left) == null
           && read($Heap, m#0, _module.Node.right) == null
         ==> Set#Equal(read($Heap, m#0, _module.Node.Contents), 
          Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, m#0, _module.Node.data)))));
  ensures _module.Node.Valid#canCall($Heap, m#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, m#0)
       || (read($Heap, m#0, _module.Node.left) != null
           && read($Heap, m#0, _module.Node.right) == null
         ==> Set#Equal(read($Heap, m#0, _module.Node.Contents), 
          Set#Union(read($Heap, read($Heap, m#0, _module.Node.left), _module.Node.Contents), 
            Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, m#0, _module.Node.data))))));
  ensures _module.Node.Valid#canCall($Heap, m#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, m#0)
       || (read($Heap, m#0, _module.Node.left) == null
           && read($Heap, m#0, _module.Node.right) != null
         ==> Set#Equal(read($Heap, m#0, _module.Node.Contents), 
          Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, m#0, _module.Node.data))), 
            read($Heap, read($Heap, m#0, _module.Node.right), _module.Node.Contents))));
  ensures _module.Node.Valid#canCall($Heap, m#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, m#0)
       || (read($Heap, m#0, _module.Node.left) != null
           && read($Heap, m#0, _module.Node.right) != null
         ==> Set#Disjoint(read($Heap, read($Heap, m#0, _module.Node.left), _module.Node.Repr), 
          read($Heap, read($Heap, m#0, _module.Node.right), _module.Node.Repr)));
  ensures _module.Node.Valid#canCall($Heap, m#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, m#0)
       || (read($Heap, m#0, _module.Node.left) != null
           && read($Heap, m#0, _module.Node.right) != null
         ==> Set#Equal(read($Heap, m#0, _module.Node.Contents), 
          Set#Union(Set#Union(read($Heap, read($Heap, m#0, _module.Node.left), _module.Node.Contents), 
              Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, m#0, _module.Node.data)))), 
            read($Heap, read($Heap, m#0, _module.Node.right), _module.Node.Contents))));
  free ensures true;
  ensures n#0 == null
     ==> (forall $o: ref :: 
      { read($Heap, m#0, _module.Node.Repr)[$Box($o)] } 
      read($Heap, m#0, _module.Node.Repr)[$Box($o)]
         ==> $o != null && !read(old($Heap), $o, alloc));
  ensures n#0 == null
     ==> Set#Equal(read($Heap, m#0, _module.Node.Contents), 
      Set#UnionOne(Set#Empty(): Set Box, $Box(x#0)));
  free ensures true;
  ensures n#0 != null ==> m#0 == n#0;
  ensures n#0 != null
     ==> Set#Equal(read($Heap, n#0, _module.Node.Contents), 
      Set#Union(read(old($Heap), n#0, _module.Node.Contents), 
        Set#UnionOne(Set#Empty(): Set Box, $Box(x#0))));
  free ensures true;
  ensures n#0 != null
     ==> (forall $o: ref :: 
      { read(old($Heap), $o, alloc) } 
      read($Heap, n#0, _module.Node.Repr)[$Box($o)]
           && !read(old($Heap), n#0, _module.Node.Repr)[$Box($o)]
         ==> $o != null && !read(old($Heap), $o, alloc));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || (if n#0 != null
           then read(old($Heap), n#0, _module.Node.Repr)
           else Set#Empty(): Set Box)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.IntSet.InsertHelper(x#0: int, n#0: ref) returns (defass#m#0: bool, m#0: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $nw: ref;
  var x##0_0: int;
  var t#2_0: ref
     where $Is(t#2_0, Tclass._module.Node())
       && $IsAlloc(t#2_0, Tclass._module.Node(), $Heap);
  var $rhs##2_0: ref
     where $Is($rhs##2_0, Tclass._module.Node())
       && $IsAlloc($rhs##2_0, Tclass._module.Node(), $Heap);
  var x##2_0: int;
  var n##2_0: ref;
  var $rhs#2_0: ref where $Is($rhs#2_0, Tclass._module.Node?());
  var $rhs#2_1: Set Box where $Is($rhs#2_1, TSet(Tclass._System.object()));
  var t#0: ref
     where $Is(t#0, Tclass._module.Node()) && $IsAlloc(t#0, Tclass._module.Node(), $Heap);
  var $rhs##0: ref
     where $Is($rhs##0, Tclass._module.Node())
       && $IsAlloc($rhs##0, Tclass._module.Node(), $Heap);
  var x##0: int;
  var n##0: ref;
  var $rhs#0: ref where $Is($rhs#0, Tclass._module.Node?());
  var $rhs#1: Set Box where $Is($rhs#1, TSet(Tclass._System.object()));
  var $rhs#2: Set Box where $Is($rhs#2, TSet(TInt));

    // AddMethodImpl: InsertHelper, Impl$$_module.IntSet.InsertHelper
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> (if n#0 != null
           then read($Heap, n#0, _module.Node.Repr)
           else Set#Empty(): Set Box)[$Box($o)]);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(59,2): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(60,5)
    assume true;
    if (n#0 == null)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(61,9)
        assume true;
        // ----- init call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(61,21)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        x##0_0 := x#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call $nw := Call$$_module.Node.Init(x##0_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(61,27)"} true;
        m#0 := $nw;
        defass#m#0 := true;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(61,27)"} true;
    }
    else
    {
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(62,12)
        assert n#0 != null;
        assume true;
        if (x#0 == read($Heap, n#0, _module.Node.data))
        {
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(63,9)
            assume true;
            assume true;
            assert $Is(n#0, Tclass._module.Node());
            m#0 := n#0;
            defass#m#0 := true;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(63,12)"} true;
        }
        else
        {
            // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(65,7)
            assert n#0 != null;
            assume true;
            if (x#0 < read($Heap, n#0, _module.Node.data))
            {
                // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(66,9)
                assert {:subsumption 0} n#0 != null;
                if (read($Heap, n#0, _module.Node.right) != null)
                {
                    assert {:subsumption 0} n#0 != null;
                    assert {:subsumption 0} read($Heap, n#0, _module.Node.right) != null;
                    assume _module.Node.Valid#canCall($Heap, read($Heap, n#0, _module.Node.right));
                }

                assume read($Heap, n#0, _module.Node.right) != null
                   ==> _module.Node.Valid#canCall($Heap, read($Heap, n#0, _module.Node.right));
                assert {:subsumption 0} read($Heap, n#0, _module.Node.right) == null
                   || _module.Node.Valid($LS($LS($LZ)), $Heap, read($Heap, n#0, _module.Node.right));
                assume read($Heap, n#0, _module.Node.right) == null
                   || _module.Node.Valid($LS($LS($LZ)), $Heap, read($Heap, n#0, _module.Node.right));
                // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(67,30)
                assume true;
                // TrCallStmt: Adding lhs with type Node
                // TrCallStmt: Before ProcessCallStmt
                assume true;
                // ProcessCallStmt: CheckSubrange
                x##2_0 := x#0;
                assert n#0 != null;
                assume true;
                // ProcessCallStmt: CheckSubrange
                n##2_0 := read($Heap, n#0, _module.Node.left);
                assert (forall<alpha> $o: ref, $f: Field alpha :: 
                  $o != null
                       && read($Heap, $o, alloc)
                       && (if n##2_0 != null
                         then read($Heap, n##2_0, _module.Node.Repr)
                         else Set#Empty(): Set Box)[$Box($o)]
                     ==> $_Frame[$o, $f]);
                assert Set#Subset((if n##2_0 == null
                       then Set#Empty(): Set Box
                       else read($Heap, n##2_0, _module.Node.Repr)), 
                    (if n#0 == null
                       then Set#Empty(): Set Box
                       else read(old($Heap), n#0, _module.Node.Repr)))
                   && !Set#Subset((if n#0 == null
                       then Set#Empty(): Set Box
                       else read(old($Heap), n#0, _module.Node.Repr)), 
                    (if n##2_0 == null
                       then Set#Empty(): Set Box
                       else read($Heap, n##2_0, _module.Node.Repr)));
                // ProcessCallStmt: Make the call
                call $rhs##2_0 := Call$$_module.IntSet.InsertHelper(x##2_0, n##2_0);
                // TrCallStmt: After ProcessCallStmt
                t#2_0 := $rhs##2_0;
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(67,40)"} true;
                // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(68,16)
                assert n#0 != null;
                assume true;
                assert $_Frame[n#0, _module.Node.left];
                assume true;
                $rhs#2_0 := t#2_0;
                $Heap := update($Heap, n#0, _module.Node.left, $rhs#2_0);
                assume $IsGoodHeap($Heap);
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(68,19)"} true;
                // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(69,16)
                assert n#0 != null;
                assume true;
                assert $_Frame[n#0, _module.Node.Repr];
                assert n#0 != null;
                assert n#0 != null;
                assert read($Heap, n#0, _module.Node.left) != null;
                assume true;
                $rhs#2_1 := Set#Union(read($Heap, n#0, _module.Node.Repr), 
                  read($Heap, read($Heap, n#0, _module.Node.left), _module.Node.Repr));
                $Heap := update($Heap, n#0, _module.Node.Repr, $rhs#2_1);
                assume $IsGoodHeap($Heap);
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(69,38)"} true;
            }
            else
            {
                // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(71,9)
                assert {:subsumption 0} n#0 != null;
                if (read($Heap, n#0, _module.Node.left) != null)
                {
                    assert {:subsumption 0} n#0 != null;
                    assert {:subsumption 0} read($Heap, n#0, _module.Node.left) != null;
                    assume _module.Node.Valid#canCall($Heap, read($Heap, n#0, _module.Node.left));
                }

                assume read($Heap, n#0, _module.Node.left) != null
                   ==> _module.Node.Valid#canCall($Heap, read($Heap, n#0, _module.Node.left));
                assert {:subsumption 0} read($Heap, n#0, _module.Node.left) == null
                   || _module.Node.Valid($LS($LS($LZ)), $Heap, read($Heap, n#0, _module.Node.left));
                assume read($Heap, n#0, _module.Node.left) == null
                   || _module.Node.Valid($LS($LS($LZ)), $Heap, read($Heap, n#0, _module.Node.left));
                // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(72,30)
                assume true;
                // TrCallStmt: Adding lhs with type Node
                // TrCallStmt: Before ProcessCallStmt
                assume true;
                // ProcessCallStmt: CheckSubrange
                x##0 := x#0;
                assert n#0 != null;
                assume true;
                // ProcessCallStmt: CheckSubrange
                n##0 := read($Heap, n#0, _module.Node.right);
                assert (forall<alpha> $o: ref, $f: Field alpha :: 
                  $o != null
                       && read($Heap, $o, alloc)
                       && (if n##0 != null
                         then read($Heap, n##0, _module.Node.Repr)
                         else Set#Empty(): Set Box)[$Box($o)]
                     ==> $_Frame[$o, $f]);
                assert Set#Subset((if n##0 == null
                       then Set#Empty(): Set Box
                       else read($Heap, n##0, _module.Node.Repr)), 
                    (if n#0 == null
                       then Set#Empty(): Set Box
                       else read(old($Heap), n#0, _module.Node.Repr)))
                   && !Set#Subset((if n#0 == null
                       then Set#Empty(): Set Box
                       else read(old($Heap), n#0, _module.Node.Repr)), 
                    (if n##0 == null
                       then Set#Empty(): Set Box
                       else read($Heap, n##0, _module.Node.Repr)));
                // ProcessCallStmt: Make the call
                call $rhs##0 := Call$$_module.IntSet.InsertHelper(x##0, n##0);
                // TrCallStmt: After ProcessCallStmt
                t#0 := $rhs##0;
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(72,41)"} true;
                // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(73,17)
                assert n#0 != null;
                assume true;
                assert $_Frame[n#0, _module.Node.right];
                assume true;
                $rhs#0 := t#0;
                $Heap := update($Heap, n#0, _module.Node.right, $rhs#0);
                assume $IsGoodHeap($Heap);
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(73,20)"} true;
                // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(74,16)
                assert n#0 != null;
                assume true;
                assert $_Frame[n#0, _module.Node.Repr];
                assert n#0 != null;
                assert n#0 != null;
                assert read($Heap, n#0, _module.Node.right) != null;
                assume true;
                $rhs#1 := Set#Union(read($Heap, n#0, _module.Node.Repr), 
                  read($Heap, read($Heap, n#0, _module.Node.right), _module.Node.Repr));
                $Heap := update($Heap, n#0, _module.Node.Repr, $rhs#1);
                assume $IsGoodHeap($Heap);
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(74,39)"} true;
            }

            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(76,18)
            assert n#0 != null;
            assume true;
            assert $_Frame[n#0, _module.Node.Contents];
            assert n#0 != null;
            assume true;
            $rhs#2 := Set#Union(read($Heap, n#0, _module.Node.Contents), 
              Set#UnionOne(Set#Empty(): Set Box, $Box(x#0)));
            $Heap := update($Heap, n#0, _module.Node.Contents, $rhs#2);
            assume $IsGoodHeap($Heap);
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(76,36)"} true;
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(77,9)
            assume true;
            assume true;
            assert $Is(n#0, Tclass._module.Node());
            m#0 := n#0;
            defass#m#0 := true;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(77,12)"} true;
        }
    }

    assert defass#m#0;
}



procedure CheckWellformed$$_module.IntSet.Remove(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.IntSet())
         && $IsAlloc(this, Tclass._module.IntSet(), $Heap), 
    x#0: int);
  free requires 13 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.IntSet.Remove(this: ref, x#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Remove, CheckWellformed$$_module.IntSet.Remove
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.IntSet.Repr)[$Box($o)]);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(81,9): initial state"} true;
    assume _module.IntSet.Valid#canCall($Heap, this);
    assume _module.IntSet.Valid($Heap, this);
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc)
         ==> $Heap[$o] == old($Heap)[$o]
           || read(old($Heap), this, _module.IntSet.Repr)[$Box($o)]);
    assume $HeapSucc(old($Heap), $Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(84,20): post-state"} true;
    assume _module.IntSet.Valid#canCall($Heap, this);
    assume _module.IntSet.Valid($Heap, this);
    assert $IsAlloc(this, Tclass._module.IntSet(), old($Heap));
    assume (forall $o: ref :: 
      { read(old($Heap), $o, alloc) } 
      read($Heap, this, _module.IntSet.Repr)[$Box($o)]
           && !read(old($Heap), this, _module.IntSet.Repr)[$Box($o)]
         ==> $o != null && !read(old($Heap), $o, alloc));
    assert $IsAlloc(this, Tclass._module.IntSet(), old($Heap));
    assume Set#Equal(read($Heap, this, _module.IntSet.Contents), 
      Set#Difference(read(old($Heap), this, _module.IntSet.Contents), 
        Set#UnionOne(Set#Empty(): Set Box, $Box(x#0))));
}



procedure Call$$_module.IntSet.Remove(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.IntSet())
         && $IsAlloc(this, Tclass._module.IntSet(), $Heap), 
    x#0: int);
  // user-defined preconditions
  requires _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || read($Heap, this, _module.IntSet.Repr)[$Box(this)];
  requires _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) == null
         ==> Set#Equal(read($Heap, this, _module.IntSet.Contents), Set#Empty(): Set Box));
  requires _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> read($Heap, this, _module.IntSet.Repr)[$Box(read($Heap, this, _module.IntSet.root))]);
  requires _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> Set#Subset(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr), 
          read($Heap, this, _module.IntSet.Repr)));
  requires _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> !read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr)[$Box(this)]);
  requires _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr)[$Box(read($Heap, this, _module.IntSet.root))]);
  requires _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
             ==> read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr)[$Box(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left))]));
  requires _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
             ==> Set#Subset(read($Heap, 
                read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left), 
                _module.Node.Repr), 
              read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr))));
  requires _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
             ==> !read($Heap, 
              read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left), 
              _module.Node.Repr)[$Box(read($Heap, this, _module.IntSet.root))]));
  requires _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
             ==> _module.Node.Valid($LS($LS($LZ)), 
              $Heap, 
              read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left))));
  requires _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
             ==> (forall y#0: int :: 
              { read($Heap, 
                  read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left), 
                  _module.Node.Contents)[$Box(y#0)] } 
              true
                 ==> 
                read($Heap, 
                  read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left), 
                  _module.Node.Contents)[$Box(y#0)]
                 ==> y#0 < read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.data))));
  requires _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
             ==> read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr)[$Box(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right))]));
  requires _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
             ==> Set#Subset(read($Heap, 
                read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right), 
                _module.Node.Repr), 
              read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr))));
  requires _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
             ==> !read($Heap, 
              read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right), 
              _module.Node.Repr)[$Box(read($Heap, this, _module.IntSet.root))]));
  requires _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
             ==> _module.Node.Valid($LS($LS($LZ)), 
              $Heap, 
              read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right))));
  requires _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
             ==> (forall y#1: int :: 
              { read($Heap, 
                  read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right), 
                  _module.Node.Contents)[$Box(y#1)] } 
              true
                 ==> 
                read($Heap, 
                  read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right), 
                  _module.Node.Contents)[$Box(y#1)]
                 ==> read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.data) < y#1)));
  requires _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) == null
               && read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) == null
             ==> Set#Equal(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Contents), 
              Set#UnionOne(Set#Empty(): Set Box, 
                $Box(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.data))))));
  requires _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
               && read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) == null
             ==> Set#Equal(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Contents), 
              Set#Union(read($Heap, 
                  read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left), 
                  _module.Node.Contents), 
                Set#UnionOne(Set#Empty(): Set Box, 
                  $Box(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.data)))))));
  requires _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) == null
               && read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
             ==> Set#Equal(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Contents), 
              Set#Union(Set#UnionOne(Set#Empty(): Set Box, 
                  $Box(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.data))), 
                read($Heap, 
                  read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right), 
                  _module.Node.Contents)))));
  requires _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
               && read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
             ==> Set#Disjoint(read($Heap, 
                read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left), 
                _module.Node.Repr), 
              read($Heap, 
                read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right), 
                _module.Node.Repr))));
  requires _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
               && read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
             ==> Set#Equal(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Contents), 
              Set#Union(Set#Union(read($Heap, 
                    read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left), 
                    _module.Node.Contents), 
                  Set#UnionOne(Set#Empty(): Set Box, 
                    $Box(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.data)))), 
                read($Heap, 
                  read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right), 
                  _module.Node.Contents)))));
  requires _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> Set#Equal(read($Heap, this, _module.IntSet.Contents), 
          read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Contents)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.IntSet.Valid#canCall($Heap, this);
  free ensures _module.IntSet.Valid#canCall($Heap, this)
     && 
    _module.IntSet.Valid($Heap, this)
     && 
    read($Heap, this, _module.IntSet.Repr)[$Box(this)]
     && (read($Heap, this, _module.IntSet.root) == null
       ==> Set#Equal(read($Heap, this, _module.IntSet.Contents), Set#Empty(): Set Box))
     && (read($Heap, this, _module.IntSet.root) != null
       ==> read($Heap, this, _module.IntSet.Repr)[$Box(read($Heap, this, _module.IntSet.root))]
         && Set#Subset(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr), 
          read($Heap, this, _module.IntSet.Repr))
         && !read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr)[$Box(this)]
         && _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
         && Set#Equal(read($Heap, this, _module.IntSet.Contents), 
          read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Contents)));
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    read($Heap, this, _module.IntSet.Repr)[$Box($o)]
         && !read(old($Heap), this, _module.IntSet.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures Set#Equal(read($Heap, this, _module.IntSet.Contents), 
    Set#Difference(read(old($Heap), this, _module.IntSet.Contents), 
      Set#UnionOne(Set#Empty(): Set Box, $Box(x#0))));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || read(old($Heap), this, _module.IntSet.Repr)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.IntSet.Remove(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.IntSet())
         && $IsAlloc(this, Tclass._module.IntSet(), $Heap), 
    x#0: int)
   returns ($_reverifyPost: bool);
  free requires 13 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.IntSet.Valid#canCall($Heap, this)
     && 
    _module.IntSet.Valid($Heap, this)
     && 
    read($Heap, this, _module.IntSet.Repr)[$Box(this)]
     && (read($Heap, this, _module.IntSet.root) == null
       ==> Set#Equal(read($Heap, this, _module.IntSet.Contents), Set#Empty(): Set Box))
     && (read($Heap, this, _module.IntSet.root) != null
       ==> read($Heap, this, _module.IntSet.Repr)[$Box(read($Heap, this, _module.IntSet.root))]
         && Set#Subset(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr), 
          read($Heap, this, _module.IntSet.Repr))
         && !read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr)[$Box(this)]
         && _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
         && Set#Equal(read($Heap, this, _module.IntSet.Contents), 
          read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Contents)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.IntSet.Valid#canCall($Heap, this);
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || read($Heap, this, _module.IntSet.Repr)[$Box(this)];
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) == null
         ==> Set#Equal(read($Heap, this, _module.IntSet.Contents), Set#Empty(): Set Box));
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> read($Heap, this, _module.IntSet.Repr)[$Box(read($Heap, this, _module.IntSet.root))]);
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> Set#Subset(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr), 
          read($Heap, this, _module.IntSet.Repr)));
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> !read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr)[$Box(this)]);
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr)[$Box(read($Heap, this, _module.IntSet.root))]);
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
             ==> read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr)[$Box(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left))]));
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
             ==> Set#Subset(read($Heap, 
                read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left), 
                _module.Node.Repr), 
              read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr))));
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
             ==> !read($Heap, 
              read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left), 
              _module.Node.Repr)[$Box(read($Heap, this, _module.IntSet.root))]));
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
             ==> _module.Node.Valid($LS($LS($LZ)), 
              $Heap, 
              read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left))));
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
             ==> (forall y#6: int :: 
              { read($Heap, 
                  read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left), 
                  _module.Node.Contents)[$Box(y#6)] } 
              true
                 ==> 
                read($Heap, 
                  read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left), 
                  _module.Node.Contents)[$Box(y#6)]
                 ==> y#6 < read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.data))));
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
             ==> read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr)[$Box(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right))]));
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
             ==> Set#Subset(read($Heap, 
                read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right), 
                _module.Node.Repr), 
              read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr))));
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
             ==> !read($Heap, 
              read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right), 
              _module.Node.Repr)[$Box(read($Heap, this, _module.IntSet.root))]));
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
             ==> _module.Node.Valid($LS($LS($LZ)), 
              $Heap, 
              read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right))));
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
             ==> (forall y#7: int :: 
              { read($Heap, 
                  read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right), 
                  _module.Node.Contents)[$Box(y#7)] } 
              true
                 ==> 
                read($Heap, 
                  read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right), 
                  _module.Node.Contents)[$Box(y#7)]
                 ==> read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.data) < y#7)));
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) == null
               && read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) == null
             ==> Set#Equal(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Contents), 
              Set#UnionOne(Set#Empty(): Set Box, 
                $Box(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.data))))));
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
               && read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) == null
             ==> Set#Equal(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Contents), 
              Set#Union(read($Heap, 
                  read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left), 
                  _module.Node.Contents), 
                Set#UnionOne(Set#Empty(): Set Box, 
                  $Box(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.data)))))));
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) == null
               && read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
             ==> Set#Equal(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Contents), 
              Set#Union(Set#UnionOne(Set#Empty(): Set Box, 
                  $Box(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.data))), 
                read($Heap, 
                  read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right), 
                  _module.Node.Contents)))));
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
               && read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
             ==> Set#Disjoint(read($Heap, 
                read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left), 
                _module.Node.Repr), 
              read($Heap, 
                read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right), 
                _module.Node.Repr))));
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, this, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.IntSet.root))
           || (read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left) != null
               && read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right) != null
             ==> Set#Equal(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Contents), 
              Set#Union(Set#Union(read($Heap, 
                    read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.left), 
                    _module.Node.Contents), 
                  Set#UnionOne(Set#Empty(): Set Box, 
                    $Box(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.data)))), 
                read($Heap, 
                  read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.right), 
                  _module.Node.Contents)))));
  ensures _module.IntSet.Valid#canCall($Heap, this)
     ==> _module.IntSet.Valid($Heap, this)
       || (read($Heap, this, _module.IntSet.root) != null
         ==> Set#Equal(read($Heap, this, _module.IntSet.Contents), 
          read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Contents)));
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    read($Heap, this, _module.IntSet.Repr)[$Box($o)]
         && !read(old($Heap), this, _module.IntSet.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures Set#Equal(read($Heap, this, _module.IntSet.Contents), 
    Set#Difference(read(old($Heap), this, _module.IntSet.Contents), 
      Set#UnionOne(Set#Empty(): Set Box, $Box(x#0))));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || read(old($Heap), this, _module.IntSet.Repr)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.IntSet.Remove(this: ref, x#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var newRoot#0_0: ref
     where $Is(newRoot#0_0, Tclass._module.Node?())
       && $IsAlloc(newRoot#0_0, Tclass._module.Node?(), $Heap);
  var $rhs##0_0: ref
     where $Is($rhs##0_0, Tclass._module.Node?())
       && $IsAlloc($rhs##0_0, Tclass._module.Node?(), $Heap);
  var x##0_0: int;
  var $rhs#0_0: ref where $Is($rhs#0_0, Tclass._module.Node?());
  var $rhs#0_0_0: Set Box where $Is($rhs#0_0_0, TSet(TInt));
  var $rhs#0_0_1: Set Box where $Is($rhs#0_0_1, TSet(Tclass._System.object()));
  var $rhs#0_1: Set Box where $Is($rhs#0_1, TSet(TInt));
  var $rhs#0_2: Set Box where $Is($rhs#0_2, TSet(Tclass._System.object()));

    // AddMethodImpl: Remove, Impl$$_module.IntSet.Remove
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.IntSet.Repr)[$Box($o)]);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(86,2): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(87,5)
    assume true;
    if (read($Heap, this, _module.IntSet.root) != null)
    {
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(88,33)
        assume true;
        // TrCallStmt: Adding lhs with type Node?
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        assert read($Heap, this, _module.IntSet.root) != null;
        assume true;
        // ProcessCallStmt: CheckSubrange
        x##0_0 := x#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null
               && read($Heap, $o, alloc)
               && read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr)[$Box($o)]
             ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call $rhs##0_0 := Call$$_module.Node.Remove(read($Heap, this, _module.IntSet.root), x##0_0);
        // TrCallStmt: After ProcessCallStmt
        newRoot#0_0 := $rhs##0_0;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(88,35)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(89,12)
        assume true;
        assert $_Frame[this, _module.IntSet.root];
        assume true;
        $rhs#0_0 := newRoot#0_0;
        $Heap := update($Heap, this, _module.IntSet.root, $rhs#0_0);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(89,21)"} true;
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(90,7)
        assume true;
        if (read($Heap, this, _module.IntSet.root) == null)
        {
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(91,18)
            assume true;
            assert $_Frame[this, _module.IntSet.Contents];
            assume true;
            $rhs#0_0_0 := Lit(Set#Empty(): Set Box);
            $Heap := update($Heap, this, _module.IntSet.Contents, $rhs#0_0_0);
            assume $IsGoodHeap($Heap);
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(91,22)"} true;
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(92,14)
            assume true;
            assert $_Frame[this, _module.IntSet.Repr];
            assume true;
            assert $Is(Set#UnionOne(Set#Empty(): Set Box, $Box(this)), TSet(Tclass._System.object()));
            $rhs#0_0_1 := Set#UnionOne(Set#Empty(): Set Box, $Box(this));
            $Heap := update($Heap, this, _module.IntSet.Repr, $rhs#0_0_1);
            assume $IsGoodHeap($Heap);
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(92,22)"} true;
        }
        else
        {
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(94,18)
            assume true;
            assert $_Frame[this, _module.IntSet.Contents];
            assert read($Heap, this, _module.IntSet.root) != null;
            assume true;
            $rhs#0_1 := read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Contents);
            $Heap := update($Heap, this, _module.IntSet.Contents, $rhs#0_1);
            assume $IsGoodHeap($Heap);
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(94,33)"} true;
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(95,14)
            assume true;
            assert $_Frame[this, _module.IntSet.Repr];
            assert read($Heap, this, _module.IntSet.root) != null;
            assume true;
            $rhs#0_2 := Set#Union(read($Heap, read($Heap, this, _module.IntSet.root), _module.Node.Repr), 
              Set#UnionOne(Set#Empty(): Set Box, $Box(this)));
            $Heap := update($Heap, this, _module.IntSet.Repr, $rhs#0_2);
            assume $IsGoodHeap($Heap);
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(95,34)"} true;
        }
    }
    else
    {
    }
}



// _module.IntSet: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.IntSet()) } 
  $Is(c#0, Tclass._module.IntSet())
     <==> $Is(c#0, Tclass._module.IntSet?()) && c#0 != null);

// _module.IntSet: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.IntSet(), $h) } 
  $IsAlloc(c#0, Tclass._module.IntSet(), $h)
     <==> $IsAlloc(c#0, Tclass._module.IntSet?(), $h));

const unique class._module.Node?: ClassName;

// Node: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.Node?()) } 
  $Is($o, Tclass._module.Node?())
     <==> $o == null || dtype($o) == Tclass._module.Node?());

// Node: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.Node?(), $h) } 
  $IsAlloc($o, Tclass._module.Node?(), $h) <==> $o == null || read($h, $o, alloc));

const _module.Node.Contents: Field (Set Box);

// Node.Contents: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Node.Contents) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Node?()
     ==> $Is(read($h, $o, _module.Node.Contents), TSet(TInt)));

// Node.Contents: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Node.Contents) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Node?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Node.Contents), TSet(TInt), $h));

const _module.Node.Repr: Field (Set Box);

// Node.Repr: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Node.Repr) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Node?()
     ==> $Is(read($h, $o, _module.Node.Repr), TSet(Tclass._System.object())));

// Node.Repr: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Node.Repr) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Node?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Node.Repr), TSet(Tclass._System.object()), $h));

const _module.Node.data: Field int;

// Node.data: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Node.data) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Node?()
     ==> $Is(read($h, $o, _module.Node.data), TInt));

// Node.data: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Node.data) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Node?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Node.data), TInt, $h));

const _module.Node.left: Field ref;

// Node.left: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Node.left) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Node?()
     ==> $Is(read($h, $o, _module.Node.left), Tclass._module.Node?()));

// Node.left: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Node.left) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Node?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Node.left), Tclass._module.Node?(), $h));

const _module.Node.right: Field ref;

// Node.right: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Node.right) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Node?()
     ==> $Is(read($h, $o, _module.Node.right), Tclass._module.Node?()));

// Node.right: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Node.right) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Node?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Node.right), Tclass._module.Node?(), $h));

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
      $o != null && ($o == this || read($h0, this, _module.Node.Repr)[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.Node.Valid($ly, $h0, this) == _module.Node.Valid($ly, $h1, this));

// consequence axiom for _module.Node.Valid
axiom 1 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, this: ref :: 
    { _module.Node.Valid($ly, $Heap, this) } 
    _module.Node.Valid#canCall($Heap, this)
         || (1 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.Node())
           && $IsAlloc(this, Tclass._module.Node(), $Heap))
       ==> 
      _module.Node.Valid($ly, $Heap, this)
       ==> read($Heap, this, _module.Node.Repr)[$Box(this)]);

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
axiom 1 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, this: ref :: 
    { _module.Node.Valid($LS($ly), $Heap, this), $IsGoodHeap($Heap) } 
    _module.Node.Valid#canCall($Heap, this)
         || (1 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.Node())
           && $IsAlloc(this, Tclass._module.Node(), $Heap))
       ==> (read($Heap, this, _module.Node.Repr)[$Box(this)]
           ==> (read($Heap, this, _module.Node.left) != null
               ==> 
              read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.left))]
               ==> 
              Set#Subset(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr), 
                read($Heap, this, _module.Node.Repr))
               ==> 
              !read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr)[$Box(this)]
               ==> _module.Node.Valid#canCall($Heap, read($Heap, this, _module.Node.left)))
             && (
              (read($Heap, this, _module.Node.left) != null
               ==> read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.left))]
                 && Set#Subset(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr), 
                  read($Heap, this, _module.Node.Repr))
                 && !read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr)[$Box(this)]
                 && _module.Node.Valid($ly, $Heap, read($Heap, this, _module.Node.left))
                 && (forall y#0: int :: 
                  { read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents)[$Box(y#0)] } 
                  true
                     ==> 
                    read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents)[$Box(y#0)]
                     ==> y#0 < read($Heap, this, _module.Node.data)))
               ==> 
              read($Heap, this, _module.Node.right) != null
               ==> 
              read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.right))]
               ==> 
              Set#Subset(read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr), 
                read($Heap, this, _module.Node.Repr))
               ==> 
              !read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr)[$Box(this)]
               ==> _module.Node.Valid#canCall($Heap, read($Heap, this, _module.Node.right))))
         && _module.Node.Valid($LS($ly), $Heap, this)
           == (
            read($Heap, this, _module.Node.Repr)[$Box(this)]
             && (read($Heap, this, _module.Node.left) != null
               ==> read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.left))]
                 && Set#Subset(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr), 
                  read($Heap, this, _module.Node.Repr))
                 && !read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr)[$Box(this)]
                 && _module.Node.Valid($ly, $Heap, read($Heap, this, _module.Node.left))
                 && (forall y#0: int :: 
                  { read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents)[$Box(y#0)] } 
                  true
                     ==> 
                    read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents)[$Box(y#0)]
                     ==> y#0 < read($Heap, this, _module.Node.data)))
             && (read($Heap, this, _module.Node.right) != null
               ==> read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.right))]
                 && Set#Subset(read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr), 
                  read($Heap, this, _module.Node.Repr))
                 && !read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr)[$Box(this)]
                 && _module.Node.Valid($ly, $Heap, read($Heap, this, _module.Node.right))
                 && (forall y#1: int :: 
                  { read($Heap, read($Heap, this, _module.Node.right), _module.Node.Contents)[$Box(y#1)] } 
                  true
                     ==> 
                    read($Heap, read($Heap, this, _module.Node.right), _module.Node.Contents)[$Box(y#1)]
                     ==> read($Heap, this, _module.Node.data) < y#1))
             && (read($Heap, this, _module.Node.left) == null
                 && read($Heap, this, _module.Node.right) == null
               ==> Set#Equal(read($Heap, this, _module.Node.Contents), 
                Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.data)))))
             && (read($Heap, this, _module.Node.left) != null
                 && read($Heap, this, _module.Node.right) == null
               ==> Set#Equal(read($Heap, this, _module.Node.Contents), 
                Set#Union(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents), 
                  Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.data))))))
             && (read($Heap, this, _module.Node.left) == null
                 && read($Heap, this, _module.Node.right) != null
               ==> Set#Equal(read($Heap, this, _module.Node.Contents), 
                Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.data))), 
                  read($Heap, read($Heap, this, _module.Node.right), _module.Node.Contents))))
             && (read($Heap, this, _module.Node.left) != null
                 && read($Heap, this, _module.Node.right) != null
               ==> Set#Disjoint(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr), 
                  read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr))
                 && Set#Equal(read($Heap, this, _module.Node.Contents), 
                  Set#Union(Set#Union(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents), 
                      Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.data)))), 
                    read($Heap, read($Heap, this, _module.Node.right), _module.Node.Contents))))));

procedure CheckWellformed$$_module.Node.Valid(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), $Heap));
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures _module.Node.Valid($LS($LZ), $Heap, this)
     ==> read($Heap, this, _module.Node.Repr)[$Box(this)];



implementation CheckWellformed$$_module.Node.Valid(this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;
  var y#2: int;
  var y#3: int;
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
  var b$reqreads#19: bool;
  var b$reqreads#20: bool;
  var b$reqreads#21: bool;
  var b$reqreads#22: bool;
  var b$reqreads#23: bool;
  var b$reqreads#24: bool;
  var b$reqreads#25: bool;
  var b$reqreads#26: bool;
  var b$reqreads#27: bool;
  var b$reqreads#28: bool;
  var b$reqreads#29: bool;
  var b$reqreads#30: bool;
  var b$reqreads#31: bool;
  var b$reqreads#32: bool;
  var b$reqreads#33: bool;
  var b$reqreads#34: bool;
  var b$reqreads#35: bool;
  var b$reqreads#36: bool;
  var b$reqreads#37: bool;
  var b$reqreads#38: bool;
  var b$reqreads#39: bool;
  var b$reqreads#40: bool;
  var b$reqreads#41: bool;
  var b$reqreads#42: bool;
  var b$reqreads#43: bool;
  var b$reqreads#44: bool;
  var b$reqreads#45: bool;
  var b$reqreads#46: bool;
  var b$reqreads#47: bool;
  var b$reqreads#48: bool;
  var b$reqreads#49: bool;
  var b$reqreads#50: bool;
  var b$reqreads#51: bool;
  var b$reqreads#52: bool;
  var b$reqreads#53: bool;
  var b$reqreads#54: bool;
  var b$reqreads#55: bool;

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
    b$reqreads#19 := true;
    b$reqreads#20 := true;
    b$reqreads#21 := true;
    b$reqreads#22 := true;
    b$reqreads#23 := true;
    b$reqreads#24 := true;
    b$reqreads#25 := true;
    b$reqreads#26 := true;
    b$reqreads#27 := true;
    b$reqreads#28 := true;
    b$reqreads#29 := true;
    b$reqreads#30 := true;
    b$reqreads#31 := true;
    b$reqreads#32 := true;
    b$reqreads#33 := true;
    b$reqreads#34 := true;
    b$reqreads#35 := true;
    b$reqreads#36 := true;
    b$reqreads#37 := true;
    b$reqreads#38 := true;
    b$reqreads#39 := true;
    b$reqreads#40 := true;
    b$reqreads#41 := true;
    b$reqreads#42 := true;
    b$reqreads#43 := true;
    b$reqreads#44 := true;
    b$reqreads#45 := true;
    b$reqreads#46 := true;
    b$reqreads#47 := true;
    b$reqreads#48 := true;
    b$reqreads#49 := true;
    b$reqreads#50 := true;
    b$reqreads#51 := true;
    b$reqreads#52 := true;
    b$reqreads#53 := true;
    b$reqreads#54 := true;
    b$reqreads#55 := true;

    // AddWellformednessCheck for function Valid
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(109,12): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> $o == this || read($Heap, this, _module.Node.Repr)[$Box($o)]);
    b$reqreads#0 := $_Frame[this, _module.Node.Repr];
    assert b$reqreads#0;
    if (*)
    {
        if (*)
        {
            assert this == this
               || (Set#Subset(Set#Union(read($Heap, this, _module.Node.Repr), 
                    Set#UnionOne(Set#Empty(): Set Box, $Box(this))), 
                  Set#Union(read($Heap, this, _module.Node.Repr), 
                    Set#UnionOne(Set#Empty(): Set Box, $Box(this))))
                 && !Set#Subset(Set#Union(read($Heap, this, _module.Node.Repr), 
                    Set#UnionOne(Set#Empty(): Set Box, $Box(this))), 
                  Set#Union(read($Heap, this, _module.Node.Repr), 
                    Set#UnionOne(Set#Empty(): Set Box, $Box(this)))));
            assume this == this || _module.Node.Valid#canCall($Heap, this);
            assume _module.Node.Valid($LS($LZ), $Heap, this);
            assume read($Heap, this, _module.Node.Repr)[$Box(this)];
        }
        else
        {
            assume _module.Node.Valid($LS($LZ), $Heap, this)
               ==> read($Heap, this, _module.Node.Repr)[$Box(this)];
        }

        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc)
             ==> $o == this || read($Heap, this, _module.Node.Repr)[$Box($o)]);
        b$reqreads#1 := $_Frame[this, _module.Node.Repr];
        if (read($Heap, this, _module.Node.Repr)[$Box(this)])
        {
            b$reqreads#2 := $_Frame[this, _module.Node.left];
            if (read($Heap, this, _module.Node.left) != null)
            {
                b$reqreads#3 := $_Frame[this, _module.Node.left];
                b$reqreads#4 := $_Frame[this, _module.Node.Repr];
                if (read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.left))])
                {
                    b$reqreads#5 := $_Frame[this, _module.Node.left];
                    assert read($Heap, this, _module.Node.left) != null;
                    b$reqreads#6 := $_Frame[read($Heap, this, _module.Node.left), _module.Node.Repr];
                    b$reqreads#7 := $_Frame[this, _module.Node.Repr];
                }

                if (read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.left))]
                   && Set#Subset(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr), 
                    read($Heap, this, _module.Node.Repr)))
                {
                    b$reqreads#8 := $_Frame[this, _module.Node.left];
                    assert read($Heap, this, _module.Node.left) != null;
                    b$reqreads#9 := $_Frame[read($Heap, this, _module.Node.left), _module.Node.Repr];
                }

                if (read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.left))]
                   && Set#Subset(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr), 
                    read($Heap, this, _module.Node.Repr))
                   && !read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr)[$Box(this)])
                {
                    b$reqreads#10 := $_Frame[this, _module.Node.left];
                    assert read($Heap, this, _module.Node.left) != null;
                    b$reqreads#11 := (forall<alpha> $o: ref, $f: Field alpha :: 
                      $o != null
                           && read($Heap, $o, alloc)
                           && ($o == read($Heap, this, _module.Node.left)
                             || read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr)[$Box($o)])
                         ==> $_Frame[$o, $f]);
                    assert Set#Subset(Set#Union(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr), 
                          Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.left)))), 
                        Set#Union(read($Heap, this, _module.Node.Repr), 
                          Set#UnionOne(Set#Empty(): Set Box, $Box(this))))
                       && !Set#Subset(Set#Union(read($Heap, this, _module.Node.Repr), 
                          Set#UnionOne(Set#Empty(): Set Box, $Box(this))), 
                        Set#Union(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr), 
                          Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.left)))));
                    assume _module.Node.Valid#canCall($Heap, read($Heap, this, _module.Node.left));
                }

                if (read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.left))]
                   && Set#Subset(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr), 
                    read($Heap, this, _module.Node.Repr))
                   && !read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr)[$Box(this)]
                   && _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.left)))
                {
                    // Begin Comprehension WF check
                    havoc y#2;
                    if (true)
                    {
                        b$reqreads#12 := $_Frame[this, _module.Node.left];
                        assert read($Heap, this, _module.Node.left) != null;
                        b$reqreads#13 := $_Frame[read($Heap, this, _module.Node.left), _module.Node.Contents];
                        if (read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents)[$Box(y#2)])
                        {
                            b$reqreads#14 := $_Frame[this, _module.Node.data];
                        }
                    }

                    // End Comprehension WF check
                }
            }
        }

        if (read($Heap, this, _module.Node.Repr)[$Box(this)]
           && (read($Heap, this, _module.Node.left) != null
             ==> read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.left))]
               && Set#Subset(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr), 
                read($Heap, this, _module.Node.Repr))
               && !read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr)[$Box(this)]
               && _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.left))
               && (forall y#4: int :: 
                { read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents)[$Box(y#4)] } 
                true
                   ==> 
                  read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents)[$Box(y#4)]
                   ==> y#4 < read($Heap, this, _module.Node.data))))
        {
            b$reqreads#15 := $_Frame[this, _module.Node.right];
            if (read($Heap, this, _module.Node.right) != null)
            {
                b$reqreads#16 := $_Frame[this, _module.Node.right];
                b$reqreads#17 := $_Frame[this, _module.Node.Repr];
                if (read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.right))])
                {
                    b$reqreads#18 := $_Frame[this, _module.Node.right];
                    assert read($Heap, this, _module.Node.right) != null;
                    b$reqreads#19 := $_Frame[read($Heap, this, _module.Node.right), _module.Node.Repr];
                    b$reqreads#20 := $_Frame[this, _module.Node.Repr];
                }

                if (read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.right))]
                   && Set#Subset(read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr), 
                    read($Heap, this, _module.Node.Repr)))
                {
                    b$reqreads#21 := $_Frame[this, _module.Node.right];
                    assert read($Heap, this, _module.Node.right) != null;
                    b$reqreads#22 := $_Frame[read($Heap, this, _module.Node.right), _module.Node.Repr];
                }

                if (read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.right))]
                   && Set#Subset(read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr), 
                    read($Heap, this, _module.Node.Repr))
                   && !read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr)[$Box(this)])
                {
                    b$reqreads#23 := $_Frame[this, _module.Node.right];
                    assert read($Heap, this, _module.Node.right) != null;
                    b$reqreads#24 := (forall<alpha> $o: ref, $f: Field alpha :: 
                      $o != null
                           && read($Heap, $o, alloc)
                           && ($o == read($Heap, this, _module.Node.right)
                             || read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr)[$Box($o)])
                         ==> $_Frame[$o, $f]);
                    assert Set#Subset(Set#Union(read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr), 
                          Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.right)))), 
                        Set#Union(read($Heap, this, _module.Node.Repr), 
                          Set#UnionOne(Set#Empty(): Set Box, $Box(this))))
                       && !Set#Subset(Set#Union(read($Heap, this, _module.Node.Repr), 
                          Set#UnionOne(Set#Empty(): Set Box, $Box(this))), 
                        Set#Union(read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr), 
                          Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.right)))));
                    assume _module.Node.Valid#canCall($Heap, read($Heap, this, _module.Node.right));
                }

                if (read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.right))]
                   && Set#Subset(read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr), 
                    read($Heap, this, _module.Node.Repr))
                   && !read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr)[$Box(this)]
                   && _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.right)))
                {
                    // Begin Comprehension WF check
                    havoc y#3;
                    if (true)
                    {
                        b$reqreads#25 := $_Frame[this, _module.Node.right];
                        assert read($Heap, this, _module.Node.right) != null;
                        b$reqreads#26 := $_Frame[read($Heap, this, _module.Node.right), _module.Node.Contents];
                        if (read($Heap, read($Heap, this, _module.Node.right), _module.Node.Contents)[$Box(y#3)])
                        {
                            b$reqreads#27 := $_Frame[this, _module.Node.data];
                        }
                    }

                    // End Comprehension WF check
                }
            }
        }

        if (read($Heap, this, _module.Node.Repr)[$Box(this)]
           && (read($Heap, this, _module.Node.left) != null
             ==> read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.left))]
               && Set#Subset(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr), 
                read($Heap, this, _module.Node.Repr))
               && !read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr)[$Box(this)]
               && _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.left))
               && (forall y#4: int :: 
                { read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents)[$Box(y#4)] } 
                true
                   ==> 
                  read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents)[$Box(y#4)]
                   ==> y#4 < read($Heap, this, _module.Node.data)))
           && (read($Heap, this, _module.Node.right) != null
             ==> read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.right))]
               && Set#Subset(read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr), 
                read($Heap, this, _module.Node.Repr))
               && !read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr)[$Box(this)]
               && _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.right))
               && (forall y#5: int :: 
                { read($Heap, read($Heap, this, _module.Node.right), _module.Node.Contents)[$Box(y#5)] } 
                true
                   ==> 
                  read($Heap, read($Heap, this, _module.Node.right), _module.Node.Contents)[$Box(y#5)]
                   ==> read($Heap, this, _module.Node.data) < y#5)))
        {
            b$reqreads#28 := $_Frame[this, _module.Node.left];
            if (read($Heap, this, _module.Node.left) == null)
            {
                b$reqreads#29 := $_Frame[this, _module.Node.right];
            }

            if (read($Heap, this, _module.Node.left) == null
               && read($Heap, this, _module.Node.right) == null)
            {
                b$reqreads#30 := $_Frame[this, _module.Node.Contents];
                b$reqreads#31 := $_Frame[this, _module.Node.data];
            }
        }

        if (read($Heap, this, _module.Node.Repr)[$Box(this)]
           && (read($Heap, this, _module.Node.left) != null
             ==> read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.left))]
               && Set#Subset(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr), 
                read($Heap, this, _module.Node.Repr))
               && !read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr)[$Box(this)]
               && _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.left))
               && (forall y#4: int :: 
                { read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents)[$Box(y#4)] } 
                true
                   ==> 
                  read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents)[$Box(y#4)]
                   ==> y#4 < read($Heap, this, _module.Node.data)))
           && (read($Heap, this, _module.Node.right) != null
             ==> read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.right))]
               && Set#Subset(read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr), 
                read($Heap, this, _module.Node.Repr))
               && !read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr)[$Box(this)]
               && _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.right))
               && (forall y#5: int :: 
                { read($Heap, read($Heap, this, _module.Node.right), _module.Node.Contents)[$Box(y#5)] } 
                true
                   ==> 
                  read($Heap, read($Heap, this, _module.Node.right), _module.Node.Contents)[$Box(y#5)]
                   ==> read($Heap, this, _module.Node.data) < y#5))
           && (read($Heap, this, _module.Node.left) == null
               && read($Heap, this, _module.Node.right) == null
             ==> Set#Equal(read($Heap, this, _module.Node.Contents), 
              Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.data))))))
        {
            b$reqreads#32 := $_Frame[this, _module.Node.left];
            if (read($Heap, this, _module.Node.left) != null)
            {
                b$reqreads#33 := $_Frame[this, _module.Node.right];
            }

            if (read($Heap, this, _module.Node.left) != null
               && read($Heap, this, _module.Node.right) == null)
            {
                b$reqreads#34 := $_Frame[this, _module.Node.Contents];
                b$reqreads#35 := $_Frame[this, _module.Node.left];
                assert read($Heap, this, _module.Node.left) != null;
                b$reqreads#36 := $_Frame[read($Heap, this, _module.Node.left), _module.Node.Contents];
                b$reqreads#37 := $_Frame[this, _module.Node.data];
            }
        }

        if (read($Heap, this, _module.Node.Repr)[$Box(this)]
           && (read($Heap, this, _module.Node.left) != null
             ==> read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.left))]
               && Set#Subset(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr), 
                read($Heap, this, _module.Node.Repr))
               && !read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr)[$Box(this)]
               && _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.left))
               && (forall y#4: int :: 
                { read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents)[$Box(y#4)] } 
                true
                   ==> 
                  read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents)[$Box(y#4)]
                   ==> y#4 < read($Heap, this, _module.Node.data)))
           && (read($Heap, this, _module.Node.right) != null
             ==> read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.right))]
               && Set#Subset(read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr), 
                read($Heap, this, _module.Node.Repr))
               && !read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr)[$Box(this)]
               && _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.right))
               && (forall y#5: int :: 
                { read($Heap, read($Heap, this, _module.Node.right), _module.Node.Contents)[$Box(y#5)] } 
                true
                   ==> 
                  read($Heap, read($Heap, this, _module.Node.right), _module.Node.Contents)[$Box(y#5)]
                   ==> read($Heap, this, _module.Node.data) < y#5))
           && (read($Heap, this, _module.Node.left) == null
               && read($Heap, this, _module.Node.right) == null
             ==> Set#Equal(read($Heap, this, _module.Node.Contents), 
              Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.data)))))
           && (read($Heap, this, _module.Node.left) != null
               && read($Heap, this, _module.Node.right) == null
             ==> Set#Equal(read($Heap, this, _module.Node.Contents), 
              Set#Union(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents), 
                Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.data)))))))
        {
            b$reqreads#38 := $_Frame[this, _module.Node.left];
            if (read($Heap, this, _module.Node.left) == null)
            {
                b$reqreads#39 := $_Frame[this, _module.Node.right];
            }

            if (read($Heap, this, _module.Node.left) == null
               && read($Heap, this, _module.Node.right) != null)
            {
                b$reqreads#40 := $_Frame[this, _module.Node.Contents];
                b$reqreads#41 := $_Frame[this, _module.Node.data];
                b$reqreads#42 := $_Frame[this, _module.Node.right];
                assert read($Heap, this, _module.Node.right) != null;
                b$reqreads#43 := $_Frame[read($Heap, this, _module.Node.right), _module.Node.Contents];
            }
        }

        if (read($Heap, this, _module.Node.Repr)[$Box(this)]
           && (read($Heap, this, _module.Node.left) != null
             ==> read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.left))]
               && Set#Subset(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr), 
                read($Heap, this, _module.Node.Repr))
               && !read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr)[$Box(this)]
               && _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.left))
               && (forall y#4: int :: 
                { read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents)[$Box(y#4)] } 
                true
                   ==> 
                  read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents)[$Box(y#4)]
                   ==> y#4 < read($Heap, this, _module.Node.data)))
           && (read($Heap, this, _module.Node.right) != null
             ==> read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.right))]
               && Set#Subset(read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr), 
                read($Heap, this, _module.Node.Repr))
               && !read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr)[$Box(this)]
               && _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.right))
               && (forall y#5: int :: 
                { read($Heap, read($Heap, this, _module.Node.right), _module.Node.Contents)[$Box(y#5)] } 
                true
                   ==> 
                  read($Heap, read($Heap, this, _module.Node.right), _module.Node.Contents)[$Box(y#5)]
                   ==> read($Heap, this, _module.Node.data) < y#5))
           && (read($Heap, this, _module.Node.left) == null
               && read($Heap, this, _module.Node.right) == null
             ==> Set#Equal(read($Heap, this, _module.Node.Contents), 
              Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.data)))))
           && (read($Heap, this, _module.Node.left) != null
               && read($Heap, this, _module.Node.right) == null
             ==> Set#Equal(read($Heap, this, _module.Node.Contents), 
              Set#Union(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents), 
                Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.data))))))
           && (read($Heap, this, _module.Node.left) == null
               && read($Heap, this, _module.Node.right) != null
             ==> Set#Equal(read($Heap, this, _module.Node.Contents), 
              Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.data))), 
                read($Heap, read($Heap, this, _module.Node.right), _module.Node.Contents)))))
        {
            b$reqreads#44 := $_Frame[this, _module.Node.left];
            if (read($Heap, this, _module.Node.left) != null)
            {
                b$reqreads#45 := $_Frame[this, _module.Node.right];
            }

            if (read($Heap, this, _module.Node.left) != null
               && read($Heap, this, _module.Node.right) != null)
            {
                b$reqreads#46 := $_Frame[this, _module.Node.left];
                assert read($Heap, this, _module.Node.left) != null;
                b$reqreads#47 := $_Frame[read($Heap, this, _module.Node.left), _module.Node.Repr];
                b$reqreads#48 := $_Frame[this, _module.Node.right];
                assert read($Heap, this, _module.Node.right) != null;
                b$reqreads#49 := $_Frame[read($Heap, this, _module.Node.right), _module.Node.Repr];
                if (Set#Disjoint(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr), 
                  read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr)))
                {
                    b$reqreads#50 := $_Frame[this, _module.Node.Contents];
                    b$reqreads#51 := $_Frame[this, _module.Node.left];
                    assert read($Heap, this, _module.Node.left) != null;
                    b$reqreads#52 := $_Frame[read($Heap, this, _module.Node.left), _module.Node.Contents];
                    b$reqreads#53 := $_Frame[this, _module.Node.data];
                    b$reqreads#54 := $_Frame[this, _module.Node.right];
                    assert read($Heap, this, _module.Node.right) != null;
                    b$reqreads#55 := $_Frame[read($Heap, this, _module.Node.right), _module.Node.Contents];
                }
            }
        }

        assume _module.Node.Valid($LS($LZ), $Heap, this)
           == (
            read($Heap, this, _module.Node.Repr)[$Box(this)]
             && (read($Heap, this, _module.Node.left) != null
               ==> read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.left))]
                 && Set#Subset(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr), 
                  read($Heap, this, _module.Node.Repr))
                 && !read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr)[$Box(this)]
                 && _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.left))
                 && (forall y#4: int :: 
                  { read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents)[$Box(y#4)] } 
                  true
                     ==> 
                    read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents)[$Box(y#4)]
                     ==> y#4 < read($Heap, this, _module.Node.data)))
             && (read($Heap, this, _module.Node.right) != null
               ==> read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.right))]
                 && Set#Subset(read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr), 
                  read($Heap, this, _module.Node.Repr))
                 && !read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr)[$Box(this)]
                 && _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.right))
                 && (forall y#5: int :: 
                  { read($Heap, read($Heap, this, _module.Node.right), _module.Node.Contents)[$Box(y#5)] } 
                  true
                     ==> 
                    read($Heap, read($Heap, this, _module.Node.right), _module.Node.Contents)[$Box(y#5)]
                     ==> read($Heap, this, _module.Node.data) < y#5))
             && (read($Heap, this, _module.Node.left) == null
                 && read($Heap, this, _module.Node.right) == null
               ==> Set#Equal(read($Heap, this, _module.Node.Contents), 
                Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.data)))))
             && (read($Heap, this, _module.Node.left) != null
                 && read($Heap, this, _module.Node.right) == null
               ==> Set#Equal(read($Heap, this, _module.Node.Contents), 
                Set#Union(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents), 
                  Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.data))))))
             && (read($Heap, this, _module.Node.left) == null
                 && read($Heap, this, _module.Node.right) != null
               ==> Set#Equal(read($Heap, this, _module.Node.Contents), 
                Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.data))), 
                  read($Heap, read($Heap, this, _module.Node.right), _module.Node.Contents))))
             && (read($Heap, this, _module.Node.left) != null
                 && read($Heap, this, _module.Node.right) != null
               ==> Set#Disjoint(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr), 
                  read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr))
                 && Set#Equal(read($Heap, this, _module.Node.Contents), 
                  Set#Union(Set#Union(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents), 
                      Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.data)))), 
                    read($Heap, read($Heap, this, _module.Node.right), _module.Node.Contents)))));
        assume read($Heap, this, _module.Node.Repr)[$Box(this)]
           ==> (read($Heap, this, _module.Node.left) != null
               ==> 
              read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.left))]
               ==> 
              Set#Subset(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr), 
                read($Heap, this, _module.Node.Repr))
               ==> 
              !read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr)[$Box(this)]
               ==> _module.Node.Valid#canCall($Heap, read($Heap, this, _module.Node.left)))
             && (
              (read($Heap, this, _module.Node.left) != null
               ==> read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.left))]
                 && Set#Subset(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr), 
                  read($Heap, this, _module.Node.Repr))
                 && !read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr)[$Box(this)]
                 && _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.left))
                 && (forall y#4: int :: 
                  { read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents)[$Box(y#4)] } 
                  true
                     ==> 
                    read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents)[$Box(y#4)]
                     ==> y#4 < read($Heap, this, _module.Node.data)))
               ==> 
              read($Heap, this, _module.Node.right) != null
               ==> 
              read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.right))]
               ==> 
              Set#Subset(read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr), 
                read($Heap, this, _module.Node.Repr))
               ==> 
              !read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr)[$Box(this)]
               ==> _module.Node.Valid#canCall($Heap, read($Heap, this, _module.Node.right)));
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
        assert b$reqreads#13;
        assert b$reqreads#14;
        assert b$reqreads#15;
        assert b$reqreads#16;
        assert b$reqreads#17;
        assert b$reqreads#18;
        assert b$reqreads#19;
        assert b$reqreads#20;
        assert b$reqreads#21;
        assert b$reqreads#22;
        assert b$reqreads#23;
        assert b$reqreads#24;
        assert b$reqreads#25;
        assert b$reqreads#26;
        assert b$reqreads#27;
        assert b$reqreads#28;
        assert b$reqreads#29;
        assert b$reqreads#30;
        assert b$reqreads#31;
        assert b$reqreads#32;
        assert b$reqreads#33;
        assert b$reqreads#34;
        assert b$reqreads#35;
        assert b$reqreads#36;
        assert b$reqreads#37;
        assert b$reqreads#38;
        assert b$reqreads#39;
        assert b$reqreads#40;
        assert b$reqreads#41;
        assert b$reqreads#42;
        assert b$reqreads#43;
        assert b$reqreads#44;
        assert b$reqreads#45;
        assert b$reqreads#46;
        assert b$reqreads#47;
        assert b$reqreads#48;
        assert b$reqreads#49;
        assert b$reqreads#50;
        assert b$reqreads#51;
        assert b$reqreads#52;
        assert b$reqreads#53;
        assert b$reqreads#54;
        assert b$reqreads#55;
    }
}



procedure CheckWellformed$$_module.Node.Init(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), $Heap), 
    x#0: int);
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Node.Init(x#0: int)
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Node.Valid#canCall($Heap, this);
  free ensures _module.Node.Valid#canCall($Heap, this)
     && 
    _module.Node.Valid($LS($LZ), $Heap, this)
     && 
    read($Heap, this, _module.Node.Repr)[$Box(this)]
     && (read($Heap, this, _module.Node.left) != null
       ==> read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.left))]
         && Set#Subset(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr), 
          read($Heap, this, _module.Node.Repr))
         && !read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr)[$Box(this)]
         && _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.left))
         && (forall y#0: int :: 
          { read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents)[$Box(y#0)] } 
          true
             ==> 
            read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents)[$Box(y#0)]
             ==> y#0 < read($Heap, this, _module.Node.data)))
     && (read($Heap, this, _module.Node.right) != null
       ==> read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.right))]
         && Set#Subset(read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr), 
          read($Heap, this, _module.Node.Repr))
         && !read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr)[$Box(this)]
         && _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.right))
         && (forall y#1: int :: 
          { read($Heap, read($Heap, this, _module.Node.right), _module.Node.Contents)[$Box(y#1)] } 
          true
             ==> 
            read($Heap, read($Heap, this, _module.Node.right), _module.Node.Contents)[$Box(y#1)]
             ==> read($Heap, this, _module.Node.data) < y#1))
     && (read($Heap, this, _module.Node.left) == null
         && read($Heap, this, _module.Node.right) == null
       ==> Set#Equal(read($Heap, this, _module.Node.Contents), 
        Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.data)))))
     && (read($Heap, this, _module.Node.left) != null
         && read($Heap, this, _module.Node.right) == null
       ==> Set#Equal(read($Heap, this, _module.Node.Contents), 
        Set#Union(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents), 
          Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.data))))))
     && (read($Heap, this, _module.Node.left) == null
         && read($Heap, this, _module.Node.right) != null
       ==> Set#Equal(read($Heap, this, _module.Node.Contents), 
        Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.data))), 
          read($Heap, read($Heap, this, _module.Node.right), _module.Node.Contents))))
     && (read($Heap, this, _module.Node.left) != null
         && read($Heap, this, _module.Node.right) != null
       ==> Set#Disjoint(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr), 
          read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr))
         && Set#Equal(read($Heap, this, _module.Node.Contents), 
          Set#Union(Set#Union(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents), 
              Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.data)))), 
            read($Heap, read($Heap, this, _module.Node.right), _module.Node.Contents))));
  ensures (forall $o: ref :: 
    { read($Heap, this, _module.Node.Repr)[$Box($o)] } 
    read($Heap, this, _module.Node.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures Set#Equal(read($Heap, this, _module.Node.Contents), 
    Set#UnionOne(Set#Empty(): Set Box, $Box(x#0)));
  // constructor allocates the object
  ensures !read(old($Heap), this, alloc);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Node.Init(x#0: int)
   returns (this: ref where this != null && $Is(this, Tclass._module.Node()), 
    $_reverifyPost: bool);
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.Node.Valid#canCall($Heap, this);
  ensures _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || read($Heap, this, _module.Node.Repr)[$Box(this)];
  ensures _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.left) != null
         ==> read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.left))]);
  ensures _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.left) != null
         ==> Set#Subset(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr), 
          read($Heap, this, _module.Node.Repr)));
  ensures _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.left) != null
         ==> !read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr)[$Box(this)]);
  ensures _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.left) != null
         ==> _module.Node.Valid($LS($LS($LZ)), $Heap, read($Heap, this, _module.Node.left)));
  ensures _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.left) != null
         ==> (forall y#2: int :: 
          { read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents)[$Box(y#2)] } 
          true
             ==> 
            read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents)[$Box(y#2)]
             ==> y#2 < read($Heap, this, _module.Node.data)));
  ensures _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.right) != null
         ==> read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.right))]);
  ensures _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.right) != null
         ==> Set#Subset(read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr), 
          read($Heap, this, _module.Node.Repr)));
  ensures _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.right) != null
         ==> !read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr)[$Box(this)]);
  ensures _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.right) != null
         ==> _module.Node.Valid($LS($LS($LZ)), $Heap, read($Heap, this, _module.Node.right)));
  ensures _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.right) != null
         ==> (forall y#3: int :: 
          { read($Heap, read($Heap, this, _module.Node.right), _module.Node.Contents)[$Box(y#3)] } 
          true
             ==> 
            read($Heap, read($Heap, this, _module.Node.right), _module.Node.Contents)[$Box(y#3)]
             ==> read($Heap, this, _module.Node.data) < y#3));
  ensures _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.left) == null
           && read($Heap, this, _module.Node.right) == null
         ==> Set#Equal(read($Heap, this, _module.Node.Contents), 
          Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.data)))));
  ensures _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.left) != null
           && read($Heap, this, _module.Node.right) == null
         ==> Set#Equal(read($Heap, this, _module.Node.Contents), 
          Set#Union(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents), 
            Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.data))))));
  ensures _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.left) == null
           && read($Heap, this, _module.Node.right) != null
         ==> Set#Equal(read($Heap, this, _module.Node.Contents), 
          Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.data))), 
            read($Heap, read($Heap, this, _module.Node.right), _module.Node.Contents))));
  ensures _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.left) != null
           && read($Heap, this, _module.Node.right) != null
         ==> Set#Disjoint(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr), 
          read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr)));
  ensures _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.left) != null
           && read($Heap, this, _module.Node.right) != null
         ==> Set#Equal(read($Heap, this, _module.Node.Contents), 
          Set#Union(Set#Union(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents), 
              Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.data)))), 
            read($Heap, read($Heap, this, _module.Node.right), _module.Node.Contents))));
  ensures (forall $o: ref :: 
    { read($Heap, this, _module.Node.Repr)[$Box($o)] } 
    read($Heap, this, _module.Node.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures Set#Equal(read($Heap, this, _module.Node.Contents), 
    Set#UnionOne(Set#Empty(): Set Box, $Box(x#0)));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Node.Init(x#0: int) returns (this: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var this.Contents: Set Box;
  var this.Repr: Set Box;
  var this.data: int;
  var this.left: ref;
  var this.right: ref;

    // AddMethodImpl: Init, Impl$$_module.Node.Init
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(138,2): initial state"} true;
    $_reverifyPost := false;
    // ----- divided block before new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(138,3)
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(139,10)
    assume true;
    assume true;
    this.data := x#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(139,13)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(140,10)
    assume true;
    assume true;
    this.left := null;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(140,16)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(141,11)
    assume true;
    assume true;
    this.right := null;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(141,17)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(142,14)
    assume true;
    assume true;
    this.Contents := Set#UnionOne(Set#Empty(): Set Box, $Box(x#0));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(142,19)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(143,10)
    assume true;
    assume true;
    assert $Is(Set#UnionOne(Set#Empty(): Set Box, $Box(this)), TSet(Tclass._System.object()));
    this.Repr := Set#UnionOne(Set#Empty(): Set Box, $Box(this));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(143,18)"} true;
    // ----- new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(138,3)
    assume !read($Heap, this, alloc);
    assume read($Heap, this, _module.Node.Contents) == this.Contents;
    assume read($Heap, this, _module.Node.Repr) == this.Repr;
    assume read($Heap, this, _module.Node.data) == this.data;
    assume read($Heap, this, _module.Node.left) == this.left;
    assume read($Heap, this, _module.Node.right) == this.right;
    $Heap := update($Heap, this, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    // ----- divided block after new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(138,3)
}



// function declaration for _module.Node.Find
function _module.Node.Find($ly: LayerType, $heap: Heap, this: ref, x#0: int) : bool;

function _module.Node.Find#canCall($heap: Heap, this: ref, x#0: int) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, $Heap: Heap, this: ref, x#0: int :: 
  { _module.Node.Find($LS($ly), $Heap, this, x#0) } 
  _module.Node.Find($LS($ly), $Heap, this, x#0)
     == _module.Node.Find($ly, $Heap, this, x#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, $Heap: Heap, this: ref, x#0: int :: 
  { _module.Node.Find(AsFuelBottom($ly), $Heap, this, x#0) } 
  _module.Node.Find($ly, $Heap, this, x#0)
     == _module.Node.Find($LZ, $Heap, this, x#0));

// frame axiom for _module.Node.Find
axiom (forall $ly: LayerType, $h0: Heap, $h1: Heap, this: ref, x#0: int :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.Node.Find($ly, $h1, this, x#0) } 
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
      $o != null && read($h0, this, _module.Node.Repr)[$Box($o)]
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.Node.Find($ly, $h0, this, x#0) == _module.Node.Find($ly, $h1, this, x#0));

// consequence axiom for _module.Node.Find
axiom 9 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, this: ref, x#0: int :: 
    { _module.Node.Find($ly, $Heap, this, x#0) } 
    _module.Node.Find#canCall($Heap, this, x#0)
         || (9 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.Node())
           && $IsAlloc(this, Tclass._module.Node(), $Heap)
           && _module.Node.Valid($LS($LZ), $Heap, this))
       ==> (_module.Node.Find($ly, $Heap, this, x#0)
         <==> read($Heap, this, _module.Node.Contents)[$Box(x#0)]));

function _module.Node.Find#requires(LayerType, Heap, ref, int) : bool;

// #requires axiom for _module.Node.Find
axiom (forall $ly: LayerType, $Heap: Heap, this: ref, x#0: int :: 
  { _module.Node.Find#requires($ly, $Heap, this, x#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.Node())
       && $IsAlloc(this, Tclass._module.Node(), $Heap)
     ==> _module.Node.Find#requires($ly, $Heap, this, x#0)
       == _module.Node.Valid($LS($LZ), $Heap, this));

// definition axiom for _module.Node.Find (revealed)
axiom 9 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, this: ref, x#0: int :: 
    { _module.Node.Find($LS($ly), $Heap, this, x#0), $IsGoodHeap($Heap) } 
    _module.Node.Find#canCall($Heap, this, x#0)
         || (9 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.Node())
           && $IsAlloc(this, Tclass._module.Node(), $Heap)
           && _module.Node.Valid($LS($LZ), $Heap, this))
       ==> (x#0 != read($Heap, this, _module.Node.data)
           ==> (read($Heap, this, _module.Node.left) != null
                 && x#0 < read($Heap, this, _module.Node.data)
               ==> _module.Node.Find#canCall($Heap, read($Heap, this, _module.Node.left), x#0))
             && (!(read($Heap, this, _module.Node.left) != null
                 && x#0 < read($Heap, this, _module.Node.data))
               ==> 
              read($Heap, this, _module.Node.right) != null
                 && read($Heap, this, _module.Node.data) < x#0
               ==> _module.Node.Find#canCall($Heap, read($Heap, this, _module.Node.right), x#0)))
         && _module.Node.Find($LS($ly), $Heap, this, x#0)
           == (if x#0 == read($Heap, this, _module.Node.data)
             then true
             else (if read($Heap, this, _module.Node.left) != null
                 && x#0 < read($Heap, this, _module.Node.data)
               then _module.Node.Find($ly, $Heap, read($Heap, this, _module.Node.left), x#0)
               else (if read($Heap, this, _module.Node.right) != null
                   && read($Heap, this, _module.Node.data) < x#0
                 then _module.Node.Find($ly, $Heap, read($Heap, this, _module.Node.right), x#0)
                 else false))));

procedure CheckWellformed$$_module.Node.Find(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), $Heap), 
    x#0: int);
  free requires 9 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures _module.Node.Find($LS($LS($LZ)), $Heap, this, x#0)
     <==> read($Heap, this, _module.Node.Contents)[$Box(x#0)];



implementation CheckWellformed$$_module.Node.Find(this: ref, x#0: int)
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
  var b$reqreads#9: bool;
  var b$reqreads#10: bool;

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

    // AddWellformednessCheck for function Find
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(146,18): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.Node.Repr)[$Box($o)]);
    b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && read($Heap, $o, alloc)
           && ($o == this || read($Heap, this, _module.Node.Repr)[$Box($o)])
         ==> $_Frame[$o, $f]);
    assume _module.Node.Valid#canCall($Heap, this);
    assume _module.Node.Valid($LS($LZ), $Heap, this);
    assert b$reqreads#0;
    b$reqreads#1 := $_Frame[this, _module.Node.Repr];
    assert b$reqreads#1;
    if (*)
    {
        ##x#0 := x#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##x#0, TInt, $Heap);
        assert {:subsumption 0} _module.Node.Valid#canCall($Heap, this)
           ==> _module.Node.Valid($LS($LZ), $Heap, this)
             || read($Heap, this, _module.Node.Repr)[$Box(this)];
        assert {:subsumption 0} _module.Node.Valid#canCall($Heap, this)
           ==> _module.Node.Valid($LS($LZ), $Heap, this)
             || (read($Heap, this, _module.Node.left) != null
               ==> read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.left))]);
        assert {:subsumption 0} _module.Node.Valid#canCall($Heap, this)
           ==> _module.Node.Valid($LS($LZ), $Heap, this)
             || (read($Heap, this, _module.Node.left) != null
               ==> Set#Subset(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr), 
                read($Heap, this, _module.Node.Repr)));
        assert {:subsumption 0} _module.Node.Valid#canCall($Heap, this)
           ==> _module.Node.Valid($LS($LZ), $Heap, this)
             || (read($Heap, this, _module.Node.left) != null
               ==> !read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr)[$Box(this)]);
        assert {:subsumption 0} _module.Node.Valid#canCall($Heap, this)
           ==> _module.Node.Valid($LS($LZ), $Heap, this)
             || (read($Heap, this, _module.Node.left) != null
               ==> _module.Node.Valid($LS($LS($LZ)), $Heap, read($Heap, this, _module.Node.left)));
        assert {:subsumption 0} _module.Node.Valid#canCall($Heap, this)
           ==> _module.Node.Valid($LS($LZ), $Heap, this)
             || (read($Heap, this, _module.Node.left) != null
               ==> (forall y#0: int :: 
                { read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents)[$Box(y#0)] } 
                true
                   ==> 
                  read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents)[$Box(y#0)]
                   ==> y#0 < read($Heap, this, _module.Node.data)));
        assert {:subsumption 0} _module.Node.Valid#canCall($Heap, this)
           ==> _module.Node.Valid($LS($LZ), $Heap, this)
             || (read($Heap, this, _module.Node.right) != null
               ==> read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.right))]);
        assert {:subsumption 0} _module.Node.Valid#canCall($Heap, this)
           ==> _module.Node.Valid($LS($LZ), $Heap, this)
             || (read($Heap, this, _module.Node.right) != null
               ==> Set#Subset(read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr), 
                read($Heap, this, _module.Node.Repr)));
        assert {:subsumption 0} _module.Node.Valid#canCall($Heap, this)
           ==> _module.Node.Valid($LS($LZ), $Heap, this)
             || (read($Heap, this, _module.Node.right) != null
               ==> !read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr)[$Box(this)]);
        assert {:subsumption 0} _module.Node.Valid#canCall($Heap, this)
           ==> _module.Node.Valid($LS($LZ), $Heap, this)
             || (read($Heap, this, _module.Node.right) != null
               ==> _module.Node.Valid($LS($LS($LZ)), $Heap, read($Heap, this, _module.Node.right)));
        assert {:subsumption 0} _module.Node.Valid#canCall($Heap, this)
           ==> _module.Node.Valid($LS($LZ), $Heap, this)
             || (read($Heap, this, _module.Node.right) != null
               ==> (forall y#1: int :: 
                { read($Heap, read($Heap, this, _module.Node.right), _module.Node.Contents)[$Box(y#1)] } 
                true
                   ==> 
                  read($Heap, read($Heap, this, _module.Node.right), _module.Node.Contents)[$Box(y#1)]
                   ==> read($Heap, this, _module.Node.data) < y#1));
        assert {:subsumption 0} _module.Node.Valid#canCall($Heap, this)
           ==> _module.Node.Valid($LS($LZ), $Heap, this)
             || (read($Heap, this, _module.Node.left) == null
                 && read($Heap, this, _module.Node.right) == null
               ==> Set#Equal(read($Heap, this, _module.Node.Contents), 
                Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.data)))));
        assert {:subsumption 0} _module.Node.Valid#canCall($Heap, this)
           ==> _module.Node.Valid($LS($LZ), $Heap, this)
             || (read($Heap, this, _module.Node.left) != null
                 && read($Heap, this, _module.Node.right) == null
               ==> Set#Equal(read($Heap, this, _module.Node.Contents), 
                Set#Union(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents), 
                  Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.data))))));
        assert {:subsumption 0} _module.Node.Valid#canCall($Heap, this)
           ==> _module.Node.Valid($LS($LZ), $Heap, this)
             || (read($Heap, this, _module.Node.left) == null
                 && read($Heap, this, _module.Node.right) != null
               ==> Set#Equal(read($Heap, this, _module.Node.Contents), 
                Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.data))), 
                  read($Heap, read($Heap, this, _module.Node.right), _module.Node.Contents))));
        assert {:subsumption 0} _module.Node.Valid#canCall($Heap, this)
           ==> _module.Node.Valid($LS($LZ), $Heap, this)
             || (read($Heap, this, _module.Node.left) != null
                 && read($Heap, this, _module.Node.right) != null
               ==> Set#Disjoint(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr), 
                read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr)));
        assert {:subsumption 0} _module.Node.Valid#canCall($Heap, this)
           ==> _module.Node.Valid($LS($LZ), $Heap, this)
             || (read($Heap, this, _module.Node.left) != null
                 && read($Heap, this, _module.Node.right) != null
               ==> Set#Equal(read($Heap, this, _module.Node.Contents), 
                Set#Union(Set#Union(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents), 
                    Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.data)))), 
                  read($Heap, read($Heap, this, _module.Node.right), _module.Node.Contents))));
        assume _module.Node.Valid($LS($LZ), $Heap, this);
        assert (this == this && x#0 == x#0)
           || (Set#Subset(read($Heap, this, _module.Node.Repr), read($Heap, this, _module.Node.Repr))
             && !Set#Subset(read($Heap, this, _module.Node.Repr), read($Heap, this, _module.Node.Repr)));
        assume (this == this && x#0 == x#0) || _module.Node.Find#canCall($Heap, this, x#0);
        assume _module.Node.Find($LS($LZ), $Heap, this, x#0)
           <==> read($Heap, this, _module.Node.Contents)[$Box(x#0)];
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc)
             ==> read($Heap, this, _module.Node.Repr)[$Box($o)]);
        b$reqreads#2 := $_Frame[this, _module.Node.data];
        if (x#0 == read($Heap, this, _module.Node.data))
        {
            assume _module.Node.Find($LS($LZ), $Heap, this, x#0) == Lit(true);
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.Node.Find($LS($LZ), $Heap, this, x#0), TBool);
        }
        else
        {
            b$reqreads#3 := $_Frame[this, _module.Node.left];
            if (read($Heap, this, _module.Node.left) != null)
            {
                b$reqreads#4 := $_Frame[this, _module.Node.data];
            }

            if (read($Heap, this, _module.Node.left) != null
               && x#0 < read($Heap, this, _module.Node.data))
            {
                b$reqreads#5 := $_Frame[this, _module.Node.left];
                assert read($Heap, this, _module.Node.left) != null;
                ##x#1 := x#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##x#1, TInt, $Heap);
                assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.Node.left))
                   ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.left))
                     || read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr)[$Box(read($Heap, this, _module.Node.left))];
                assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.Node.left))
                   ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.left))
                     || (read($Heap, read($Heap, this, _module.Node.left), _module.Node.left) != null
                       ==> read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr)[$Box(read($Heap, read($Heap, this, _module.Node.left), _module.Node.left))]);
                assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.Node.left))
                   ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.left))
                     || (read($Heap, read($Heap, this, _module.Node.left), _module.Node.left) != null
                       ==> Set#Subset(read($Heap, 
                          read($Heap, read($Heap, this, _module.Node.left), _module.Node.left), 
                          _module.Node.Repr), 
                        read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr)));
                assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.Node.left))
                   ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.left))
                     || (read($Heap, read($Heap, this, _module.Node.left), _module.Node.left) != null
                       ==> !read($Heap, 
                        read($Heap, read($Heap, this, _module.Node.left), _module.Node.left), 
                        _module.Node.Repr)[$Box(read($Heap, this, _module.Node.left))]);
                assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.Node.left))
                   ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.left))
                     || (read($Heap, read($Heap, this, _module.Node.left), _module.Node.left) != null
                       ==> _module.Node.Valid($LS($LS($LZ)), 
                        $Heap, 
                        read($Heap, read($Heap, this, _module.Node.left), _module.Node.left)));
                assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.Node.left))
                   ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.left))
                     || (read($Heap, read($Heap, this, _module.Node.left), _module.Node.left) != null
                       ==> (forall y#2: int :: 
                        { read($Heap, 
                            read($Heap, read($Heap, this, _module.Node.left), _module.Node.left), 
                            _module.Node.Contents)[$Box(y#2)] } 
                        true
                           ==> 
                          read($Heap, 
                            read($Heap, read($Heap, this, _module.Node.left), _module.Node.left), 
                            _module.Node.Contents)[$Box(y#2)]
                           ==> y#2 < read($Heap, read($Heap, this, _module.Node.left), _module.Node.data)));
                assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.Node.left))
                   ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.left))
                     || (read($Heap, read($Heap, this, _module.Node.left), _module.Node.right) != null
                       ==> read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr)[$Box(read($Heap, read($Heap, this, _module.Node.left), _module.Node.right))]);
                assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.Node.left))
                   ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.left))
                     || (read($Heap, read($Heap, this, _module.Node.left), _module.Node.right) != null
                       ==> Set#Subset(read($Heap, 
                          read($Heap, read($Heap, this, _module.Node.left), _module.Node.right), 
                          _module.Node.Repr), 
                        read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr)));
                assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.Node.left))
                   ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.left))
                     || (read($Heap, read($Heap, this, _module.Node.left), _module.Node.right) != null
                       ==> !read($Heap, 
                        read($Heap, read($Heap, this, _module.Node.left), _module.Node.right), 
                        _module.Node.Repr)[$Box(read($Heap, this, _module.Node.left))]);
                assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.Node.left))
                   ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.left))
                     || (read($Heap, read($Heap, this, _module.Node.left), _module.Node.right) != null
                       ==> _module.Node.Valid($LS($LS($LZ)), 
                        $Heap, 
                        read($Heap, read($Heap, this, _module.Node.left), _module.Node.right)));
                assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.Node.left))
                   ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.left))
                     || (read($Heap, read($Heap, this, _module.Node.left), _module.Node.right) != null
                       ==> (forall y#3: int :: 
                        { read($Heap, 
                            read($Heap, read($Heap, this, _module.Node.left), _module.Node.right), 
                            _module.Node.Contents)[$Box(y#3)] } 
                        true
                           ==> 
                          read($Heap, 
                            read($Heap, read($Heap, this, _module.Node.left), _module.Node.right), 
                            _module.Node.Contents)[$Box(y#3)]
                           ==> read($Heap, read($Heap, this, _module.Node.left), _module.Node.data) < y#3));
                assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.Node.left))
                   ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.left))
                     || (read($Heap, read($Heap, this, _module.Node.left), _module.Node.left) == null
                         && read($Heap, read($Heap, this, _module.Node.left), _module.Node.right) == null
                       ==> Set#Equal(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents), 
                        Set#UnionOne(Set#Empty(): Set Box, 
                          $Box(read($Heap, read($Heap, this, _module.Node.left), _module.Node.data)))));
                assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.Node.left))
                   ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.left))
                     || (read($Heap, read($Heap, this, _module.Node.left), _module.Node.left) != null
                         && read($Heap, read($Heap, this, _module.Node.left), _module.Node.right) == null
                       ==> Set#Equal(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents), 
                        Set#Union(read($Heap, 
                            read($Heap, read($Heap, this, _module.Node.left), _module.Node.left), 
                            _module.Node.Contents), 
                          Set#UnionOne(Set#Empty(): Set Box, 
                            $Box(read($Heap, read($Heap, this, _module.Node.left), _module.Node.data))))));
                assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.Node.left))
                   ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.left))
                     || (read($Heap, read($Heap, this, _module.Node.left), _module.Node.left) == null
                         && read($Heap, read($Heap, this, _module.Node.left), _module.Node.right) != null
                       ==> Set#Equal(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents), 
                        Set#Union(Set#UnionOne(Set#Empty(): Set Box, 
                            $Box(read($Heap, read($Heap, this, _module.Node.left), _module.Node.data))), 
                          read($Heap, 
                            read($Heap, read($Heap, this, _module.Node.left), _module.Node.right), 
                            _module.Node.Contents))));
                assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.Node.left))
                   ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.left))
                     || (read($Heap, read($Heap, this, _module.Node.left), _module.Node.left) != null
                         && read($Heap, read($Heap, this, _module.Node.left), _module.Node.right) != null
                       ==> Set#Disjoint(read($Heap, 
                          read($Heap, read($Heap, this, _module.Node.left), _module.Node.left), 
                          _module.Node.Repr), 
                        read($Heap, 
                          read($Heap, read($Heap, this, _module.Node.left), _module.Node.right), 
                          _module.Node.Repr)));
                assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.Node.left))
                   ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.left))
                     || (read($Heap, read($Heap, this, _module.Node.left), _module.Node.left) != null
                         && read($Heap, read($Heap, this, _module.Node.left), _module.Node.right) != null
                       ==> Set#Equal(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents), 
                        Set#Union(Set#Union(read($Heap, 
                              read($Heap, read($Heap, this, _module.Node.left), _module.Node.left), 
                              _module.Node.Contents), 
                            Set#UnionOne(Set#Empty(): Set Box, 
                              $Box(read($Heap, read($Heap, this, _module.Node.left), _module.Node.data)))), 
                          read($Heap, 
                            read($Heap, read($Heap, this, _module.Node.left), _module.Node.right), 
                            _module.Node.Contents))));
                assume _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.left));
                b$reqreads#6 := (forall<alpha> $o: ref, $f: Field alpha :: 
                  $o != null
                       && read($Heap, $o, alloc)
                       && read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr)[$Box($o)]
                     ==> $_Frame[$o, $f]);
                assert Set#Subset(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr), 
                    read($Heap, this, _module.Node.Repr))
                   && !Set#Subset(read($Heap, this, _module.Node.Repr), 
                    read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr));
                assume _module.Node.Find#canCall($Heap, read($Heap, this, _module.Node.left), x#0);
                assume _module.Node.Find($LS($LZ), $Heap, this, x#0)
                   == _module.Node.Find($LS($LZ), $Heap, read($Heap, this, _module.Node.left), x#0);
                assume _module.Node.Find#canCall($Heap, read($Heap, this, _module.Node.left), x#0);
                // CheckWellformedWithResult: any expression
                assume $Is(_module.Node.Find($LS($LZ), $Heap, this, x#0), TBool);
            }
            else
            {
                b$reqreads#7 := $_Frame[this, _module.Node.right];
                if (read($Heap, this, _module.Node.right) != null)
                {
                    b$reqreads#8 := $_Frame[this, _module.Node.data];
                }

                if (read($Heap, this, _module.Node.right) != null
                   && read($Heap, this, _module.Node.data) < x#0)
                {
                    b$reqreads#9 := $_Frame[this, _module.Node.right];
                    assert read($Heap, this, _module.Node.right) != null;
                    ##x#2 := x#0;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##x#2, TInt, $Heap);
                    assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.Node.right))
                       ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.right))
                         || read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr)[$Box(read($Heap, this, _module.Node.right))];
                    assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.Node.right))
                       ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.right))
                         || (read($Heap, read($Heap, this, _module.Node.right), _module.Node.left) != null
                           ==> read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr)[$Box(read($Heap, read($Heap, this, _module.Node.right), _module.Node.left))]);
                    assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.Node.right))
                       ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.right))
                         || (read($Heap, read($Heap, this, _module.Node.right), _module.Node.left) != null
                           ==> Set#Subset(read($Heap, 
                              read($Heap, read($Heap, this, _module.Node.right), _module.Node.left), 
                              _module.Node.Repr), 
                            read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr)));
                    assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.Node.right))
                       ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.right))
                         || (read($Heap, read($Heap, this, _module.Node.right), _module.Node.left) != null
                           ==> !read($Heap, 
                            read($Heap, read($Heap, this, _module.Node.right), _module.Node.left), 
                            _module.Node.Repr)[$Box(read($Heap, this, _module.Node.right))]);
                    assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.Node.right))
                       ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.right))
                         || (read($Heap, read($Heap, this, _module.Node.right), _module.Node.left) != null
                           ==> _module.Node.Valid($LS($LS($LZ)), 
                            $Heap, 
                            read($Heap, read($Heap, this, _module.Node.right), _module.Node.left)));
                    assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.Node.right))
                       ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.right))
                         || (read($Heap, read($Heap, this, _module.Node.right), _module.Node.left) != null
                           ==> (forall y#4: int :: 
                            { read($Heap, 
                                read($Heap, read($Heap, this, _module.Node.right), _module.Node.left), 
                                _module.Node.Contents)[$Box(y#4)] } 
                            true
                               ==> 
                              read($Heap, 
                                read($Heap, read($Heap, this, _module.Node.right), _module.Node.left), 
                                _module.Node.Contents)[$Box(y#4)]
                               ==> y#4 < read($Heap, read($Heap, this, _module.Node.right), _module.Node.data)));
                    assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.Node.right))
                       ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.right))
                         || (read($Heap, read($Heap, this, _module.Node.right), _module.Node.right) != null
                           ==> read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr)[$Box(read($Heap, read($Heap, this, _module.Node.right), _module.Node.right))]);
                    assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.Node.right))
                       ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.right))
                         || (read($Heap, read($Heap, this, _module.Node.right), _module.Node.right) != null
                           ==> Set#Subset(read($Heap, 
                              read($Heap, read($Heap, this, _module.Node.right), _module.Node.right), 
                              _module.Node.Repr), 
                            read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr)));
                    assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.Node.right))
                       ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.right))
                         || (read($Heap, read($Heap, this, _module.Node.right), _module.Node.right) != null
                           ==> !read($Heap, 
                            read($Heap, read($Heap, this, _module.Node.right), _module.Node.right), 
                            _module.Node.Repr)[$Box(read($Heap, this, _module.Node.right))]);
                    assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.Node.right))
                       ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.right))
                         || (read($Heap, read($Heap, this, _module.Node.right), _module.Node.right) != null
                           ==> _module.Node.Valid($LS($LS($LZ)), 
                            $Heap, 
                            read($Heap, read($Heap, this, _module.Node.right), _module.Node.right)));
                    assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.Node.right))
                       ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.right))
                         || (read($Heap, read($Heap, this, _module.Node.right), _module.Node.right) != null
                           ==> (forall y#5: int :: 
                            { read($Heap, 
                                read($Heap, read($Heap, this, _module.Node.right), _module.Node.right), 
                                _module.Node.Contents)[$Box(y#5)] } 
                            true
                               ==> 
                              read($Heap, 
                                read($Heap, read($Heap, this, _module.Node.right), _module.Node.right), 
                                _module.Node.Contents)[$Box(y#5)]
                               ==> read($Heap, read($Heap, this, _module.Node.right), _module.Node.data) < y#5));
                    assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.Node.right))
                       ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.right))
                         || (read($Heap, read($Heap, this, _module.Node.right), _module.Node.left) == null
                             && read($Heap, read($Heap, this, _module.Node.right), _module.Node.right) == null
                           ==> Set#Equal(read($Heap, read($Heap, this, _module.Node.right), _module.Node.Contents), 
                            Set#UnionOne(Set#Empty(): Set Box, 
                              $Box(read($Heap, read($Heap, this, _module.Node.right), _module.Node.data)))));
                    assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.Node.right))
                       ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.right))
                         || (read($Heap, read($Heap, this, _module.Node.right), _module.Node.left) != null
                             && read($Heap, read($Heap, this, _module.Node.right), _module.Node.right) == null
                           ==> Set#Equal(read($Heap, read($Heap, this, _module.Node.right), _module.Node.Contents), 
                            Set#Union(read($Heap, 
                                read($Heap, read($Heap, this, _module.Node.right), _module.Node.left), 
                                _module.Node.Contents), 
                              Set#UnionOne(Set#Empty(): Set Box, 
                                $Box(read($Heap, read($Heap, this, _module.Node.right), _module.Node.data))))));
                    assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.Node.right))
                       ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.right))
                         || (read($Heap, read($Heap, this, _module.Node.right), _module.Node.left) == null
                             && read($Heap, read($Heap, this, _module.Node.right), _module.Node.right) != null
                           ==> Set#Equal(read($Heap, read($Heap, this, _module.Node.right), _module.Node.Contents), 
                            Set#Union(Set#UnionOne(Set#Empty(): Set Box, 
                                $Box(read($Heap, read($Heap, this, _module.Node.right), _module.Node.data))), 
                              read($Heap, 
                                read($Heap, read($Heap, this, _module.Node.right), _module.Node.right), 
                                _module.Node.Contents))));
                    assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.Node.right))
                       ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.right))
                         || (read($Heap, read($Heap, this, _module.Node.right), _module.Node.left) != null
                             && read($Heap, read($Heap, this, _module.Node.right), _module.Node.right) != null
                           ==> Set#Disjoint(read($Heap, 
                              read($Heap, read($Heap, this, _module.Node.right), _module.Node.left), 
                              _module.Node.Repr), 
                            read($Heap, 
                              read($Heap, read($Heap, this, _module.Node.right), _module.Node.right), 
                              _module.Node.Repr)));
                    assert {:subsumption 0} _module.Node.Valid#canCall($Heap, read($Heap, this, _module.Node.right))
                       ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.right))
                         || (read($Heap, read($Heap, this, _module.Node.right), _module.Node.left) != null
                             && read($Heap, read($Heap, this, _module.Node.right), _module.Node.right) != null
                           ==> Set#Equal(read($Heap, read($Heap, this, _module.Node.right), _module.Node.Contents), 
                            Set#Union(Set#Union(read($Heap, 
                                  read($Heap, read($Heap, this, _module.Node.right), _module.Node.left), 
                                  _module.Node.Contents), 
                                Set#UnionOne(Set#Empty(): Set Box, 
                                  $Box(read($Heap, read($Heap, this, _module.Node.right), _module.Node.data)))), 
                              read($Heap, 
                                read($Heap, read($Heap, this, _module.Node.right), _module.Node.right), 
                                _module.Node.Contents))));
                    assume _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.right));
                    b$reqreads#10 := (forall<alpha> $o: ref, $f: Field alpha :: 
                      $o != null
                           && read($Heap, $o, alloc)
                           && read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr)[$Box($o)]
                         ==> $_Frame[$o, $f]);
                    assert Set#Subset(read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr), 
                        read($Heap, this, _module.Node.Repr))
                       && !Set#Subset(read($Heap, this, _module.Node.Repr), 
                        read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr));
                    assume _module.Node.Find#canCall($Heap, read($Heap, this, _module.Node.right), x#0);
                    assume _module.Node.Find($LS($LZ), $Heap, this, x#0)
                       == _module.Node.Find($LS($LZ), $Heap, read($Heap, this, _module.Node.right), x#0);
                    assume _module.Node.Find#canCall($Heap, read($Heap, this, _module.Node.right), x#0);
                    // CheckWellformedWithResult: any expression
                    assume $Is(_module.Node.Find($LS($LZ), $Heap, this, x#0), TBool);
                }
                else
                {
                    assume _module.Node.Find($LS($LZ), $Heap, this, x#0) == Lit(false);
                    assume true;
                    // CheckWellformedWithResult: any expression
                    assume $Is(_module.Node.Find($LS($LZ), $Heap, this, x#0), TBool);
                }
            }
        }

        assert b$reqreads#2;
        assert b$reqreads#3;
        assert b$reqreads#4;
        assert b$reqreads#5;
        assert b$reqreads#6;
        assert b$reqreads#7;
        assert b$reqreads#8;
        assert b$reqreads#9;
        assert b$reqreads#10;
    }
}



procedure CheckWellformed$$_module.Node.Remove(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), $Heap), 
    x#0: int)
   returns (node#0: ref
       where $Is(node#0, Tclass._module.Node?())
         && $IsAlloc(node#0, Tclass._module.Node?(), $Heap));
  free requires 12 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Node.Remove(this: ref, x#0: int) returns (node#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Remove, CheckWellformed$$_module.Node.Remove
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.Node.Repr)[$Box($o)]);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(162,9): initial state"} true;
    assume _module.Node.Valid#canCall($Heap, this);
    assume _module.Node.Valid($LS($LZ), $Heap, this);
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc)
         ==> $Heap[$o] == old($Heap)[$o]
           || read(old($Heap), this, _module.Node.Repr)[$Box($o)]);
    assume $HeapSucc(old($Heap), $Heap);
    havoc node#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(165,12): post-state"} true;
    assert $IsAlloc(this, Tclass._module.Node(), old($Heap));
    assume (forall $o: ref :: 
      { read(old($Heap), $o, alloc) } 
      read($Heap, this, _module.Node.Repr)[$Box($o)]
           && !read(old($Heap), this, _module.Node.Repr)[$Box($o)]
         ==> $o != null && !read(old($Heap), $o, alloc));
    if (*)
    {
        assume node#0 != null;
        assert node#0 != null;
        assume _module.Node.Valid#canCall($Heap, node#0);
        assume _module.Node.Valid($LS($LZ), $Heap, node#0);
    }
    else
    {
        assume node#0 != null ==> _module.Node.Valid($LS($LZ), $Heap, node#0);
    }

    if (*)
    {
        assume node#0 == null;
        assert $IsAlloc(this, Tclass._module.Node(), old($Heap));
        assume Set#Subset(read(old($Heap), this, _module.Node.Contents), 
          Set#UnionOne(Set#Empty(): Set Box, $Box(x#0)));
    }
    else
    {
        assume node#0 == null
           ==> Set#Subset(read(old($Heap), this, _module.Node.Contents), 
            Set#UnionOne(Set#Empty(): Set Box, $Box(x#0)));
    }

    if (*)
    {
        assume node#0 != null;
        assert node#0 != null;
        assume Set#Subset(read($Heap, node#0, _module.Node.Repr), read($Heap, this, _module.Node.Repr));
        assert node#0 != null;
        assert $IsAlloc(this, Tclass._module.Node(), old($Heap));
        assume Set#Equal(read($Heap, node#0, _module.Node.Contents), 
          Set#Difference(read(old($Heap), this, _module.Node.Contents), 
            Set#UnionOne(Set#Empty(): Set Box, $Box(x#0))));
    }
    else
    {
        assume node#0 != null
           ==> Set#Subset(read($Heap, node#0, _module.Node.Repr), read($Heap, this, _module.Node.Repr))
             && Set#Equal(read($Heap, node#0, _module.Node.Contents), 
              Set#Difference(read(old($Heap), this, _module.Node.Contents), 
                Set#UnionOne(Set#Empty(): Set Box, $Box(x#0))));
    }
}



procedure Call$$_module.Node.Remove(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), $Heap), 
    x#0: int)
   returns (node#0: ref
       where $Is(node#0, Tclass._module.Node?())
         && $IsAlloc(node#0, Tclass._module.Node?(), $Heap));
  // user-defined preconditions
  requires _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || read($Heap, this, _module.Node.Repr)[$Box(this)];
  requires _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.left) != null
         ==> read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.left))]);
  requires _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.left) != null
         ==> Set#Subset(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr), 
          read($Heap, this, _module.Node.Repr)));
  requires _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.left) != null
         ==> !read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr)[$Box(this)]);
  requires _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.left) != null
         ==> _module.Node.Valid($LS($LS($LZ)), $Heap, read($Heap, this, _module.Node.left)));
  requires _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.left) != null
         ==> (forall y#0: int :: 
          { read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents)[$Box(y#0)] } 
          true
             ==> 
            read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents)[$Box(y#0)]
             ==> y#0 < read($Heap, this, _module.Node.data)));
  requires _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.right) != null
         ==> read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.right))]);
  requires _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.right) != null
         ==> Set#Subset(read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr), 
          read($Heap, this, _module.Node.Repr)));
  requires _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.right) != null
         ==> !read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr)[$Box(this)]);
  requires _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.right) != null
         ==> _module.Node.Valid($LS($LS($LZ)), $Heap, read($Heap, this, _module.Node.right)));
  requires _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.right) != null
         ==> (forall y#1: int :: 
          { read($Heap, read($Heap, this, _module.Node.right), _module.Node.Contents)[$Box(y#1)] } 
          true
             ==> 
            read($Heap, read($Heap, this, _module.Node.right), _module.Node.Contents)[$Box(y#1)]
             ==> read($Heap, this, _module.Node.data) < y#1));
  requires _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.left) == null
           && read($Heap, this, _module.Node.right) == null
         ==> Set#Equal(read($Heap, this, _module.Node.Contents), 
          Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.data)))));
  requires _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.left) != null
           && read($Heap, this, _module.Node.right) == null
         ==> Set#Equal(read($Heap, this, _module.Node.Contents), 
          Set#Union(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents), 
            Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.data))))));
  requires _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.left) == null
           && read($Heap, this, _module.Node.right) != null
         ==> Set#Equal(read($Heap, this, _module.Node.Contents), 
          Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.data))), 
            read($Heap, read($Heap, this, _module.Node.right), _module.Node.Contents))));
  requires _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.left) != null
           && read($Heap, this, _module.Node.right) != null
         ==> Set#Disjoint(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr), 
          read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr)));
  requires _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.left) != null
           && read($Heap, this, _module.Node.right) != null
         ==> Set#Equal(read($Heap, this, _module.Node.Contents), 
          Set#Union(Set#Union(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents), 
              Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.data)))), 
            read($Heap, read($Heap, this, _module.Node.right), _module.Node.Contents))));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    read($Heap, this, _module.Node.Repr)[$Box($o)]
         && !read(old($Heap), this, _module.Node.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures node#0 != null ==> _module.Node.Valid#canCall($Heap, node#0);
  free ensures node#0 != null
     ==> _module.Node.Valid#canCall($Heap, node#0)
       && 
      _module.Node.Valid($LS($LZ), $Heap, node#0)
       && 
      read($Heap, node#0, _module.Node.Repr)[$Box(node#0)]
       && (read($Heap, node#0, _module.Node.left) != null
         ==> read($Heap, node#0, _module.Node.Repr)[$Box(read($Heap, node#0, _module.Node.left))]
           && Set#Subset(read($Heap, read($Heap, node#0, _module.Node.left), _module.Node.Repr), 
            read($Heap, node#0, _module.Node.Repr))
           && !read($Heap, read($Heap, node#0, _module.Node.left), _module.Node.Repr)[$Box(node#0)]
           && _module.Node.Valid($LS($LZ), $Heap, read($Heap, node#0, _module.Node.left))
           && (forall y#2: int :: 
            { read($Heap, read($Heap, node#0, _module.Node.left), _module.Node.Contents)[$Box(y#2)] } 
            true
               ==> 
              read($Heap, read($Heap, node#0, _module.Node.left), _module.Node.Contents)[$Box(y#2)]
               ==> y#2 < read($Heap, node#0, _module.Node.data)))
       && (read($Heap, node#0, _module.Node.right) != null
         ==> read($Heap, node#0, _module.Node.Repr)[$Box(read($Heap, node#0, _module.Node.right))]
           && Set#Subset(read($Heap, read($Heap, node#0, _module.Node.right), _module.Node.Repr), 
            read($Heap, node#0, _module.Node.Repr))
           && !read($Heap, read($Heap, node#0, _module.Node.right), _module.Node.Repr)[$Box(node#0)]
           && _module.Node.Valid($LS($LZ), $Heap, read($Heap, node#0, _module.Node.right))
           && (forall y#3: int :: 
            { read($Heap, read($Heap, node#0, _module.Node.right), _module.Node.Contents)[$Box(y#3)] } 
            true
               ==> 
              read($Heap, read($Heap, node#0, _module.Node.right), _module.Node.Contents)[$Box(y#3)]
               ==> read($Heap, node#0, _module.Node.data) < y#3))
       && (read($Heap, node#0, _module.Node.left) == null
           && read($Heap, node#0, _module.Node.right) == null
         ==> Set#Equal(read($Heap, node#0, _module.Node.Contents), 
          Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, node#0, _module.Node.data)))))
       && (read($Heap, node#0, _module.Node.left) != null
           && read($Heap, node#0, _module.Node.right) == null
         ==> Set#Equal(read($Heap, node#0, _module.Node.Contents), 
          Set#Union(read($Heap, read($Heap, node#0, _module.Node.left), _module.Node.Contents), 
            Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, node#0, _module.Node.data))))))
       && (read($Heap, node#0, _module.Node.left) == null
           && read($Heap, node#0, _module.Node.right) != null
         ==> Set#Equal(read($Heap, node#0, _module.Node.Contents), 
          Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, node#0, _module.Node.data))), 
            read($Heap, read($Heap, node#0, _module.Node.right), _module.Node.Contents))))
       && (read($Heap, node#0, _module.Node.left) != null
           && read($Heap, node#0, _module.Node.right) != null
         ==> Set#Disjoint(read($Heap, read($Heap, node#0, _module.Node.left), _module.Node.Repr), 
            read($Heap, read($Heap, node#0, _module.Node.right), _module.Node.Repr))
           && Set#Equal(read($Heap, node#0, _module.Node.Contents), 
            Set#Union(Set#Union(read($Heap, read($Heap, node#0, _module.Node.left), _module.Node.Contents), 
                Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, node#0, _module.Node.data)))), 
              read($Heap, read($Heap, node#0, _module.Node.right), _module.Node.Contents))));
  free ensures true;
  ensures node#0 == null
     ==> Set#Subset(read(old($Heap), this, _module.Node.Contents), 
      Set#UnionOne(Set#Empty(): Set Box, $Box(x#0)));
  free ensures true;
  ensures node#0 != null
     ==> Set#Subset(read($Heap, node#0, _module.Node.Repr), read($Heap, this, _module.Node.Repr));
  ensures node#0 != null
     ==> Set#Equal(read($Heap, node#0, _module.Node.Contents), 
      Set#Difference(read(old($Heap), this, _module.Node.Contents), 
        Set#UnionOne(Set#Empty(): Set Box, $Box(x#0))));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || read(old($Heap), this, _module.Node.Repr)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Node.Remove(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), $Heap), 
    x#0: int)
   returns (node#0: ref
       where $Is(node#0, Tclass._module.Node?())
         && $IsAlloc(node#0, Tclass._module.Node?(), $Heap), 
    $_reverifyPost: bool);
  free requires 12 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.Node.Valid#canCall($Heap, this)
     && 
    _module.Node.Valid($LS($LZ), $Heap, this)
     && 
    read($Heap, this, _module.Node.Repr)[$Box(this)]
     && (read($Heap, this, _module.Node.left) != null
       ==> read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.left))]
         && Set#Subset(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr), 
          read($Heap, this, _module.Node.Repr))
         && !read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr)[$Box(this)]
         && _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.left))
         && (forall y#4: int :: 
          { read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents)[$Box(y#4)] } 
          true
             ==> 
            read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents)[$Box(y#4)]
             ==> y#4 < read($Heap, this, _module.Node.data)))
     && (read($Heap, this, _module.Node.right) != null
       ==> read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.right))]
         && Set#Subset(read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr), 
          read($Heap, this, _module.Node.Repr))
         && !read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr)[$Box(this)]
         && _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.right))
         && (forall y#5: int :: 
          { read($Heap, read($Heap, this, _module.Node.right), _module.Node.Contents)[$Box(y#5)] } 
          true
             ==> 
            read($Heap, read($Heap, this, _module.Node.right), _module.Node.Contents)[$Box(y#5)]
             ==> read($Heap, this, _module.Node.data) < y#5))
     && (read($Heap, this, _module.Node.left) == null
         && read($Heap, this, _module.Node.right) == null
       ==> Set#Equal(read($Heap, this, _module.Node.Contents), 
        Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.data)))))
     && (read($Heap, this, _module.Node.left) != null
         && read($Heap, this, _module.Node.right) == null
       ==> Set#Equal(read($Heap, this, _module.Node.Contents), 
        Set#Union(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents), 
          Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.data))))))
     && (read($Heap, this, _module.Node.left) == null
         && read($Heap, this, _module.Node.right) != null
       ==> Set#Equal(read($Heap, this, _module.Node.Contents), 
        Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.data))), 
          read($Heap, read($Heap, this, _module.Node.right), _module.Node.Contents))))
     && (read($Heap, this, _module.Node.left) != null
         && read($Heap, this, _module.Node.right) != null
       ==> Set#Disjoint(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr), 
          read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr))
         && Set#Equal(read($Heap, this, _module.Node.Contents), 
          Set#Union(Set#Union(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents), 
              Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.data)))), 
            read($Heap, read($Heap, this, _module.Node.right), _module.Node.Contents))));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    read($Heap, this, _module.Node.Repr)[$Box($o)]
         && !read(old($Heap), this, _module.Node.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures node#0 != null ==> _module.Node.Valid#canCall($Heap, node#0);
  ensures node#0 != null
     ==> 
    _module.Node.Valid#canCall($Heap, node#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, node#0)
       || read($Heap, node#0, _module.Node.Repr)[$Box(node#0)];
  ensures node#0 != null
     ==> 
    _module.Node.Valid#canCall($Heap, node#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, node#0)
       || (read($Heap, node#0, _module.Node.left) != null
         ==> read($Heap, node#0, _module.Node.Repr)[$Box(read($Heap, node#0, _module.Node.left))]);
  ensures node#0 != null
     ==> 
    _module.Node.Valid#canCall($Heap, node#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, node#0)
       || (read($Heap, node#0, _module.Node.left) != null
         ==> Set#Subset(read($Heap, read($Heap, node#0, _module.Node.left), _module.Node.Repr), 
          read($Heap, node#0, _module.Node.Repr)));
  ensures node#0 != null
     ==> 
    _module.Node.Valid#canCall($Heap, node#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, node#0)
       || (read($Heap, node#0, _module.Node.left) != null
         ==> !read($Heap, read($Heap, node#0, _module.Node.left), _module.Node.Repr)[$Box(node#0)]);
  ensures node#0 != null
     ==> 
    _module.Node.Valid#canCall($Heap, node#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, node#0)
       || (read($Heap, node#0, _module.Node.left) != null
         ==> _module.Node.Valid($LS($LS($LZ)), $Heap, read($Heap, node#0, _module.Node.left)));
  ensures node#0 != null
     ==> 
    _module.Node.Valid#canCall($Heap, node#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, node#0)
       || (read($Heap, node#0, _module.Node.left) != null
         ==> (forall y#6: int :: 
          { read($Heap, read($Heap, node#0, _module.Node.left), _module.Node.Contents)[$Box(y#6)] } 
          true
             ==> 
            read($Heap, read($Heap, node#0, _module.Node.left), _module.Node.Contents)[$Box(y#6)]
             ==> y#6 < read($Heap, node#0, _module.Node.data)));
  ensures node#0 != null
     ==> 
    _module.Node.Valid#canCall($Heap, node#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, node#0)
       || (read($Heap, node#0, _module.Node.right) != null
         ==> read($Heap, node#0, _module.Node.Repr)[$Box(read($Heap, node#0, _module.Node.right))]);
  ensures node#0 != null
     ==> 
    _module.Node.Valid#canCall($Heap, node#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, node#0)
       || (read($Heap, node#0, _module.Node.right) != null
         ==> Set#Subset(read($Heap, read($Heap, node#0, _module.Node.right), _module.Node.Repr), 
          read($Heap, node#0, _module.Node.Repr)));
  ensures node#0 != null
     ==> 
    _module.Node.Valid#canCall($Heap, node#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, node#0)
       || (read($Heap, node#0, _module.Node.right) != null
         ==> !read($Heap, read($Heap, node#0, _module.Node.right), _module.Node.Repr)[$Box(node#0)]);
  ensures node#0 != null
     ==> 
    _module.Node.Valid#canCall($Heap, node#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, node#0)
       || (read($Heap, node#0, _module.Node.right) != null
         ==> _module.Node.Valid($LS($LS($LZ)), $Heap, read($Heap, node#0, _module.Node.right)));
  ensures node#0 != null
     ==> 
    _module.Node.Valid#canCall($Heap, node#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, node#0)
       || (read($Heap, node#0, _module.Node.right) != null
         ==> (forall y#7: int :: 
          { read($Heap, read($Heap, node#0, _module.Node.right), _module.Node.Contents)[$Box(y#7)] } 
          true
             ==> 
            read($Heap, read($Heap, node#0, _module.Node.right), _module.Node.Contents)[$Box(y#7)]
             ==> read($Heap, node#0, _module.Node.data) < y#7));
  ensures node#0 != null
     ==> 
    _module.Node.Valid#canCall($Heap, node#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, node#0)
       || (read($Heap, node#0, _module.Node.left) == null
           && read($Heap, node#0, _module.Node.right) == null
         ==> Set#Equal(read($Heap, node#0, _module.Node.Contents), 
          Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, node#0, _module.Node.data)))));
  ensures node#0 != null
     ==> 
    _module.Node.Valid#canCall($Heap, node#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, node#0)
       || (read($Heap, node#0, _module.Node.left) != null
           && read($Heap, node#0, _module.Node.right) == null
         ==> Set#Equal(read($Heap, node#0, _module.Node.Contents), 
          Set#Union(read($Heap, read($Heap, node#0, _module.Node.left), _module.Node.Contents), 
            Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, node#0, _module.Node.data))))));
  ensures node#0 != null
     ==> 
    _module.Node.Valid#canCall($Heap, node#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, node#0)
       || (read($Heap, node#0, _module.Node.left) == null
           && read($Heap, node#0, _module.Node.right) != null
         ==> Set#Equal(read($Heap, node#0, _module.Node.Contents), 
          Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, node#0, _module.Node.data))), 
            read($Heap, read($Heap, node#0, _module.Node.right), _module.Node.Contents))));
  ensures node#0 != null
     ==> 
    _module.Node.Valid#canCall($Heap, node#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, node#0)
       || (read($Heap, node#0, _module.Node.left) != null
           && read($Heap, node#0, _module.Node.right) != null
         ==> Set#Disjoint(read($Heap, read($Heap, node#0, _module.Node.left), _module.Node.Repr), 
          read($Heap, read($Heap, node#0, _module.Node.right), _module.Node.Repr)));
  ensures node#0 != null
     ==> 
    _module.Node.Valid#canCall($Heap, node#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, node#0)
       || (read($Heap, node#0, _module.Node.left) != null
           && read($Heap, node#0, _module.Node.right) != null
         ==> Set#Equal(read($Heap, node#0, _module.Node.Contents), 
          Set#Union(Set#Union(read($Heap, read($Heap, node#0, _module.Node.left), _module.Node.Contents), 
              Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, node#0, _module.Node.data)))), 
            read($Heap, read($Heap, node#0, _module.Node.right), _module.Node.Contents))));
  free ensures true;
  ensures node#0 == null
     ==> Set#Subset(read(old($Heap), this, _module.Node.Contents), 
      Set#UnionOne(Set#Empty(): Set Box, $Box(x#0)));
  free ensures true;
  ensures node#0 != null
     ==> Set#Subset(read($Heap, node#0, _module.Node.Repr), read($Heap, this, _module.Node.Repr));
  ensures node#0 != null
     ==> Set#Equal(read($Heap, node#0, _module.Node.Contents), 
      Set#Difference(read(old($Heap), this, _module.Node.Contents), 
        Set#UnionOne(Set#Empty(): Set Box, $Box(x#0))));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || read(old($Heap), this, _module.Node.Repr)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Node.Remove(this: ref, x#0: int) returns (node#0: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var t#0_0: ref
     where $Is(t#0_0, Tclass._module.Node?())
       && $IsAlloc(t#0_0, Tclass._module.Node?(), $Heap);
  var $rhs##0_0: ref
     where $Is($rhs##0_0, Tclass._module.Node?())
       && $IsAlloc($rhs##0_0, Tclass._module.Node?(), $Heap);
  var x##0_0: int;
  var $rhs#0_0: ref where $Is($rhs#0_0, Tclass._module.Node?());
  var $rhs#0_1: Set Box where $Is($rhs#0_1, TSet(TInt));
  var $rhs#0_0_0: Set Box where $Is($rhs#0_0_0, TSet(Tclass._System.object()));
  var t#1_0: ref
     where $Is(t#1_0, Tclass._module.Node?())
       && $IsAlloc(t#1_0, Tclass._module.Node?(), $Heap);
  var $rhs##1_0: ref
     where $Is($rhs##1_0, Tclass._module.Node?())
       && $IsAlloc($rhs##1_0, Tclass._module.Node?(), $Heap);
  var x##1_0: int;
  var $rhs#1_0: ref where $Is($rhs#1_0, Tclass._module.Node?());
  var $rhs#1_1: Set Box where $Is($rhs#1_1, TSet(TInt));
  var $rhs#1_0_0: Set Box where $Is($rhs#1_0_0, TSet(Tclass._System.object()));
  var min#2_0: int;
  var r#2_0: ref
     where $Is(r#2_0, Tclass._module.Node?())
       && $IsAlloc(r#2_0, Tclass._module.Node?(), $Heap);
  var $rhs##2_0: int;
  var $rhs##2_1: ref
     where $Is($rhs##2_1, Tclass._module.Node?())
       && $IsAlloc($rhs##2_1, Tclass._module.Node?(), $Heap);
  var $rhs#2_0: int;
  var $rhs#2_1: ref where $Is($rhs#2_1, Tclass._module.Node?());
  var $rhs#2_2: Set Box where $Is($rhs#2_2, TSet(TInt));
  var $rhs#2_3_0: Set Box where $Is($rhs#2_3_0, TSet(Tclass._System.object()));

    // AddMethodImpl: Remove, Impl$$_module.Node.Remove
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.Node.Repr)[$Box($o)]);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(170,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(171,10)
    assume true;
    assume true;
    node#0 := this;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(171,16)"} true;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(172,5)
    if (read($Heap, this, _module.Node.left) != null)
    {
    }

    assume true;
    if (read($Heap, this, _module.Node.left) != null
       && x#0 < read($Heap, this, _module.Node.data))
    {
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(173,27)
        assume true;
        // TrCallStmt: Adding lhs with type Node?
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        assert read($Heap, this, _module.Node.left) != null;
        assume true;
        // ProcessCallStmt: CheckSubrange
        x##0_0 := x#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null
               && read($Heap, $o, alloc)
               && read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr)[$Box($o)]
             ==> $_Frame[$o, $f]);
        assert Set#Subset(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr), 
            read(old($Heap), this, _module.Node.Repr))
           && !Set#Subset(read(old($Heap), this, _module.Node.Repr), 
            read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr));
        // ProcessCallStmt: Make the call
        call $rhs##0_0 := Call$$_module.Node.Remove(read($Heap, this, _module.Node.left), x##0_0);
        // TrCallStmt: After ProcessCallStmt
        t#0_0 := $rhs##0_0;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(173,29)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(174,12)
        assume true;
        assert $_Frame[this, _module.Node.left];
        assume true;
        $rhs#0_0 := t#0_0;
        $Heap := update($Heap, this, _module.Node.left, $rhs#0_0);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(174,15)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(175,16)
        assume true;
        assert $_Frame[this, _module.Node.Contents];
        assume true;
        $rhs#0_1 := Set#Difference(read($Heap, this, _module.Node.Contents), 
          Set#UnionOne(Set#Empty(): Set Box, $Box(x#0)));
        $Heap := update($Heap, this, _module.Node.Contents, $rhs#0_1);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(175,32)"} true;
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(176,7)
        assume true;
        if (read($Heap, this, _module.Node.left) != null)
        {
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(176,30)
            assume true;
            assert $_Frame[this, _module.Node.Repr];
            assert read($Heap, this, _module.Node.left) != null;
            assume true;
            $rhs#0_0_0 := Set#Union(read($Heap, this, _module.Node.Repr), 
              read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr));
            $Heap := update($Heap, this, _module.Node.Repr, $rhs#0_0_0);
            assume $IsGoodHeap($Heap);
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(176,48)"} true;
        }
        else
        {
        }
    }
    else
    {
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(177,12)
        if (read($Heap, this, _module.Node.right) != null)
        {
        }

        assume true;
        if (read($Heap, this, _module.Node.right) != null
           && read($Heap, this, _module.Node.data) < x#0)
        {
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(178,28)
            assume true;
            // TrCallStmt: Adding lhs with type Node?
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            assert read($Heap, this, _module.Node.right) != null;
            assume true;
            // ProcessCallStmt: CheckSubrange
            x##1_0 := x#0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: 
              $o != null
                   && read($Heap, $o, alloc)
                   && read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr)[$Box($o)]
                 ==> $_Frame[$o, $f]);
            assert Set#Subset(read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr), 
                read(old($Heap), this, _module.Node.Repr))
               && !Set#Subset(read(old($Heap), this, _module.Node.Repr), 
                read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr));
            // ProcessCallStmt: Make the call
            call $rhs##1_0 := Call$$_module.Node.Remove(read($Heap, this, _module.Node.right), x##1_0);
            // TrCallStmt: After ProcessCallStmt
            t#1_0 := $rhs##1_0;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(178,30)"} true;
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(179,13)
            assume true;
            assert $_Frame[this, _module.Node.right];
            assume true;
            $rhs#1_0 := t#1_0;
            $Heap := update($Heap, this, _module.Node.right, $rhs#1_0);
            assume $IsGoodHeap($Heap);
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(179,16)"} true;
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(180,16)
            assume true;
            assert $_Frame[this, _module.Node.Contents];
            assume true;
            $rhs#1_1 := Set#Difference(read($Heap, this, _module.Node.Contents), 
              Set#UnionOne(Set#Empty(): Set Box, $Box(x#0)));
            $Heap := update($Heap, this, _module.Node.Contents, $rhs#1_1);
            assume $IsGoodHeap($Heap);
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(180,32)"} true;
            // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(181,7)
            assume true;
            if (read($Heap, this, _module.Node.right) != null)
            {
                // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(181,31)
                assume true;
                assert $_Frame[this, _module.Node.Repr];
                assert read($Heap, this, _module.Node.right) != null;
                assume true;
                $rhs#1_0_0 := Set#Union(read($Heap, this, _module.Node.Repr), 
                  read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr));
                $Heap := update($Heap, this, _module.Node.Repr, $rhs#1_0_0);
                assume $IsGoodHeap($Heap);
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(181,50)"} true;
            }
            else
            {
            }
        }
        else
        {
            // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(182,12)
            assume true;
            if (x#0 == read($Heap, this, _module.Node.data))
            {
                // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(183,7)
                if (read($Heap, this, _module.Node.left) == null)
                {
                }

                assume true;
                if (read($Heap, this, _module.Node.left) == null
                   && read($Heap, this, _module.Node.right) == null)
                {
                    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(184,14)
                    assume true;
                    assume true;
                    node#0 := null;
                    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(184,20)"} true;
                }
                else
                {
                    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(185,14)
                    assume true;
                    if (read($Heap, this, _module.Node.left) == null)
                    {
                        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(186,14)
                        assume true;
                        assume true;
                        node#0 := read($Heap, this, _module.Node.right);
                        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(186,21)"} true;
                    }
                    else
                    {
                        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(187,14)
                        assume true;
                        if (read($Heap, this, _module.Node.right) == null)
                        {
                            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(188,14)
                            assume true;
                            assume true;
                            node#0 := read($Heap, this, _module.Node.left);
                            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(188,20)"} true;
                        }
                        else
                        {
                            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(191,38)
                            assume true;
                            assume true;
                            // TrCallStmt: Adding lhs with type int
                            // TrCallStmt: Adding lhs with type Node?
                            // TrCallStmt: Before ProcessCallStmt
                            assume true;
                            assert read($Heap, this, _module.Node.right) != null;
                            assert (forall<alpha> $o: ref, $f: Field alpha :: 
                              $o != null
                                   && read($Heap, $o, alloc)
                                   && read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr)[$Box($o)]
                                 ==> $_Frame[$o, $f]);
                            // ProcessCallStmt: Make the call
                            call $rhs##2_0, $rhs##2_1 := Call$$_module.Node.RemoveMin(read($Heap, this, _module.Node.right));
                            // TrCallStmt: After ProcessCallStmt
                            min#2_0 := $rhs##2_0;
                            r#2_0 := $rhs##2_1;
                            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(191,39)"} true;
                            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(192,14)
                            assume true;
                            assert $_Frame[this, _module.Node.data];
                            assume true;
                            $rhs#2_0 := min#2_0;
                            $Heap := update($Heap, this, _module.Node.data, $rhs#2_0);
                            assume $IsGoodHeap($Heap);
                            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(192,19)"} true;
                            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(192,29)
                            assume true;
                            assert $_Frame[this, _module.Node.right];
                            assume true;
                            $rhs#2_1 := r#2_0;
                            $Heap := update($Heap, this, _module.Node.right, $rhs#2_1);
                            assume $IsGoodHeap($Heap);
                            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(192,32)"} true;
                            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(193,18)
                            assume true;
                            assert $_Frame[this, _module.Node.Contents];
                            assume true;
                            $rhs#2_2 := Set#Difference(read($Heap, this, _module.Node.Contents), 
                              Set#UnionOne(Set#Empty(): Set Box, $Box(x#0)));
                            $Heap := update($Heap, this, _module.Node.Contents, $rhs#2_2);
                            assume $IsGoodHeap($Heap);
                            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(193,34)"} true;
                            // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(194,9)
                            assume true;
                            if (read($Heap, this, _module.Node.right) != null)
                            {
                                // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(194,33)
                                assume true;
                                assert $_Frame[this, _module.Node.Repr];
                                assert read($Heap, this, _module.Node.right) != null;
                                assume true;
                                $rhs#2_3_0 := Set#Union(read($Heap, this, _module.Node.Repr), 
                                  read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr));
                                $Heap := update($Heap, this, _module.Node.Repr, $rhs#2_3_0);
                                assume $IsGoodHeap($Heap);
                                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(194,52)"} true;
                            }
                            else
                            {
                            }
                        }
                    }
                }
            }
            else
            {
            }
        }
    }
}



procedure CheckWellformed$$_module.Node.RemoveMin(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), $Heap))
   returns (min#0: int, 
    node#0: ref
       where $Is(node#0, Tclass._module.Node?())
         && $IsAlloc(node#0, Tclass._module.Node?(), $Heap));
  free requires 11 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Node.RemoveMin(this: ref) returns (min#0: int, node#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var x#0: int;

    // AddMethodImpl: RemoveMin, CheckWellformed$$_module.Node.RemoveMin
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.Node.Repr)[$Box($o)]);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(199,9): initial state"} true;
    assume _module.Node.Valid#canCall($Heap, this);
    assume _module.Node.Valid($LS($LZ), $Heap, this);
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc)
         ==> $Heap[$o] == old($Heap)[$o]
           || read(old($Heap), this, _module.Node.Repr)[$Box($o)]);
    assume $HeapSucc(old($Heap), $Heap);
    havoc min#0, node#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(202,12): post-state"} true;
    assert $IsAlloc(this, Tclass._module.Node(), old($Heap));
    assume (forall $o: ref :: 
      { read(old($Heap), $o, alloc) } 
      read($Heap, this, _module.Node.Repr)[$Box($o)]
           && !read(old($Heap), this, _module.Node.Repr)[$Box($o)]
         ==> $o != null && !read(old($Heap), $o, alloc));
    if (*)
    {
        assume node#0 != null;
        assert node#0 != null;
        assume _module.Node.Valid#canCall($Heap, node#0);
        assume _module.Node.Valid($LS($LZ), $Heap, node#0);
    }
    else
    {
        assume node#0 != null ==> _module.Node.Valid($LS($LZ), $Heap, node#0);
    }

    if (*)
    {
        assume node#0 == null;
        assert $IsAlloc(this, Tclass._module.Node(), old($Heap));
        assume Set#Equal(read(old($Heap), this, _module.Node.Contents), 
          Set#UnionOne(Set#Empty(): Set Box, $Box(min#0)));
    }
    else
    {
        assume node#0 == null
           ==> Set#Equal(read(old($Heap), this, _module.Node.Contents), 
            Set#UnionOne(Set#Empty(): Set Box, $Box(min#0)));
    }

    if (*)
    {
        assume node#0 != null;
        assert node#0 != null;
        assume Set#Subset(read($Heap, node#0, _module.Node.Repr), read($Heap, this, _module.Node.Repr));
        assert node#0 != null;
        assert $IsAlloc(this, Tclass._module.Node(), old($Heap));
        assume Set#Equal(read($Heap, node#0, _module.Node.Contents), 
          Set#Difference(read(old($Heap), this, _module.Node.Contents), 
            Set#UnionOne(Set#Empty(): Set Box, $Box(min#0))));
    }
    else
    {
        assume node#0 != null
           ==> Set#Subset(read($Heap, node#0, _module.Node.Repr), read($Heap, this, _module.Node.Repr))
             && Set#Equal(read($Heap, node#0, _module.Node.Contents), 
              Set#Difference(read(old($Heap), this, _module.Node.Contents), 
                Set#UnionOne(Set#Empty(): Set Box, $Box(min#0))));
    }

    assert $IsAlloc(this, Tclass._module.Node(), old($Heap));
    assume read(old($Heap), this, _module.Node.Contents)[$Box(min#0)];
    // Begin Comprehension WF check
    havoc x#0;
    if (true)
    {
        assert $IsAlloc(this, Tclass._module.Node(), old($Heap));
        if (read(old($Heap), this, _module.Node.Contents)[$Box(x#0)])
        {
        }
    }

    // End Comprehension WF check
    assume (forall x#1: int :: 
      { read(old($Heap), this, _module.Node.Contents)[$Box(x#1)] } 
      true
         ==> 
        read(old($Heap), this, _module.Node.Contents)[$Box(x#1)]
         ==> min#0 <= x#1);
}



procedure Call$$_module.Node.RemoveMin(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), $Heap))
   returns (min#0: int, 
    node#0: ref
       where $Is(node#0, Tclass._module.Node?())
         && $IsAlloc(node#0, Tclass._module.Node?(), $Heap));
  // user-defined preconditions
  requires _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || read($Heap, this, _module.Node.Repr)[$Box(this)];
  requires _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.left) != null
         ==> read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.left))]);
  requires _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.left) != null
         ==> Set#Subset(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr), 
          read($Heap, this, _module.Node.Repr)));
  requires _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.left) != null
         ==> !read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr)[$Box(this)]);
  requires _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.left) != null
         ==> _module.Node.Valid($LS($LS($LZ)), $Heap, read($Heap, this, _module.Node.left)));
  requires _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.left) != null
         ==> (forall y#0: int :: 
          { read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents)[$Box(y#0)] } 
          true
             ==> 
            read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents)[$Box(y#0)]
             ==> y#0 < read($Heap, this, _module.Node.data)));
  requires _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.right) != null
         ==> read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.right))]);
  requires _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.right) != null
         ==> Set#Subset(read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr), 
          read($Heap, this, _module.Node.Repr)));
  requires _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.right) != null
         ==> !read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr)[$Box(this)]);
  requires _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.right) != null
         ==> _module.Node.Valid($LS($LS($LZ)), $Heap, read($Heap, this, _module.Node.right)));
  requires _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.right) != null
         ==> (forall y#1: int :: 
          { read($Heap, read($Heap, this, _module.Node.right), _module.Node.Contents)[$Box(y#1)] } 
          true
             ==> 
            read($Heap, read($Heap, this, _module.Node.right), _module.Node.Contents)[$Box(y#1)]
             ==> read($Heap, this, _module.Node.data) < y#1));
  requires _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.left) == null
           && read($Heap, this, _module.Node.right) == null
         ==> Set#Equal(read($Heap, this, _module.Node.Contents), 
          Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.data)))));
  requires _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.left) != null
           && read($Heap, this, _module.Node.right) == null
         ==> Set#Equal(read($Heap, this, _module.Node.Contents), 
          Set#Union(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents), 
            Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.data))))));
  requires _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.left) == null
           && read($Heap, this, _module.Node.right) != null
         ==> Set#Equal(read($Heap, this, _module.Node.Contents), 
          Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.data))), 
            read($Heap, read($Heap, this, _module.Node.right), _module.Node.Contents))));
  requires _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.left) != null
           && read($Heap, this, _module.Node.right) != null
         ==> Set#Disjoint(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr), 
          read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr)));
  requires _module.Node.Valid#canCall($Heap, this)
     ==> _module.Node.Valid($LS($LZ), $Heap, this)
       || (read($Heap, this, _module.Node.left) != null
           && read($Heap, this, _module.Node.right) != null
         ==> Set#Equal(read($Heap, this, _module.Node.Contents), 
          Set#Union(Set#Union(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents), 
              Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.data)))), 
            read($Heap, read($Heap, this, _module.Node.right), _module.Node.Contents))));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    read($Heap, this, _module.Node.Repr)[$Box($o)]
         && !read(old($Heap), this, _module.Node.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures node#0 != null ==> _module.Node.Valid#canCall($Heap, node#0);
  free ensures node#0 != null
     ==> _module.Node.Valid#canCall($Heap, node#0)
       && 
      _module.Node.Valid($LS($LZ), $Heap, node#0)
       && 
      read($Heap, node#0, _module.Node.Repr)[$Box(node#0)]
       && (read($Heap, node#0, _module.Node.left) != null
         ==> read($Heap, node#0, _module.Node.Repr)[$Box(read($Heap, node#0, _module.Node.left))]
           && Set#Subset(read($Heap, read($Heap, node#0, _module.Node.left), _module.Node.Repr), 
            read($Heap, node#0, _module.Node.Repr))
           && !read($Heap, read($Heap, node#0, _module.Node.left), _module.Node.Repr)[$Box(node#0)]
           && _module.Node.Valid($LS($LZ), $Heap, read($Heap, node#0, _module.Node.left))
           && (forall y#2: int :: 
            { read($Heap, read($Heap, node#0, _module.Node.left), _module.Node.Contents)[$Box(y#2)] } 
            true
               ==> 
              read($Heap, read($Heap, node#0, _module.Node.left), _module.Node.Contents)[$Box(y#2)]
               ==> y#2 < read($Heap, node#0, _module.Node.data)))
       && (read($Heap, node#0, _module.Node.right) != null
         ==> read($Heap, node#0, _module.Node.Repr)[$Box(read($Heap, node#0, _module.Node.right))]
           && Set#Subset(read($Heap, read($Heap, node#0, _module.Node.right), _module.Node.Repr), 
            read($Heap, node#0, _module.Node.Repr))
           && !read($Heap, read($Heap, node#0, _module.Node.right), _module.Node.Repr)[$Box(node#0)]
           && _module.Node.Valid($LS($LZ), $Heap, read($Heap, node#0, _module.Node.right))
           && (forall y#3: int :: 
            { read($Heap, read($Heap, node#0, _module.Node.right), _module.Node.Contents)[$Box(y#3)] } 
            true
               ==> 
              read($Heap, read($Heap, node#0, _module.Node.right), _module.Node.Contents)[$Box(y#3)]
               ==> read($Heap, node#0, _module.Node.data) < y#3))
       && (read($Heap, node#0, _module.Node.left) == null
           && read($Heap, node#0, _module.Node.right) == null
         ==> Set#Equal(read($Heap, node#0, _module.Node.Contents), 
          Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, node#0, _module.Node.data)))))
       && (read($Heap, node#0, _module.Node.left) != null
           && read($Heap, node#0, _module.Node.right) == null
         ==> Set#Equal(read($Heap, node#0, _module.Node.Contents), 
          Set#Union(read($Heap, read($Heap, node#0, _module.Node.left), _module.Node.Contents), 
            Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, node#0, _module.Node.data))))))
       && (read($Heap, node#0, _module.Node.left) == null
           && read($Heap, node#0, _module.Node.right) != null
         ==> Set#Equal(read($Heap, node#0, _module.Node.Contents), 
          Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, node#0, _module.Node.data))), 
            read($Heap, read($Heap, node#0, _module.Node.right), _module.Node.Contents))))
       && (read($Heap, node#0, _module.Node.left) != null
           && read($Heap, node#0, _module.Node.right) != null
         ==> Set#Disjoint(read($Heap, read($Heap, node#0, _module.Node.left), _module.Node.Repr), 
            read($Heap, read($Heap, node#0, _module.Node.right), _module.Node.Repr))
           && Set#Equal(read($Heap, node#0, _module.Node.Contents), 
            Set#Union(Set#Union(read($Heap, read($Heap, node#0, _module.Node.left), _module.Node.Contents), 
                Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, node#0, _module.Node.data)))), 
              read($Heap, read($Heap, node#0, _module.Node.right), _module.Node.Contents))));
  free ensures true;
  ensures node#0 == null
     ==> Set#Equal(read(old($Heap), this, _module.Node.Contents), 
      Set#UnionOne(Set#Empty(): Set Box, $Box(min#0)));
  free ensures true;
  ensures node#0 != null
     ==> Set#Subset(read($Heap, node#0, _module.Node.Repr), read($Heap, this, _module.Node.Repr));
  ensures node#0 != null
     ==> Set#Equal(read($Heap, node#0, _module.Node.Contents), 
      Set#Difference(read(old($Heap), this, _module.Node.Contents), 
        Set#UnionOne(Set#Empty(): Set Box, $Box(min#0))));
  free ensures true;
  ensures read(old($Heap), this, _module.Node.Contents)[$Box(min#0)];
  ensures (forall x#1: int :: 
    { read(old($Heap), this, _module.Node.Contents)[$Box(x#1)] } 
    true
       ==> 
      read(old($Heap), this, _module.Node.Contents)[$Box(x#1)]
       ==> min#0 <= x#1);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || read(old($Heap), this, _module.Node.Repr)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Node.RemoveMin(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), $Heap))
   returns (min#0: int, 
    node#0: ref
       where $Is(node#0, Tclass._module.Node?())
         && $IsAlloc(node#0, Tclass._module.Node?(), $Heap), 
    $_reverifyPost: bool);
  free requires 11 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.Node.Valid#canCall($Heap, this)
     && 
    _module.Node.Valid($LS($LZ), $Heap, this)
     && 
    read($Heap, this, _module.Node.Repr)[$Box(this)]
     && (read($Heap, this, _module.Node.left) != null
       ==> read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.left))]
         && Set#Subset(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr), 
          read($Heap, this, _module.Node.Repr))
         && !read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr)[$Box(this)]
         && _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.left))
         && (forall y#4: int :: 
          { read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents)[$Box(y#4)] } 
          true
             ==> 
            read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents)[$Box(y#4)]
             ==> y#4 < read($Heap, this, _module.Node.data)))
     && (read($Heap, this, _module.Node.right) != null
       ==> read($Heap, this, _module.Node.Repr)[$Box(read($Heap, this, _module.Node.right))]
         && Set#Subset(read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr), 
          read($Heap, this, _module.Node.Repr))
         && !read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr)[$Box(this)]
         && _module.Node.Valid($LS($LZ), $Heap, read($Heap, this, _module.Node.right))
         && (forall y#5: int :: 
          { read($Heap, read($Heap, this, _module.Node.right), _module.Node.Contents)[$Box(y#5)] } 
          true
             ==> 
            read($Heap, read($Heap, this, _module.Node.right), _module.Node.Contents)[$Box(y#5)]
             ==> read($Heap, this, _module.Node.data) < y#5))
     && (read($Heap, this, _module.Node.left) == null
         && read($Heap, this, _module.Node.right) == null
       ==> Set#Equal(read($Heap, this, _module.Node.Contents), 
        Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.data)))))
     && (read($Heap, this, _module.Node.left) != null
         && read($Heap, this, _module.Node.right) == null
       ==> Set#Equal(read($Heap, this, _module.Node.Contents), 
        Set#Union(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents), 
          Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.data))))))
     && (read($Heap, this, _module.Node.left) == null
         && read($Heap, this, _module.Node.right) != null
       ==> Set#Equal(read($Heap, this, _module.Node.Contents), 
        Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.data))), 
          read($Heap, read($Heap, this, _module.Node.right), _module.Node.Contents))))
     && (read($Heap, this, _module.Node.left) != null
         && read($Heap, this, _module.Node.right) != null
       ==> Set#Disjoint(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr), 
          read($Heap, read($Heap, this, _module.Node.right), _module.Node.Repr))
         && Set#Equal(read($Heap, this, _module.Node.Contents), 
          Set#Union(Set#Union(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Contents), 
              Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, this, _module.Node.data)))), 
            read($Heap, read($Heap, this, _module.Node.right), _module.Node.Contents))));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    read($Heap, this, _module.Node.Repr)[$Box($o)]
         && !read(old($Heap), this, _module.Node.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures node#0 != null ==> _module.Node.Valid#canCall($Heap, node#0);
  ensures node#0 != null
     ==> 
    _module.Node.Valid#canCall($Heap, node#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, node#0)
       || read($Heap, node#0, _module.Node.Repr)[$Box(node#0)];
  ensures node#0 != null
     ==> 
    _module.Node.Valid#canCall($Heap, node#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, node#0)
       || (read($Heap, node#0, _module.Node.left) != null
         ==> read($Heap, node#0, _module.Node.Repr)[$Box(read($Heap, node#0, _module.Node.left))]);
  ensures node#0 != null
     ==> 
    _module.Node.Valid#canCall($Heap, node#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, node#0)
       || (read($Heap, node#0, _module.Node.left) != null
         ==> Set#Subset(read($Heap, read($Heap, node#0, _module.Node.left), _module.Node.Repr), 
          read($Heap, node#0, _module.Node.Repr)));
  ensures node#0 != null
     ==> 
    _module.Node.Valid#canCall($Heap, node#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, node#0)
       || (read($Heap, node#0, _module.Node.left) != null
         ==> !read($Heap, read($Heap, node#0, _module.Node.left), _module.Node.Repr)[$Box(node#0)]);
  ensures node#0 != null
     ==> 
    _module.Node.Valid#canCall($Heap, node#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, node#0)
       || (read($Heap, node#0, _module.Node.left) != null
         ==> _module.Node.Valid($LS($LS($LZ)), $Heap, read($Heap, node#0, _module.Node.left)));
  ensures node#0 != null
     ==> 
    _module.Node.Valid#canCall($Heap, node#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, node#0)
       || (read($Heap, node#0, _module.Node.left) != null
         ==> (forall y#6: int :: 
          { read($Heap, read($Heap, node#0, _module.Node.left), _module.Node.Contents)[$Box(y#6)] } 
          true
             ==> 
            read($Heap, read($Heap, node#0, _module.Node.left), _module.Node.Contents)[$Box(y#6)]
             ==> y#6 < read($Heap, node#0, _module.Node.data)));
  ensures node#0 != null
     ==> 
    _module.Node.Valid#canCall($Heap, node#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, node#0)
       || (read($Heap, node#0, _module.Node.right) != null
         ==> read($Heap, node#0, _module.Node.Repr)[$Box(read($Heap, node#0, _module.Node.right))]);
  ensures node#0 != null
     ==> 
    _module.Node.Valid#canCall($Heap, node#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, node#0)
       || (read($Heap, node#0, _module.Node.right) != null
         ==> Set#Subset(read($Heap, read($Heap, node#0, _module.Node.right), _module.Node.Repr), 
          read($Heap, node#0, _module.Node.Repr)));
  ensures node#0 != null
     ==> 
    _module.Node.Valid#canCall($Heap, node#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, node#0)
       || (read($Heap, node#0, _module.Node.right) != null
         ==> !read($Heap, read($Heap, node#0, _module.Node.right), _module.Node.Repr)[$Box(node#0)]);
  ensures node#0 != null
     ==> 
    _module.Node.Valid#canCall($Heap, node#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, node#0)
       || (read($Heap, node#0, _module.Node.right) != null
         ==> _module.Node.Valid($LS($LS($LZ)), $Heap, read($Heap, node#0, _module.Node.right)));
  ensures node#0 != null
     ==> 
    _module.Node.Valid#canCall($Heap, node#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, node#0)
       || (read($Heap, node#0, _module.Node.right) != null
         ==> (forall y#7: int :: 
          { read($Heap, read($Heap, node#0, _module.Node.right), _module.Node.Contents)[$Box(y#7)] } 
          true
             ==> 
            read($Heap, read($Heap, node#0, _module.Node.right), _module.Node.Contents)[$Box(y#7)]
             ==> read($Heap, node#0, _module.Node.data) < y#7));
  ensures node#0 != null
     ==> 
    _module.Node.Valid#canCall($Heap, node#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, node#0)
       || (read($Heap, node#0, _module.Node.left) == null
           && read($Heap, node#0, _module.Node.right) == null
         ==> Set#Equal(read($Heap, node#0, _module.Node.Contents), 
          Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, node#0, _module.Node.data)))));
  ensures node#0 != null
     ==> 
    _module.Node.Valid#canCall($Heap, node#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, node#0)
       || (read($Heap, node#0, _module.Node.left) != null
           && read($Heap, node#0, _module.Node.right) == null
         ==> Set#Equal(read($Heap, node#0, _module.Node.Contents), 
          Set#Union(read($Heap, read($Heap, node#0, _module.Node.left), _module.Node.Contents), 
            Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, node#0, _module.Node.data))))));
  ensures node#0 != null
     ==> 
    _module.Node.Valid#canCall($Heap, node#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, node#0)
       || (read($Heap, node#0, _module.Node.left) == null
           && read($Heap, node#0, _module.Node.right) != null
         ==> Set#Equal(read($Heap, node#0, _module.Node.Contents), 
          Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, node#0, _module.Node.data))), 
            read($Heap, read($Heap, node#0, _module.Node.right), _module.Node.Contents))));
  ensures node#0 != null
     ==> 
    _module.Node.Valid#canCall($Heap, node#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, node#0)
       || (read($Heap, node#0, _module.Node.left) != null
           && read($Heap, node#0, _module.Node.right) != null
         ==> Set#Disjoint(read($Heap, read($Heap, node#0, _module.Node.left), _module.Node.Repr), 
          read($Heap, read($Heap, node#0, _module.Node.right), _module.Node.Repr)));
  ensures node#0 != null
     ==> 
    _module.Node.Valid#canCall($Heap, node#0)
     ==> _module.Node.Valid($LS($LZ), $Heap, node#0)
       || (read($Heap, node#0, _module.Node.left) != null
           && read($Heap, node#0, _module.Node.right) != null
         ==> Set#Equal(read($Heap, node#0, _module.Node.Contents), 
          Set#Union(Set#Union(read($Heap, read($Heap, node#0, _module.Node.left), _module.Node.Contents), 
              Set#UnionOne(Set#Empty(): Set Box, $Box(read($Heap, node#0, _module.Node.data)))), 
            read($Heap, read($Heap, node#0, _module.Node.right), _module.Node.Contents))));
  free ensures true;
  ensures node#0 == null
     ==> Set#Equal(read(old($Heap), this, _module.Node.Contents), 
      Set#UnionOne(Set#Empty(): Set Box, $Box(min#0)));
  free ensures true;
  ensures node#0 != null
     ==> Set#Subset(read($Heap, node#0, _module.Node.Repr), read($Heap, this, _module.Node.Repr));
  ensures node#0 != null
     ==> Set#Equal(read($Heap, node#0, _module.Node.Contents), 
      Set#Difference(read(old($Heap), this, _module.Node.Contents), 
        Set#UnionOne(Set#Empty(): Set Box, $Box(min#0))));
  free ensures true;
  ensures read(old($Heap), this, _module.Node.Contents)[$Box(min#0)];
  ensures (forall x#1: int :: 
    { read(old($Heap), this, _module.Node.Contents)[$Box(x#1)] } 
    true
       ==> 
      read(old($Heap), this, _module.Node.Contents)[$Box(x#1)]
       ==> min#0 <= x#1);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || read(old($Heap), this, _module.Node.Repr)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Node.RemoveMin(this: ref) returns (min#0: int, node#0: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var t#0: ref
     where $Is(t#0, Tclass._module.Node?()) && $IsAlloc(t#0, Tclass._module.Node?(), $Heap);
  var $rhs##0: int;
  var $rhs##1: ref
     where $Is($rhs##1, Tclass._module.Node?())
       && $IsAlloc($rhs##1, Tclass._module.Node?(), $Heap);
  var $rhs#0: ref where $Is($rhs#0, Tclass._module.Node?());
  var $rhs#1: Set Box where $Is($rhs#1, TSet(TInt));
  var $rhs#1_0: Set Box where $Is($rhs#1_0, TSet(Tclass._System.object()));

    // AddMethodImpl: RemoveMin, Impl$$_module.Node.RemoveMin
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, _module.Node.Repr)[$Box($o)]);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(208,2): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(209,5)
    assume true;
    if (read($Heap, this, _module.Node.left) == null)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(210,11)
        assume true;
        assume true;
        min#0 := read($Heap, this, _module.Node.data);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(210,17)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(211,12)
        assume true;
        assume true;
        node#0 := read($Heap, this, _module.Node.right);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(211,19)"} true;
    }
    else
    {
        havoc t#0 /* where $Is(t#0, Tclass._module.Node?()) && $IsAlloc(t#0, Tclass._module.Node?(), $Heap) */;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(214,31)
        assume true;
        assume true;
        // TrCallStmt: Adding lhs with type int
        // TrCallStmt: Adding lhs with type Node?
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        assert read($Heap, this, _module.Node.left) != null;
        assert (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null
               && read($Heap, $o, alloc)
               && read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr)[$Box($o)]
             ==> $_Frame[$o, $f]);
        assert Set#Subset(read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr), 
            read(old($Heap), this, _module.Node.Repr))
           && !Set#Subset(read(old($Heap), this, _module.Node.Repr), 
            read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr));
        // ProcessCallStmt: Make the call
        call $rhs##0, $rhs##1 := Call$$_module.Node.RemoveMin(read($Heap, this, _module.Node.left));
        // TrCallStmt: After ProcessCallStmt
        min#0 := $rhs##0;
        t#0 := $rhs##1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(214,32)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(215,12)
        assume true;
        assert $_Frame[this, _module.Node.left];
        assume true;
        $rhs#0 := t#0;
        $Heap := update($Heap, this, _module.Node.left, $rhs#0);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(215,15)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(216,12)
        assume true;
        assume true;
        node#0 := this;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(216,18)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(217,16)
        assume true;
        assert $_Frame[this, _module.Node.Contents];
        assume true;
        $rhs#1 := Set#Difference(read($Heap, this, _module.Node.Contents), 
          Set#UnionOne(Set#Empty(): Set Box, $Box(min#0)));
        $Heap := update($Heap, this, _module.Node.Contents, $rhs#1);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(217,34)"} true;
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(218,7)
        assume true;
        if (read($Heap, this, _module.Node.left) != null)
        {
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(218,30)
            assume true;
            assert $_Frame[this, _module.Node.Repr];
            assert read($Heap, this, _module.Node.left) != null;
            assume true;
            $rhs#1_0 := Set#Union(read($Heap, this, _module.Node.Repr), 
              read($Heap, read($Heap, this, _module.Node.left), _module.Node.Repr));
            $Heap := update($Heap, this, _module.Node.Repr, $rhs#1_0);
            assume $IsGoodHeap($Heap);
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(218,48)"} true;
        }
        else
        {
        }
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

const unique class._module.Main?: ClassName;

function Tclass._module.Main?() : Ty;

const unique Tagclass._module.Main?: TyTag;

// Tclass._module.Main? Tag
axiom Tag(Tclass._module.Main?()) == Tagclass._module.Main?
   && TagFamily(Tclass._module.Main?()) == tytagFamily$Main;

// Box/unbox axiom for Tclass._module.Main?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Main?()) } 
  $IsBox(bx, Tclass._module.Main?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Main?()));

// Main: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.Main?()) } 
  $Is($o, Tclass._module.Main?())
     <==> $o == null || dtype($o) == Tclass._module.Main?());

// Main: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.Main?(), $h) } 
  $IsAlloc($o, Tclass._module.Main?(), $h) <==> $o == null || read($h, $o, alloc));

function Tclass._module.Main() : Ty;

const unique Tagclass._module.Main: TyTag;

// Tclass._module.Main Tag
axiom Tag(Tclass._module.Main()) == Tagclass._module.Main
   && TagFamily(Tclass._module.Main()) == tytagFamily$Main;

// Box/unbox axiom for Tclass._module.Main
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Main()) } 
  $IsBox(bx, Tclass._module.Main())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Main()));

procedure CheckWellformed$$_module.Main.Client0(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Main())
         && $IsAlloc(this, Tclass._module.Main(), $Heap), 
    x#0: int);
  free requires 14 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Main.Client0(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Main())
         && $IsAlloc(this, Tclass._module.Main(), $Heap), 
    x#0: int);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Main.Client0(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Main())
         && $IsAlloc(this, Tclass._module.Main(), $Heap), 
    x#0: int)
   returns ($_reverifyPost: bool);
  free requires 14 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Main.Client0(this: ref, x#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var s#0: ref
     where $Is(s#0, Tclass._module.IntSet())
       && $IsAlloc(s#0, Tclass._module.IntSet(), $Heap);
  var $nw: ref;
  var x##0: int;
  var x##1: int;
  var present#0: bool;
  var ##x#0: int;

    // AddMethodImpl: Client0, Impl$$_module.Main.Client0
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(225,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(226,11)
    assume true;
    // ----- init call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(226,25)
    // TrCallStmt: Before ProcessCallStmt
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $nw := Call$$_module.IntSet.Init();
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(226,30)"} true;
    s#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(226,30)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(228,13)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert s#0 != null;
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##0 := LitInt(12);
    assert (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && read($Heap, $o, alloc)
           && read($Heap, s#0, _module.IntSet.Repr)[$Box($o)]
         ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.IntSet.Insert(s#0, x##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(228,16)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(229,13)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert s#0 != null;
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##1 := LitInt(24);
    assert (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && read($Heap, $o, alloc)
           && read($Heap, s#0, _module.IntSet.Repr)[$Box($o)]
         ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.IntSet.Insert(s#0, x##1);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(229,16)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(230,17)
    assume true;
    assert s#0 != null;
    ##x#0 := x#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##x#0, TInt, $Heap);
    assert {:subsumption 0} _module.IntSet.Valid#canCall($Heap, s#0)
       ==> _module.IntSet.Valid($Heap, s#0)
         || read($Heap, s#0, _module.IntSet.Repr)[$Box(s#0)];
    assert {:subsumption 0} _module.IntSet.Valid#canCall($Heap, s#0)
       ==> _module.IntSet.Valid($Heap, s#0)
         || (read($Heap, s#0, _module.IntSet.root) == null
           ==> Set#Equal(read($Heap, s#0, _module.IntSet.Contents), Set#Empty(): Set Box));
    assert {:subsumption 0} _module.IntSet.Valid#canCall($Heap, s#0)
       ==> _module.IntSet.Valid($Heap, s#0)
         || (read($Heap, s#0, _module.IntSet.root) != null
           ==> read($Heap, s#0, _module.IntSet.Repr)[$Box(read($Heap, s#0, _module.IntSet.root))]);
    assert {:subsumption 0} _module.IntSet.Valid#canCall($Heap, s#0)
       ==> _module.IntSet.Valid($Heap, s#0)
         || (read($Heap, s#0, _module.IntSet.root) != null
           ==> Set#Subset(read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.Repr), 
            read($Heap, s#0, _module.IntSet.Repr)));
    assert {:subsumption 0} _module.IntSet.Valid#canCall($Heap, s#0)
       ==> _module.IntSet.Valid($Heap, s#0)
         || (read($Heap, s#0, _module.IntSet.root) != null
           ==> !read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.Repr)[$Box(s#0)]);
    assert {:subsumption 0} _module.IntSet.Valid#canCall($Heap, s#0)
       ==> _module.IntSet.Valid($Heap, s#0)
         || (read($Heap, s#0, _module.IntSet.root) != null
           ==> 
          _module.Node.Valid#canCall($Heap, read($Heap, s#0, _module.IntSet.root))
           ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, s#0, _module.IntSet.root))
             || read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.Repr)[$Box(read($Heap, s#0, _module.IntSet.root))]);
    assert {:subsumption 0} _module.IntSet.Valid#canCall($Heap, s#0)
       ==> _module.IntSet.Valid($Heap, s#0)
         || (read($Heap, s#0, _module.IntSet.root) != null
           ==> 
          _module.Node.Valid#canCall($Heap, read($Heap, s#0, _module.IntSet.root))
           ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, s#0, _module.IntSet.root))
             || (read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.left) != null
               ==> read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.Repr)[$Box(read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.left))]));
    assert {:subsumption 0} _module.IntSet.Valid#canCall($Heap, s#0)
       ==> _module.IntSet.Valid($Heap, s#0)
         || (read($Heap, s#0, _module.IntSet.root) != null
           ==> 
          _module.Node.Valid#canCall($Heap, read($Heap, s#0, _module.IntSet.root))
           ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, s#0, _module.IntSet.root))
             || (read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.left) != null
               ==> Set#Subset(read($Heap, 
                  read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.left), 
                  _module.Node.Repr), 
                read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.Repr))));
    assert {:subsumption 0} _module.IntSet.Valid#canCall($Heap, s#0)
       ==> _module.IntSet.Valid($Heap, s#0)
         || (read($Heap, s#0, _module.IntSet.root) != null
           ==> 
          _module.Node.Valid#canCall($Heap, read($Heap, s#0, _module.IntSet.root))
           ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, s#0, _module.IntSet.root))
             || (read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.left) != null
               ==> !read($Heap, 
                read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.left), 
                _module.Node.Repr)[$Box(read($Heap, s#0, _module.IntSet.root))]));
    assert {:subsumption 0} _module.IntSet.Valid#canCall($Heap, s#0)
       ==> _module.IntSet.Valid($Heap, s#0)
         || (read($Heap, s#0, _module.IntSet.root) != null
           ==> 
          _module.Node.Valid#canCall($Heap, read($Heap, s#0, _module.IntSet.root))
           ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, s#0, _module.IntSet.root))
             || (read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.left) != null
               ==> _module.Node.Valid($LS($LS($LZ)), 
                $Heap, 
                read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.left))));
    assert {:subsumption 0} _module.IntSet.Valid#canCall($Heap, s#0)
       ==> _module.IntSet.Valid($Heap, s#0)
         || (read($Heap, s#0, _module.IntSet.root) != null
           ==> 
          _module.Node.Valid#canCall($Heap, read($Heap, s#0, _module.IntSet.root))
           ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, s#0, _module.IntSet.root))
             || (read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.left) != null
               ==> (forall y#0: int :: 
                { read($Heap, 
                    read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.left), 
                    _module.Node.Contents)[$Box(y#0)] } 
                true
                   ==> 
                  read($Heap, 
                    read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.left), 
                    _module.Node.Contents)[$Box(y#0)]
                   ==> y#0 < read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.data))));
    assert {:subsumption 0} _module.IntSet.Valid#canCall($Heap, s#0)
       ==> _module.IntSet.Valid($Heap, s#0)
         || (read($Heap, s#0, _module.IntSet.root) != null
           ==> 
          _module.Node.Valid#canCall($Heap, read($Heap, s#0, _module.IntSet.root))
           ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, s#0, _module.IntSet.root))
             || (read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.right) != null
               ==> read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.Repr)[$Box(read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.right))]));
    assert {:subsumption 0} _module.IntSet.Valid#canCall($Heap, s#0)
       ==> _module.IntSet.Valid($Heap, s#0)
         || (read($Heap, s#0, _module.IntSet.root) != null
           ==> 
          _module.Node.Valid#canCall($Heap, read($Heap, s#0, _module.IntSet.root))
           ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, s#0, _module.IntSet.root))
             || (read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.right) != null
               ==> Set#Subset(read($Heap, 
                  read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.right), 
                  _module.Node.Repr), 
                read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.Repr))));
    assert {:subsumption 0} _module.IntSet.Valid#canCall($Heap, s#0)
       ==> _module.IntSet.Valid($Heap, s#0)
         || (read($Heap, s#0, _module.IntSet.root) != null
           ==> 
          _module.Node.Valid#canCall($Heap, read($Heap, s#0, _module.IntSet.root))
           ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, s#0, _module.IntSet.root))
             || (read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.right) != null
               ==> !read($Heap, 
                read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.right), 
                _module.Node.Repr)[$Box(read($Heap, s#0, _module.IntSet.root))]));
    assert {:subsumption 0} _module.IntSet.Valid#canCall($Heap, s#0)
       ==> _module.IntSet.Valid($Heap, s#0)
         || (read($Heap, s#0, _module.IntSet.root) != null
           ==> 
          _module.Node.Valid#canCall($Heap, read($Heap, s#0, _module.IntSet.root))
           ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, s#0, _module.IntSet.root))
             || (read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.right) != null
               ==> _module.Node.Valid($LS($LS($LZ)), 
                $Heap, 
                read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.right))));
    assert {:subsumption 0} _module.IntSet.Valid#canCall($Heap, s#0)
       ==> _module.IntSet.Valid($Heap, s#0)
         || (read($Heap, s#0, _module.IntSet.root) != null
           ==> 
          _module.Node.Valid#canCall($Heap, read($Heap, s#0, _module.IntSet.root))
           ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, s#0, _module.IntSet.root))
             || (read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.right) != null
               ==> (forall y#1: int :: 
                { read($Heap, 
                    read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.right), 
                    _module.Node.Contents)[$Box(y#1)] } 
                true
                   ==> 
                  read($Heap, 
                    read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.right), 
                    _module.Node.Contents)[$Box(y#1)]
                   ==> read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.data) < y#1)));
    assert {:subsumption 0} _module.IntSet.Valid#canCall($Heap, s#0)
       ==> _module.IntSet.Valid($Heap, s#0)
         || (read($Heap, s#0, _module.IntSet.root) != null
           ==> 
          _module.Node.Valid#canCall($Heap, read($Heap, s#0, _module.IntSet.root))
           ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, s#0, _module.IntSet.root))
             || (read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.left) == null
                 && read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.right) == null
               ==> Set#Equal(read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.Contents), 
                Set#UnionOne(Set#Empty(): Set Box, 
                  $Box(read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.data))))));
    assert {:subsumption 0} _module.IntSet.Valid#canCall($Heap, s#0)
       ==> _module.IntSet.Valid($Heap, s#0)
         || (read($Heap, s#0, _module.IntSet.root) != null
           ==> 
          _module.Node.Valid#canCall($Heap, read($Heap, s#0, _module.IntSet.root))
           ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, s#0, _module.IntSet.root))
             || (read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.left) != null
                 && read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.right) == null
               ==> Set#Equal(read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.Contents), 
                Set#Union(read($Heap, 
                    read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.left), 
                    _module.Node.Contents), 
                  Set#UnionOne(Set#Empty(): Set Box, 
                    $Box(read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.data)))))));
    assert {:subsumption 0} _module.IntSet.Valid#canCall($Heap, s#0)
       ==> _module.IntSet.Valid($Heap, s#0)
         || (read($Heap, s#0, _module.IntSet.root) != null
           ==> 
          _module.Node.Valid#canCall($Heap, read($Heap, s#0, _module.IntSet.root))
           ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, s#0, _module.IntSet.root))
             || (read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.left) == null
                 && read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.right) != null
               ==> Set#Equal(read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.Contents), 
                Set#Union(Set#UnionOne(Set#Empty(): Set Box, 
                    $Box(read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.data))), 
                  read($Heap, 
                    read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.right), 
                    _module.Node.Contents)))));
    assert {:subsumption 0} _module.IntSet.Valid#canCall($Heap, s#0)
       ==> _module.IntSet.Valid($Heap, s#0)
         || (read($Heap, s#0, _module.IntSet.root) != null
           ==> 
          _module.Node.Valid#canCall($Heap, read($Heap, s#0, _module.IntSet.root))
           ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, s#0, _module.IntSet.root))
             || (read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.left) != null
                 && read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.right) != null
               ==> Set#Disjoint(read($Heap, 
                  read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.left), 
                  _module.Node.Repr), 
                read($Heap, 
                  read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.right), 
                  _module.Node.Repr))));
    assert {:subsumption 0} _module.IntSet.Valid#canCall($Heap, s#0)
       ==> _module.IntSet.Valid($Heap, s#0)
         || (read($Heap, s#0, _module.IntSet.root) != null
           ==> 
          _module.Node.Valid#canCall($Heap, read($Heap, s#0, _module.IntSet.root))
           ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, s#0, _module.IntSet.root))
             || (read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.left) != null
                 && read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.right) != null
               ==> Set#Equal(read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.Contents), 
                Set#Union(Set#Union(read($Heap, 
                      read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.left), 
                      _module.Node.Contents), 
                    Set#UnionOne(Set#Empty(): Set Box, 
                      $Box(read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.data)))), 
                  read($Heap, 
                    read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.right), 
                    _module.Node.Contents)))));
    assert {:subsumption 0} _module.IntSet.Valid#canCall($Heap, s#0)
       ==> _module.IntSet.Valid($Heap, s#0)
         || (read($Heap, s#0, _module.IntSet.root) != null
           ==> Set#Equal(read($Heap, s#0, _module.IntSet.Contents), 
            read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.Contents)));
    assume _module.IntSet.Valid($Heap, s#0);
    assume _module.IntSet.Find#canCall($Heap, s#0, x#0);
    assume _module.IntSet.Find#canCall($Heap, s#0, x#0);
    present#0 := _module.IntSet.Find($Heap, s#0, x#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(230,28)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(231,5)
    if (x#0 != LitInt(12))
    {
    }

    assume true;
    assert present#0 <==> x#0 == LitInt(12) || x#0 == LitInt(24);
}



procedure CheckWellformed$$_module.Main.Client1(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Main())
         && $IsAlloc(this, Tclass._module.Main(), $Heap), 
    s#0: ref
       where $Is(s#0, Tclass._module.IntSet())
         && $IsAlloc(s#0, Tclass._module.IntSet(), $Heap), 
    x#0: int);
  free requires 7 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Main.Client1(this: ref, s#0: ref, x#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Client1, CheckWellformed$$_module.Main.Client1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, s#0, _module.IntSet.Repr)[$Box($o)]);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(234,9): initial state"} true;
    assert s#0 != null;
    assume _module.IntSet.Valid#canCall($Heap, s#0);
    assume _module.IntSet.Valid($Heap, s#0);
    assert s#0 != null;
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc)
         ==> $Heap[$o] == old($Heap)[$o]
           || read(old($Heap), s#0, _module.IntSet.Repr)[$Box($o)]);
    assume $HeapSucc(old($Heap), $Heap);
}



procedure Call$$_module.Main.Client1(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Main())
         && $IsAlloc(this, Tclass._module.Main(), $Heap), 
    s#0: ref
       where $Is(s#0, Tclass._module.IntSet())
         && $IsAlloc(s#0, Tclass._module.IntSet(), $Heap), 
    x#0: int);
  // user-defined preconditions
  requires _module.IntSet.Valid#canCall($Heap, s#0)
     ==> _module.IntSet.Valid($Heap, s#0)
       || read($Heap, s#0, _module.IntSet.Repr)[$Box(s#0)];
  requires _module.IntSet.Valid#canCall($Heap, s#0)
     ==> _module.IntSet.Valid($Heap, s#0)
       || (read($Heap, s#0, _module.IntSet.root) == null
         ==> Set#Equal(read($Heap, s#0, _module.IntSet.Contents), Set#Empty(): Set Box));
  requires _module.IntSet.Valid#canCall($Heap, s#0)
     ==> _module.IntSet.Valid($Heap, s#0)
       || (read($Heap, s#0, _module.IntSet.root) != null
         ==> read($Heap, s#0, _module.IntSet.Repr)[$Box(read($Heap, s#0, _module.IntSet.root))]);
  requires _module.IntSet.Valid#canCall($Heap, s#0)
     ==> _module.IntSet.Valid($Heap, s#0)
       || (read($Heap, s#0, _module.IntSet.root) != null
         ==> Set#Subset(read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.Repr), 
          read($Heap, s#0, _module.IntSet.Repr)));
  requires _module.IntSet.Valid#canCall($Heap, s#0)
     ==> _module.IntSet.Valid($Heap, s#0)
       || (read($Heap, s#0, _module.IntSet.root) != null
         ==> !read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.Repr)[$Box(s#0)]);
  requires _module.IntSet.Valid#canCall($Heap, s#0)
     ==> _module.IntSet.Valid($Heap, s#0)
       || (read($Heap, s#0, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, s#0, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, s#0, _module.IntSet.root))
           || read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.Repr)[$Box(read($Heap, s#0, _module.IntSet.root))]);
  requires _module.IntSet.Valid#canCall($Heap, s#0)
     ==> _module.IntSet.Valid($Heap, s#0)
       || (read($Heap, s#0, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, s#0, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, s#0, _module.IntSet.root))
           || (read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.left) != null
             ==> read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.Repr)[$Box(read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.left))]));
  requires _module.IntSet.Valid#canCall($Heap, s#0)
     ==> _module.IntSet.Valid($Heap, s#0)
       || (read($Heap, s#0, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, s#0, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, s#0, _module.IntSet.root))
           || (read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.left) != null
             ==> Set#Subset(read($Heap, 
                read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.left), 
                _module.Node.Repr), 
              read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.Repr))));
  requires _module.IntSet.Valid#canCall($Heap, s#0)
     ==> _module.IntSet.Valid($Heap, s#0)
       || (read($Heap, s#0, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, s#0, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, s#0, _module.IntSet.root))
           || (read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.left) != null
             ==> !read($Heap, 
              read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.left), 
              _module.Node.Repr)[$Box(read($Heap, s#0, _module.IntSet.root))]));
  requires _module.IntSet.Valid#canCall($Heap, s#0)
     ==> _module.IntSet.Valid($Heap, s#0)
       || (read($Heap, s#0, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, s#0, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, s#0, _module.IntSet.root))
           || (read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.left) != null
             ==> _module.Node.Valid($LS($LS($LZ)), 
              $Heap, 
              read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.left))));
  requires _module.IntSet.Valid#canCall($Heap, s#0)
     ==> _module.IntSet.Valid($Heap, s#0)
       || (read($Heap, s#0, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, s#0, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, s#0, _module.IntSet.root))
           || (read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.left) != null
             ==> (forall y#0: int :: 
              { read($Heap, 
                  read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.left), 
                  _module.Node.Contents)[$Box(y#0)] } 
              true
                 ==> 
                read($Heap, 
                  read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.left), 
                  _module.Node.Contents)[$Box(y#0)]
                 ==> y#0 < read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.data))));
  requires _module.IntSet.Valid#canCall($Heap, s#0)
     ==> _module.IntSet.Valid($Heap, s#0)
       || (read($Heap, s#0, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, s#0, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, s#0, _module.IntSet.root))
           || (read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.right) != null
             ==> read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.Repr)[$Box(read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.right))]));
  requires _module.IntSet.Valid#canCall($Heap, s#0)
     ==> _module.IntSet.Valid($Heap, s#0)
       || (read($Heap, s#0, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, s#0, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, s#0, _module.IntSet.root))
           || (read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.right) != null
             ==> Set#Subset(read($Heap, 
                read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.right), 
                _module.Node.Repr), 
              read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.Repr))));
  requires _module.IntSet.Valid#canCall($Heap, s#0)
     ==> _module.IntSet.Valid($Heap, s#0)
       || (read($Heap, s#0, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, s#0, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, s#0, _module.IntSet.root))
           || (read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.right) != null
             ==> !read($Heap, 
              read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.right), 
              _module.Node.Repr)[$Box(read($Heap, s#0, _module.IntSet.root))]));
  requires _module.IntSet.Valid#canCall($Heap, s#0)
     ==> _module.IntSet.Valid($Heap, s#0)
       || (read($Heap, s#0, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, s#0, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, s#0, _module.IntSet.root))
           || (read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.right) != null
             ==> _module.Node.Valid($LS($LS($LZ)), 
              $Heap, 
              read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.right))));
  requires _module.IntSet.Valid#canCall($Heap, s#0)
     ==> _module.IntSet.Valid($Heap, s#0)
       || (read($Heap, s#0, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, s#0, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, s#0, _module.IntSet.root))
           || (read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.right) != null
             ==> (forall y#1: int :: 
              { read($Heap, 
                  read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.right), 
                  _module.Node.Contents)[$Box(y#1)] } 
              true
                 ==> 
                read($Heap, 
                  read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.right), 
                  _module.Node.Contents)[$Box(y#1)]
                 ==> read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.data) < y#1)));
  requires _module.IntSet.Valid#canCall($Heap, s#0)
     ==> _module.IntSet.Valid($Heap, s#0)
       || (read($Heap, s#0, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, s#0, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, s#0, _module.IntSet.root))
           || (read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.left) == null
               && read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.right) == null
             ==> Set#Equal(read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.Contents), 
              Set#UnionOne(Set#Empty(): Set Box, 
                $Box(read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.data))))));
  requires _module.IntSet.Valid#canCall($Heap, s#0)
     ==> _module.IntSet.Valid($Heap, s#0)
       || (read($Heap, s#0, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, s#0, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, s#0, _module.IntSet.root))
           || (read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.left) != null
               && read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.right) == null
             ==> Set#Equal(read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.Contents), 
              Set#Union(read($Heap, 
                  read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.left), 
                  _module.Node.Contents), 
                Set#UnionOne(Set#Empty(): Set Box, 
                  $Box(read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.data)))))));
  requires _module.IntSet.Valid#canCall($Heap, s#0)
     ==> _module.IntSet.Valid($Heap, s#0)
       || (read($Heap, s#0, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, s#0, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, s#0, _module.IntSet.root))
           || (read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.left) == null
               && read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.right) != null
             ==> Set#Equal(read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.Contents), 
              Set#Union(Set#UnionOne(Set#Empty(): Set Box, 
                  $Box(read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.data))), 
                read($Heap, 
                  read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.right), 
                  _module.Node.Contents)))));
  requires _module.IntSet.Valid#canCall($Heap, s#0)
     ==> _module.IntSet.Valid($Heap, s#0)
       || (read($Heap, s#0, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, s#0, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, s#0, _module.IntSet.root))
           || (read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.left) != null
               && read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.right) != null
             ==> Set#Disjoint(read($Heap, 
                read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.left), 
                _module.Node.Repr), 
              read($Heap, 
                read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.right), 
                _module.Node.Repr))));
  requires _module.IntSet.Valid#canCall($Heap, s#0)
     ==> _module.IntSet.Valid($Heap, s#0)
       || (read($Heap, s#0, _module.IntSet.root) != null
         ==> 
        _module.Node.Valid#canCall($Heap, read($Heap, s#0, _module.IntSet.root))
         ==> _module.Node.Valid($LS($LZ), $Heap, read($Heap, s#0, _module.IntSet.root))
           || (read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.left) != null
               && read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.right) != null
             ==> Set#Equal(read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.Contents), 
              Set#Union(Set#Union(read($Heap, 
                    read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.left), 
                    _module.Node.Contents), 
                  Set#UnionOne(Set#Empty(): Set Box, 
                    $Box(read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.data)))), 
                read($Heap, 
                  read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.right), 
                  _module.Node.Contents)))));
  requires _module.IntSet.Valid#canCall($Heap, s#0)
     ==> _module.IntSet.Valid($Heap, s#0)
       || (read($Heap, s#0, _module.IntSet.root) != null
         ==> Set#Equal(read($Heap, s#0, _module.IntSet.Contents), 
          read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.Contents)));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || read(old($Heap), s#0, _module.IntSet.Repr)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Main.Client1(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Main())
         && $IsAlloc(this, Tclass._module.Main(), $Heap), 
    s#0: ref
       where $Is(s#0, Tclass._module.IntSet())
         && $IsAlloc(s#0, Tclass._module.IntSet(), $Heap), 
    x#0: int)
   returns ($_reverifyPost: bool);
  free requires 7 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.IntSet.Valid#canCall($Heap, s#0)
     && 
    _module.IntSet.Valid($Heap, s#0)
     && 
    read($Heap, s#0, _module.IntSet.Repr)[$Box(s#0)]
     && (read($Heap, s#0, _module.IntSet.root) == null
       ==> Set#Equal(read($Heap, s#0, _module.IntSet.Contents), Set#Empty(): Set Box))
     && (read($Heap, s#0, _module.IntSet.root) != null
       ==> read($Heap, s#0, _module.IntSet.Repr)[$Box(read($Heap, s#0, _module.IntSet.root))]
         && Set#Subset(read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.Repr), 
          read($Heap, s#0, _module.IntSet.Repr))
         && !read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.Repr)[$Box(s#0)]
         && _module.Node.Valid($LS($LZ), $Heap, read($Heap, s#0, _module.IntSet.root))
         && Set#Equal(read($Heap, s#0, _module.IntSet.Contents), 
          read($Heap, read($Heap, s#0, _module.IntSet.root), _module.Node.Contents)));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || read(old($Heap), s#0, _module.IntSet.Repr)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Main.Client1(this: ref, s#0: ref, x#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var x##0: int;
  var x##1: int;

    // AddMethodImpl: Client1, Impl$$_module.Main.Client1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, s#0, _module.IntSet.Repr)[$Box($o)]);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(237,2): initial state"} true;
    $_reverifyPost := false;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(238,13)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert s#0 != null;
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##0 := x#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && read($Heap, $o, alloc)
           && read($Heap, s#0, _module.IntSet.Repr)[$Box($o)]
         ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.IntSet.Insert(s#0, x##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(238,15)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(239,13)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert s#0 != null;
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##1 := LitInt(24);
    assert (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && read($Heap, $o, alloc)
           && read($Heap, s#0, _module.IntSet.Repr)[$Box($o)]
         ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.IntSet.Insert(s#0, x##1);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(239,16)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/BinaryTree.dfy(240,5)
    assert {:subsumption 0} s#0 != null;
    assert $IsAlloc(s#0, Tclass._module.IntSet(), old($Heap));
    assert {:subsumption 0} s#0 != null;
    assume true;
    assert Set#Equal(Set#Difference(read(old($Heap), s#0, _module.IntSet.Contents), 
        Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(x#0)), $Box(LitInt(24)))), 
      Set#Difference(read($Heap, s#0, _module.IntSet.Contents), 
        Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(x#0)), $Box(LitInt(24)))));
}



// _module.Main: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.Main()) } 
  $Is(c#0, Tclass._module.Main())
     <==> $Is(c#0, Tclass._module.Main?()) && c#0 != null);

// _module.Main: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.Main(), $h) } 
  $IsAlloc(c#0, Tclass._module.Main(), $h)
     <==> $IsAlloc(c#0, Tclass._module.Main?(), $h));

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

const unique tytagFamily$_tuple#2: TyTagFamily;

const unique tytagFamily$_tuple#0: TyTagFamily;

const unique tytagFamily$IntSet: TyTagFamily;

const unique tytagFamily$Node: TyTagFamily;

const unique tytagFamily$Main: TyTagFamily;

const unique tytagFamily$_default: TyTagFamily;

const unique field$Contents: NameFamily;

const unique field$Repr: NameFamily;

const unique field$root: NameFamily;

const unique field$left: NameFamily;

const unique field$data: NameFamily;

const unique field$right: NameFamily;
