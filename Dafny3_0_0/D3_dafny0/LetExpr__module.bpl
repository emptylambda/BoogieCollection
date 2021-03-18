// Dafny 3.0.0.30204
// Command Line Options: -compile:0 -noVerify /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy -print:./LetExpr.bpl

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

const unique class._module.AClass?: ClassName;

function Tclass._module.AClass?() : Ty;

const unique Tagclass._module.AClass?: TyTag;

// Tclass._module.AClass? Tag
axiom Tag(Tclass._module.AClass?()) == Tagclass._module.AClass?
   && TagFamily(Tclass._module.AClass?()) == tytagFamily$AClass;

// Box/unbox axiom for Tclass._module.AClass?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.AClass?()) } 
  $IsBox(bx, Tclass._module.AClass?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.AClass?()));

// AClass: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.AClass?()) } 
  $Is($o, Tclass._module.AClass?())
     <==> $o == null || dtype($o) == Tclass._module.AClass?());

// AClass: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.AClass?(), $h) } 
  $IsAlloc($o, Tclass._module.AClass?(), $h)
     <==> $o == null || read($h, $o, alloc));

axiom FDim(_module.AClass.index) == 0
   && FieldOfDecl(class._module.AClass?, field$index) == _module.AClass.index
   && !$IsGhostField(_module.AClass.index);

const _module.AClass.index: Field int;

// AClass.index: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.AClass.index) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.AClass?()
     ==> $Is(read($h, $o, _module.AClass.index), TInt));

// AClass.index: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.AClass.index) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.AClass?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.AClass.index), TInt, $h));

function Tclass._module.AClass() : Ty;

const unique Tagclass._module.AClass: TyTag;

// Tclass._module.AClass Tag
axiom Tag(Tclass._module.AClass()) == Tagclass._module.AClass
   && TagFamily(Tclass._module.AClass()) == tytagFamily$AClass;

// Box/unbox axiom for Tclass._module.AClass
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.AClass()) } 
  $IsBox(bx, Tclass._module.AClass())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.AClass()));

procedure CheckWellformed$$_module.AClass.P(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AClass())
         && $IsAlloc(this, Tclass._module.AClass(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._System.array(TInt))
         && $IsAlloc(a#0, Tclass._System.array(TInt), $Heap))
   returns (b#0: bool, ii#0: int);
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.AClass.P(this: ref, a#0: ref) returns (b#0: bool, ii#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var k#0: int;
  var newIndex#Z#0: int;
  var let#0#0#0: int;
  var oldIndex#Z#0: int;
  var let#1#0#0: int;
  var oi#Z#0: int;
  var let#2#0#0: int;

    // AddMethodImpl: P, CheckWellformed$$_module.AClass.P
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this || $o == a#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(71,9): initial state"} true;
    havoc k#0;
    assume true;
    assume LitInt(0) <= k#0;
    assert a#0 != null;
    assume k#0 < _System.array.Length(a#0);
    assert a#0 != null;
    assert 0 <= k#0 && k#0 < _System.array.Length(a#0);
    assume $Unbox(read($Heap, a#0, IndexField(k#0))): int == LitInt(19);
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc)
         ==> $Heap[$o] == old($Heap)[$o] || $o == this || $o == a#0);
    assume $HeapSucc(old($Heap), $Heap);
    havoc b#0, ii#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(74,15): post-state"} true;
    assume ii#0 == read($Heap, this, _module.AClass.index);
    if (LitInt(0) <= read($Heap, this, _module.AClass.index))
    {
        assert a#0 != null;
    }

    assume LitInt(0) <= read($Heap, this, _module.AClass.index)
       && read($Heap, this, _module.AClass.index) < _System.array.Length(a#0);
    assert a#0 != null;
    assert $IsAlloc(a#0, Tclass._System.array?(TInt), old($Heap));
    assert 0 <= ii#0 && ii#0 < _System.array.Length(a#0);
    assume $Unbox(read(old($Heap), a#0, IndexField(ii#0))): int == LitInt(19);
    if (LitInt(0) <= read($Heap, this, _module.AClass.index))
    {
        assert a#0 != null;
    }

    assume LitInt(0) <= read($Heap, this, _module.AClass.index)
       && read($Heap, this, _module.AClass.index) < _System.array.Length(a#0);
    havoc newIndex#Z#0;
    assume true;
    assume let#0#0#0 == read($Heap, this, _module.AClass.index);
    assume true;
    // CheckWellformedWithResult: any expression
    assume $Is(let#0#0#0, TInt);
    assume newIndex#Z#0 == let#0#0#0;
    assert a#0 != null;
    assert $IsAlloc(a#0, Tclass._System.array?(TInt), old($Heap));
    assert 0 <= newIndex#Z#0 && newIndex#Z#0 < _System.array.Length(a#0);
    assume (var newIndex#0 := read($Heap, this, _module.AClass.index); 
      $Unbox(read(old($Heap), a#0, IndexField(newIndex#0))): int == LitInt(19));
    if (*)
    {
        assume b#0;
        havoc oldIndex#Z#0;
        assume true;
        assert $IsAlloc(this, Tclass._module.AClass(), old($Heap));
        assume let#1#0#0 == read(old($Heap), this, _module.AClass.index);
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#1#0#0, TInt);
        assume oldIndex#Z#0 == let#1#0#0;
        if (LitInt(0) <= oldIndex#Z#0)
        {
            assert a#0 != null;
            assert $IsAlloc(a#0, Tclass._System.array(TInt), old($Heap));
        }

        if (LitInt(0) <= oldIndex#Z#0 && oldIndex#Z#0 < _System.array.Length(a#0))
        {
            assert a#0 != null;
            assert $IsAlloc(a#0, Tclass._System.array?(TInt), old($Heap));
            assert 0 <= oldIndex#Z#0 && oldIndex#Z#0 < _System.array.Length(a#0);
        }

        assume (var oldIndex#0 := read(old($Heap), this, _module.AClass.index); 
          LitInt(0) <= oldIndex#0
             && oldIndex#0 < _System.array.Length(a#0)
             && $Unbox(read(old($Heap), a#0, IndexField(oldIndex#0))): int == LitInt(17));
    }
    else
    {
        assume b#0
           ==> (var oldIndex#0 := read(old($Heap), this, _module.AClass.index); 
            LitInt(0) <= oldIndex#0
               && oldIndex#0 < _System.array.Length(a#0)
               && $Unbox(read(old($Heap), a#0, IndexField(oldIndex#0))): int == LitInt(17));
    }

    havoc oi#Z#0;
    assume true;
    assert $IsAlloc(this, Tclass._module.AClass(), old($Heap));
    assume let#2#0#0 == read(old($Heap), this, _module.AClass.index);
    assume true;
    // CheckWellformedWithResult: any expression
    assume $Is(let#2#0#0, TInt);
    assume oi#Z#0 == let#2#0#0;
    if (oi#Z#0 == read($Heap, this, _module.AClass.index))
    {
        assert a#0 != null;
        assert 0 <= oi#Z#0 && oi#Z#0 < _System.array.Length(a#0);
        if ($Unbox(read($Heap, a#0, IndexField(oi#Z#0))): int == LitInt(21))
        {
            assert a#0 != null;
            assert $IsAlloc(a#0, Tclass._System.array?(TInt), old($Heap));
            assert 0 <= oi#Z#0 && oi#Z#0 < _System.array.Length(a#0);
        }
    }

    assume (var oi#0 := read(old($Heap), this, _module.AClass.index); 
      oi#0 == read($Heap, this, _module.AClass.index)
         ==> $Unbox(read($Heap, a#0, IndexField(oi#0))): int == LitInt(21)
           && $Unbox(read(old($Heap), a#0, IndexField(oi#0))): int == LitInt(19));
}



procedure Call$$_module.AClass.P(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AClass())
         && $IsAlloc(this, Tclass._module.AClass(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._System.array(TInt))
         && $IsAlloc(a#0, Tclass._System.array(TInt), $Heap))
   returns (b#0: bool, ii#0: int);
  // user-defined preconditions
  requires (exists k#1: int :: 
    { $Unbox(read($Heap, a#0, IndexField(k#1))): int } 
    LitInt(0) <= k#1
       && k#1 < _System.array.Length(a#0)
       && $Unbox(read($Heap, a#0, IndexField(k#1))): int == LitInt(19));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures ii#0 == read($Heap, this, _module.AClass.index);
  free ensures true;
  ensures LitInt(0) <= read($Heap, this, _module.AClass.index);
  ensures read($Heap, this, _module.AClass.index) < _System.array.Length(a#0);
  ensures $Unbox(read(old($Heap), a#0, IndexField(ii#0))): int == LitInt(19);
  free ensures true;
  ensures LitInt(0) <= read($Heap, this, _module.AClass.index);
  ensures read($Heap, this, _module.AClass.index) < _System.array.Length(a#0);
  ensures (var newIndex#0 := read($Heap, this, _module.AClass.index); 
    $Unbox(read(old($Heap), a#0, IndexField(newIndex#0))): int == LitInt(19));
  free ensures true;
  ensures b#0
     ==> (var oldIndex#0 := read(old($Heap), this, _module.AClass.index); 
      LitInt(0) <= oldIndex#0);
  ensures b#0
     ==> (var oldIndex#0 := read(old($Heap), this, _module.AClass.index); 
      oldIndex#0 < _System.array.Length(a#0));
  ensures b#0
     ==> (var oldIndex#0 := read(old($Heap), this, _module.AClass.index); 
      $Unbox(read(old($Heap), a#0, IndexField(oldIndex#0))): int == LitInt(17));
  free ensures true;
  ensures (var oi#0 := read(old($Heap), this, _module.AClass.index); 
    oi#0 == read($Heap, this, _module.AClass.index)
       ==> $Unbox(read($Heap, a#0, IndexField(oi#0))): int == LitInt(21));
  ensures (var oi#0 := read(old($Heap), this, _module.AClass.index); 
    oi#0 == read($Heap, this, _module.AClass.index)
       ==> $Unbox(read(old($Heap), a#0, IndexField(oi#0))): int == LitInt(19));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this || $o == a#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.AClass.P(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AClass())
         && $IsAlloc(this, Tclass._module.AClass(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._System.array(TInt))
         && $IsAlloc(a#0, Tclass._System.array(TInt), $Heap))
   returns (b#0: bool, ii#0: int, $_reverifyPost: bool);
  free requires 1 == $FunctionContextHeight;
  // user-defined preconditions
  requires (exists k#1: int :: 
    { $Unbox(read($Heap, a#0, IndexField(k#1))): int } 
    LitInt(0) <= k#1
       && k#1 < _System.array.Length(a#0)
       && $Unbox(read($Heap, a#0, IndexField(k#1))): int == LitInt(19));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures ii#0 == read($Heap, this, _module.AClass.index);
  free ensures true;
  ensures LitInt(0) <= read($Heap, this, _module.AClass.index);
  ensures read($Heap, this, _module.AClass.index) < _System.array.Length(a#0);
  ensures $Unbox(read(old($Heap), a#0, IndexField(ii#0))): int == LitInt(19);
  free ensures true;
  ensures LitInt(0) <= read($Heap, this, _module.AClass.index);
  ensures read($Heap, this, _module.AClass.index) < _System.array.Length(a#0);
  ensures (var newIndex#0 := read($Heap, this, _module.AClass.index); 
    $Unbox(read(old($Heap), a#0, IndexField(newIndex#0))): int == LitInt(19));
  free ensures true;
  ensures b#0
     ==> (var oldIndex#0 := read(old($Heap), this, _module.AClass.index); 
      LitInt(0) <= oldIndex#0);
  ensures b#0
     ==> (var oldIndex#0 := read(old($Heap), this, _module.AClass.index); 
      oldIndex#0 < _System.array.Length(a#0));
  ensures b#0
     ==> (var oldIndex#0 := read(old($Heap), this, _module.AClass.index); 
      $Unbox(read(old($Heap), a#0, IndexField(oldIndex#0))): int == LitInt(17));
  free ensures true;
  ensures (var oi#0 := read(old($Heap), this, _module.AClass.index); 
    oi#0 == read($Heap, this, _module.AClass.index)
       ==> $Unbox(read($Heap, a#0, IndexField(oi#0))): int == LitInt(21));
  ensures (var oi#0 := read(old($Heap), this, _module.AClass.index); 
    oi#0 == read($Heap, this, _module.AClass.index)
       ==> $Unbox(read(old($Heap), a#0, IndexField(oi#0))): int == LitInt(19));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this || $o == a#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.AClass.P(this: ref, a#0: ref) returns (b#0: bool, ii#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var i#0: int;
  var j#0: int;
  var $rhs#0: int;
  var $rhs#1: int;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var k#2: int;
  var k#4: int;
  var k#6: int;
  var $decr$loop#00: int;
  var $obj1: ref;
  var $index1: Field Box;
  var $rhs#0_0: int;
  var $rhs#0_1: int;
  var $rhs#2: int;

    // AddMethodImpl: P, Impl$$_module.AClass.P
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this || $o == a#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(83,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(84,7)
    assume true;
    if (LitInt(0) <= read($Heap, this, _module.AClass.index))
    {
        assert a#0 != null;
    }

    if (LitInt(0) <= read($Heap, this, _module.AClass.index)
       && read($Heap, this, _module.AClass.index) < _System.array.Length(a#0))
    {
        assert a#0 != null;
        assert 0 <= read($Heap, this, _module.AClass.index)
           && read($Heap, this, _module.AClass.index) < _System.array.Length(a#0);
    }

    assume true;
    b#0 := LitInt(0) <= read($Heap, this, _module.AClass.index)
       && read($Heap, this, _module.AClass.index) < _System.array.Length(a#0)
       && $Unbox(read($Heap, a#0, IndexField(read($Heap, this, _module.AClass.index)))): int
         == LitInt(17);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(84,48)"} true;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(85,14)
    assume true;
    assume true;
    assume true;
    $rhs#0 := LitInt(0);
    assume true;
    $rhs#1 := LitInt(-1);
    i#0 := $rhs#0;
    j#0 := $rhs#1;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(85,21)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(86,5)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := _System.array.Length(a#0) - i#0;
    havoc $w$loop#0;
    while (true)
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> LitInt(0) <= i#0;
      invariant $w$loop#0 ==> i#0 <= _System.array.Length(a#0);
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0
         ==> (forall k#3: int :: 
          { $Unbox(read($Heap, a#0, IndexField(k#3))): int } 
          true
             ==> 
            LitInt(0) <= k#3 && k#3 < i#0
             ==> $Unbox(read($Heap, a#0, IndexField(k#3))): int == LitInt(21));
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0
         ==> (forall k#5: int :: 
          { $Unbox(read(old($Heap), a#0, IndexField(k#5))): int } 
            { $Unbox(read($Heap, a#0, IndexField(k#5))): int } 
          true
             ==> 
            i#0 <= k#5 && k#5 < _System.array.Length(a#0)
             ==> $Unbox(read($Heap, a#0, IndexField(k#5))): int
               == $Unbox(read(old($Heap), a#0, IndexField(k#5))): int);
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0
         ==> (
            LitInt(0) <= j#0
             && j#0 < i#0
             && $Unbox(read(old($Heap), a#0, IndexField(j#0))): int == LitInt(19))
           || (j#0 == LitInt(-1)
             && (exists k#7: int :: 
              { $Unbox(read($Heap, a#0, IndexField(k#7))): int } 
              i#0 <= k#7
                 && k#7 < _System.array.Length(a#0)
                 && $Unbox(read($Heap, a#0, IndexField(k#7))): int == LitInt(19)));
      free invariant (forall $o: ref :: 
        { $Heap[$o] } 
        $o != null && read(old($Heap), $o, alloc)
           ==> $Heap[$o] == $PreLoopHeap$loop#0[$o] || $o == this || $o == a#0);
      free invariant $HeapSucc($PreLoopHeap$loop#0, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
        { read($Heap, $o, $f) } 
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
      free invariant _System.array.Length(a#0) - i#0 <= $decr_init$loop#00
         && (_System.array.Length(a#0) - i#0 == $decr_init$loop#00 ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(86,4): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            if (LitInt(0) <= i#0)
            {
                assert {:subsumption 0} a#0 != null;
            }

            assume true;
            assume LitInt(0) <= i#0 && i#0 <= _System.array.Length(a#0);
            // Begin Comprehension WF check
            havoc k#2;
            if (true)
            {
                if (LitInt(0) <= k#2)
                {
                }

                if (LitInt(0) <= k#2 && k#2 < i#0)
                {
                    assert a#0 != null;
                    assert {:subsumption 0} 0 <= k#2 && k#2 < _System.array.Length(a#0);
                }
            }

            // End Comprehension WF check
            assume true;
            assume (forall k#3: int :: 
              { $Unbox(read($Heap, a#0, IndexField(k#3))): int } 
              true
                 ==> 
                LitInt(0) <= k#3 && k#3 < i#0
                 ==> $Unbox(read($Heap, a#0, IndexField(k#3))): int == LitInt(21));
            // Begin Comprehension WF check
            havoc k#4;
            if (true)
            {
                if (i#0 <= k#4)
                {
                    assert {:subsumption 0} a#0 != null;
                }

                if (i#0 <= k#4 && k#4 < _System.array.Length(a#0))
                {
                    assert a#0 != null;
                    assert {:subsumption 0} 0 <= k#4 && k#4 < _System.array.Length(a#0);
                    assert a#0 != null;
                    assert $IsAlloc(a#0, Tclass._System.array?(TInt), old($Heap));
                    assert {:subsumption 0} 0 <= k#4 && k#4 < _System.array.Length(a#0);
                }
            }

            // End Comprehension WF check
            assume true;
            assume (forall k#5: int :: 
              { $Unbox(read(old($Heap), a#0, IndexField(k#5))): int } 
                { $Unbox(read($Heap, a#0, IndexField(k#5))): int } 
              true
                 ==> 
                i#0 <= k#5 && k#5 < _System.array.Length(a#0)
                 ==> $Unbox(read($Heap, a#0, IndexField(k#5))): int
                   == $Unbox(read(old($Heap), a#0, IndexField(k#5))): int);
            if (LitInt(0) <= j#0)
            {
            }

            if (LitInt(0) <= j#0 && j#0 < i#0)
            {
                assert a#0 != null;
                assert $IsAlloc(a#0, Tclass._System.array?(TInt), old($Heap));
                assert {:subsumption 0} 0 <= j#0 && j#0 < _System.array.Length(a#0);
            }

            if (!(
              LitInt(0) <= j#0
               && j#0 < i#0
               && $Unbox(read(old($Heap), a#0, IndexField(j#0))): int == LitInt(19)))
            {
                if (j#0 == LitInt(-1))
                {
                    // Begin Comprehension WF check
                    havoc k#6;
                    if (true)
                    {
                        if (i#0 <= k#6)
                        {
                            assert {:subsumption 0} a#0 != null;
                        }

                        if (i#0 <= k#6 && k#6 < _System.array.Length(a#0))
                        {
                            assert a#0 != null;
                            assert {:subsumption 0} 0 <= k#6 && k#6 < _System.array.Length(a#0);
                        }
                    }

                    // End Comprehension WF check
                }
            }

            assume true;
            assume (
                LitInt(0) <= j#0
                 && j#0 < i#0
                 && $Unbox(read(old($Heap), a#0, IndexField(j#0))): int == LitInt(19))
               || (j#0 == LitInt(-1)
                 && (exists k#7: int :: 
                  { $Unbox(read($Heap, a#0, IndexField(k#7))): int } 
                  i#0 <= k#7
                     && k#7 < _System.array.Length(a#0)
                     && $Unbox(read($Heap, a#0, IndexField(k#7))): int == LitInt(19)));
            assert a#0 != null;
            assume true;
            assume false;
        }

        assert a#0 != null;
        assume true;
        if (_System.array.Length(a#0) <= i#0)
        {
            break;
        }

        $decr$loop#00 := _System.array.Length(a#0) - i#0;
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(93,7)
        assert a#0 != null;
        assert 0 <= i#0 && i#0 < _System.array.Length(a#0);
        assume true;
        if ($Unbox(read($Heap, a#0, IndexField(i#0))): int == LitInt(19))
        {
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(93,27)
            assume true;
            assume true;
            j#0 := i#0;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(93,30)"} true;
        }
        else
        {
        }

        // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(94,15)
        assume true;
        assert a#0 != null;
        assert 0 <= i#0 && i#0 < _System.array.Length(a#0);
        assume true;
        $obj1 := a#0;
        $index1 := IndexField(i#0);
        assert $_Frame[$obj1, $index1];
        assume true;
        $rhs#0_0 := i#0 + 1;
        assume true;
        $rhs#0_1 := LitInt(21);
        i#0 := $rhs#0_0;
        $Heap := update($Heap, $obj1, $index1, $Box($rhs#0_1));
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(94,26)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(86,5)
        assert 0 <= $decr$loop#00 || _System.array.Length(a#0) - i#0 == $decr$loop#00;
        assert _System.array.Length(a#0) - i#0 < $decr$loop#00;
        assume true;
        assume true;
        assume true;
        assume true;
    }

    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(96,11)
    assume true;
    assert $_Frame[this, _module.AClass.index];
    assume true;
    $rhs#2 := j#0;
    $Heap := update($Heap, this, _module.AClass.index, $rhs#2);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(96,14)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(97,8)
    assume true;
    assume true;
    ii#0 := read($Heap, this, _module.AClass.index);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(97,15)"} true;
}



procedure CheckWellformed$$_module.AClass.PMain(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AClass())
         && $IsAlloc(this, Tclass._module.AClass(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._System.array(TInt))
         && $IsAlloc(a#0, Tclass._System.array(TInt), $Heap));
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.AClass.PMain(this: ref, a#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var k#0: int;

    // AddMethodImpl: PMain, CheckWellformed$$_module.AClass.PMain
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this || $o == a#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(100,9): initial state"} true;
    havoc k#0;
    assume true;
    assume LitInt(0) <= k#0;
    assert a#0 != null;
    assume k#0 < _System.array.Length(a#0);
    assert a#0 != null;
    assert 0 <= k#0 && k#0 < _System.array.Length(a#0);
    assume $Unbox(read($Heap, a#0, IndexField(k#0))): int == LitInt(19);
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc)
         ==> $Heap[$o] == old($Heap)[$o] || $o == this || $o == a#0);
    assume $HeapSucc(old($Heap), $Heap);
}



procedure Call$$_module.AClass.PMain(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AClass())
         && $IsAlloc(this, Tclass._module.AClass(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._System.array(TInt))
         && $IsAlloc(a#0, Tclass._System.array(TInt), $Heap));
  // user-defined preconditions
  requires (exists k#1: int :: 
    { $Unbox(read($Heap, a#0, IndexField(k#1))): int } 
    LitInt(0) <= k#1
       && k#1 < _System.array.Length(a#0)
       && $Unbox(read($Heap, a#0, IndexField(k#1))): int == LitInt(19));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this || $o == a#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.AClass.PMain(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AClass())
         && $IsAlloc(this, Tclass._module.AClass(), $Heap), 
    a#0: ref
       where $Is(a#0, Tclass._System.array(TInt))
         && $IsAlloc(a#0, Tclass._System.array(TInt), $Heap))
   returns ($_reverifyPost: bool);
  free requires 2 == $FunctionContextHeight;
  // user-defined preconditions
  requires (exists k#1: int :: 
    { $Unbox(read($Heap, a#0, IndexField(k#1))): int } 
    LitInt(0) <= k#1
       && k#1 < _System.array.Length(a#0)
       && $Unbox(read($Heap, a#0, IndexField(k#1))): int == LitInt(19));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this || $o == a#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.AClass.PMain(this: ref, a#0: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var s#0: Seq Box where $Is(s#0, TSeq(TInt)) && $IsAlloc(s#0, TSeq(TInt), $Heap);
  var b17#0: bool;
  var ii#0: int;
  var $rhs##0: bool;
  var $rhs##1: int;
  var a##0: ref;

    // AddMethodImpl: PMain, Impl$$_module.AClass.PMain
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this || $o == a#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(103,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(104,11)
    assume true;
    assert a#0 != null;
    assume true;
    s#0 := Seq#FromArray($Heap, a#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(104,18)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(105,21)
    assume true;
    assume true;
    // TrCallStmt: Adding lhs with type bool
    // TrCallStmt: Adding lhs with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##0 := a#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) && ($o == this || $o == a##0)
         ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0, $rhs##1 := Call$$_module.AClass.P(this, a##0);
    // TrCallStmt: After ProcessCallStmt
    b17#0 := $rhs##0;
    ii#0 := $rhs##1;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(105,23)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(106,5)
    assert a#0 != null;
    assert $IsAlloc(a#0, Tclass._System.array?(TInt), old($Heap));
    assume true;
    assert Seq#Equal(s#0, Seq#FromArray(old($Heap), a#0));
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(107,5)
    assert {:subsumption 0} 0 <= read($Heap, this, _module.AClass.index)
       && read($Heap, this, _module.AClass.index) < Seq#Length(s#0);
    assume true;
    assert $Unbox(Seq#Index(s#0, read($Heap, this, _module.AClass.index))): int
       == LitInt(19);
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(108,5)
    if (*)
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(109,7)
        assert a#0 != null;
        assert {:subsumption 0} 0 <= read($Heap, this, _module.AClass.index)
           && read($Heap, this, _module.AClass.index) < _System.array.Length(a#0);
        assume true;
        assert $Unbox(read($Heap, a#0, IndexField(read($Heap, this, _module.AClass.index)))): int
           == LitInt(19);
    }
    else
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(111,7)
        if (b17#0)
        {
            assert $IsAlloc(this, Tclass._module.AClass(), old($Heap));
            if (LitInt(0) <= read(old($Heap), this, _module.AClass.index))
            {
                assert $IsAlloc(this, Tclass._module.AClass(), old($Heap));
                assert {:subsumption 0} a#0 != null;
            }

            if (LitInt(0) <= read(old($Heap), this, _module.AClass.index)
               && read(old($Heap), this, _module.AClass.index) < _System.array.Length(a#0))
            {
                assert a#0 != null;
                assert $IsAlloc(a#0, Tclass._System.array?(TInt), old($Heap));
                assert $IsAlloc(this, Tclass._module.AClass(), old($Heap));
                assert {:subsumption 0} 0 <= read(old($Heap), this, _module.AClass.index)
                   && read(old($Heap), this, _module.AClass.index) < _System.array.Length(a#0);
            }
        }

        assume true;
        assert {:subsumption 0} b17#0 ==> LitInt(0) <= read(old($Heap), this, _module.AClass.index);
        assert {:subsumption 0} b17#0
           ==> read(old($Heap), this, _module.AClass.index) < _System.array.Length(a#0);
        assert {:subsumption 0} b17#0
           ==> $Unbox(read(old($Heap), a#0, IndexField(read(old($Heap), this, _module.AClass.index)))): int
             == LitInt(17);
        assume b17#0
           ==> LitInt(0) <= read(old($Heap), this, _module.AClass.index)
             && read(old($Heap), this, _module.AClass.index) < _System.array.Length(a#0)
             && $Unbox(read(old($Heap), a#0, IndexField(read(old($Heap), this, _module.AClass.index)))): int
               == LitInt(17);
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(112,7)
        assert $IsAlloc(this, Tclass._module.AClass(), old($Heap));
        if (read($Heap, this, _module.AClass.index)
           == read(old($Heap), this, _module.AClass.index))
        {
            assert a#0 != null;
            assert {:subsumption 0} 0 <= read($Heap, this, _module.AClass.index)
               && read($Heap, this, _module.AClass.index) < _System.array.Length(a#0);
            if ($Unbox(read($Heap, a#0, IndexField(read($Heap, this, _module.AClass.index)))): int
               == LitInt(21))
            {
                assert a#0 != null;
                assert $IsAlloc(a#0, Tclass._System.array?(TInt), old($Heap));
                assert $IsAlloc(this, Tclass._module.AClass(), old($Heap));
                assert {:subsumption 0} 0 <= read(old($Heap), this, _module.AClass.index)
                   && read(old($Heap), this, _module.AClass.index) < _System.array.Length(a#0);
            }
        }

        assume true;
        assert {:subsumption 0} read($Heap, this, _module.AClass.index)
             == read(old($Heap), this, _module.AClass.index)
           ==> $Unbox(read($Heap, a#0, IndexField(read($Heap, this, _module.AClass.index)))): int
             == LitInt(21);
        assert {:subsumption 0} read($Heap, this, _module.AClass.index)
             == read(old($Heap), this, _module.AClass.index)
           ==> $Unbox(read(old($Heap), a#0, IndexField(read(old($Heap), this, _module.AClass.index)))): int
             == LitInt(19);
        assume read($Heap, this, _module.AClass.index)
             == read(old($Heap), this, _module.AClass.index)
           ==> $Unbox(read($Heap, a#0, IndexField(read($Heap, this, _module.AClass.index)))): int
               == LitInt(21)
             && $Unbox(read(old($Heap), a#0, IndexField(read(old($Heap), this, _module.AClass.index)))): int
               == LitInt(19);
    }
}



// _module.AClass: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.AClass()) } 
  $Is(c#0, Tclass._module.AClass())
     <==> $Is(c#0, Tclass._module.AClass?()) && c#0 != null);

// _module.AClass: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.AClass(), $h) } 
  $IsAlloc(c#0, Tclass._module.AClass(), $h)
     <==> $IsAlloc(c#0, Tclass._module.AClass?(), $h));

const unique class._module.TrickySubstitution?: ClassName;

function Tclass._module.TrickySubstitution?() : Ty;

const unique Tagclass._module.TrickySubstitution?: TyTag;

// Tclass._module.TrickySubstitution? Tag
axiom Tag(Tclass._module.TrickySubstitution?())
     == Tagclass._module.TrickySubstitution?
   && TagFamily(Tclass._module.TrickySubstitution?())
     == tytagFamily$TrickySubstitution;

// Box/unbox axiom for Tclass._module.TrickySubstitution?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.TrickySubstitution?()) } 
  $IsBox(bx, Tclass._module.TrickySubstitution?())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.TrickySubstitution?()));

// TrickySubstitution: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.TrickySubstitution?()) } 
  $Is($o, Tclass._module.TrickySubstitution?())
     <==> $o == null || dtype($o) == Tclass._module.TrickySubstitution?());

// TrickySubstitution: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.TrickySubstitution?(), $h) } 
  $IsAlloc($o, Tclass._module.TrickySubstitution?(), $h)
     <==> $o == null || read($h, $o, alloc));

// function declaration for _module.TrickySubstitution.F0
function _module.TrickySubstitution.F0(this: ref, x#0: int) : int;

function _module.TrickySubstitution.F0#canCall(this: ref, x#0: int) : bool;

function Tclass._module.TrickySubstitution() : Ty;

const unique Tagclass._module.TrickySubstitution: TyTag;

// Tclass._module.TrickySubstitution Tag
axiom Tag(Tclass._module.TrickySubstitution()) == Tagclass._module.TrickySubstitution
   && TagFamily(Tclass._module.TrickySubstitution()) == tytagFamily$TrickySubstitution;

// Box/unbox axiom for Tclass._module.TrickySubstitution
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.TrickySubstitution()) } 
  $IsBox(bx, Tclass._module.TrickySubstitution())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.TrickySubstitution()));

// consequence axiom for _module.TrickySubstitution.F0
axiom 18 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref, x#0: int :: 
    { _module.TrickySubstitution.F0(this, x#0), $IsGoodHeap($Heap) } 
    _module.TrickySubstitution.F0#canCall(this, x#0)
         || (18 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.TrickySubstitution())
           && $IsAlloc(this, Tclass._module.TrickySubstitution(), $Heap))
       ==> _module.TrickySubstitution.F0(this, x#0) == x#0);

function _module.TrickySubstitution.F0#requires(ref, int) : bool;

// #requires axiom for _module.TrickySubstitution.F0
axiom (forall $Heap: Heap, this: ref, x#0: int :: 
  { _module.TrickySubstitution.F0#requires(this, x#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.TrickySubstitution())
       && $IsAlloc(this, Tclass._module.TrickySubstitution(), $Heap)
     ==> _module.TrickySubstitution.F0#requires(this, x#0) == true);

function $let#0_g(x: int) : int;

function $let#0$canCall(x: int) : bool;

axiom (forall x: int :: { $let#0_g(x) } $let#0$canCall(x) ==> x == $let#0_g(x));

// definition axiom for _module.TrickySubstitution.F0 (revealed)
axiom 18 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref, x#0: int :: 
    { _module.TrickySubstitution.F0(this, x#0), $IsGoodHeap($Heap) } 
    _module.TrickySubstitution.F0#canCall(this, x#0)
         || (18 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.TrickySubstitution())
           && $IsAlloc(this, Tclass._module.TrickySubstitution(), $Heap))
       ==> $let#0$canCall(x#0)
         && _module.TrickySubstitution.F0(this, x#0) == (var g#0 := $let#0_g(x#0); g#0));

// definition axiom for _module.TrickySubstitution.F0 for decreasing-related literals (revealed)
axiom 18 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref, x#0: int :: 
    {:weight 3} { _module.TrickySubstitution.F0(this, LitInt(x#0)), $IsGoodHeap($Heap) } 
    _module.TrickySubstitution.F0#canCall(this, LitInt(x#0))
         || (18 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.TrickySubstitution())
           && $IsAlloc(this, Tclass._module.TrickySubstitution(), $Heap))
       ==> $let#0$canCall(LitInt(x#0))
         && _module.TrickySubstitution.F0(this, LitInt(x#0))
           == (var g#1 := $let#0_g(LitInt(x#0)); g#1));

// definition axiom for _module.TrickySubstitution.F0 for all literals (revealed)
axiom 18 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref, x#0: int :: 
    {:weight 3} { _module.TrickySubstitution.F0(Lit(this), LitInt(x#0)), $IsGoodHeap($Heap) } 
    _module.TrickySubstitution.F0#canCall(Lit(this), LitInt(x#0))
         || (18 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.TrickySubstitution())
           && $IsAlloc(this, Tclass._module.TrickySubstitution(), $Heap))
       ==> $let#0$canCall(LitInt(x#0))
         && _module.TrickySubstitution.F0(Lit(this), LitInt(x#0))
           == (var g#2 := $let#0_g(LitInt(x#0)); g#2));

procedure CheckWellformed$$_module.TrickySubstitution.F0(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.TrickySubstitution())
         && $IsAlloc(this, Tclass._module.TrickySubstitution(), $Heap), 
    x#0: int);
  free requires 18 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures _module.TrickySubstitution.F0(this, x#0) == x#0;



implementation CheckWellformed$$_module.TrickySubstitution.F0(this: ref, x#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##x#0: int;
  var g#3: int;


    // AddWellformednessCheck for function F0
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(160,11): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        ##x#0 := x#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##x#0, TInt, $Heap);
        assert 0 <= x#0 || ##x#0 == x#0;
        assert (this == this && x#0 == x#0) || ##x#0 < x#0;
        assume (this == this && x#0 == x#0) || _module.TrickySubstitution.F0#canCall(this, x#0);
        assume _module.TrickySubstitution.F0(this, x#0) == x#0;
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        havoc g#3;
        if (true)
        {
        }

        assert ($Is(x#0, TInt) && x#0 == x#0)
           || 
          ($Is(LitInt(0), TInt) && x#0 == LitInt(0))
           || (exists g#4: int :: x#0 == g#4);
        assume true;
        assume x#0 == g#3;
        assume $let#0$canCall(x#0);
        assume _module.TrickySubstitution.F0(this, x#0) == g#3;
        assume true;
        // CheckWellformedWithResult: Let expression
        assume $Is(_module.TrickySubstitution.F0(this, x#0), TInt);
    }
}



// function declaration for _module.TrickySubstitution.F1
function _module.TrickySubstitution.F1(this: ref, x#0: int) : int;

function _module.TrickySubstitution.F1#canCall(this: ref, x#0: int) : bool;

// consequence axiom for _module.TrickySubstitution.F1
axiom 19 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref, x#0: int :: 
    { _module.TrickySubstitution.F1(this, x#0), $IsGoodHeap($Heap) } 
    _module.TrickySubstitution.F1#canCall(this, x#0)
         || (19 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.TrickySubstitution())
           && $IsAlloc(this, Tclass._module.TrickySubstitution(), $Heap))
       ==> _module.TrickySubstitution.F1(this, x#0) == x#0);

function _module.TrickySubstitution.F1#requires(ref, int) : bool;

// #requires axiom for _module.TrickySubstitution.F1
axiom (forall $Heap: Heap, this: ref, x#0: int :: 
  { _module.TrickySubstitution.F1#requires(this, x#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.TrickySubstitution())
       && $IsAlloc(this, Tclass._module.TrickySubstitution(), $Heap)
     ==> _module.TrickySubstitution.F1#requires(this, x#0) == true);

function $let#4_g(f: int) : int;

function $let#4$canCall(f: int) : bool;

axiom (forall f: int :: { $let#4_g(f) } $let#4$canCall(f) ==> f == $let#4_g(f));

// definition axiom for _module.TrickySubstitution.F1 (revealed)
axiom 19 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref, x#0: int :: 
    { _module.TrickySubstitution.F1(this, x#0), $IsGoodHeap($Heap) } 
    _module.TrickySubstitution.F1#canCall(this, x#0)
         || (19 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.TrickySubstitution())
           && $IsAlloc(this, Tclass._module.TrickySubstitution(), $Heap))
       ==> (var f#0 := x#0; $let#4$canCall(f#0))
         && _module.TrickySubstitution.F1(this, x#0)
           == (var f#0 := x#0; (var g#0 := $let#4_g(f#0); g#0)));

// definition axiom for _module.TrickySubstitution.F1 for decreasing-related literals (revealed)
axiom 19 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref, x#0: int :: 
    {:weight 3} { _module.TrickySubstitution.F1(this, LitInt(x#0)), $IsGoodHeap($Heap) } 
    _module.TrickySubstitution.F1#canCall(this, LitInt(x#0))
         || (19 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.TrickySubstitution())
           && $IsAlloc(this, Tclass._module.TrickySubstitution(), $Heap))
       ==> (var f#2 := LitInt(x#0); $let#4$canCall(f#2))
         && _module.TrickySubstitution.F1(this, LitInt(x#0))
           == (var f#2 := LitInt(x#0); (var g#1 := $let#4_g(f#2); g#1)));

// definition axiom for _module.TrickySubstitution.F1 for all literals (revealed)
axiom 19 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref, x#0: int :: 
    {:weight 3} { _module.TrickySubstitution.F1(Lit(this), LitInt(x#0)), $IsGoodHeap($Heap) } 
    _module.TrickySubstitution.F1#canCall(Lit(this), LitInt(x#0))
         || (19 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.TrickySubstitution())
           && $IsAlloc(this, Tclass._module.TrickySubstitution(), $Heap))
       ==> (var f#3 := LitInt(x#0); $let#4$canCall(f#3))
         && _module.TrickySubstitution.F1(Lit(this), LitInt(x#0))
           == (var f#3 := LitInt(x#0); (var g#2 := $let#4_g(f#3); g#2)));

procedure CheckWellformed$$_module.TrickySubstitution.F1(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.TrickySubstitution())
         && $IsAlloc(this, Tclass._module.TrickySubstitution(), $Heap), 
    x#0: int);
  free requires 19 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures _module.TrickySubstitution.F1(this, x#0) == x#0;



implementation CheckWellformed$$_module.TrickySubstitution.F1(this: ref, x#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##x#0: int;
  var f#Z#0: int;
  var let#0#0#0: int;
  var g#3: int;


    // AddWellformednessCheck for function F1
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(167,11): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        ##x#0 := x#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##x#0, TInt, $Heap);
        assert 0 <= x#0 || ##x#0 == x#0;
        assert (this == this && x#0 == x#0) || ##x#0 < x#0;
        assume (this == this && x#0 == x#0) || _module.TrickySubstitution.F1#canCall(this, x#0);
        assume _module.TrickySubstitution.F1(this, x#0) == x#0;
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        havoc f#Z#0;
        assume true;
        assume let#0#0#0 == x#0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0#0#0, TInt);
        assume f#Z#0 == let#0#0#0;
        havoc g#3;
        if (true)
        {
        }

        assert ($Is(f#Z#0, TInt) && f#Z#0 == f#Z#0)
           || 
          ($Is(LitInt(0), TInt) && f#Z#0 == LitInt(0))
           || (exists g#4: int :: f#Z#0 == g#4);
        assume true;
        assume f#Z#0 == g#3;
        assume $let#4$canCall(f#Z#0);
        assume _module.TrickySubstitution.F1(this, x#0) == g#3;
        assume true;
        // CheckWellformedWithResult: Let expression
        assume $Is(_module.TrickySubstitution.F1(this, x#0), TInt);
    }
}



// function declaration for _module.TrickySubstitution.F2
function _module.TrickySubstitution.F2(this: ref, x#0: int) : int;

function _module.TrickySubstitution.F2#canCall(this: ref, x#0: int) : bool;

// consequence axiom for _module.TrickySubstitution.F2
axiom 20 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref, x#0: int :: 
    { _module.TrickySubstitution.F2(this, x#0), $IsGoodHeap($Heap) } 
    _module.TrickySubstitution.F2#canCall(this, x#0)
         || (20 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.TrickySubstitution())
           && $IsAlloc(this, Tclass._module.TrickySubstitution(), $Heap))
       ==> _module.TrickySubstitution.F2(this, x#0) == x#0);

function _module.TrickySubstitution.F2#requires(ref, int) : bool;

// #requires axiom for _module.TrickySubstitution.F2
axiom (forall $Heap: Heap, this: ref, x#0: int :: 
  { _module.TrickySubstitution.F2#requires(this, x#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.TrickySubstitution())
       && $IsAlloc(this, Tclass._module.TrickySubstitution(), $Heap)
     ==> _module.TrickySubstitution.F2#requires(this, x#0) == true);

function $let#9_f(x: int) : int;

function $let#9_g(x: int) : int;

function $let#9$canCall(x: int) : bool;

axiom (forall x: int :: 
  { $let#9_g(x) } { $let#9_f(x) } 
  $let#9$canCall(x) ==> $let#9_f(x) == x && $let#9_f(x) == $let#9_g(x));

// definition axiom for _module.TrickySubstitution.F2 (revealed)
axiom 20 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref, x#0: int :: 
    { _module.TrickySubstitution.F2(this, x#0), $IsGoodHeap($Heap) } 
    _module.TrickySubstitution.F2#canCall(this, x#0)
         || (20 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.TrickySubstitution())
           && $IsAlloc(this, Tclass._module.TrickySubstitution(), $Heap))
       ==> $let#9$canCall(x#0)
         && _module.TrickySubstitution.F2(this, x#0)
           == (var f#0, g#0 := $let#9_f(x#0), $let#9_g(x#0); g#0));

// definition axiom for _module.TrickySubstitution.F2 for decreasing-related literals (revealed)
axiom 20 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref, x#0: int :: 
    {:weight 3} { _module.TrickySubstitution.F2(this, LitInt(x#0)), $IsGoodHeap($Heap) } 
    _module.TrickySubstitution.F2#canCall(this, LitInt(x#0))
         || (20 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.TrickySubstitution())
           && $IsAlloc(this, Tclass._module.TrickySubstitution(), $Heap))
       ==> $let#9$canCall(LitInt(x#0))
         && _module.TrickySubstitution.F2(this, LitInt(x#0))
           == (var f#1, g#1 := $let#9_f(LitInt(x#0)), $let#9_g(LitInt(x#0)); g#1));

// definition axiom for _module.TrickySubstitution.F2 for all literals (revealed)
axiom 20 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref, x#0: int :: 
    {:weight 3} { _module.TrickySubstitution.F2(Lit(this), LitInt(x#0)), $IsGoodHeap($Heap) } 
    _module.TrickySubstitution.F2#canCall(Lit(this), LitInt(x#0))
         || (20 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.TrickySubstitution())
           && $IsAlloc(this, Tclass._module.TrickySubstitution(), $Heap))
       ==> $let#9$canCall(LitInt(x#0))
         && _module.TrickySubstitution.F2(Lit(this), LitInt(x#0))
           == (var f#2, g#2 := $let#9_f(LitInt(x#0)), $let#9_g(LitInt(x#0)); g#2));

procedure CheckWellformed$$_module.TrickySubstitution.F2(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.TrickySubstitution())
         && $IsAlloc(this, Tclass._module.TrickySubstitution(), $Heap), 
    x#0: int);
  free requires 20 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures _module.TrickySubstitution.F2(this, x#0) == x#0;



implementation CheckWellformed$$_module.TrickySubstitution.F2(this: ref, x#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##x#0: int;
  var f#3: int;
  var g#3: int;


    // AddWellformednessCheck for function F2
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(175,11): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        ##x#0 := x#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##x#0, TInt, $Heap);
        assert 0 <= x#0 || ##x#0 == x#0;
        assert (this == this && x#0 == x#0) || ##x#0 < x#0;
        assume (this == this && x#0 == x#0) || _module.TrickySubstitution.F2#canCall(this, x#0);
        assume _module.TrickySubstitution.F2(this, x#0) == x#0;
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        havoc f#3;
        havoc g#3;
        if (true)
        {
            if (f#3 == x#0)
            {
            }
        }

        assert ($Is(x#0, TInt) && $Is(x#0, TInt) && x#0 == x#0 && x#0 == x#0)
           || 
          (
            $Is(LitInt(0), TInt)
             && $Is(LitInt(0), TInt)
             && 
            LitInt(0) == x#0
             && LitInt(0) == LitInt(0))
           || 
          (exists f#4: int :: $Is(f#4, TInt) && f#4 == x#0 && f#4 == f#4)
           || 
          (
            $Is(LitInt(0), TInt)
             && $Is(LitInt(0), TInt)
             && 
            LitInt(0) == x#0
             && LitInt(0) == LitInt(0))
           || 
          ($Is(x#0, TInt) && $Is(LitInt(0), TInt) && x#0 == x#0 && x#0 == LitInt(0))
           || 
          (
            $Is(LitInt(0), TInt)
             && $Is(LitInt(0), TInt)
             && 
            LitInt(0) == x#0
             && LitInt(0) == LitInt(0))
           || 
          (exists f#4: int :: $Is(LitInt(0), TInt) && f#4 == x#0 && f#4 == LitInt(0))
           || 
          (exists g#4: int :: $Is(g#4, TInt) && g#4 == x#0 && g#4 == g#4)
           || 
          (exists g#4: int :: $Is(x#0, TInt) && x#0 == x#0 && x#0 == g#4)
           || 
          (exists g#4: int :: 
            $Is(LitInt(0), TInt) && LitInt(0) == x#0 && LitInt(0) == g#4)
           || (exists f#4: int, g#4: int :: f#4 == x#0 && f#4 == g#4);
        assume true;
        assume f#3 == x#0 && f#3 == g#3;
        assume $let#9$canCall(x#0);
        assume _module.TrickySubstitution.F2(this, x#0) == g#3;
        assume true;
        // CheckWellformedWithResult: Let expression
        assume $Is(_module.TrickySubstitution.F2(this, x#0), TInt);
    }
}



// function declaration for _module.TrickySubstitution.F3
function _module.TrickySubstitution.F3(this: ref, x#0: int) : int;

function _module.TrickySubstitution.F3#canCall(this: ref, x#0: int) : bool;

// consequence axiom for _module.TrickySubstitution.F3
axiom 21 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref, x#0: int :: 
    { _module.TrickySubstitution.F3(this, x#0), $IsGoodHeap($Heap) } 
    _module.TrickySubstitution.F3#canCall(this, x#0)
         || (21 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.TrickySubstitution())
           && $IsAlloc(this, Tclass._module.TrickySubstitution(), $Heap))
       ==> _module.TrickySubstitution.F3(this, x#0) == x#0);

function _module.TrickySubstitution.F3#requires(ref, int) : bool;

// #requires axiom for _module.TrickySubstitution.F3
axiom (forall $Heap: Heap, this: ref, x#0: int :: 
  { _module.TrickySubstitution.F3#requires(this, x#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.TrickySubstitution())
       && $IsAlloc(this, Tclass._module.TrickySubstitution(), $Heap)
     ==> _module.TrickySubstitution.F3#requires(this, x#0) == true);

function $let#13_f(x: int) : int;

function $let#13$canCall(x: int) : bool;

axiom (forall x: int :: { $let#13_f(x) } $let#13$canCall(x) ==> $let#13_f(x) == x);

function $let#15_g(f: int) : int;

function $let#15$canCall(f: int) : bool;

axiom (forall f: int :: { $let#15_g(f) } $let#15$canCall(f) ==> f == $let#15_g(f));

// definition axiom for _module.TrickySubstitution.F3 (revealed)
axiom 21 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref, x#0: int :: 
    { _module.TrickySubstitution.F3(this, x#0), $IsGoodHeap($Heap) } 
    _module.TrickySubstitution.F3#canCall(this, x#0)
         || (21 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.TrickySubstitution())
           && $IsAlloc(this, Tclass._module.TrickySubstitution(), $Heap))
       ==> $let#13$canCall(x#0)
         && $let#15$canCall($let#13_f(x#0))
         && _module.TrickySubstitution.F3(this, x#0)
           == (var f#0 := $let#13_f(x#0); (var g#0 := $let#15_g(f#0); g#0)));

// definition axiom for _module.TrickySubstitution.F3 for decreasing-related literals (revealed)
axiom 21 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref, x#0: int :: 
    {:weight 3} { _module.TrickySubstitution.F3(this, LitInt(x#0)), $IsGoodHeap($Heap) } 
    _module.TrickySubstitution.F3#canCall(this, LitInt(x#0))
         || (21 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.TrickySubstitution())
           && $IsAlloc(this, Tclass._module.TrickySubstitution(), $Heap))
       ==> $let#13$canCall(LitInt(x#0))
         && $let#15$canCall($let#13_f(LitInt(x#0)))
         && _module.TrickySubstitution.F3(this, LitInt(x#0))
           == (var f#2 := $let#13_f(LitInt(x#0)); (var g#1 := $let#15_g(f#2); g#1)));

// definition axiom for _module.TrickySubstitution.F3 for all literals (revealed)
axiom 21 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref, x#0: int :: 
    {:weight 3} { _module.TrickySubstitution.F3(Lit(this), LitInt(x#0)), $IsGoodHeap($Heap) } 
    _module.TrickySubstitution.F3#canCall(Lit(this), LitInt(x#0))
         || (21 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.TrickySubstitution())
           && $IsAlloc(this, Tclass._module.TrickySubstitution(), $Heap))
       ==> $let#13$canCall(LitInt(x#0))
         && $let#15$canCall($let#13_f(LitInt(x#0)))
         && _module.TrickySubstitution.F3(Lit(this), LitInt(x#0))
           == (var f#3 := $let#13_f(LitInt(x#0)); (var g#2 := $let#15_g(f#3); g#2)));

procedure CheckWellformed$$_module.TrickySubstitution.F3(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.TrickySubstitution())
         && $IsAlloc(this, Tclass._module.TrickySubstitution(), $Heap), 
    x#0: int);
  free requires 21 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures _module.TrickySubstitution.F3(this, x#0) == x#0;



implementation CheckWellformed$$_module.TrickySubstitution.F3(this: ref, x#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##x#0: int;
  var f#4: int;
  var g#3: int;


    // AddWellformednessCheck for function F3
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(182,11): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        ##x#0 := x#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##x#0, TInt, $Heap);
        assert 0 <= x#0 || ##x#0 == x#0;
        assert (this == this && x#0 == x#0) || ##x#0 < x#0;
        assume (this == this && x#0 == x#0) || _module.TrickySubstitution.F3#canCall(this, x#0);
        assume _module.TrickySubstitution.F3(this, x#0) == x#0;
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        havoc f#4;
        if (true)
        {
        }

        assert ($Is(x#0, TInt) && x#0 == x#0)
           || 
          ($Is(LitInt(0), TInt) && LitInt(0) == x#0)
           || (exists f#1: int :: f#1 == x#0);
        assume true;
        assume f#4 == x#0;
        havoc g#3;
        if (true)
        {
        }

        assert ($Is(f#4, TInt) && f#4 == f#4)
           || 
          ($Is(LitInt(0), TInt) && f#4 == LitInt(0))
           || (exists g#4: int :: f#4 == g#4);
        assume true;
        assume f#4 == g#3;
        assume $let#15$canCall(f#4);
        assume $let#13$canCall(x#0);
        assume _module.TrickySubstitution.F3(this, x#0) == (var g#5 := $let#15_g(f#4); g#5);
        assume $let#15$canCall(f#4);
        // CheckWellformedWithResult: Let expression
        assume $Is(_module.TrickySubstitution.F3(this, x#0), TInt);
    }
}



axiom FDim(_module.TrickySubstitution.v) == 0
   && FieldOfDecl(class._module.TrickySubstitution?, field$v)
     == _module.TrickySubstitution.v
   && !$IsGhostField(_module.TrickySubstitution.v);

const _module.TrickySubstitution.v: Field int;

// TrickySubstitution.v: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.TrickySubstitution.v) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.TrickySubstitution?()
     ==> $Is(read($h, $o, _module.TrickySubstitution.v), TInt));

// TrickySubstitution.v: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.TrickySubstitution.v) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.TrickySubstitution?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.TrickySubstitution.v), TInt, $h));

axiom FDim(_module.TrickySubstitution.w) == 0
   && FieldOfDecl(class._module.TrickySubstitution?, field$w)
     == _module.TrickySubstitution.w
   && !$IsGhostField(_module.TrickySubstitution.w);

const _module.TrickySubstitution.w: Field int;

// TrickySubstitution.w: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.TrickySubstitution.w) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.TrickySubstitution?()
     ==> $Is(read($h, $o, _module.TrickySubstitution.w), TInt));

// TrickySubstitution.w: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.TrickySubstitution.w) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.TrickySubstitution?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.TrickySubstitution.w), TInt, $h));

// function declaration for _module.TrickySubstitution.F4
function _module.TrickySubstitution.F4($heap: Heap, this: ref, x#0: int) : int;

function _module.TrickySubstitution.F4#canCall($heap: Heap, this: ref, x#0: int) : bool;

// frame axiom for _module.TrickySubstitution.F4
axiom (forall $h0: Heap, $h1: Heap, this: ref, x#0: int :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.TrickySubstitution.F4($h1, this, x#0) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.TrickySubstitution())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && $o == this ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.TrickySubstitution.F4($h0, this, x#0)
       == _module.TrickySubstitution.F4($h1, this, x#0));

// consequence axiom for _module.TrickySubstitution.F4
axiom 22 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref, x#0: int :: 
    { _module.TrickySubstitution.F4($Heap, this, x#0) } 
    _module.TrickySubstitution.F4#canCall($Heap, this, x#0)
         || (22 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.TrickySubstitution())
           && $IsAlloc(this, Tclass._module.TrickySubstitution(), $Heap)
           && 
          read($Heap, this, _module.TrickySubstitution.v) + x#0 == LitInt(3)
           && read($Heap, this, _module.TrickySubstitution.w) == LitInt(2))
       ==> _module.TrickySubstitution.F4($Heap, this, x#0) == LitInt(5));

function _module.TrickySubstitution.F4#requires(Heap, ref, int) : bool;

// #requires axiom for _module.TrickySubstitution.F4
axiom (forall $Heap: Heap, this: ref, x#0: int :: 
  { _module.TrickySubstitution.F4#requires($Heap, this, x#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.TrickySubstitution())
       && $IsAlloc(this, Tclass._module.TrickySubstitution(), $Heap)
     ==> _module.TrickySubstitution.F4#requires($Heap, this, x#0)
       == (read($Heap, this, _module.TrickySubstitution.v) + x#0 == LitInt(3)
         && read($Heap, this, _module.TrickySubstitution.w) == LitInt(2)));

function $let#28_g($heap: Heap, this: ref, f: int) : int;

function $let#28$canCall($heap: Heap, this: ref, f: int) : bool;

axiom (forall $heap: Heap, this: ref, f: int :: 
  { $let#28_g($heap, this, f) } 
  $let#28$canCall($heap, this, f)
     ==> f + read($heap, this, _module.TrickySubstitution.w) == $let#28_g($heap, this, f));

// definition axiom for _module.TrickySubstitution.F4 (revealed)
axiom 22 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref, x#0: int :: 
    { _module.TrickySubstitution.F4($Heap, this, x#0), $IsGoodHeap($Heap) } 
    _module.TrickySubstitution.F4#canCall($Heap, this, x#0)
         || (22 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.TrickySubstitution())
           && $IsAlloc(this, Tclass._module.TrickySubstitution(), $Heap)
           && 
          read($Heap, this, _module.TrickySubstitution.v) + x#0 == LitInt(3)
           && read($Heap, this, _module.TrickySubstitution.w) == LitInt(2))
       ==> (var f#0 := read($Heap, this, _module.TrickySubstitution.v) + x#0; 
          $let#28$canCall($Heap, this, f#0))
         && _module.TrickySubstitution.F4($Heap, this, x#0)
           == (var f#0 := read($Heap, this, _module.TrickySubstitution.v) + x#0; 
            (var g#0 := $let#28_g($Heap, this, f#0); g#0)));

procedure CheckWellformed$$_module.TrickySubstitution.F4(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.TrickySubstitution())
         && $IsAlloc(this, Tclass._module.TrickySubstitution(), $Heap), 
    x#0: int);
  free requires 22 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures _module.TrickySubstitution.F4($Heap, this, x#0) == LitInt(5);



implementation CheckWellformed$$_module.TrickySubstitution.F4(this: ref, x#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;
  var ##x#0: int;
  var f#Z#0: int;
  var let#0#0#0: int;
  var g#1: int;
  var b$reqreads#2: bool;
  var b$reqreads#3: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;
    b$reqreads#3 := true;

    // AddWellformednessCheck for function F4
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(193,11): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    b$reqreads#0 := $_Frame[this, _module.TrickySubstitution.v];
    assume read($Heap, this, _module.TrickySubstitution.v) + x#0 == LitInt(3);
    b$reqreads#1 := $_Frame[this, _module.TrickySubstitution.w];
    assume read($Heap, this, _module.TrickySubstitution.w) == LitInt(2);
    assert b$reqreads#0;
    assert b$reqreads#1;
    if (*)
    {
        ##x#0 := x#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##x#0, TInt, $Heap);
        assert {:subsumption 0} read($Heap, this, _module.TrickySubstitution.v) + ##x#0 == LitInt(3);
        assert {:subsumption 0} read($Heap, this, _module.TrickySubstitution.w) == LitInt(2);
        assume read($Heap, this, _module.TrickySubstitution.v) + ##x#0 == LitInt(3)
           && read($Heap, this, _module.TrickySubstitution.w) == LitInt(2);
        assert 0 <= x#0
           || (Set#Subset(Set#UnionOne(Set#Empty(): Set Box, $Box(this)), 
              Set#UnionOne(Set#Empty(): Set Box, $Box(this)))
             && !Set#Subset(Set#UnionOne(Set#Empty(): Set Box, $Box(this)), 
              Set#UnionOne(Set#Empty(): Set Box, $Box(this))))
           || ##x#0 == x#0;
        assert (this == this && x#0 == x#0)
           || 
          (Set#Subset(Set#UnionOne(Set#Empty(): Set Box, $Box(this)), 
              Set#UnionOne(Set#Empty(): Set Box, $Box(this)))
             && !Set#Subset(Set#UnionOne(Set#Empty(): Set Box, $Box(this)), 
              Set#UnionOne(Set#Empty(): Set Box, $Box(this))))
           || (Set#Equal(Set#UnionOne(Set#Empty(): Set Box, $Box(this)), 
              Set#UnionOne(Set#Empty(): Set Box, $Box(this)))
             && ##x#0 < x#0);
        assume (this == this && x#0 == x#0)
           || _module.TrickySubstitution.F4#canCall($Heap, this, x#0);
        assume _module.TrickySubstitution.F4($Heap, this, x#0) == LitInt(5);
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> $o == this);
        havoc f#Z#0;
        assume true;
        b$reqreads#2 := $_Frame[this, _module.TrickySubstitution.v];
        assume let#0#0#0 == read($Heap, this, _module.TrickySubstitution.v) + x#0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0#0#0, TInt);
        assume f#Z#0 == let#0#0#0;
        havoc g#1;
        if (true)
        {
            b$reqreads#3 := $_Frame[this, _module.TrickySubstitution.w];
        }

        assert ($Is(f#Z#0 + read($Heap, this, _module.TrickySubstitution.w), TInt)
             && f#Z#0 + read($Heap, this, _module.TrickySubstitution.w)
               == f#Z#0 + read($Heap, this, _module.TrickySubstitution.w))
           || 
          ($Is(LitInt(0), TInt)
             && f#Z#0 + read($Heap, this, _module.TrickySubstitution.w) == LitInt(0))
           || (exists g#2: int :: 
            f#Z#0 + read($Heap, this, _module.TrickySubstitution.w) == g#2);
        assume true;
        assume f#Z#0 + read($Heap, this, _module.TrickySubstitution.w) == g#1;
        assume $let#28$canCall($Heap, this, f#Z#0);
        assume _module.TrickySubstitution.F4($Heap, this, x#0) == g#1;
        assume true;
        // CheckWellformedWithResult: Let expression
        assume $Is(_module.TrickySubstitution.F4($Heap, this, x#0), TInt);
        assert b$reqreads#2;
        assert b$reqreads#3;
    }
}



// function declaration for _module.TrickySubstitution.F5
function _module.TrickySubstitution.F5(this: ref, n#0: int) : bool;

function _module.TrickySubstitution.F5#canCall(this: ref, n#0: int) : bool;

// consequence axiom for _module.TrickySubstitution.F5
axiom 28 <= $FunctionContextHeight
   ==> (forall this: ref, n#0: int :: 
    { _module.TrickySubstitution.F5(this, n#0) } 
    _module.TrickySubstitution.F5#canCall(this, n#0)
         || (28 != $FunctionContextHeight
           && 
          this != null
           && $Is(this, Tclass._module.TrickySubstitution()))
       ==> true);

function _module.TrickySubstitution.F5#requires(ref, int) : bool;

// #requires axiom for _module.TrickySubstitution.F5
axiom (forall $Heap: Heap, this: ref, n#0: int :: 
  { _module.TrickySubstitution.F5#requires(this, n#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.TrickySubstitution())
       && $IsAlloc(this, Tclass._module.TrickySubstitution(), $Heap)
     ==> _module.TrickySubstitution.F5#requires(this, n#0) == true);

function $let#31_j(i: int) : int;

function $let#31_k(i: int) : int;

function $let#31$canCall(i: int) : bool;

axiom (forall i: int :: 
  { $let#31_k(i) } { $let#31_j(i) } 
  $let#31$canCall(i) ==> $let#31_k(i) <= $let#31_j(i) && $let#31_j(i) < i);

// definition axiom for _module.TrickySubstitution.F5 (revealed)
axiom 28 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref, n#0: int :: 
    { _module.TrickySubstitution.F5(this, n#0), $IsGoodHeap($Heap) } 
    _module.TrickySubstitution.F5#canCall(this, n#0)
         || (28 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.TrickySubstitution())
           && $IsAlloc(this, Tclass._module.TrickySubstitution(), $Heap))
       ==> (forall i#0: int :: 0 < i#0 ==> i#0 < n#0 ==> $let#31$canCall(i#0))
         && _module.TrickySubstitution.F5(this, n#0)
           == (forall i#0: int :: 
            true
               ==> 
              0 < i#0 && i#0 < n#0
               ==> (var j#0, k#0 := $let#31_j(i#0), $let#31_k(i#0); k#0 <= j#0 && j#0 < i#0)));

// definition axiom for _module.TrickySubstitution.F5 for decreasing-related literals (revealed)
axiom 28 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref, n#0: int :: 
    {:weight 3} { _module.TrickySubstitution.F5(this, LitInt(n#0)), $IsGoodHeap($Heap) } 
    _module.TrickySubstitution.F5#canCall(this, LitInt(n#0))
         || (28 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.TrickySubstitution())
           && $IsAlloc(this, Tclass._module.TrickySubstitution(), $Heap))
       ==> (forall i#2: int :: 0 < i#2 ==> i#2 < n#0 ==> $let#31$canCall(i#2))
         && _module.TrickySubstitution.F5(this, LitInt(n#0))
           == (forall i#2: int :: 
            true
               ==> 
              0 < i#2 && i#2 < n#0
               ==> (var j#1, k#1 := $let#31_j(i#2), $let#31_k(i#2); k#1 <= j#1 && j#1 < i#2)));

// definition axiom for _module.TrickySubstitution.F5 for all literals (revealed)
axiom 28 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref, n#0: int :: 
    {:weight 3} { _module.TrickySubstitution.F5(Lit(this), LitInt(n#0)), $IsGoodHeap($Heap) } 
    _module.TrickySubstitution.F5#canCall(Lit(this), LitInt(n#0))
         || (28 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.TrickySubstitution())
           && $IsAlloc(this, Tclass._module.TrickySubstitution(), $Heap))
       ==> (forall i#3: int :: 0 < i#3 ==> i#3 < n#0 ==> $let#31$canCall(i#3))
         && _module.TrickySubstitution.F5(Lit(this), LitInt(n#0))
           == (forall i#3: int :: 
            true
               ==> 
              0 < i#3 && i#3 < n#0
               ==> (var j#2, k#2 := $let#31_j(i#3), $let#31_k(i#3); k#2 <= j#2 && j#2 < i#3)));

procedure CheckWellformed$$_module.TrickySubstitution.F5(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.TrickySubstitution())
         && $IsAlloc(this, Tclass._module.TrickySubstitution(), $Heap), 
    n#0: int);
  free requires 28 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.TrickySubstitution.F5(this: ref, n#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var i#4: int;
  var j#3: int;
  var k#3: int;


    // AddWellformednessCheck for function F5
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(204,12): initial state"} true;
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
        // Begin Comprehension WF check
        havoc i#4;
        if (true)
        {
            if (0 < i#4)
            {
            }

            if (0 < i#4 && i#4 < n#0)
            {
                havoc j#3;
                havoc k#3;
                if (true)
                {
                    if (k#3 <= j#3)
                    {
                    }
                }

                assert (
                    $Is(i#4 - 1, TInt)
                     && $Is(i#4 - 1 + 1 - 1, TInt)
                     && 
                    i#4 - 1 + 1 - 1 <= i#4 - 1
                     && i#4 - 1 < i#4)
                   || 
                  (
                    $Is(LitInt(0), TInt)
                     && $Is(LitInt(0 + 1 - 1), TInt)
                     && 
                    LitInt(0 + 1 - 1) <= LitInt(0)
                     && 0 < i#4)
                   || 
                  (exists j#4: int :: $Is(j#4 + 1 - 1, TInt) && j#4 + 1 - 1 <= j#4 && j#4 < i#4)
                   || 
                  (
                    $Is(i#4 - 1, TInt)
                     && $Is(LitInt(0), TInt)
                     && 
                    LitInt(0) <= i#4 - 1
                     && i#4 - 1 < i#4)
                   || 
                  (
                    $Is(LitInt(0), TInt)
                     && $Is(LitInt(0), TInt)
                     && 
                    LitInt(0) <= LitInt(0)
                     && 0 < i#4)
                   || 
                  (
                    $Is(LitInt(0), TInt)
                     && $Is(LitInt(0), TInt)
                     && 
                    LitInt(0) <= LitInt(0)
                     && 0 < i#4)
                   || 
                  (exists j#4: int :: $Is(LitInt(0), TInt) && LitInt(0) <= j#4 && j#4 < i#4)
                   || 
                  (exists k#4: int :: $Is(i#4 - 1, TInt) && k#4 <= i#4 - 1 && i#4 - 1 < i#4)
                   || 
                  (exists k#4: int :: $Is(k#4, TInt) && k#4 <= k#4 && k#4 < i#4)
                   || 
                  (exists k#4: int :: $Is(LitInt(0), TInt) && k#4 <= LitInt(0) && 0 < i#4)
                   || (exists j#4: int, k#4: int :: k#4 <= j#4 && j#4 < i#4);
                assume true;
                assume k#3 <= j#3 && j#3 < i#4;
                if (k#3 <= j#3)
                {
                }

                assume $let#31$canCall(i#4);
            }
        }

        // End Comprehension WF check
        assume _module.TrickySubstitution.F5(this, n#0)
           == (forall i#1: int :: 
            true
               ==> 
              0 < i#1 && i#1 < n#0
               ==> (var j#4, k#4 := $let#31_j(i#1), $let#31_k(i#1); k#4 <= j#4 && j#4 < i#1));
        assume (forall i#1: int :: 0 < i#1 && i#1 < n#0 ==> $let#31$canCall(i#1));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.TrickySubstitution.F5(this, n#0), TBool);
    }
}



procedure CheckWellformed$$_module.TrickySubstitution.M(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.TrickySubstitution())
         && $IsAlloc(this, Tclass._module.TrickySubstitution(), $Heap), 
    x#0: int);
  free requires 29 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.TrickySubstitution.M(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.TrickySubstitution())
         && $IsAlloc(this, Tclass._module.TrickySubstitution(), $Heap), 
    x#0: int);
  // user-defined preconditions
  requires read($Heap, this, _module.TrickySubstitution.v) + x#0 == LitInt(3);
  requires read($Heap, this, _module.TrickySubstitution.w) == LitInt(2);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.TrickySubstitution.M(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.TrickySubstitution())
         && $IsAlloc(this, Tclass._module.TrickySubstitution(), $Heap), 
    x#0: int)
   returns ($_reverifyPost: bool);
  free requires 29 == $FunctionContextHeight;
  // user-defined preconditions
  requires read($Heap, this, _module.TrickySubstitution.v) + x#0 == LitInt(3);
  requires read($Heap, this, _module.TrickySubstitution.w) == LitInt(2);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



function $let#36_g($heap$old: Heap, this: ref, f: int) : int;

function $let#36$canCall($heap$old: Heap, this: ref, f: int) : bool;

axiom (forall $heap$old: Heap, this: ref, f: int :: 
  { $let#36_g($heap$old, this, f) } 
  $let#36$canCall($heap$old, this, f)
     ==> f + read($heap$old, this, _module.TrickySubstitution.w)
       == $let#36_g($heap$old, this, f));

implementation Impl$$_module.TrickySubstitution.M(this: ref, x#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: int;
  var $rhs#1: int;
  var f#Z#0: int;
  var let#0#0#0: int;
  var g#0: int;

    // AddMethodImpl: M, Impl$$_module.TrickySubstitution.M
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(212,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(213,12)
    assume true;
    assert $_Frame[this, _module.TrickySubstitution.v];
    assume true;
    $rhs#0 := read($Heap, this, _module.TrickySubstitution.v) + 1;
    $Heap := update($Heap, this, _module.TrickySubstitution.v, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(213,24)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(214,12)
    assume true;
    assert $_Frame[this, _module.TrickySubstitution.w];
    assume true;
    $rhs#1 := read($Heap, this, _module.TrickySubstitution.w) + 10;
    $Heap := update($Heap, this, _module.TrickySubstitution.w, $rhs#1);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(214,25)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(215,5)
    havoc f#Z#0;
    assume true;
    assume let#0#0#0 == read($Heap, this, _module.TrickySubstitution.v) + x#0;
    assume true;
    // CheckWellformedWithResult: any expression
    assume $Is(let#0#0#0, TInt);
    assume f#Z#0 == let#0#0#0;
    havoc g#0;
    if (true)
    {
        assert $IsAlloc(this, Tclass._module.TrickySubstitution(), old($Heap));
    }

    assert ($Is(f#Z#0 + read(old($Heap), this, _module.TrickySubstitution.w), TInt)
         && f#Z#0 + read(old($Heap), this, _module.TrickySubstitution.w)
           == f#Z#0 + read(old($Heap), this, _module.TrickySubstitution.w))
       || 
      ($Is(LitInt(0), TInt)
         && f#Z#0 + read(old($Heap), this, _module.TrickySubstitution.w) == LitInt(0))
       || (exists g#1: int :: 
        f#Z#0 + read(old($Heap), this, _module.TrickySubstitution.w) == g#1);
    assume true;
    assume f#Z#0 + read(old($Heap), this, _module.TrickySubstitution.w) == g#0;
    assume $let#36$canCall(old($Heap), this, f#Z#0);
    assume (var f#0 := read($Heap, this, _module.TrickySubstitution.v) + x#0; 
      $let#36$canCall(old($Heap), this, f#0));
    assert LitInt(6)
       == (var f#0 := read($Heap, this, _module.TrickySubstitution.v) + x#0; 
        (var g#1 := $let#36_g(old($Heap), this, f#0); g#1));
}



procedure CheckWellformed$$_module.TrickySubstitution.N(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.TrickySubstitution())
         && $IsAlloc(this, Tclass._module.TrickySubstitution(), $Heap))
   returns (r#0: int, s#0: int);
  free requires 30 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.TrickySubstitution.N(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.TrickySubstitution())
         && $IsAlloc(this, Tclass._module.TrickySubstitution(), $Heap))
   returns (r#0: int, s#0: int);
  // user-defined preconditions
  requires read($Heap, this, _module.TrickySubstitution.w) == LitInt(12);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures r#0 == LitInt(12);
  ensures LitInt(12) == s#0;
  ensures read($Heap, this, _module.TrickySubstitution.w) == LitInt(13);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.TrickySubstitution.N(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.TrickySubstitution())
         && $IsAlloc(this, Tclass._module.TrickySubstitution(), $Heap))
   returns (r#0: int, s#0: int, $_reverifyPost: bool);
  free requires 30 == $FunctionContextHeight;
  // user-defined preconditions
  requires read($Heap, this, _module.TrickySubstitution.w) == LitInt(12);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures r#0 == LitInt(12);
  ensures LitInt(12) == s#0;
  ensures read($Heap, this, _module.TrickySubstitution.w) == LitInt(13);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



function $let#38_y($heap$old: Heap, this: ref) : int;

function $let#38$canCall($heap$old: Heap, this: ref) : bool;

axiom (forall $heap$old: Heap, this: ref :: 
  { $let#38_y($heap$old, this) } 
  $let#38$canCall($heap$old, this)
     ==> $let#38_y($heap$old, this)
       == read($heap$old, this, _module.TrickySubstitution.w));

function $let#39_y($heap: Heap, this: ref) : int;

function $let#39$canCall($heap: Heap, this: ref) : bool;

axiom (forall $heap: Heap, this: ref :: 
  { $let#39_y($heap, this) } 
  $let#39$canCall($heap, this)
     ==> $let#39_y($heap, this) == read($heap, this, _module.TrickySubstitution.w));

implementation Impl$$_module.TrickySubstitution.N(this: ref) returns (r#0: int, s#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: int;
  var y#0: int;
  var y#2: int;

    // AddMethodImpl: N, Impl$$_module.TrickySubstitution.N
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(225,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(226,7)
    assume true;
    assert $_Frame[this, _module.TrickySubstitution.w];
    assume true;
    $rhs#0 := read($Heap, this, _module.TrickySubstitution.w) + 1;
    $Heap := update($Heap, this, _module.TrickySubstitution.w, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(226,14)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(227,7)
    assume true;
    havoc y#0;
    if (true)
    {
        assert $IsAlloc(this, Tclass._module.TrickySubstitution(), old($Heap));
    }

    assert ($Is(read(old($Heap), this, _module.TrickySubstitution.w), TInt)
         && read(old($Heap), this, _module.TrickySubstitution.w)
           == read(old($Heap), this, _module.TrickySubstitution.w))
       || 
      ($Is(LitInt(0), TInt)
         && LitInt(0) == read(old($Heap), this, _module.TrickySubstitution.w))
       || (exists y#1: int :: y#1 == read(old($Heap), this, _module.TrickySubstitution.w));
    assume true;
    assume y#0 == read(old($Heap), this, _module.TrickySubstitution.w);
    assume $let#38$canCall(old($Heap), this);
    assume $let#38$canCall(old($Heap), this);
    r#0 := (var y#1 := $let#38_y(old($Heap), this); y#1);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(227,32)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(228,7)
    assume true;
    havoc y#2;
    if (true)
    {
        assert $IsAlloc(this, Tclass._module.TrickySubstitution(), old($Heap));
    }

    assert ($Is(read(old($Heap), this, _module.TrickySubstitution.w), TInt)
         && read(old($Heap), this, _module.TrickySubstitution.w)
           == read(old($Heap), this, _module.TrickySubstitution.w))
       || 
      ($Is(LitInt(0), TInt)
         && LitInt(0) == read(old($Heap), this, _module.TrickySubstitution.w))
       || (exists y#3: int :: y#3 == read(old($Heap), this, _module.TrickySubstitution.w));
    assume true;
    assume y#2 == read(old($Heap), this, _module.TrickySubstitution.w);
    assume $let#39$canCall(old($Heap), this);
    assume $let#39$canCall(old($Heap), this);
    s#0 := (var y#3 := $let#39_y(old($Heap), this); y#3);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(228,32)"} true;
}



// _module.TrickySubstitution: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.TrickySubstitution()) } 
  $Is(c#0, Tclass._module.TrickySubstitution())
     <==> $Is(c#0, Tclass._module.TrickySubstitution?()) && c#0 != null);

// _module.TrickySubstitution: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.TrickySubstitution(), $h) } 
  $IsAlloc(c#0, Tclass._module.TrickySubstitution(), $h)
     <==> $IsAlloc(c#0, Tclass._module.TrickySubstitution?(), $h));

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
  { $IsAllocBox(_module.List.head(d), _module.List$T, $h) } 
  $IsGoodHeap($h)
       && 
      _module.List.Cons_q(d)
       && $IsAlloc(d, Tclass._module.List(_module.List$T), $h)
     ==> $IsAllocBox(_module.List.head(d), _module.List$T, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _module.List$T: Ty, $h: Heap :: 
  { $IsAlloc(_module.List.tail(d), Tclass._module.List(_module.List$T), $h) } 
  $IsGoodHeap($h)
       && 
      _module.List.Cons_q(d)
       && $IsAlloc(d, Tclass._module.List(_module.List$T), $h)
     ==> $IsAlloc(_module.List.tail(d), Tclass._module.List(_module.List$T), $h));

// Constructor literal
axiom (forall a#9#0#0: Box, a#9#1#0: DatatypeType :: 
  { #_module.List.Cons(Lit(a#9#0#0), Lit(a#9#1#0)) } 
  #_module.List.Cons(Lit(a#9#0#0), Lit(a#9#1#0))
     == Lit(#_module.List.Cons(a#9#0#0, a#9#1#0)));

function _module.List.head(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#10#0#0: Box, a#10#1#0: DatatypeType :: 
  { #_module.List.Cons(a#10#0#0, a#10#1#0) } 
  _module.List.head(#_module.List.Cons(a#10#0#0, a#10#1#0)) == a#10#0#0);

// Inductive rank
axiom (forall a#11#0#0: Box, a#11#1#0: DatatypeType :: 
  { #_module.List.Cons(a#11#0#0, a#11#1#0) } 
  BoxRank(a#11#0#0) < DtRank(#_module.List.Cons(a#11#0#0, a#11#1#0)));

function _module.List.tail(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#12#0#0: Box, a#12#1#0: DatatypeType :: 
  { #_module.List.Cons(a#12#0#0, a#12#1#0) } 
  _module.List.tail(#_module.List.Cons(a#12#0#0, a#12#1#0)) == a#12#1#0);

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
       <==> _module.List.head(a) == _module.List.head(b)
         && _module.List#Equal(_module.List.tail(a), _module.List.tail(b))));

// Datatype extensionality axiom: _module.List
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.List#Equal(a, b) } 
  _module.List#Equal(a, b) <==> a == b);

const unique class._module.List: ClassName;

// Constructor function declaration
function #_module.Tuple.Pair(Box, Box) : DatatypeType;

const unique ##_module.Tuple.Pair: DtCtorId;

// Constructor identifier
axiom (forall a#14#0#0: Box, a#14#1#0: Box :: 
  { #_module.Tuple.Pair(a#14#0#0, a#14#1#0) } 
  DatatypeCtorId(#_module.Tuple.Pair(a#14#0#0, a#14#1#0)) == ##_module.Tuple.Pair);

function _module.Tuple.Pair_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Tuple.Pair_q(d) } 
  _module.Tuple.Pair_q(d) <==> DatatypeCtorId(d) == ##_module.Tuple.Pair);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Tuple.Pair_q(d) } 
  _module.Tuple.Pair_q(d)
     ==> (exists a#15#0#0: Box, a#15#1#0: Box :: 
      d == #_module.Tuple.Pair(a#15#0#0, a#15#1#0)));

function Tclass._module.Tuple(Ty, Ty) : Ty;

const unique Tagclass._module.Tuple: TyTag;

// Tclass._module.Tuple Tag
axiom (forall _module.Tuple$T: Ty, _module.Tuple$U: Ty :: 
  { Tclass._module.Tuple(_module.Tuple$T, _module.Tuple$U) } 
  Tag(Tclass._module.Tuple(_module.Tuple$T, _module.Tuple$U))
       == Tagclass._module.Tuple
     && TagFamily(Tclass._module.Tuple(_module.Tuple$T, _module.Tuple$U))
       == tytagFamily$Tuple);

// Tclass._module.Tuple injectivity 0
axiom (forall _module.Tuple$T: Ty, _module.Tuple$U: Ty :: 
  { Tclass._module.Tuple(_module.Tuple$T, _module.Tuple$U) } 
  Tclass._module.Tuple_0(Tclass._module.Tuple(_module.Tuple$T, _module.Tuple$U))
     == _module.Tuple$T);

function Tclass._module.Tuple_0(Ty) : Ty;

// Tclass._module.Tuple injectivity 1
axiom (forall _module.Tuple$T: Ty, _module.Tuple$U: Ty :: 
  { Tclass._module.Tuple(_module.Tuple$T, _module.Tuple$U) } 
  Tclass._module.Tuple_1(Tclass._module.Tuple(_module.Tuple$T, _module.Tuple$U))
     == _module.Tuple$U);

function Tclass._module.Tuple_1(Ty) : Ty;

// Box/unbox axiom for Tclass._module.Tuple
axiom (forall _module.Tuple$T: Ty, _module.Tuple$U: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.Tuple(_module.Tuple$T, _module.Tuple$U)) } 
  $IsBox(bx, Tclass._module.Tuple(_module.Tuple$T, _module.Tuple$U))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Tuple(_module.Tuple$T, _module.Tuple$U)));

// Constructor $Is
axiom (forall _module.Tuple$T: Ty, _module.Tuple$U: Ty, a#16#0#0: Box, a#16#1#0: Box :: 
  { $Is(#_module.Tuple.Pair(a#16#0#0, a#16#1#0), 
      Tclass._module.Tuple(_module.Tuple$T, _module.Tuple$U)) } 
  $Is(#_module.Tuple.Pair(a#16#0#0, a#16#1#0), 
      Tclass._module.Tuple(_module.Tuple$T, _module.Tuple$U))
     <==> $IsBox(a#16#0#0, _module.Tuple$T) && $IsBox(a#16#1#0, _module.Tuple$U));

// Constructor $IsAlloc
axiom (forall _module.Tuple$T: Ty, _module.Tuple$U: Ty, a#17#0#0: Box, a#17#1#0: Box, $h: Heap :: 
  { $IsAlloc(#_module.Tuple.Pair(a#17#0#0, a#17#1#0), 
      Tclass._module.Tuple(_module.Tuple$T, _module.Tuple$U), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Tuple.Pair(a#17#0#0, a#17#1#0), 
        Tclass._module.Tuple(_module.Tuple$T, _module.Tuple$U), 
        $h)
       <==> $IsAllocBox(a#17#0#0, _module.Tuple$T, $h)
         && $IsAllocBox(a#17#1#0, _module.Tuple$U, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _module.Tuple$T: Ty, $h: Heap :: 
  { $IsAllocBox(_module.Tuple._0(d), _module.Tuple$T, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Tuple.Pair_q(d)
       && (exists _module.Tuple$U: Ty :: 
        { $IsAlloc(d, Tclass._module.Tuple(_module.Tuple$T, _module.Tuple$U), $h) } 
        $IsAlloc(d, Tclass._module.Tuple(_module.Tuple$T, _module.Tuple$U), $h))
     ==> $IsAllocBox(_module.Tuple._0(d), _module.Tuple$T, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _module.Tuple$U: Ty, $h: Heap :: 
  { $IsAllocBox(_module.Tuple._1(d), _module.Tuple$U, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Tuple.Pair_q(d)
       && (exists _module.Tuple$T: Ty :: 
        { $IsAlloc(d, Tclass._module.Tuple(_module.Tuple$T, _module.Tuple$U), $h) } 
        $IsAlloc(d, Tclass._module.Tuple(_module.Tuple$T, _module.Tuple$U), $h))
     ==> $IsAllocBox(_module.Tuple._1(d), _module.Tuple$U, $h));

// Constructor literal
axiom (forall a#18#0#0: Box, a#18#1#0: Box :: 
  { #_module.Tuple.Pair(Lit(a#18#0#0), Lit(a#18#1#0)) } 
  #_module.Tuple.Pair(Lit(a#18#0#0), Lit(a#18#1#0))
     == Lit(#_module.Tuple.Pair(a#18#0#0, a#18#1#0)));

function _module.Tuple._0(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#19#0#0: Box, a#19#1#0: Box :: 
  { #_module.Tuple.Pair(a#19#0#0, a#19#1#0) } 
  _module.Tuple._0(#_module.Tuple.Pair(a#19#0#0, a#19#1#0)) == a#19#0#0);

// Inductive rank
axiom (forall a#20#0#0: Box, a#20#1#0: Box :: 
  { #_module.Tuple.Pair(a#20#0#0, a#20#1#0) } 
  BoxRank(a#20#0#0) < DtRank(#_module.Tuple.Pair(a#20#0#0, a#20#1#0)));

function _module.Tuple._1(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#21#0#0: Box, a#21#1#0: Box :: 
  { #_module.Tuple.Pair(a#21#0#0, a#21#1#0) } 
  _module.Tuple._1(#_module.Tuple.Pair(a#21#0#0, a#21#1#0)) == a#21#1#0);

// Inductive rank
axiom (forall a#22#0#0: Box, a#22#1#0: Box :: 
  { #_module.Tuple.Pair(a#22#0#0, a#22#1#0) } 
  BoxRank(a#22#1#0) < DtRank(#_module.Tuple.Pair(a#22#0#0, a#22#1#0)));

// Depth-one case-split function
function $IsA#_module.Tuple(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.Tuple(d) } 
  $IsA#_module.Tuple(d) ==> _module.Tuple.Pair_q(d));

// Questionmark data type disjunctivity
axiom (forall _module.Tuple$T: Ty, _module.Tuple$U: Ty, d: DatatypeType :: 
  { _module.Tuple.Pair_q(d), $Is(d, Tclass._module.Tuple(_module.Tuple$T, _module.Tuple$U)) } 
  $Is(d, Tclass._module.Tuple(_module.Tuple$T, _module.Tuple$U))
     ==> _module.Tuple.Pair_q(d));

// Datatype extensional equality declaration
function _module.Tuple#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.Tuple.Pair
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Tuple#Equal(a, b) } 
  true
     ==> (_module.Tuple#Equal(a, b)
       <==> _module.Tuple._0(a) == _module.Tuple._0(b)
         && _module.Tuple._1(a) == _module.Tuple._1(b)));

// Datatype extensionality axiom: _module.Tuple
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Tuple#Equal(a, b) } 
  _module.Tuple#Equal(a, b) <==> a == b);

const unique class._module.Tuple: ClassName;

// Constructor function declaration
function #_module.Friend.Agnes(int) : DatatypeType;

const unique ##_module.Friend.Agnes: DtCtorId;

// Constructor identifier
axiom (forall a#23#0#0: int :: 
  { #_module.Friend.Agnes(a#23#0#0) } 
  DatatypeCtorId(#_module.Friend.Agnes(a#23#0#0)) == ##_module.Friend.Agnes);

function _module.Friend.Agnes_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Friend.Agnes_q(d) } 
  _module.Friend.Agnes_q(d) <==> DatatypeCtorId(d) == ##_module.Friend.Agnes);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Friend.Agnes_q(d) } 
  _module.Friend.Agnes_q(d)
     ==> (exists a#24#0#0: int :: d == #_module.Friend.Agnes(a#24#0#0)));

function Tclass._module.Friend() : Ty;

const unique Tagclass._module.Friend: TyTag;

// Tclass._module.Friend Tag
axiom Tag(Tclass._module.Friend()) == Tagclass._module.Friend
   && TagFamily(Tclass._module.Friend()) == tytagFamily$Friend;

// Box/unbox axiom for Tclass._module.Friend
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Friend()) } 
  $IsBox(bx, Tclass._module.Friend())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Friend()));

// Constructor $Is
axiom (forall a#25#0#0: int :: 
  { $Is(#_module.Friend.Agnes(a#25#0#0), Tclass._module.Friend()) } 
  $Is(#_module.Friend.Agnes(a#25#0#0), Tclass._module.Friend())
     <==> $Is(a#25#0#0, TInt));

// Constructor $IsAlloc
axiom (forall a#26#0#0: int, $h: Heap :: 
  { $IsAlloc(#_module.Friend.Agnes(a#26#0#0), Tclass._module.Friend(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Friend.Agnes(a#26#0#0), Tclass._module.Friend(), $h)
       <==> $IsAlloc(a#26#0#0, TInt, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Friend._h0(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Friend.Agnes_q(d)
       && $IsAlloc(d, Tclass._module.Friend(), $h)
     ==> $IsAlloc(_module.Friend._h0(d), TInt, $h));

// Constructor literal
axiom (forall a#27#0#0: int :: 
  { #_module.Friend.Agnes(LitInt(a#27#0#0)) } 
  #_module.Friend.Agnes(LitInt(a#27#0#0)) == Lit(#_module.Friend.Agnes(a#27#0#0)));

function _module.Friend._h0(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#28#0#0: int :: 
  { #_module.Friend.Agnes(a#28#0#0) } 
  _module.Friend._h0(#_module.Friend.Agnes(a#28#0#0)) == a#28#0#0);

// Constructor function declaration
function #_module.Friend.Agatha(int) : DatatypeType;

const unique ##_module.Friend.Agatha: DtCtorId;

// Constructor identifier
axiom (forall a#29#0#0: int :: 
  { #_module.Friend.Agatha(a#29#0#0) } 
  DatatypeCtorId(#_module.Friend.Agatha(a#29#0#0)) == ##_module.Friend.Agatha);

function _module.Friend.Agatha_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Friend.Agatha_q(d) } 
  _module.Friend.Agatha_q(d) <==> DatatypeCtorId(d) == ##_module.Friend.Agatha);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Friend.Agatha_q(d) } 
  _module.Friend.Agatha_q(d)
     ==> (exists a#30#0#0: int :: d == #_module.Friend.Agatha(a#30#0#0)));

// Constructor $Is
axiom (forall a#31#0#0: int :: 
  { $Is(#_module.Friend.Agatha(a#31#0#0), Tclass._module.Friend()) } 
  $Is(#_module.Friend.Agatha(a#31#0#0), Tclass._module.Friend())
     <==> $Is(a#31#0#0, TInt));

// Constructor $IsAlloc
axiom (forall a#32#0#0: int, $h: Heap :: 
  { $IsAlloc(#_module.Friend.Agatha(a#32#0#0), Tclass._module.Friend(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Friend.Agatha(a#32#0#0), Tclass._module.Friend(), $h)
       <==> $IsAlloc(a#32#0#0, TInt, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Friend._h1(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Friend.Agatha_q(d)
       && $IsAlloc(d, Tclass._module.Friend(), $h)
     ==> $IsAlloc(_module.Friend._h1(d), TInt, $h));

// Constructor literal
axiom (forall a#33#0#0: int :: 
  { #_module.Friend.Agatha(LitInt(a#33#0#0)) } 
  #_module.Friend.Agatha(LitInt(a#33#0#0))
     == Lit(#_module.Friend.Agatha(a#33#0#0)));

function _module.Friend._h1(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#34#0#0: int :: 
  { #_module.Friend.Agatha(a#34#0#0) } 
  _module.Friend._h1(#_module.Friend.Agatha(a#34#0#0)) == a#34#0#0);

// Constructor function declaration
function #_module.Friend.Jermaine(int) : DatatypeType;

const unique ##_module.Friend.Jermaine: DtCtorId;

// Constructor identifier
axiom (forall a#35#0#0: int :: 
  { #_module.Friend.Jermaine(a#35#0#0) } 
  DatatypeCtorId(#_module.Friend.Jermaine(a#35#0#0)) == ##_module.Friend.Jermaine);

function _module.Friend.Jermaine_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Friend.Jermaine_q(d) } 
  _module.Friend.Jermaine_q(d) <==> DatatypeCtorId(d) == ##_module.Friend.Jermaine);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Friend.Jermaine_q(d) } 
  _module.Friend.Jermaine_q(d)
     ==> (exists a#36#0#0: int :: d == #_module.Friend.Jermaine(a#36#0#0)));

// Constructor $Is
axiom (forall a#37#0#0: int :: 
  { $Is(#_module.Friend.Jermaine(a#37#0#0), Tclass._module.Friend()) } 
  $Is(#_module.Friend.Jermaine(a#37#0#0), Tclass._module.Friend())
     <==> $Is(a#37#0#0, TInt));

// Constructor $IsAlloc
axiom (forall a#38#0#0: int, $h: Heap :: 
  { $IsAlloc(#_module.Friend.Jermaine(a#38#0#0), Tclass._module.Friend(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Friend.Jermaine(a#38#0#0), Tclass._module.Friend(), $h)
       <==> $IsAlloc(a#38#0#0, TInt, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Friend._h2(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Friend.Jermaine_q(d)
       && $IsAlloc(d, Tclass._module.Friend(), $h)
     ==> $IsAlloc(_module.Friend._h2(d), TInt, $h));

// Constructor literal
axiom (forall a#39#0#0: int :: 
  { #_module.Friend.Jermaine(LitInt(a#39#0#0)) } 
  #_module.Friend.Jermaine(LitInt(a#39#0#0))
     == Lit(#_module.Friend.Jermaine(a#39#0#0)));

function _module.Friend._h2(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#40#0#0: int :: 
  { #_module.Friend.Jermaine(a#40#0#0) } 
  _module.Friend._h2(#_module.Friend.Jermaine(a#40#0#0)) == a#40#0#0);

// Constructor function declaration
function #_module.Friend.Jack(int) : DatatypeType;

const unique ##_module.Friend.Jack: DtCtorId;

// Constructor identifier
axiom (forall a#41#0#0: int :: 
  { #_module.Friend.Jack(a#41#0#0) } 
  DatatypeCtorId(#_module.Friend.Jack(a#41#0#0)) == ##_module.Friend.Jack);

function _module.Friend.Jack_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Friend.Jack_q(d) } 
  _module.Friend.Jack_q(d) <==> DatatypeCtorId(d) == ##_module.Friend.Jack);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Friend.Jack_q(d) } 
  _module.Friend.Jack_q(d)
     ==> (exists a#42#0#0: int :: d == #_module.Friend.Jack(a#42#0#0)));

// Constructor $Is
axiom (forall a#43#0#0: int :: 
  { $Is(#_module.Friend.Jack(a#43#0#0), Tclass._module.Friend()) } 
  $Is(#_module.Friend.Jack(a#43#0#0), Tclass._module.Friend())
     <==> $Is(a#43#0#0, TInt));

// Constructor $IsAlloc
axiom (forall a#44#0#0: int, $h: Heap :: 
  { $IsAlloc(#_module.Friend.Jack(a#44#0#0), Tclass._module.Friend(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Friend.Jack(a#44#0#0), Tclass._module.Friend(), $h)
       <==> $IsAlloc(a#44#0#0, TInt, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Friend._h3(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Friend.Jack_q(d)
       && $IsAlloc(d, Tclass._module.Friend(), $h)
     ==> $IsAlloc(_module.Friend._h3(d), TInt, $h));

// Constructor literal
axiom (forall a#45#0#0: int :: 
  { #_module.Friend.Jack(LitInt(a#45#0#0)) } 
  #_module.Friend.Jack(LitInt(a#45#0#0)) == Lit(#_module.Friend.Jack(a#45#0#0)));

function _module.Friend._h3(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#46#0#0: int :: 
  { #_module.Friend.Jack(a#46#0#0) } 
  _module.Friend._h3(#_module.Friend.Jack(a#46#0#0)) == a#46#0#0);

// Depth-one case-split function
function $IsA#_module.Friend(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.Friend(d) } 
  $IsA#_module.Friend(d)
     ==> _module.Friend.Agnes_q(d)
       || _module.Friend.Agatha_q(d)
       || _module.Friend.Jermaine_q(d)
       || _module.Friend.Jack_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.Friend.Jack_q(d), $Is(d, Tclass._module.Friend()) } 
    { _module.Friend.Jermaine_q(d), $Is(d, Tclass._module.Friend()) } 
    { _module.Friend.Agatha_q(d), $Is(d, Tclass._module.Friend()) } 
    { _module.Friend.Agnes_q(d), $Is(d, Tclass._module.Friend()) } 
  $Is(d, Tclass._module.Friend())
     ==> _module.Friend.Agnes_q(d)
       || _module.Friend.Agatha_q(d)
       || _module.Friend.Jermaine_q(d)
       || _module.Friend.Jack_q(d));

// Datatype extensional equality declaration
function _module.Friend#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.Friend.Agnes
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Friend#Equal(a, b), _module.Friend.Agnes_q(a) } 
    { _module.Friend#Equal(a, b), _module.Friend.Agnes_q(b) } 
  _module.Friend.Agnes_q(a) && _module.Friend.Agnes_q(b)
     ==> (_module.Friend#Equal(a, b) <==> _module.Friend._h0(a) == _module.Friend._h0(b)));

// Datatype extensional equality definition: #_module.Friend.Agatha
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Friend#Equal(a, b), _module.Friend.Agatha_q(a) } 
    { _module.Friend#Equal(a, b), _module.Friend.Agatha_q(b) } 
  _module.Friend.Agatha_q(a) && _module.Friend.Agatha_q(b)
     ==> (_module.Friend#Equal(a, b) <==> _module.Friend._h1(a) == _module.Friend._h1(b)));

// Datatype extensional equality definition: #_module.Friend.Jermaine
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Friend#Equal(a, b), _module.Friend.Jermaine_q(a) } 
    { _module.Friend#Equal(a, b), _module.Friend.Jermaine_q(b) } 
  _module.Friend.Jermaine_q(a) && _module.Friend.Jermaine_q(b)
     ==> (_module.Friend#Equal(a, b) <==> _module.Friend._h2(a) == _module.Friend._h2(b)));

// Datatype extensional equality definition: #_module.Friend.Jack
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Friend#Equal(a, b), _module.Friend.Jack_q(a) } 
    { _module.Friend#Equal(a, b), _module.Friend.Jack_q(b) } 
  _module.Friend.Jack_q(a) && _module.Friend.Jack_q(b)
     ==> (_module.Friend#Equal(a, b) <==> _module.Friend._h3(a) == _module.Friend._h3(b)));

// Datatype extensionality axiom: _module.Friend
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Friend#Equal(a, b) } 
  _module.Friend#Equal(a, b) <==> a == b);

const unique class._module.Friend: ClassName;

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

procedure CheckWellformed$$_module.__default.M0(n#0: int);
  free requires 31 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.M0(n#0: int);
  // user-defined preconditions
  requires (var f#0 := LitInt(100); n#0 < f#0);
  requires (var t#0, f#1 := Lit(true), Lit(false); (t#0 && f#1) || n#0 < 100);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.M0(n#0: int) returns ($_reverifyPost: bool);
  free requires 31 == $FunctionContextHeight;
  // user-defined preconditions
  requires (var f#0 := LitInt(100); n#0 < f#0);
  requires (var t#0, f#1 := Lit(true), Lit(false); (t#0 && f#1) || n#0 < 100);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.M0(n#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: M0, Impl$$_module.__default.M0
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(7,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(8,3)
    assume true;
    assert n#0 < 200;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(9,3)
    assume true;
    assert LitInt(0) <= n#0;
}



procedure CheckWellformed$$_module.__default.M1();
  free requires 32 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.M1();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.M1() returns ($_reverifyPost: bool);
  free requires 32 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.M1() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var f#Z#0: int;
  var let#0#0#0: int;
  var g#Z#0: int;
  var let#1#0#0: int;

    // AddMethodImpl: M1, Impl$$_module.__default.M1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(13,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(14,3)
    havoc f#Z#0;
    assume true;
    assume let#0#0#0 == LitInt(54);
    assume true;
    // CheckWellformedWithResult: any expression
    assume $Is(let#0#0#0, TInt);
    assume f#Z#0 == let#0#0#0;
    havoc g#Z#0;
    assume true;
    assume let#1#0#0 == f#Z#0 + 1;
    assume true;
    // CheckWellformedWithResult: any expression
    assume $Is(let#1#0#0, TInt);
    assume g#Z#0 == let#1#0#0;
    assume true;
    assert (var f#0 := LitInt(54); (var g#0 := LitInt(f#0 + 1); g#0 == LitInt(55)));
}



procedure CheckWellformed$$_module.__default.M2();
  free requires 33 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.M2();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.M2() returns ($_reverifyPost: bool);
  free requires 33 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.M2() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var f#Z#0: int;
  var let#0#0#0: int;
  var f#Z#1: int;
  var let#1#0#0: int;

    // AddMethodImpl: M2, Impl$$_module.__default.M2
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(18,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(19,3)
    havoc f#Z#0;
    assume true;
    assume let#0#0#0 == LitInt(54);
    assume true;
    // CheckWellformedWithResult: any expression
    assume $Is(let#0#0#0, TInt);
    assume f#Z#0 == let#0#0#0;
    havoc f#Z#1;
    assume true;
    assume let#1#0#0 == f#Z#0 + 1;
    assume true;
    // CheckWellformedWithResult: any expression
    assume $Is(let#1#0#0, TInt);
    assume f#Z#1 == let#1#0#0;
    assume true;
    assert (var f#0 := LitInt(54); (var f#1 := LitInt(f#0 + 1); f#1 == LitInt(55)));
}



// function declaration for _module._default.Fib
function _module.__default.Fib($ly: LayerType, n#0: int) : int;

function _module.__default.Fib#canCall(n#0: int) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, n#0: int :: 
  { _module.__default.Fib($LS($ly), n#0) } 
  _module.__default.Fib($LS($ly), n#0) == _module.__default.Fib($ly, n#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, n#0: int :: 
  { _module.__default.Fib(AsFuelBottom($ly), n#0) } 
  _module.__default.Fib($ly, n#0) == _module.__default.Fib($LZ, n#0));

// consequence axiom for _module.__default.Fib
axiom 5 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: int :: 
    { _module.__default.Fib($ly, n#0) } 
    _module.__default.Fib#canCall(n#0)
         || (5 != $FunctionContextHeight && LitInt(0) <= n#0)
       ==> LitInt(0) <= _module.__default.Fib($ly, n#0));

function _module.__default.Fib#requires(LayerType, int) : bool;

// #requires axiom for _module.__default.Fib
axiom (forall $ly: LayerType, n#0: int :: 
  { _module.__default.Fib#requires($ly, n#0) } 
  LitInt(0) <= n#0 ==> _module.__default.Fib#requires($ly, n#0) == true);

// definition axiom for _module.__default.Fib (revealed)
axiom 5 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: int :: 
    { _module.__default.Fib($LS($ly), n#0) } 
    _module.__default.Fib#canCall(n#0)
         || (5 != $FunctionContextHeight && LitInt(0) <= n#0)
       ==> (2 <= n#0
           ==> _module.__default.Fib#canCall(n#0 - 1) && _module.__default.Fib#canCall(n#0 - 2))
         && _module.__default.Fib($LS($ly), n#0)
           == (if n#0 < 2
             then n#0
             else _module.__default.Fib($ly, n#0 - 1) + _module.__default.Fib($ly, n#0 - 2)));

// definition axiom for _module.__default.Fib for all literals (revealed)
axiom 5 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: int :: 
    {:weight 3} { _module.__default.Fib($LS($ly), LitInt(n#0)) } 
    _module.__default.Fib#canCall(LitInt(n#0))
         || (5 != $FunctionContextHeight && LitInt(0) <= n#0)
       ==> (!Lit(n#0 < 2)
           ==> _module.__default.Fib#canCall(LitInt(n#0 - 1))
             && _module.__default.Fib#canCall(LitInt(n#0 - 2)))
         && _module.__default.Fib($LS($ly), LitInt(n#0))
           == (if n#0 < 2
             then n#0
             else _module.__default.Fib($LS($ly), LitInt(n#0 - 1))
               + _module.__default.Fib($LS($ly), LitInt(n#0 - 2))));

procedure CheckWellformed$$_module.__default.Fib(n#0: int where LitInt(0) <= n#0);
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Fib(n#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##n#0: int;
  var ##n#1: int;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function Fib
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(22,16): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume LitInt(0) <= _module.__default.Fib($LS($LZ), n#0);
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (n#0 < 2)
        {
            assume _module.__default.Fib($LS($LZ), n#0) == n#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.Fib($LS($LZ), n#0), Tclass._System.nat());
        }
        else
        {
            assert $Is(n#0 - 1, Tclass._System.nat());
            ##n#0 := n#0 - 1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0 <= n#0 || ##n#0 == n#0;
            assert ##n#0 < n#0;
            assume _module.__default.Fib#canCall(n#0 - 1);
            assert $Is(n#0 - 2, Tclass._System.nat());
            ##n#1 := n#0 - 2;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#1, Tclass._System.nat(), $Heap);
            b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0 <= n#0 || ##n#1 == n#0;
            assert ##n#1 < n#0;
            assume _module.__default.Fib#canCall(n#0 - 2);
            assert $Is(_module.__default.Fib($LS($LZ), n#0 - 1)
                 + _module.__default.Fib($LS($LZ), n#0 - 2), 
              Tclass._System.nat());
            assume _module.__default.Fib($LS($LZ), n#0)
               == _module.__default.Fib($LS($LZ), n#0 - 1)
                 + _module.__default.Fib($LS($LZ), n#0 - 2);
            assume _module.__default.Fib#canCall(n#0 - 1) && _module.__default.Fib#canCall(n#0 - 2);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.Fib($LS($LZ), n#0), Tclass._System.nat());
        }

        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



procedure CheckWellformed$$_module.__default.M3(a#0: ref
       where $Is(a#0, Tclass._System.array(TInt))
         && $IsAlloc(a#0, Tclass._System.array(TInt), $Heap))
   returns (r#0: int);
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.M3(a#0: ref) returns (r#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var i#0: int;
  var t#Z#0: int;
  var let#0#0#0: int;

    // AddMethodImpl: M3, CheckWellformed$$_module.__default.M3
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(27,7): initial state"} true;
    havoc i#0;
    assume true;
    if (*)
    {
        assume LitInt(0) <= i#0;
        assert a#0 != null;
        assume i#0 < _System.array.Length(a#0);
        assert a#0 != null;
        assert 0 <= i#0 && i#0 < _System.array.Length(a#0);
        assume $Unbox(read($Heap, a#0, IndexField(i#0))): int == LitInt(6);
    }
    else
    {
        assume LitInt(0) <= i#0 && i#0 < _System.array.Length(a#0)
           ==> $Unbox(read($Heap, a#0, IndexField(i#0))): int == LitInt(6);
    }

    assume (forall i#1: int :: 
      { $Unbox(read($Heap, a#0, IndexField(i#1))): int } 
      true
         ==> 
        LitInt(0) <= i#1 && i#1 < _System.array.Length(a#0)
         ==> $Unbox(read($Heap, a#0, IndexField(i#1))): int == LitInt(6));
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
    assume $HeapSucc(old($Heap), $Heap);
    havoc r#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(29,32): post-state"} true;
    havoc t#Z#0;
    assume true;
    assume let#0#0#0 == r#0;
    assume true;
    // CheckWellformedWithResult: any expression
    assume $Is(let#0#0#0, TInt);
    assume t#Z#0 == let#0#0#0;
    assume r#0 + (var t#0 := r#0; Mul(t#0, LitInt(2))) == Mul(LitInt(3), r#0);
}



procedure Call$$_module.__default.M3(a#0: ref
       where $Is(a#0, Tclass._System.array(TInt))
         && $IsAlloc(a#0, Tclass._System.array(TInt), $Heap))
   returns (r#0: int);
  // user-defined preconditions
  requires (forall i#1: int :: 
    { $Unbox(read($Heap, a#0, IndexField(i#1))): int } 
    true
       ==> 
      LitInt(0) <= i#1 && i#1 < _System.array.Length(a#0)
       ==> $Unbox(read($Heap, a#0, IndexField(i#1))): int == LitInt(6));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures r#0 + (var t#0 := r#0; Mul(t#0, LitInt(2))) == Mul(LitInt(3), r#0);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.M3(a#0: ref
       where $Is(a#0, Tclass._System.array(TInt))
         && $IsAlloc(a#0, Tclass._System.array(TInt), $Heap))
   returns (r#0: int, $_reverifyPost: bool);
  free requires 6 == $FunctionContextHeight;
  // user-defined preconditions
  requires (forall i#1: int :: 
    { $Unbox(read($Heap, a#0, IndexField(i#1))): int } 
    true
       ==> 
      LitInt(0) <= i#1 && i#1 < _System.array.Length(a#0)
       ==> $Unbox(read($Heap, a#0, IndexField(i#1))): int == LitInt(6));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures r#0 + (var t#0 := r#0; Mul(t#0, LitInt(2))) == Mul(LitInt(3), r#0);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.M3(a#0: ref) returns (r#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##n#0: int;
  var ##n#1: int;
  var ##n#2: int;
  var ##n#3: int;
  var ##n#4: int;
  var ##n#5: int;
  var x#0: int where LitInt(0) <= x#0;
  var y#0: int where LitInt(0) <= y#0;
  var $rhs#0: int where LitInt(0) <= $rhs#0;
  var ##n#6: int;
  var $rhs#1: int where LitInt(0) <= $rhs#1;
  var ##n#7: int;
  var ##n#8: int;
  var ##n#9: int;
  var ##n#10: int;
  var ##n#11: int;
  var ##n#12: int;
  var ##n#13: int;
  var ##n#14: int;
  var ##n#15: int;
  var i#2: int;
  var j#0: int;

    // AddMethodImpl: M3, Impl$$_module.__default.M3
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(30,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(31,3)
    assert $Is(LitInt(2), Tclass._System.nat());
    ##n#0 := LitInt(2);
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
    assume _module.__default.Fib#canCall(LitInt(2));
    assert $Is(LitInt(4), Tclass._System.nat());
    ##n#1 := LitInt(4);
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#1, Tclass._System.nat(), $Heap);
    assume _module.__default.Fib#canCall(LitInt(4));
    assert $Is(LitInt(0), Tclass._System.nat());
    ##n#2 := LitInt(0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#2, Tclass._System.nat(), $Heap);
    assume _module.__default.Fib#canCall(LitInt(0));
    assert $Is(LitInt(1), Tclass._System.nat());
    ##n#3 := LitInt(1);
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#3, Tclass._System.nat(), $Heap);
    assume _module.__default.Fib#canCall(LitInt(1));
    assert $Is(LitInt(2), Tclass._System.nat());
    ##n#4 := LitInt(2);
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#4, Tclass._System.nat(), $Heap);
    assume _module.__default.Fib#canCall(LitInt(2));
    assert $Is(LitInt(3), Tclass._System.nat());
    ##n#5 := LitInt(3);
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#5, Tclass._System.nat(), $Heap);
    assume _module.__default.Fib#canCall(LitInt(3));
    assume _module.__default.Fib#canCall(LitInt(2))
       && _module.__default.Fib#canCall(LitInt(4))
       && 
      _module.__default.Fib#canCall(LitInt(0))
       && _module.__default.Fib#canCall(LitInt(1))
       && _module.__default.Fib#canCall(LitInt(2))
       && _module.__default.Fib#canCall(LitInt(3));
    assert {:subsumption 0} LitInt(_module.__default.Fib($LS($LS($LZ)), LitInt(2))
           + _module.__default.Fib($LS($LS($LZ)), LitInt(4)))
       == LitInt(_module.__default.Fib($LS($LS($LZ)), LitInt(0))
           + _module.__default.Fib($LS($LS($LZ)), LitInt(1))
           + _module.__default.Fib($LS($LS($LZ)), LitInt(2))
           + _module.__default.Fib($LS($LS($LZ)), LitInt(3)));
    assume LitInt(_module.__default.Fib($LS($LZ), LitInt(2))
           + _module.__default.Fib($LS($LZ), LitInt(4)))
       == LitInt(_module.__default.Fib($LS($LZ), LitInt(0))
           + _module.__default.Fib($LS($LZ), LitInt(1))
           + _module.__default.Fib($LS($LZ), LitInt(2))
           + _module.__default.Fib($LS($LZ), LitInt(3)));
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(34,13)
    assume true;
    assume true;
    assert $Is(LitInt(8), Tclass._System.nat());
    ##n#6 := LitInt(8);
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#6, Tclass._System.nat(), $Heap);
    assume _module.__default.Fib#canCall(LitInt(8));
    assume _module.__default.Fib#canCall(LitInt(8));
    $rhs#0 := LitInt(_module.__default.Fib($LS($LZ), LitInt(8)));
    assert $Is(LitInt(11), Tclass._System.nat());
    ##n#7 := LitInt(11);
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#7, Tclass._System.nat(), $Heap);
    assume _module.__default.Fib#canCall(LitInt(11));
    assume _module.__default.Fib#canCall(LitInt(11));
    $rhs#1 := LitInt(_module.__default.Fib($LS($LZ), LitInt(11)));
    x#0 := $rhs#0;
    y#0 := $rhs#1;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(34,30)"} true;
    // ----- assume statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(35,5)
    assume true;
    assume x#0 == LitInt(21);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(36,5)
    assert $Is(LitInt(7), Tclass._System.nat());
    ##n#8 := LitInt(7);
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#8, Tclass._System.nat(), $Heap);
    assume _module.__default.Fib#canCall(LitInt(7));
    if (LitInt(_module.__default.Fib($LS($LZ), LitInt(7))) == LitInt(3))
    {
        assert $Is(LitInt(9), Tclass._System.nat());
        ##n#9 := LitInt(9);
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#9, Tclass._System.nat(), $Heap);
        assume _module.__default.Fib#canCall(LitInt(9));
    }

    assume _module.__default.Fib#canCall(LitInt(7))
       && (LitInt(_module.__default.Fib($LS($LZ), LitInt(7))) == LitInt(3)
         ==> _module.__default.Fib#canCall(LitInt(9)));
    assert {:subsumption 0} LitInt(_module.__default.Fib($LS($LZ), LitInt(7))) == LitInt(3)
       ==> LitInt(_module.__default.Fib($LS($LS($LZ)), LitInt(9))) == LitInt(24);
    assume LitInt(_module.__default.Fib($LS($LZ), LitInt(7))) == LitInt(3)
       ==> LitInt(_module.__default.Fib($LS($LZ), LitInt(9))) == LitInt(24);
    // ----- assume statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(37,5)
    assert $Is(LitInt(1000), Tclass._System.nat());
    ##n#10 := LitInt(1000);
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#10, Tclass._System.nat(), $Heap);
    assume _module.__default.Fib#canCall(LitInt(1000));
    assume _module.__default.Fib#canCall(LitInt(1000));
    assume LitInt(_module.__default.Fib($LS($LZ), LitInt(1000))) == LitInt(1000);
    // ----- assume statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(38,5)
    assert $Is(LitInt(9), Tclass._System.nat());
    ##n#11 := LitInt(9);
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#11, Tclass._System.nat(), $Heap);
    assume _module.__default.Fib#canCall(LitInt(9));
    assert $Is(LitInt(8), Tclass._System.nat());
    ##n#12 := LitInt(8);
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#12, Tclass._System.nat(), $Heap);
    assume _module.__default.Fib#canCall(LitInt(8));
    assume _module.__default.Fib#canCall(LitInt(9))
       && _module.__default.Fib#canCall(LitInt(8));
    assume LitInt(_module.__default.Fib($LS($LZ), LitInt(9))
           - _module.__default.Fib($LS($LZ), LitInt(8)))
       == LitInt(13);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(39,5)
    assert $Is(LitInt(9), Tclass._System.nat());
    ##n#13 := LitInt(9);
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#13, Tclass._System.nat(), $Heap);
    assume _module.__default.Fib#canCall(LitInt(9));
    assert $Is(LitInt(10), Tclass._System.nat());
    ##n#14 := LitInt(10);
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#14, Tclass._System.nat(), $Heap);
    assume _module.__default.Fib#canCall(LitInt(10));
    assume _module.__default.Fib#canCall(LitInt(9))
       && _module.__default.Fib#canCall(LitInt(10));
    assert {:subsumption 0} LitInt(_module.__default.Fib($LS($LS($LZ)), LitInt(9)))
       <= LitInt(_module.__default.Fib($LS($LS($LZ)), LitInt(10)));
    assume LitInt(_module.__default.Fib($LS($LZ), LitInt(9)))
       <= LitInt(_module.__default.Fib($LS($LZ), LitInt(10)));
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(40,5)
    assume true;
    assert y#0 == LitInt(89);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(43,3)
    assert $Is(LitInt(1000), Tclass._System.nat());
    ##n#15 := LitInt(1000);
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#15, Tclass._System.nat(), $Heap);
    assume _module.__default.Fib#canCall(LitInt(1000));
    assume _module.__default.Fib#canCall(LitInt(1000));
    assert {:subsumption 0} LitInt(_module.__default.Fib($LS($LS($LZ)), LitInt(1000))) == LitInt(1000);
    assume LitInt(_module.__default.Fib($LS($LZ), LitInt(1000))) == LitInt(1000);
    // ----- forall statement (proof) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(45,3)
    if (*)
    {
        // Assume Fuel Constant
        havoc i#2;
        assume true;
        if (LitInt(0) <= i#2)
        {
            assert {:subsumption 0} a#0 != null;
        }

        assume true;
        assume LitInt(0) <= i#2 && i#2 < _System.array.Length(a#0);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(46,11)
        assume true;
        assume true;
        j#0 := i#2 + 1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(46,16)"} true;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(47,5)
        assert {:subsumption 0} a#0 != null;
        if (j#0 < _System.array.Length(a#0))
        {
            assert a#0 != null;
            assert {:subsumption 0} 0 <= i#2 && i#2 < _System.array.Length(a#0);
            assert a#0 != null;
            assert {:subsumption 0} 0 <= j#0 && j#0 < _System.array.Length(a#0);
        }

        assume true;
        assert {:subsumption 0} j#0 < _System.array.Length(a#0)
           ==> $Unbox(read($Heap, a#0, IndexField(i#2))): int
             == $Unbox(read($Heap, a#0, IndexField(j#0))): int;
        assume j#0 < _System.array.Length(a#0)
           ==> $Unbox(read($Heap, a#0, IndexField(i#2))): int
             == $Unbox(read($Heap, a#0, IndexField(j#0))): int;
        assert true;
        assume false;
    }
    else
    {
        assume (forall i#3: int :: 
          LitInt(0) <= i#3 && i#3 < _System.array.Length(a#0) ==> Lit(true));
    }

    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(48,2)"} true;
}



procedure CheckWellformed$$_module.__default.M4(a#0: ref
       where $Is(a#0, Tclass._System.array(TInt))
         && $IsAlloc(a#0, Tclass._System.array(TInt), $Heap))
   returns (r#0: int);
  free requires 7 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.M4(a#0: ref) returns (r#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var i#0: int;
  var t#Z#0: int;
  var let#0#0#0: int;

    // AddMethodImpl: M4, CheckWellformed$$_module.__default.M4
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(52,7): initial state"} true;
    havoc i#0;
    assume true;
    if (*)
    {
        assume LitInt(0) <= i#0;
        assert a#0 != null;
        assume i#0 < _System.array.Length(a#0);
        assert a#0 != null;
        assert 0 <= i#0 && i#0 < _System.array.Length(a#0);
        assume $Unbox(read($Heap, a#0, IndexField(i#0))): int == LitInt(6);
    }
    else
    {
        assume LitInt(0) <= i#0 && i#0 < _System.array.Length(a#0)
           ==> $Unbox(read($Heap, a#0, IndexField(i#0))): int == LitInt(6);
    }

    assume (forall i#1: int :: 
      { $Unbox(read($Heap, a#0, IndexField(i#1))): int } 
      true
         ==> 
        LitInt(0) <= i#1 && i#1 < _System.array.Length(a#0)
         ==> $Unbox(read($Heap, a#0, IndexField(i#1))): int == LitInt(6));
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
    assume $HeapSucc(old($Heap), $Heap);
    havoc r#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(54,32): post-state"} true;
    havoc t#Z#0;
    assume true;
    assume let#0#0#0 == r#0;
    assume true;
    // CheckWellformedWithResult: any expression
    assume $Is(let#0#0#0, TInt);
    assume t#Z#0 == let#0#0#0;
    assume r#0 + (var t#0 := r#0; Mul(t#0, LitInt(2))) == Mul(LitInt(3), r#0);
}



procedure Call$$_module.__default.M4(a#0: ref
       where $Is(a#0, Tclass._System.array(TInt))
         && $IsAlloc(a#0, Tclass._System.array(TInt), $Heap))
   returns (r#0: int);
  // user-defined preconditions
  requires (forall i#1: int :: 
    { $Unbox(read($Heap, a#0, IndexField(i#1))): int } 
    true
       ==> 
      LitInt(0) <= i#1 && i#1 < _System.array.Length(a#0)
       ==> $Unbox(read($Heap, a#0, IndexField(i#1))): int == LitInt(6));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures r#0 + (var t#0 := r#0; Mul(t#0, LitInt(2))) == Mul(LitInt(3), r#0);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.M4(a#0: ref
       where $Is(a#0, Tclass._System.array(TInt))
         && $IsAlloc(a#0, Tclass._System.array(TInt), $Heap))
   returns (r#0: int, $_reverifyPost: bool);
  free requires 7 == $FunctionContextHeight;
  // user-defined preconditions
  requires (forall i#1: int :: 
    { $Unbox(read($Heap, a#0, IndexField(i#1))): int } 
    true
       ==> 
      LitInt(0) <= i#1 && i#1 < _System.array.Length(a#0)
       ==> $Unbox(read($Heap, a#0, IndexField(i#1))): int == LitInt(6));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures r#0 + (var t#0 := r#0; Mul(t#0, LitInt(2))) == Mul(LitInt(3), r#0);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.M4(a#0: ref) returns (r#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##n#0: int;
  var ##n#1: int;
  var ##n#2: int;
  var ##n#3: int;
  var ##n#4: int;
  var ##n#5: int;
  var x#Z#0: int;
  var y#Z#0: int;
  var let#1#0#0: int;
  var ##n#6: int;
  var let#1#1#0: int;
  var ##n#7: int;
  var ##n#8: int;
  var ##n#9: int;
  var ##n#10: int;
  var ##n#11: int;
  var ##n#12: int;
  var ##n#13: int;
  var ##n#14: int;
  var ##n#15: int;
  var i#2: int;
  var j#Z#0: int;
  var let#2#0#0: int;

    // AddMethodImpl: M4, Impl$$_module.__default.M4
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(55,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(56,3)
    assert $Is(LitInt(2), Tclass._System.nat());
    ##n#0 := LitInt(2);
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
    assume _module.__default.Fib#canCall(LitInt(2));
    assert $Is(LitInt(4), Tclass._System.nat());
    ##n#1 := LitInt(4);
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#1, Tclass._System.nat(), $Heap);
    assume _module.__default.Fib#canCall(LitInt(4));
    assert $Is(LitInt(0), Tclass._System.nat());
    ##n#2 := LitInt(0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#2, Tclass._System.nat(), $Heap);
    assume _module.__default.Fib#canCall(LitInt(0));
    assert $Is(LitInt(1), Tclass._System.nat());
    ##n#3 := LitInt(1);
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#3, Tclass._System.nat(), $Heap);
    assume _module.__default.Fib#canCall(LitInt(1));
    assert $Is(LitInt(2), Tclass._System.nat());
    ##n#4 := LitInt(2);
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#4, Tclass._System.nat(), $Heap);
    assume _module.__default.Fib#canCall(LitInt(2));
    assert $Is(LitInt(3), Tclass._System.nat());
    ##n#5 := LitInt(3);
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#5, Tclass._System.nat(), $Heap);
    assume _module.__default.Fib#canCall(LitInt(3));
    assume _module.__default.Fib#canCall(LitInt(2))
       && _module.__default.Fib#canCall(LitInt(4))
       && 
      _module.__default.Fib#canCall(LitInt(0))
       && _module.__default.Fib#canCall(LitInt(1))
       && _module.__default.Fib#canCall(LitInt(2))
       && _module.__default.Fib#canCall(LitInt(3));
    assert {:subsumption 0} LitInt(_module.__default.Fib($LS($LS($LZ)), LitInt(2))
           + _module.__default.Fib($LS($LS($LZ)), LitInt(4)))
       == LitInt(_module.__default.Fib($LS($LS($LZ)), LitInt(0))
           + _module.__default.Fib($LS($LS($LZ)), LitInt(1))
           + _module.__default.Fib($LS($LS($LZ)), LitInt(2))
           + _module.__default.Fib($LS($LS($LZ)), LitInt(3)));
    assume LitInt(_module.__default.Fib($LS($LZ), LitInt(2))
           + _module.__default.Fib($LS($LZ), LitInt(4)))
       == LitInt(_module.__default.Fib($LS($LZ), LitInt(0))
           + _module.__default.Fib($LS($LZ), LitInt(1))
           + _module.__default.Fib($LS($LZ), LitInt(2))
           + _module.__default.Fib($LS($LZ), LitInt(3)));
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(57,3)
    havoc x#Z#0;
    havoc y#Z#0;
    assume LitInt(0) <= x#Z#0 && LitInt(0) <= y#Z#0;
    assert $Is(LitInt(8), Tclass._System.nat());
    ##n#6 := LitInt(8);
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#6, Tclass._System.nat(), $Heap);
    assume _module.__default.Fib#canCall(LitInt(8));
    assume let#1#0#0 == LitInt(_module.__default.Fib($LS($LZ), LitInt(8)));
    assume _module.__default.Fib#canCall(LitInt(8));
    // CheckWellformedWithResult: any expression
    assume $Is(let#1#0#0, Tclass._System.nat());
    assume x#Z#0 == let#1#0#0;
    assert $Is(LitInt(11), Tclass._System.nat());
    ##n#7 := LitInt(11);
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#7, Tclass._System.nat(), $Heap);
    assume _module.__default.Fib#canCall(LitInt(11));
    assume let#1#1#0 == LitInt(_module.__default.Fib($LS($LZ), LitInt(11)));
    assume _module.__default.Fib#canCall(LitInt(11));
    // CheckWellformedWithResult: any expression
    assume $Is(let#1#1#0, Tclass._System.nat());
    assume y#Z#0 == let#1#1#0;
    // ----- assume statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(59,5)
    assume true;
    assume x#Z#0 == LitInt(21);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(60,5)
    assert $Is(LitInt(7), Tclass._System.nat());
    ##n#8 := LitInt(7);
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#8, Tclass._System.nat(), $Heap);
    assume _module.__default.Fib#canCall(LitInt(7));
    if (LitInt(_module.__default.Fib($LS($LZ), LitInt(7))) == LitInt(3))
    {
        assert $Is(LitInt(9), Tclass._System.nat());
        ##n#9 := LitInt(9);
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#9, Tclass._System.nat(), $Heap);
        assume _module.__default.Fib#canCall(LitInt(9));
    }

    assume _module.__default.Fib#canCall(LitInt(7))
       && (LitInt(_module.__default.Fib($LS($LZ), LitInt(7))) == LitInt(3)
         ==> _module.__default.Fib#canCall(LitInt(9)));
    assert {:subsumption 0} LitInt(_module.__default.Fib($LS($LZ), LitInt(7))) == LitInt(3)
       ==> LitInt(_module.__default.Fib($LS($LS($LZ)), LitInt(9))) == LitInt(24);
    assume LitInt(_module.__default.Fib($LS($LZ), LitInt(7))) == LitInt(3)
       ==> LitInt(_module.__default.Fib($LS($LZ), LitInt(9))) == LitInt(24);
    // ----- assume statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(61,5)
    assert $Is(LitInt(1000), Tclass._System.nat());
    ##n#10 := LitInt(1000);
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#10, Tclass._System.nat(), $Heap);
    assume _module.__default.Fib#canCall(LitInt(1000));
    assume _module.__default.Fib#canCall(LitInt(1000));
    assume LitInt(_module.__default.Fib($LS($LZ), LitInt(1000))) == LitInt(1000);
    // ----- assume statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(62,5)
    assert $Is(LitInt(9), Tclass._System.nat());
    ##n#11 := LitInt(9);
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#11, Tclass._System.nat(), $Heap);
    assume _module.__default.Fib#canCall(LitInt(9));
    assert $Is(LitInt(8), Tclass._System.nat());
    ##n#12 := LitInt(8);
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#12, Tclass._System.nat(), $Heap);
    assume _module.__default.Fib#canCall(LitInt(8));
    assume _module.__default.Fib#canCall(LitInt(9))
       && _module.__default.Fib#canCall(LitInt(8));
    assume LitInt(_module.__default.Fib($LS($LZ), LitInt(9))
           - _module.__default.Fib($LS($LZ), LitInt(8)))
       == LitInt(13);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(63,5)
    assert $Is(LitInt(9), Tclass._System.nat());
    ##n#13 := LitInt(9);
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#13, Tclass._System.nat(), $Heap);
    assume _module.__default.Fib#canCall(LitInt(9));
    assert $Is(LitInt(10), Tclass._System.nat());
    ##n#14 := LitInt(10);
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#14, Tclass._System.nat(), $Heap);
    assume _module.__default.Fib#canCall(LitInt(10));
    assume _module.__default.Fib#canCall(LitInt(9))
       && _module.__default.Fib#canCall(LitInt(10));
    assert {:subsumption 0} LitInt(_module.__default.Fib($LS($LS($LZ)), LitInt(9)))
       <= LitInt(_module.__default.Fib($LS($LS($LZ)), LitInt(10)));
    assume LitInt(_module.__default.Fib($LS($LZ), LitInt(9)))
       <= LitInt(_module.__default.Fib($LS($LZ), LitInt(10)));
    assume _module.__default.Fib#canCall(LitInt(8))
       && _module.__default.Fib#canCall(LitInt(11));
    assert {:subsumption 0} (var x#0, y#0 := LitInt(_module.__default.Fib($LS($LS($LZ)), LitInt(8))), 
        LitInt(_module.__default.Fib($LS($LS($LZ)), LitInt(11))); 
      x#0 == LitInt(21)
         ==> 
        (LitInt(_module.__default.Fib($LS($LZ), LitInt(7))) == LitInt(3)
         ==> LitInt(_module.__default.Fib($LS($LZ), LitInt(9))) == LitInt(24))
         ==> 
        LitInt(_module.__default.Fib($LS($LZ), LitInt(1000))) == LitInt(1000)
         ==> 
        LitInt(_module.__default.Fib($LS($LZ), LitInt(9))
               - _module.__default.Fib($LS($LZ), LitInt(8)))
           == LitInt(13)
         ==> 
        LitInt(_module.__default.Fib($LS($LZ), LitInt(9)))
           <= LitInt(_module.__default.Fib($LS($LZ), LitInt(10)))
         ==> y#0 == LitInt(89));
    assume (var x#0, y#0 := LitInt(_module.__default.Fib($LS($LZ), LitInt(8))), 
        LitInt(_module.__default.Fib($LS($LZ), LitInt(11))); 
      y#0 == LitInt(89));
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(65,3)
    assert $Is(LitInt(1000), Tclass._System.nat());
    ##n#15 := LitInt(1000);
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#15, Tclass._System.nat(), $Heap);
    assume _module.__default.Fib#canCall(LitInt(1000));
    assume _module.__default.Fib#canCall(LitInt(1000));
    assert {:subsumption 0} LitInt(_module.__default.Fib($LS($LS($LZ)), LitInt(1000))) == LitInt(1000);
    assume LitInt(_module.__default.Fib($LS($LZ), LitInt(1000))) == LitInt(1000);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(66,3)
    // Begin Comprehension WF check
    havoc i#2;
    if (true)
    {
        if (LitInt(0) <= i#2)
        {
            assert {:subsumption 0} a#0 != null;
        }

        if (LitInt(0) <= i#2 && i#2 < _System.array.Length(a#0))
        {
            havoc j#Z#0;
            assume true;
            assume let#2#0#0 == i#2 + 1;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#2#0#0, TInt);
            assume j#Z#0 == let#2#0#0;
            assert {:subsumption 0} a#0 != null;
            if (j#Z#0 < _System.array.Length(a#0))
            {
                assert a#0 != null;
                assert {:subsumption 0} 0 <= i#2 && i#2 < _System.array.Length(a#0);
                assert a#0 != null;
                assert {:subsumption 0} 0 <= j#Z#0 && j#Z#0 < _System.array.Length(a#0);
            }
        }
    }

    // End Comprehension WF check
    assume true;
    assert (forall i#3: int, _t#0#0: int :: 
      { $Unbox(read($Heap, a#0, IndexField(_t#0#0))): int, $Unbox(read($Heap, a#0, IndexField(i#3))): int } 
      _t#0#0 == i#3 + 1
         ==> 
        LitInt(0) <= i#3 && i#3 < _System.array.Length(a#0)
         ==> (var j#0 := _t#0#0; 
          j#0 < _System.array.Length(a#0)
             ==> $Unbox(read($Heap, a#0, IndexField(i#3))): int
               == $Unbox(read($Heap, a#0, IndexField(j#0))): int));
}



procedure CheckWellformed$$_module.__default.Theorem0(n#0: int);
  free requires 23 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Theorem0(n#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##n#0: int;

    // AddMethodImpl: Theorem0, CheckWellformed$$_module.__default.Theorem0
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(119,7): initial state"} true;
    assume LitInt(1) <= n#0;
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
    assume $HeapSucc(old($Heap), $Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(121,12): post-state"} true;
    assert $Is(n#0, Tclass._System.nat());
    ##n#0 := n#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
    assume _module.__default.Fib#canCall(n#0);
    assume LitInt(1) <= _module.__default.Fib($LS($LZ), n#0);
}



procedure Call$$_module.__default.Theorem0(n#0: int);
  // user-defined preconditions
  requires LitInt(1) <= n#0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Fib#canCall(n#0);
  ensures LitInt(1) <= _module.__default.Fib($LS($LS($LZ)), n#0);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.Theorem0(n#0: int) returns ($_reverifyPost: bool);
  free requires 23 == $FunctionContextHeight;
  // user-defined preconditions
  requires LitInt(1) <= n#0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Fib#canCall(n#0);
  ensures LitInt(1) <= _module.__default.Fib($LS($LS($LZ)), n#0);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.Theorem0(n#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var n##0: int;
  var n##1: int;

    // AddMethodImpl: Theorem0, Impl$$_module.__default.Theorem0
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(122,0): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(123,3)
    assume true;
    if (n#0 < 3)
    {
    }
    else
    {
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(125,13)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        n##0 := n#0 - 2;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assert 0 <= n#0 || n##0 == n#0;
        assert n##0 < n#0;
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.Theorem0(n##0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(125,17)"} true;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(126,13)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        n##1 := n#0 - 1;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assert 0 <= n#0 || n##1 == n#0;
        assert n##1 < n#0;
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.Theorem0(n##1);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(126,17)"} true;
    }
}



procedure {:_induction n#0} CheckWellformed$$_module.__default.Theorem1(n#0: int);
  free requires 24 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:_induction n#0} CheckWellformed$$_module.__default.Theorem1(n#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##n#0: int;

    // AddMethodImpl: Theorem1, CheckWellformed$$_module.__default.Theorem1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(130,13): initial state"} true;
    assume LitInt(1) <= n#0;
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(132,12): post-state"} true;
    assert $Is(n#0, Tclass._System.nat());
    ##n#0 := n#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
    assume _module.__default.Fib#canCall(n#0);
    assume LitInt(1) <= _module.__default.Fib($LS($LZ), n#0);
}



procedure {:_induction n#0} Call$$_module.__default.Theorem1(n#0: int);
  // user-defined preconditions
  requires LitInt(1) <= n#0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Fib#canCall(n#0);
  ensures LitInt(1) <= _module.__default.Fib($LS($LS($LZ)), n#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction n#0} Impl$$_module.__default.Theorem1(n#0: int) returns ($_reverifyPost: bool);
  free requires 24 == $FunctionContextHeight;
  // user-defined preconditions
  requires LitInt(1) <= n#0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Fib#canCall(n#0);
  ensures LitInt(1) <= _module.__default.Fib($LS($LS($LZ)), n#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction n#0} Impl$$_module.__default.Theorem1(n#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;

    // AddMethodImpl: Theorem1, Impl$$_module.__default.Theorem1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(133,0): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#n0#0: int :: 
      LitInt(1) <= $ih#n0#0 && 0 <= $ih#n0#0 && $ih#n0#0 < n#0
         ==> LitInt(1) <= _module.__default.Fib($LS($LZ), $ih#n0#0));
    $_reverifyPost := false;
}



// function declaration for _module._default.Theorem2
function _module.__default.Theorem2($ly: LayerType, n#0: int) : int;

function _module.__default.Theorem2#canCall(n#0: int) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, n#0: int :: 
  { _module.__default.Theorem2($LS($ly), n#0) } 
  _module.__default.Theorem2($LS($ly), n#0)
     == _module.__default.Theorem2($ly, n#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, n#0: int :: 
  { _module.__default.Theorem2(AsFuelBottom($ly), n#0) } 
  _module.__default.Theorem2($ly, n#0) == _module.__default.Theorem2($LZ, n#0));

// consequence axiom for _module.__default.Theorem2
axiom 25 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: int :: 
    { _module.__default.Theorem2($ly, n#0) } 
    _module.__default.Theorem2#canCall(n#0)
         || (25 != $FunctionContextHeight && LitInt(1) <= n#0)
       ==> LitInt(1) <= _module.__default.Fib($LS($LZ), n#0));

function _module.__default.Theorem2#requires(LayerType, int) : bool;

// #requires axiom for _module.__default.Theorem2
axiom (forall $ly: LayerType, n#0: int :: 
  { _module.__default.Theorem2#requires($ly, n#0) } 
  _module.__default.Theorem2#requires($ly, n#0) == (LitInt(1) <= n#0));

// definition axiom for _module.__default.Theorem2 (revealed)
axiom 25 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: int :: 
    { _module.__default.Theorem2($LS($ly), n#0) } 
    _module.__default.Theorem2#canCall(n#0)
         || (25 != $FunctionContextHeight && LitInt(1) <= n#0)
       ==> (3 <= n#0
           ==> _module.__default.Theorem2#canCall(n#0 - 2)
             && _module.__default.Theorem2#canCall(n#0 - 1))
         && _module.__default.Theorem2($LS($ly), n#0)
           == (if n#0 < 3
             then 5
             else (var x#0 := _module.__default.Theorem2($ly, n#0 - 2); 
              (var y#0 := _module.__default.Theorem2($ly, n#0 - 1); x#0 + y#0))));

// definition axiom for _module.__default.Theorem2 for all literals (revealed)
axiom 25 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: int :: 
    {:weight 3} { _module.__default.Theorem2($LS($ly), LitInt(n#0)) } 
    _module.__default.Theorem2#canCall(LitInt(n#0))
         || (25 != $FunctionContextHeight && LitInt(1) <= LitInt(n#0))
       ==> (!Lit(n#0 < 3)
           ==> _module.__default.Theorem2#canCall(LitInt(n#0 - 2))
             && _module.__default.Theorem2#canCall(LitInt(n#0 - 1)))
         && _module.__default.Theorem2($LS($ly), LitInt(n#0))
           == (if n#0 < 3
             then 5
             else (var x#1 := LitInt(_module.__default.Theorem2($LS($ly), LitInt(n#0 - 2))); 
              (var y#1 := LitInt(_module.__default.Theorem2($LS($ly), LitInt(n#0 - 1))); 
                LitInt(x#1 + y#1)))));

procedure CheckWellformed$$_module.__default.Theorem2(n#0: int);
  free requires 25 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures LitInt(1) <= _module.__default.Fib($LS($LS($LZ)), n#0);



implementation CheckWellformed$$_module.__default.Theorem2(n#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##n#0: int;
  var x#Z#0: int;
  var let#0#0#0: int;
  var ##n#1: int;
  var y#Z#0: int;
  var let#1#0#0: int;
  var ##n#2: int;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function Theorem2
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(137,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume LitInt(1) <= n#0;
    if (*)
    {
        assert $Is(n#0, Tclass._System.nat());
        ##n#0 := n#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
        assume _module.__default.Fib#canCall(n#0);
        assume LitInt(1) <= _module.__default.Fib($LS($LZ), n#0);
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (n#0 < 3)
        {
            assume _module.__default.Theorem2($LS($LZ), n#0) == LitInt(5);
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.Theorem2($LS($LZ), n#0), TInt);
        }
        else
        {
            havoc x#Z#0;
            assume true;
            ##n#1 := n#0 - 2;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#1, TInt, $Heap);
            assert {:subsumption 0} LitInt(1) <= ##n#1;
            assume LitInt(1) <= ##n#1;
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0 <= n#0 || ##n#1 == n#0;
            assert ##n#1 < n#0;
            assume _module.__default.Theorem2#canCall(n#0 - 2);
            assume let#0#0#0 == _module.__default.Theorem2($LS($LZ), n#0 - 2);
            assume _module.__default.Theorem2#canCall(n#0 - 2);
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, TInt);
            assume x#Z#0 == let#0#0#0;
            havoc y#Z#0;
            assume true;
            ##n#2 := n#0 - 1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#2, TInt, $Heap);
            assert {:subsumption 0} LitInt(1) <= ##n#2;
            assume LitInt(1) <= ##n#2;
            b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0 <= n#0 || ##n#2 == n#0;
            assert ##n#2 < n#0;
            assume _module.__default.Theorem2#canCall(n#0 - 1);
            assume let#1#0#0 == _module.__default.Theorem2($LS($LZ), n#0 - 1);
            assume _module.__default.Theorem2#canCall(n#0 - 1);
            // CheckWellformedWithResult: any expression
            assume $Is(let#1#0#0, TInt);
            assume y#Z#0 == let#1#0#0;
            assume _module.__default.Theorem2($LS($LZ), n#0) == x#Z#0 + y#Z#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.Theorem2($LS($LZ), n#0), TInt);
        }

        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



// function declaration for _module._default.Theorem3
function _module.__default.Theorem3($ly: LayerType, n#0: int) : int;

function _module.__default.Theorem3#canCall(n#0: int) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, n#0: int :: 
  { _module.__default.Theorem3($LS($ly), n#0) } 
  _module.__default.Theorem3($LS($ly), n#0)
     == _module.__default.Theorem3($ly, n#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, n#0: int :: 
  { _module.__default.Theorem3(AsFuelBottom($ly), n#0) } 
  _module.__default.Theorem3($ly, n#0) == _module.__default.Theorem3($LZ, n#0));

// consequence axiom for _module.__default.Theorem3
axiom 26 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: int :: 
    { _module.__default.Theorem3($ly, n#0) } 
    _module.__default.Theorem3#canCall(n#0)
         || (26 != $FunctionContextHeight && LitInt(1) <= n#0)
       ==> LitInt(1) <= _module.__default.Fib($LS($LZ), n#0));

function _module.__default.Theorem3#requires(LayerType, int) : bool;

// #requires axiom for _module.__default.Theorem3
axiom (forall $ly: LayerType, n#0: int :: 
  { _module.__default.Theorem3#requires($ly, n#0) } 
  _module.__default.Theorem3#requires($ly, n#0) == (LitInt(1) <= n#0));

// definition axiom for _module.__default.Theorem3 (revealed)
axiom 26 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: int :: 
    { _module.__default.Theorem3($LS($ly), n#0) } 
    _module.__default.Theorem3#canCall(n#0)
         || (26 != $FunctionContextHeight && LitInt(1) <= n#0)
       ==> (3 <= n#0
           ==> _module.__default.Theorem3#canCall(n#0 - 2)
             && _module.__default.Theorem3#canCall(n#0 - 1))
         && _module.__default.Theorem3($LS($ly), n#0)
           == (if n#0 < 3
             then 5
             else (var x#0 := _module.__default.Theorem3($ly, n#0 - 2); 
              (var y#0 := _module.__default.Theorem3($ly, n#0 - 1); LitInt(5)))));

// definition axiom for _module.__default.Theorem3 for all literals (revealed)
axiom 26 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: int :: 
    {:weight 3} { _module.__default.Theorem3($LS($ly), LitInt(n#0)) } 
    _module.__default.Theorem3#canCall(LitInt(n#0))
         || (26 != $FunctionContextHeight && LitInt(1) <= LitInt(n#0))
       ==> (!Lit(n#0 < 3)
           ==> _module.__default.Theorem3#canCall(LitInt(n#0 - 2))
             && _module.__default.Theorem3#canCall(LitInt(n#0 - 1)))
         && _module.__default.Theorem3($LS($ly), LitInt(n#0))
           == (if n#0 < 3
             then 5
             else (var x#1 := LitInt(_module.__default.Theorem3($LS($ly), LitInt(n#0 - 2))); 
              (var y#1 := LitInt(_module.__default.Theorem3($LS($ly), LitInt(n#0 - 1))); 
                LitInt(5)))));

procedure CheckWellformed$$_module.__default.Theorem3(n#0: int);
  free requires 26 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures LitInt(1) <= _module.__default.Fib($LS($LS($LZ)), n#0);



implementation CheckWellformed$$_module.__default.Theorem3(n#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##n#0: int;
  var x#Z#0: int;
  var let#0#0#0: int;
  var ##n#1: int;
  var y#Z#0: int;
  var let#1#0#0: int;
  var ##n#2: int;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function Theorem3
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(147,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume LitInt(1) <= n#0;
    if (*)
    {
        assert $Is(n#0, Tclass._System.nat());
        ##n#0 := n#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
        assume _module.__default.Fib#canCall(n#0);
        assume LitInt(1) <= _module.__default.Fib($LS($LZ), n#0);
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (n#0 < 3)
        {
            assume _module.__default.Theorem3($LS($LZ), n#0) == LitInt(5);
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.Theorem3($LS($LZ), n#0), TInt);
        }
        else
        {
            havoc x#Z#0;
            assume true;
            ##n#1 := n#0 - 2;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#1, TInt, $Heap);
            assert {:subsumption 0} LitInt(1) <= ##n#1;
            assume LitInt(1) <= ##n#1;
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0 <= n#0 || ##n#1 == n#0;
            assert ##n#1 < n#0;
            assume _module.__default.Theorem3#canCall(n#0 - 2);
            assume let#0#0#0 == _module.__default.Theorem3($LS($LZ), n#0 - 2);
            assume _module.__default.Theorem3#canCall(n#0 - 2);
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, TInt);
            assume x#Z#0 == let#0#0#0;
            havoc y#Z#0;
            assume true;
            ##n#2 := n#0 - 1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#2, TInt, $Heap);
            assert {:subsumption 0} LitInt(1) <= ##n#2;
            assume LitInt(1) <= ##n#2;
            b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0 <= n#0 || ##n#2 == n#0;
            assert ##n#2 < n#0;
            assume _module.__default.Theorem3#canCall(n#0 - 1);
            assume let#1#0#0 == _module.__default.Theorem3($LS($LZ), n#0 - 1);
            assume _module.__default.Theorem3#canCall(n#0 - 1);
            // CheckWellformedWithResult: any expression
            assume $Is(let#1#0#0, TInt);
            assume y#Z#0 == let#1#0#0;
            assume _module.__default.Theorem3($LS($LZ), n#0) == LitInt(5);
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.Theorem3($LS($LZ), n#0), TInt);
        }

        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



procedure CheckWellformed$$_module.__default.Q(list#0: DatatypeType
       where $Is(list#0, Tclass._module.List(TInt))
         && $IsAlloc(list#0, Tclass._module.List(TInt), $Heap)
         && $IsA#_module.List(list#0), 
    anotherList#0: DatatypeType
       where $Is(anotherList#0, Tclass._module.List(TInt))
         && $IsAlloc(anotherList#0, Tclass._module.List(TInt), $Heap)
         && $IsA#_module.List(anotherList#0));
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Q(list#0: DatatypeType
       where $Is(list#0, Tclass._module.List(TInt))
         && $IsAlloc(list#0, Tclass._module.List(TInt), $Heap)
         && $IsA#_module.List(list#0), 
    anotherList#0: DatatypeType
       where $Is(anotherList#0, Tclass._module.List(TInt))
         && $IsAlloc(anotherList#0, Tclass._module.List(TInt), $Heap)
         && $IsA#_module.List(anotherList#0));
  // user-defined preconditions
  requires !_module.List#Equal(list#0, #_module.List.Nil());
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.Q(list#0: DatatypeType
       where $Is(list#0, Tclass._module.List(TInt))
         && $IsAlloc(list#0, Tclass._module.List(TInt), $Heap)
         && $IsA#_module.List(list#0), 
    anotherList#0: DatatypeType
       where $Is(anotherList#0, Tclass._module.List(TInt))
         && $IsAlloc(anotherList#0, Tclass._module.List(TInt), $Heap)
         && $IsA#_module.List(anotherList#0))
   returns ($_reverifyPost: bool);
  free requires 8 == $FunctionContextHeight;
  // user-defined preconditions
  requires !_module.List#Equal(list#0, #_module.List.Nil());
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.Q(list#0: DatatypeType, anotherList#0: DatatypeType)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var x#0: DatatypeType
     where $Is(x#0, Tclass._module.List(TInt))
       && $IsAlloc(x#0, Tclass._module.List(TInt), $Heap);
  var h#Z#0: int;
  var t#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var y#0: int;
  var _mcc#0#0: int;
  var _mcc#1#0: DatatypeType;
  var t#Z#1: DatatypeType;
  var let#1#0#0: DatatypeType;
  var h#Z#1: int;
  var let#2#0#0: int;
  var a#0#0#0: Box;
  var a#0#1#0: DatatypeType;

    // AddMethodImpl: Q, Impl$$_module.__default.Q
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(236,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(237,9)
    assume true;
    havoc h#Z#0;
    havoc t#Z#0;
    assume $Is(t#Z#0, Tclass._module.List(TInt));
    assume let#0#0#0 == list#0;
    assume true;
    // CheckWellformedWithResult: any expression
    assume $Is(let#0#0#0, Tclass._module.List(TInt));
    assert _module.List.Cons_q(let#0#0#0);
    assume #_module.List.Cons($Box(h#Z#0), t#Z#0) == let#0#0#0;
    assume true;
    x#0 := (var h#0, t#0 := $Unbox(_module.List.head(list#0)): int, _module.List.tail(list#0); 
      #_module.List.Cons($Box(h#0), t#0));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(239,14)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(240,9)
    assume true;
    if (anotherList#0 == #_module.List.Nil())
    {
        havoc a#0#0#0, a#0#1#0;
        if (anotherList#0 == #_module.List.Nil())
        {
        }
        else if (anotherList#0 == #_module.List.Cons(a#0#0#0, a#0#1#0))
        {
            assert false;
        }
        else
        {
            assume false;
        }
    }
    else if (anotherList#0 == #_module.List.Cons($Box(_mcc#0#0), _mcc#1#0))
    {
        assume $Is(_mcc#1#0, Tclass._module.List(TInt));
        havoc t#Z#1;
        assume $Is(t#Z#1, Tclass._module.List(TInt));
        assume let#1#0#0 == _mcc#1#0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#1#0#0, Tclass._module.List(TInt));
        assume t#Z#1 == let#1#0#0;
        havoc h#Z#1;
        assume true;
        assume let#2#0#0 == _mcc#0#0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#2#0#0, TInt);
        assume h#Z#1 == let#2#0#0;
    }
    else
    {
        assume false;
    }

    assume true;
    y#0 := (if _module.List.Nil_q(anotherList#0)
       then 5
       else (var t#2 := _module.List.tail(anotherList#0); 
        (var h#2 := $Unbox(_module.List.head(anotherList#0)): int; h#2)));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(242,24)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(243,3)
    assume $IsA#_module.List(list#0) && $IsA#_module.List(x#0);
    assert _module.List#Equal(list#0, x#0);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(244,3)
    if (_module.List.Cons_q(anotherList#0))
    {
        assert _module.List.Cons_q(anotherList#0);
    }

    assume true;
    assert {:subsumption 0} _module.List.Cons_q(anotherList#0)
       ==> y#0 == $Unbox(_module.List.head(anotherList#0)): int;
    assume _module.List.Cons_q(anotherList#0)
       ==> y#0 == $Unbox(_module.List.head(anotherList#0)): int;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(245,3)
    if (_module.List.Nil_q(anotherList#0))
    {
    }

    assume true;
    assert {:subsumption 0} _module.List.Nil_q(anotherList#0) ==> y#0 == LitInt(5);
    assume _module.List.Nil_q(anotherList#0) ==> y#0 == LitInt(5);
}



// function declaration for _module._default.Together
function _module.__default.Together(x#0: int, y#0: bool) : DatatypeType;

function _module.__default.Together#canCall(x#0: int, y#0: bool) : bool;

// consequence axiom for _module.__default.Together
axiom 10 <= $FunctionContextHeight
   ==> (forall x#0: int, y#0: bool :: 
    { _module.__default.Together(x#0, y#0) } 
    _module.__default.Together#canCall(x#0, y#0) || 10 != $FunctionContextHeight
       ==> $Is(_module.__default.Together(x#0, y#0), Tclass._module.Tuple(TInt, TBool)));

function _module.__default.Together#requires(int, bool) : bool;

// #requires axiom for _module.__default.Together
axiom (forall x#0: int, y#0: bool :: 
  { _module.__default.Together#requires(x#0, y#0) } 
  _module.__default.Together#requires(x#0, y#0) == true);

// definition axiom for _module.__default.Together (revealed)
axiom 10 <= $FunctionContextHeight
   ==> (forall x#0: int, y#0: bool :: 
    { _module.__default.Together(x#0, y#0) } 
    _module.__default.Together#canCall(x#0, y#0) || 10 != $FunctionContextHeight
       ==> _module.__default.Together(x#0, y#0)
         == #_module.Tuple.Pair($Box(x#0), $Box(y#0)));

// definition axiom for _module.__default.Together for all literals (revealed)
axiom 10 <= $FunctionContextHeight
   ==> (forall x#0: int, y#0: bool :: 
    {:weight 3} { _module.__default.Together(LitInt(x#0), Lit(y#0)) } 
    _module.__default.Together#canCall(LitInt(x#0), Lit(y#0))
         || 10 != $FunctionContextHeight
       ==> _module.__default.Together(LitInt(x#0), Lit(y#0))
         == Lit(#_module.Tuple.Pair($Box(LitInt(x#0)), $Box(Lit(y#0)))));

procedure CheckWellformed$$_module.__default.Together(x#0: int, y#0: bool);
  free requires 10 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure CheckWellformed$$_module.__default.LikeTogether() returns (z#0: int);
  free requires 27 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.LikeTogether() returns (z#0: int);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.LikeTogether() returns (z#0: int, $_reverifyPost: bool);
  free requires 27 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.LikeTogether() returns (z#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var xx#Z#0_0: int;
  var yy#Z#0_0: bool;
  var let#0_0#0#0: DatatypeType;
  var ##x#0_0: int;
  var ##y#0_0: bool;
  var t#1_0: int where LitInt(0) <= t#1_0;
  var t#Z#0: int;
  var let#0#0#0: int;

    // AddMethodImpl: LikeTogether, Impl$$_module.__default.LikeTogether
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(258,0): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(259,3)
    if (*)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(260,7)
        assume true;
        havoc xx#Z#0_0;
        havoc yy#Z#0_0;
        assume LitInt(0) <= xx#Z#0_0;
        ##x#0_0 := LitInt(-10);
        // assume allocatedness for argument to function
        assume $IsAlloc(##x#0_0, TInt, $Heap);
        ##y#0_0 := Lit(true);
        // assume allocatedness for argument to function
        assume $IsAlloc(##y#0_0, TBool, $Heap);
        assume _module.__default.Together#canCall(LitInt(-10), Lit(true));
        assume _module.Tuple.Pair_q(Lit(_module.__default.Together(LitInt(-10), Lit(true))));
        assume let#0_0#0#0 == Lit(_module.__default.Together(LitInt(-10), Lit(true)));
        assume _module.__default.Together#canCall(LitInt(-10), Lit(true));
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_0#0#0, Tclass._module.Tuple(TInt, TBool));
        assume _module.Tuple.Pair_q(let#0_0#0#0);
        assert $Is($Unbox(_module.Tuple._0(let#0_0#0#0)): int, Tclass._System.nat());
        assume #_module.Tuple.Pair($Box(xx#Z#0_0), $Box(yy#Z#0_0)) == let#0_0#0#0;
        assume _module.__default.Together#canCall(LitInt(-10), Lit(true));
        z#0 := (var xx#0_0, yy#0_0 := $Unbox(_module.Tuple._0(Lit(_module.__default.Together(LitInt(-10), Lit(true))))): int, 
            $Unbox(_module.Tuple._1(Lit(_module.__default.Together(LitInt(-10), Lit(true))))): bool; 
          xx#0_0 + 3);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(260,61)"} true;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(261,5)
        assume true;
        assert LitInt(0) <= z#0;
    }
    else
    {
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(262,10)
        if (*)
        {
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(263,16)
            assume true;
            assume true;
            assert $Is(LitInt(-30), Tclass._System.nat());
            t#1_0 := LitInt(-30);
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(263,21)"} true;
        }
        else
        {
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(265,7)
            assume true;
            havoc t#Z#0;
            assume LitInt(0) <= t#Z#0;
            assert $Is(LitInt(-30), Tclass._System.nat());
            assume let#0#0#0 == LitInt(-30);
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._System.nat());
            assume t#Z#0 == let#0#0#0;
            assume true;
            z#0 := (var t#0 := LitInt(-30); t#0);
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(265,29)"} true;
        }
    }
}



procedure CheckWellformed$$_module.__default.Mountain() returns (z#0: int, t#0: int where LitInt(0) <= t#0);
  free requires 11 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Mountain() returns (z#0: int, t#0: int where LitInt(0) <= t#0);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.Mountain() returns (z#0: int, t#0: int where LitInt(0) <= t#0, $_reverifyPost: bool);
  free requires 11 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.Mountain() returns (z#0: int, t#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var xx#Z#0: int;
  var yy#Z#0: bool;
  var let#0#0#0: DatatypeType;
  var ##x#0: int;
  var ##y#0: bool;

    // AddMethodImpl: Mountain, Impl$$_module.__default.Mountain
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(270,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(271,5)
    assume true;
    havoc xx#Z#0;
    havoc yy#Z#0;
    assume LitInt(0) <= xx#Z#0;
    ##x#0 := LitInt(10);
    // assume allocatedness for argument to function
    assume $IsAlloc(##x#0, TInt, $Heap);
    ##y#0 := Lit(true);
    // assume allocatedness for argument to function
    assume $IsAlloc(##y#0, TBool, $Heap);
    assume _module.__default.Together#canCall(LitInt(10), Lit(true));
    assume _module.Tuple.Pair_q(Lit(_module.__default.Together(LitInt(10), Lit(true))));
    assume let#0#0#0 == Lit(_module.__default.Together(LitInt(10), Lit(true)));
    assume _module.__default.Together#canCall(LitInt(10), Lit(true));
    // CheckWellformedWithResult: any expression
    assume $Is(let#0#0#0, Tclass._module.Tuple(TInt, TBool));
    assume _module.Tuple.Pair_q(let#0#0#0);
    assert $Is($Unbox(_module.Tuple._0(let#0#0#0)): int, Tclass._System.nat());
    assume #_module.Tuple.Pair($Box(xx#Z#0), $Box(yy#Z#0)) == let#0#0#0;
    assume _module.__default.Together#canCall(LitInt(10), Lit(true));
    z#0 := (var xx#0, yy#0 := $Unbox(_module.Tuple._0(Lit(_module.__default.Together(LitInt(10), Lit(true))))): int, 
        $Unbox(_module.Tuple._1(Lit(_module.__default.Together(LitInt(10), Lit(true))))): bool; 
      xx#0 + 3);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(271,58)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(272,3)
    assume true;
    assert LitInt(0) <= z#0;
}



// function declaration for _module._default.Rainbow
function _module.__default.Rainbow(_module._default.Rainbow$X: Ty, tup#0: DatatypeType) : int;

function _module.__default.Rainbow#canCall(_module._default.Rainbow$X: Ty, tup#0: DatatypeType) : bool;

// consequence axiom for _module.__default.Rainbow
axiom 12 <= $FunctionContextHeight
   ==> (forall _module._default.Rainbow$X: Ty, tup#0: DatatypeType :: 
    { _module.__default.Rainbow(_module._default.Rainbow$X, tup#0) } 
    _module.__default.Rainbow#canCall(_module._default.Rainbow$X, tup#0)
         || (12 != $FunctionContextHeight
           && $Is(tup#0, Tclass._module.Tuple(_module._default.Rainbow$X, TInt)))
       ==> LitInt(0) <= _module.__default.Rainbow(_module._default.Rainbow$X, tup#0));

function _module.__default.Rainbow#requires(Ty, DatatypeType) : bool;

// #requires axiom for _module.__default.Rainbow
axiom (forall _module._default.Rainbow$X: Ty, tup#0: DatatypeType :: 
  { _module.__default.Rainbow#requires(_module._default.Rainbow$X, tup#0) } 
  $Is(tup#0, Tclass._module.Tuple(_module._default.Rainbow$X, TInt))
     ==> _module.__default.Rainbow#requires(_module._default.Rainbow$X, tup#0) == true);

// definition axiom for _module.__default.Rainbow (revealed)
axiom 12 <= $FunctionContextHeight
   ==> (forall _module._default.Rainbow$X: Ty, tup#0: DatatypeType :: 
    { _module.__default.Rainbow(_module._default.Rainbow$X, tup#0) } 
    _module.__default.Rainbow#canCall(_module._default.Rainbow$X, tup#0)
         || (12 != $FunctionContextHeight
           && $Is(tup#0, Tclass._module.Tuple(_module._default.Rainbow$X, TInt)))
       ==> _module.__default.Rainbow(_module._default.Rainbow$X, tup#0)
         == (var left#0, right#0 := _module.Tuple._0(tup#0), $Unbox(_module.Tuple._1(tup#0)): int; 
          Mul(right#0, right#0)));

// definition axiom for _module.__default.Rainbow for all literals (revealed)
axiom 12 <= $FunctionContextHeight
   ==> (forall _module._default.Rainbow$X: Ty, tup#0: DatatypeType :: 
    {:weight 3} { _module.__default.Rainbow(_module._default.Rainbow$X, Lit(tup#0)) } 
    _module.__default.Rainbow#canCall(_module._default.Rainbow$X, Lit(tup#0))
         || (12 != $FunctionContextHeight
           && $Is(tup#0, Tclass._module.Tuple(_module._default.Rainbow$X, TInt)))
       ==> _module.__default.Rainbow(_module._default.Rainbow$X, Lit(tup#0))
         == (var left#1, right#1 := _module.Tuple._0(Lit(tup#0)), $Unbox(_module.Tuple._1(Lit(tup#0))): int; 
          Mul(right#1, right#1)));

procedure CheckWellformed$$_module.__default.Rainbow(_module._default.Rainbow$X: Ty, 
    tup#0: DatatypeType
       where $Is(tup#0, Tclass._module.Tuple(_module._default.Rainbow$X, TInt)));
  free requires 12 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures LitInt(0) <= _module.__default.Rainbow(_module._default.Rainbow$X, tup#0);



implementation CheckWellformed$$_module.__default.Rainbow(_module._default.Rainbow$X: Ty, tup#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##tup#0: DatatypeType;
  var left#Z#0: Box;
  var right#Z#0: int;
  var let#0#0#0: DatatypeType;


    // AddWellformednessCheck for function Rainbow
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(275,16): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        ##tup#0 := tup#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##tup#0, Tclass._module.Tuple(_module._default.Rainbow$X, TInt), $Heap);
        assert tup#0 == tup#0 || DtRank(##tup#0) < DtRank(tup#0);
        assume tup#0 == tup#0
           || _module.__default.Rainbow#canCall(_module._default.Rainbow$X, tup#0);
        assume LitInt(0) <= _module.__default.Rainbow(_module._default.Rainbow$X, tup#0);
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        havoc left#Z#0;
        havoc right#Z#0;
        assume $IsBox(left#Z#0, _module._default.Rainbow$X);
        assume let#0#0#0 == tup#0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0#0#0, Tclass._module.Tuple(_module._default.Rainbow$X, TInt));
        assume _module.Tuple.Pair_q(let#0#0#0);
        assume #_module.Tuple.Pair(left#Z#0, $Box(right#Z#0)) == let#0#0#0;
        assume _module.__default.Rainbow(_module._default.Rainbow$X, tup#0)
           == Mul(right#Z#0, right#Z#0);
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.Rainbow(_module._default.Rainbow$X, tup#0), TInt);
    }
}



// function declaration for _module._default.Fr
function _module.__default.Fr(x#0: int) : DatatypeType;

function _module.__default.Fr#canCall(x#0: int) : bool;

// consequence axiom for _module.__default.Fr
axiom 14 <= $FunctionContextHeight
   ==> (forall x#0: int :: 
    { _module.__default.Fr(x#0) } 
    _module.__default.Fr#canCall(x#0) || 14 != $FunctionContextHeight
       ==> $Is(_module.__default.Fr(x#0), Tclass._module.Friend()));

function _module.__default.Fr#requires(int) : bool;

// #requires axiom for _module.__default.Fr
axiom (forall x#0: int :: 
  { _module.__default.Fr#requires(x#0) } 
  _module.__default.Fr#requires(x#0) == true);

// definition axiom for _module.__default.Fr (revealed)
axiom 14 <= $FunctionContextHeight
   ==> (forall x#0: int :: 
    { _module.__default.Fr(x#0) } 
    _module.__default.Fr#canCall(x#0) || 14 != $FunctionContextHeight
       ==> _module.__default.Fr(x#0)
         == (if x#0 < 10 then #_module.Friend.Jermaine(x#0) else #_module.Friend.Agnes(x#0)));

// definition axiom for _module.__default.Fr for all literals (revealed)
axiom 14 <= $FunctionContextHeight
   ==> (forall x#0: int :: 
    {:weight 3} { _module.__default.Fr(LitInt(x#0)) } 
    _module.__default.Fr#canCall(LitInt(x#0)) || 14 != $FunctionContextHeight
       ==> _module.__default.Fr(LitInt(x#0))
         == (if x#0 < 10
           then #_module.Friend.Jermaine(LitInt(x#0))
           else #_module.Friend.Agnes(LitInt(x#0))));

procedure CheckWellformed$$_module.__default.Fr(x#0: int);
  free requires 14 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure CheckWellformed$$_module.__default.Friendly(n#0: int where LitInt(0) <= n#0) returns (c#0: int);
  free requires 15 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Friendly(n#0: int where LitInt(0) <= n#0) returns (c#0: int);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures c#0 == n#0;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.Friendly(n#0: int where LitInt(0) <= n#0) returns (c#0: int, $_reverifyPost: bool);
  free requires 15 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures c#0 == n#0;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.Friendly(n#0: int) returns (c#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var y#Z#0_0: int;
  var let#0_0#0#0: DatatypeType;
  var ##x#0_0: int;
  var y#Z#0: int;
  var let#0#0#0: DatatypeType;
  var ##x#0: int;

    // AddMethodImpl: Friendly, Impl$$_module.__default.Friendly
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(290,0): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(291,3)
    assume true;
    if (n#0 < 3)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(292,7)
        assume true;
        havoc y#Z#0_0;
        assume true;
        ##x#0_0 := n#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##x#0_0, TInt, $Heap);
        assume _module.__default.Fr#canCall(n#0);
        assume let#0_0#0#0 == _module.__default.Fr(n#0);
        assume _module.__default.Fr#canCall(n#0);
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_0#0#0, Tclass._module.Friend());
        assert _module.Friend.Jermaine_q(let#0_0#0#0);
        assume #_module.Friend.Jermaine(y#Z#0_0) == let#0_0#0#0;
        assume _module.__default.Fr#canCall(n#0);
        c#0 := (var y#0_0 := _module.Friend._h2(_module.__default.Fr(n#0)); y#0_0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(292,36)"} true;
    }
    else
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(294,7)
        assume true;
        havoc y#Z#0;
        assume true;
        ##x#0 := n#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##x#0, TInt, $Heap);
        assume _module.__default.Fr#canCall(n#0);
        assume let#0#0#0 == _module.__default.Fr(n#0);
        assume _module.__default.Fr#canCall(n#0);
        // CheckWellformedWithResult: any expression
        assume $Is(let#0#0#0, Tclass._module.Friend());
        assert _module.Friend.Agnes_q(let#0#0#0);
        assume #_module.Friend.Agnes(y#Z#0) == let#0#0#0;
        assume _module.__default.Fr#canCall(n#0);
        c#0 := (var y#0 := _module.Friend._h0(_module.__default.Fr(n#0)); y#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(294,33)"} true;
    }
}



// function declaration for _module._default.F_good
function _module.__default.F__good(d#0: DatatypeType) : int;

function _module.__default.F__good#canCall(d#0: DatatypeType) : bool;

// consequence axiom for _module.__default.F__good
axiom 16 <= $FunctionContextHeight
   ==> (forall d#0: DatatypeType :: 
    { _module.__default.F__good(d#0) } 
    _module.__default.F__good#canCall(d#0)
         || (16 != $FunctionContextHeight
           && 
          $Is(d#0, 
            Tclass._module.Tuple(Tclass._module.Tuple(TBool, TInt), 
              Tclass._module.Tuple(Tclass._module.Tuple(TInt, TInt), Tclass._module.Tuple(TBool, TBool))))
           && 
          LitInt(0)
             <= $Unbox(_module.Tuple._1($Unbox(_module.Tuple._0($Unbox(_module.Tuple._1(d#0)): DatatypeType)): DatatypeType)): int
           && $Unbox(_module.Tuple._1($Unbox(_module.Tuple._0($Unbox(_module.Tuple._1(d#0)): DatatypeType)): DatatypeType)): int
             < 100)
       ==> true);

function _module.__default.F__good#requires(DatatypeType) : bool;

// #requires axiom for _module.__default.F__good
axiom (forall d#0: DatatypeType :: 
  { _module.__default.F__good#requires(d#0) } 
  $Is(d#0, 
      Tclass._module.Tuple(Tclass._module.Tuple(TBool, TInt), 
        Tclass._module.Tuple(Tclass._module.Tuple(TInt, TInt), Tclass._module.Tuple(TBool, TBool))))
     ==> _module.__default.F__good#requires(d#0)
       == (LitInt(0)
           <= $Unbox(_module.Tuple._1($Unbox(_module.Tuple._0($Unbox(_module.Tuple._1(d#0)): DatatypeType)): DatatypeType)): int
         && $Unbox(_module.Tuple._1($Unbox(_module.Tuple._0($Unbox(_module.Tuple._1(d#0)): DatatypeType)): DatatypeType)): int
           < 100));

// definition axiom for _module.__default.F__good (revealed)
axiom 16 <= $FunctionContextHeight
   ==> (forall d#0: DatatypeType :: 
    { _module.__default.F__good(d#0) } 
    _module.__default.F__good#canCall(d#0)
         || (16 != $FunctionContextHeight
           && 
          $Is(d#0, 
            Tclass._module.Tuple(Tclass._module.Tuple(TBool, TInt), 
              Tclass._module.Tuple(Tclass._module.Tuple(TInt, TInt), Tclass._module.Tuple(TBool, TBool))))
           && 
          LitInt(0)
             <= $Unbox(_module.Tuple._1($Unbox(_module.Tuple._0($Unbox(_module.Tuple._1(d#0)): DatatypeType)): DatatypeType)): int
           && $Unbox(_module.Tuple._1($Unbox(_module.Tuple._0($Unbox(_module.Tuple._1(d#0)): DatatypeType)): DatatypeType)): int
             < 100)
       ==> _module.Tuple.Pair_q(d#0)
         && 
        _module.Tuple.Pair_q(d#0)
         && _module.Tuple.Pair_q($Unbox(_module.Tuple._1(d#0)): DatatypeType)
         && _module.Tuple.Pair_q($Unbox(_module.Tuple._0($Unbox(_module.Tuple._1(d#0)): DatatypeType)): DatatypeType)
         && (var p#0 := $Unbox(_module.Tuple._0(d#0)): DatatypeType; 
          _module.Tuple.Pair_q(p#0))
         && _module.__default.F__good(d#0)
           == (var p#0, b0#0, x#0, y0#0, y1#0, b1#0, b2#0, q#0 := $Unbox(_module.Tuple._0(d#0)): DatatypeType, 
              $Unbox(_module.Tuple._0($Unbox(_module.Tuple._0(d#0)): DatatypeType)): bool, 
              $Unbox(_module.Tuple._1($Unbox(_module.Tuple._0(d#0)): DatatypeType)): int, 
              $Unbox(_module.Tuple._0($Unbox(_module.Tuple._0($Unbox(_module.Tuple._1(d#0)): DatatypeType)): DatatypeType)): int, 
              $Unbox(_module.Tuple._1($Unbox(_module.Tuple._0($Unbox(_module.Tuple._1(d#0)): DatatypeType)): DatatypeType)): int, 
              $Unbox(_module.Tuple._0($Unbox(_module.Tuple._1($Unbox(_module.Tuple._1(d#0)): DatatypeType)): DatatypeType)): bool, 
              $Unbox(_module.Tuple._1($Unbox(_module.Tuple._1($Unbox(_module.Tuple._1(d#0)): DatatypeType)): DatatypeType)): bool, 
              $Unbox(_module.Tuple._1($Unbox(_module.Tuple._0($Unbox(_module.Tuple._1(d#0)): DatatypeType)): DatatypeType)): int; 
            $Unbox(_module.Tuple._1(p#0)): int + (if b0#0 then x#0 + y0#0 else x#0 + y1#0)));

// definition axiom for _module.__default.F__good for all literals (revealed)
axiom 16 <= $FunctionContextHeight
   ==> (forall d#0: DatatypeType :: 
    {:weight 3} { _module.__default.F__good(Lit(d#0)) } 
    _module.__default.F__good#canCall(Lit(d#0))
         || (16 != $FunctionContextHeight
           && 
          $Is(d#0, 
            Tclass._module.Tuple(Tclass._module.Tuple(TBool, TInt), 
              Tclass._module.Tuple(Tclass._module.Tuple(TInt, TInt), Tclass._module.Tuple(TBool, TBool))))
           && 
          LitInt(0)
             <= LitInt($Unbox(_module.Tuple._1(Lit($Unbox(_module.Tuple._0(Lit($Unbox(_module.Tuple._1(Lit(d#0))): DatatypeType))): DatatypeType))): int)
           && $Unbox(_module.Tuple._1(Lit($Unbox(_module.Tuple._0(Lit($Unbox(_module.Tuple._1(Lit(d#0))): DatatypeType))): DatatypeType))): int
             < 100)
       ==> _module.Tuple.Pair_q(Lit(d#0))
         && 
        _module.Tuple.Pair_q(Lit(d#0))
         && _module.Tuple.Pair_q(Lit($Unbox(_module.Tuple._1(Lit(d#0))): DatatypeType))
         && _module.Tuple.Pair_q(Lit($Unbox(_module.Tuple._0(Lit($Unbox(_module.Tuple._1(Lit(d#0))): DatatypeType))): DatatypeType))
         && (var p#1 := Lit($Unbox(_module.Tuple._0(Lit(d#0))): DatatypeType); 
          _module.Tuple.Pair_q(p#1))
         && _module.__default.F__good(Lit(d#0))
           == (var p#1, b0#1, x#1, y0#1, y1#1, b1#1, b2#1, q#1 := Lit($Unbox(_module.Tuple._0(Lit(d#0))): DatatypeType), 
              $Unbox(_module.Tuple._0($Unbox(_module.Tuple._0(Lit(d#0))): DatatypeType)): bool, 
              $Unbox(_module.Tuple._1($Unbox(_module.Tuple._0(Lit(d#0))): DatatypeType)): int, 
              $Unbox(_module.Tuple._0($Unbox(_module.Tuple._0($Unbox(_module.Tuple._1(Lit(d#0))): DatatypeType)): DatatypeType)): int, 
              $Unbox(_module.Tuple._1($Unbox(_module.Tuple._0($Unbox(_module.Tuple._1(Lit(d#0))): DatatypeType)): DatatypeType)): int, 
              $Unbox(_module.Tuple._0($Unbox(_module.Tuple._1($Unbox(_module.Tuple._1(Lit(d#0))): DatatypeType)): DatatypeType)): bool, 
              $Unbox(_module.Tuple._1($Unbox(_module.Tuple._1($Unbox(_module.Tuple._1(Lit(d#0))): DatatypeType)): DatatypeType)): bool, 
              LitInt($Unbox(_module.Tuple._1(Lit($Unbox(_module.Tuple._0(Lit($Unbox(_module.Tuple._1(Lit(d#0))): DatatypeType))): DatatypeType))): int); 
            $Unbox(_module.Tuple._1(p#1)): int + (if b0#1 then x#1 + y0#1 else x#1 + y1#1)));

procedure CheckWellformed$$_module.__default.F__good(d#0: DatatypeType
       where $Is(d#0, 
        Tclass._module.Tuple(Tclass._module.Tuple(TBool, TInt), 
          Tclass._module.Tuple(Tclass._module.Tuple(TInt, TInt), Tclass._module.Tuple(TBool, TBool)))));
  free requires 16 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.F__good(d#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var p#Z#0: DatatypeType;
  var b0#Z#0: bool;
  var x#Z#0: int;
  var y0#Z#0: int;
  var y1#Z#0: int;
  var b1#Z#0: bool;
  var b2#Z#0: bool;
  var q#Z#0: int;
  var let#0#0#0: DatatypeType;
  var let#0#1#0: DatatypeType;
  var let#0#2#0: int;


    // AddWellformednessCheck for function F_good
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(298,16): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume _module.Tuple.Pair_q(d#0);
    assume _module.Tuple.Pair_q($Unbox(_module.Tuple._1(d#0)): DatatypeType);
    assume _module.Tuple.Pair_q($Unbox(_module.Tuple._0($Unbox(_module.Tuple._1(d#0)): DatatypeType)): DatatypeType);
    if (LitInt(0)
       <= $Unbox(_module.Tuple._1($Unbox(_module.Tuple._0($Unbox(_module.Tuple._1(d#0)): DatatypeType)): DatatypeType)): int)
    {
        assume _module.Tuple.Pair_q(d#0);
        assume _module.Tuple.Pair_q($Unbox(_module.Tuple._1(d#0)): DatatypeType);
        assume _module.Tuple.Pair_q($Unbox(_module.Tuple._0($Unbox(_module.Tuple._1(d#0)): DatatypeType)): DatatypeType);
    }

    assume LitInt(0)
         <= $Unbox(_module.Tuple._1($Unbox(_module.Tuple._0($Unbox(_module.Tuple._1(d#0)): DatatypeType)): DatatypeType)): int
       && $Unbox(_module.Tuple._1($Unbox(_module.Tuple._0($Unbox(_module.Tuple._1(d#0)): DatatypeType)): DatatypeType)): int
         < 100;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        havoc p#Z#0;
        havoc b0#Z#0;
        havoc x#Z#0;
        havoc y0#Z#0;
        havoc y1#Z#0;
        havoc b1#Z#0;
        havoc b2#Z#0;
        havoc q#Z#0;
        assume $Is(p#Z#0, Tclass._module.Tuple(TBool, TInt)) && LitInt(0) <= y1#Z#0;
        assume _module.Tuple.Pair_q(d#0);
        assume let#0#0#0 == $Unbox(_module.Tuple._0(d#0)): DatatypeType;
        assume _module.Tuple.Pair_q(d#0);
        // CheckWellformedWithResult: any expression
        assume $Is(let#0#0#0, Tclass._module.Tuple(TBool, TInt));
        assume p#Z#0 == let#0#0#0;
        assume let#0#1#0 == d#0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0#1#0, 
          Tclass._module.Tuple(Tclass._module.Tuple(TBool, TInt), 
            Tclass._module.Tuple(Tclass._module.Tuple(TInt, TInt), Tclass._module.Tuple(TBool, TBool))));
        assume _module.Tuple.Pair_q(let#0#1#0);
        assume _module.Tuple.Pair_q($Unbox(_module.Tuple._0(let#0#1#0)): DatatypeType);
        assume _module.Tuple.Pair_q($Unbox(_module.Tuple._1(let#0#1#0)): DatatypeType);
        assume _module.Tuple.Pair_q($Unbox(_module.Tuple._0($Unbox(_module.Tuple._1(let#0#1#0)): DatatypeType)): DatatypeType);
        assert $Is($Unbox(_module.Tuple._1($Unbox(_module.Tuple._0($Unbox(_module.Tuple._1(let#0#1#0)): DatatypeType)): DatatypeType)): int, 
          Tclass._System.nat());
        assume _module.Tuple.Pair_q($Unbox(_module.Tuple._1($Unbox(_module.Tuple._1(let#0#1#0)): DatatypeType)): DatatypeType);
        assume #_module.Tuple.Pair($Box(#_module.Tuple.Pair($Box(b0#Z#0), $Box(x#Z#0))), 
            $Box(#_module.Tuple.Pair($Box(#_module.Tuple.Pair($Box(y0#Z#0), $Box(y1#Z#0))), 
                $Box(#_module.Tuple.Pair($Box(b1#Z#0), $Box(b2#Z#0))))))
           == let#0#1#0;
        assume _module.Tuple.Pair_q(d#0);
        assume _module.Tuple.Pair_q($Unbox(_module.Tuple._1(d#0)): DatatypeType);
        assume _module.Tuple.Pair_q($Unbox(_module.Tuple._0($Unbox(_module.Tuple._1(d#0)): DatatypeType)): DatatypeType);
        assume let#0#2#0
           == $Unbox(_module.Tuple._1($Unbox(_module.Tuple._0($Unbox(_module.Tuple._1(d#0)): DatatypeType)): DatatypeType)): int;
        assume _module.Tuple.Pair_q(d#0)
           && _module.Tuple.Pair_q($Unbox(_module.Tuple._1(d#0)): DatatypeType)
           && _module.Tuple.Pair_q($Unbox(_module.Tuple._0($Unbox(_module.Tuple._1(d#0)): DatatypeType)): DatatypeType);
        // CheckWellformedWithResult: any expression
        assume $Is(let#0#2#0, TInt);
        assume q#Z#0 == let#0#2#0;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(304,3)
        assume true;
        assert q#Z#0 < 200;
        assume _module.Tuple.Pair_q(p#Z#0);
        if (b0#Z#0)
        {
        }
        else
        {
        }

        assume _module.__default.F__good(d#0)
           == $Unbox(_module.Tuple._1(p#Z#0)): int
             + (if b0#Z#0 then x#Z#0 + y0#Z#0 else x#Z#0 + y1#Z#0);
        assume _module.Tuple.Pair_q(p#Z#0);
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.F__good(d#0), TInt);
    }
}



// function declaration for _module._default.F_bad
function _module.__default.F__bad(d#0: DatatypeType) : int;

function _module.__default.F__bad#canCall(d#0: DatatypeType) : bool;

// consequence axiom for _module.__default.F__bad
axiom 17 <= $FunctionContextHeight
   ==> (forall d#0: DatatypeType :: 
    { _module.__default.F__bad(d#0) } 
    _module.__default.F__bad#canCall(d#0)
         || (17 != $FunctionContextHeight
           && $Is(d#0, 
            Tclass._module.Tuple(Tclass._module.Tuple(TBool, TInt), 
              Tclass._module.Tuple(Tclass._module.Tuple(TInt, TInt), Tclass._module.Tuple(TBool, TBool)))))
       ==> true);

function _module.__default.F__bad#requires(DatatypeType) : bool;

// #requires axiom for _module.__default.F__bad
axiom (forall d#0: DatatypeType :: 
  { _module.__default.F__bad#requires(d#0) } 
  $Is(d#0, 
      Tclass._module.Tuple(Tclass._module.Tuple(TBool, TInt), 
        Tclass._module.Tuple(Tclass._module.Tuple(TInt, TInt), Tclass._module.Tuple(TBool, TBool))))
     ==> _module.__default.F__bad#requires(d#0) == true);

// definition axiom for _module.__default.F__bad (revealed)
axiom 17 <= $FunctionContextHeight
   ==> (forall d#0: DatatypeType :: 
    { _module.__default.F__bad(d#0) } 
    _module.__default.F__bad#canCall(d#0)
         || (17 != $FunctionContextHeight
           && $Is(d#0, 
            Tclass._module.Tuple(Tclass._module.Tuple(TBool, TInt), 
              Tclass._module.Tuple(Tclass._module.Tuple(TInt, TInt), Tclass._module.Tuple(TBool, TBool)))))
       ==> _module.Tuple.Pair_q(d#0)
         && 
        _module.Tuple.Pair_q(d#0)
         && _module.Tuple.Pair_q($Unbox(_module.Tuple._1(d#0)): DatatypeType)
         && _module.Tuple.Pair_q($Unbox(_module.Tuple._0($Unbox(_module.Tuple._1(d#0)): DatatypeType)): DatatypeType)
         && (var p#0 := $Unbox(_module.Tuple._0(d#0)): DatatypeType; 
          _module.Tuple.Pair_q(p#0))
         && _module.__default.F__bad(d#0)
           == (var p#0, b0#0, x#0, y0#0, y1#0, b1#0, b2#0, q#0 := $Unbox(_module.Tuple._0(d#0)): DatatypeType, 
              $Unbox(_module.Tuple._0($Unbox(_module.Tuple._0(d#0)): DatatypeType)): bool, 
              $Unbox(_module.Tuple._1($Unbox(_module.Tuple._0(d#0)): DatatypeType)): int, 
              $Unbox(_module.Tuple._0($Unbox(_module.Tuple._0($Unbox(_module.Tuple._1(d#0)): DatatypeType)): DatatypeType)): int, 
              $Unbox(_module.Tuple._1($Unbox(_module.Tuple._0($Unbox(_module.Tuple._1(d#0)): DatatypeType)): DatatypeType)): int, 
              $Unbox(_module.Tuple._0($Unbox(_module.Tuple._1($Unbox(_module.Tuple._1(d#0)): DatatypeType)): DatatypeType)): bool, 
              $Unbox(_module.Tuple._1($Unbox(_module.Tuple._1($Unbox(_module.Tuple._1(d#0)): DatatypeType)): DatatypeType)): bool, 
              $Unbox(_module.Tuple._1($Unbox(_module.Tuple._0($Unbox(_module.Tuple._1(d#0)): DatatypeType)): DatatypeType)): int; 
            $Unbox(_module.Tuple._1(p#0)): int + (if b0#0 then x#0 + y0#0 else x#0 + y1#0)));

// definition axiom for _module.__default.F__bad for all literals (revealed)
axiom 17 <= $FunctionContextHeight
   ==> (forall d#0: DatatypeType :: 
    {:weight 3} { _module.__default.F__bad(Lit(d#0)) } 
    _module.__default.F__bad#canCall(Lit(d#0))
         || (17 != $FunctionContextHeight
           && $Is(d#0, 
            Tclass._module.Tuple(Tclass._module.Tuple(TBool, TInt), 
              Tclass._module.Tuple(Tclass._module.Tuple(TInt, TInt), Tclass._module.Tuple(TBool, TBool)))))
       ==> _module.Tuple.Pair_q(Lit(d#0))
         && 
        _module.Tuple.Pair_q(Lit(d#0))
         && _module.Tuple.Pair_q(Lit($Unbox(_module.Tuple._1(Lit(d#0))): DatatypeType))
         && _module.Tuple.Pair_q(Lit($Unbox(_module.Tuple._0(Lit($Unbox(_module.Tuple._1(Lit(d#0))): DatatypeType))): DatatypeType))
         && (var p#1 := Lit($Unbox(_module.Tuple._0(Lit(d#0))): DatatypeType); 
          _module.Tuple.Pair_q(p#1))
         && _module.__default.F__bad(Lit(d#0))
           == (var p#1, b0#1, x#1, y0#1, y1#1, b1#1, b2#1, q#1 := Lit($Unbox(_module.Tuple._0(Lit(d#0))): DatatypeType), 
              $Unbox(_module.Tuple._0($Unbox(_module.Tuple._0(Lit(d#0))): DatatypeType)): bool, 
              $Unbox(_module.Tuple._1($Unbox(_module.Tuple._0(Lit(d#0))): DatatypeType)): int, 
              $Unbox(_module.Tuple._0($Unbox(_module.Tuple._0($Unbox(_module.Tuple._1(Lit(d#0))): DatatypeType)): DatatypeType)): int, 
              $Unbox(_module.Tuple._1($Unbox(_module.Tuple._0($Unbox(_module.Tuple._1(Lit(d#0))): DatatypeType)): DatatypeType)): int, 
              $Unbox(_module.Tuple._0($Unbox(_module.Tuple._1($Unbox(_module.Tuple._1(Lit(d#0))): DatatypeType)): DatatypeType)): bool, 
              $Unbox(_module.Tuple._1($Unbox(_module.Tuple._1($Unbox(_module.Tuple._1(Lit(d#0))): DatatypeType)): DatatypeType)): bool, 
              LitInt($Unbox(_module.Tuple._1(Lit($Unbox(_module.Tuple._0(Lit($Unbox(_module.Tuple._1(Lit(d#0))): DatatypeType))): DatatypeType))): int); 
            $Unbox(_module.Tuple._1(p#1)): int + (if b0#1 then x#1 + y0#1 else x#1 + y1#1)));

procedure CheckWellformed$$_module.__default.F__bad(d#0: DatatypeType
       where $Is(d#0, 
        Tclass._module.Tuple(Tclass._module.Tuple(TBool, TInt), 
          Tclass._module.Tuple(Tclass._module.Tuple(TInt, TInt), Tclass._module.Tuple(TBool, TBool)))));
  free requires 17 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.F__bad(d#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var p#Z#0: DatatypeType;
  var b0#Z#0: bool;
  var x#Z#0: int;
  var y0#Z#0: int;
  var y1#Z#0: int;
  var b1#Z#0: bool;
  var b2#Z#0: bool;
  var q#Z#0: int;
  var let#0#0#0: DatatypeType;
  var let#0#1#0: DatatypeType;
  var let#0#2#0: int;


    // AddWellformednessCheck for function F_bad
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(307,16): initial state"} true;
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
        havoc p#Z#0;
        havoc b0#Z#0;
        havoc x#Z#0;
        havoc y0#Z#0;
        havoc y1#Z#0;
        havoc b1#Z#0;
        havoc b2#Z#0;
        havoc q#Z#0;
        assume $Is(p#Z#0, Tclass._module.Tuple(TBool, TInt)) && LitInt(0) <= y1#Z#0;
        assume _module.Tuple.Pair_q(d#0);
        assume let#0#0#0 == $Unbox(_module.Tuple._0(d#0)): DatatypeType;
        assume _module.Tuple.Pair_q(d#0);
        // CheckWellformedWithResult: any expression
        assume $Is(let#0#0#0, Tclass._module.Tuple(TBool, TInt));
        assume p#Z#0 == let#0#0#0;
        assume let#0#1#0 == d#0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0#1#0, 
          Tclass._module.Tuple(Tclass._module.Tuple(TBool, TInt), 
            Tclass._module.Tuple(Tclass._module.Tuple(TInt, TInt), Tclass._module.Tuple(TBool, TBool))));
        assume _module.Tuple.Pair_q(let#0#1#0);
        assume _module.Tuple.Pair_q($Unbox(_module.Tuple._0(let#0#1#0)): DatatypeType);
        assume _module.Tuple.Pair_q($Unbox(_module.Tuple._1(let#0#1#0)): DatatypeType);
        assume _module.Tuple.Pair_q($Unbox(_module.Tuple._0($Unbox(_module.Tuple._1(let#0#1#0)): DatatypeType)): DatatypeType);
        assert $Is($Unbox(_module.Tuple._1($Unbox(_module.Tuple._0($Unbox(_module.Tuple._1(let#0#1#0)): DatatypeType)): DatatypeType)): int, 
          Tclass._System.nat());
        assume _module.Tuple.Pair_q($Unbox(_module.Tuple._1($Unbox(_module.Tuple._1(let#0#1#0)): DatatypeType)): DatatypeType);
        assume #_module.Tuple.Pair($Box(#_module.Tuple.Pair($Box(b0#Z#0), $Box(x#Z#0))), 
            $Box(#_module.Tuple.Pair($Box(#_module.Tuple.Pair($Box(y0#Z#0), $Box(y1#Z#0))), 
                $Box(#_module.Tuple.Pair($Box(b1#Z#0), $Box(b2#Z#0))))))
           == let#0#1#0;
        assume _module.Tuple.Pair_q(d#0);
        assume _module.Tuple.Pair_q($Unbox(_module.Tuple._1(d#0)): DatatypeType);
        assume _module.Tuple.Pair_q($Unbox(_module.Tuple._0($Unbox(_module.Tuple._1(d#0)): DatatypeType)): DatatypeType);
        assume let#0#2#0
           == $Unbox(_module.Tuple._1($Unbox(_module.Tuple._0($Unbox(_module.Tuple._1(d#0)): DatatypeType)): DatatypeType)): int;
        assume _module.Tuple.Pair_q(d#0)
           && _module.Tuple.Pair_q($Unbox(_module.Tuple._1(d#0)): DatatypeType)
           && _module.Tuple.Pair_q($Unbox(_module.Tuple._0($Unbox(_module.Tuple._1(d#0)): DatatypeType)): DatatypeType);
        // CheckWellformedWithResult: any expression
        assume $Is(let#0#2#0, TInt);
        assume q#Z#0 == let#0#2#0;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(313,3)
        assume true;
        assert q#Z#0 < 200;
        assume _module.Tuple.Pair_q(p#Z#0);
        if (b0#Z#0)
        {
        }
        else
        {
        }

        assume _module.__default.F__bad(d#0)
           == $Unbox(_module.Tuple._1(p#Z#0)): int
             + (if b0#Z#0 then x#Z#0 + y0#Z#0 else x#Z#0 + y1#Z#0);
        assume _module.Tuple.Pair_q(p#Z#0);
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.F__bad(d#0), TInt);
    }
}



procedure CheckWellformed$$_module.__default.LetSuchThat__Deterministic() returns (x#0: int);
  free requires 34 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.LetSuchThat__Deterministic() returns (x#0: int);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.LetSuchThat__Deterministic() returns (x#0: int, $_reverifyPost: bool);
  free requires 34 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



function $let#40_w() : int;

function $let#40$canCall() : bool;

axiom $let#40$canCall() ==> $let#40_w() == Mul(LitInt(2), $let#40_w());

function $let#41_y() : int;

function $let#41$canCall() : bool;

axiom $let#41$canCall() ==> $let#41_y() < 0;

function $let#42_y() : int;

function $let#42$canCall() : bool;

axiom $let#42$canCall() ==> $let#42_y() < 0;

function $let#43_a(t: Set Box) : int;

function $let#43_b(t: Set Box) : int;

function $let#43$canCall(t: Set Box) : bool;

axiom (forall t: Set Box :: 
  { $let#43_b(t) } { $let#43_a(t) } 
  $let#43$canCall(t)
     ==> t[$Box($let#43_a(t))] && t[$Box($let#43_b(t))] && $let#43_a(t) != $let#43_b(t));

implementation Impl$$_module.__default.LetSuchThat__Deterministic() returns (x#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var w#0_0: int;
  var w#0_2: int;
  var y#1_0: int;
  var y#1_2: int;
  var y#2_0: int;
  var y#2_2: int;
  var t#0: Set Box where $Is(t#0, TSet(TInt)) && $IsAlloc(t#0, TSet(TInt), $Heap);
  var s#0: Set Box where $Is(s#0, TSet(TInt)) && $IsAlloc(s#0, TSet(TInt), $Heap);
  var a#0: int;
  var b#0: int;

    // AddMethodImpl: LetSuchThat_Deterministic, Impl$$_module.__default.LetSuchThat__Deterministic
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(320,0): initial state"} true;
    $_reverifyPost := false;
    // ----- alternative statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(321,3)
    if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(323,9)
        assume true;
        havoc y#2_0;
        if (true)
        {
        }

        assert ($Is(LitInt(0 - 1), TInt) && Lit(0 - 1 < 0))
           || 
          ($Is(LitInt(0), TInt) && Lit(0 < 0))
           || (exists y#2_1: int :: y#2_1 < 0);
        assume true;
        assume y#2_0 < 0;
        havoc y#2_2;
        assume true;
        assume true;
        assume y#2_2 < 0;
        assume true;
        assert y#2_0 == y#2_2;
        assume $let#42$canCall();
        assume $let#42$canCall();
        x#0 := (var y#2_1 := $let#42_y(); y#2_1);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(323,28)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(325,9)
        assume true;
        havoc y#1_0;
        if (true)
        {
        }

        assert ($Is(LitInt(0 - 1), TInt) && Lit(0 - 1 < 0))
           || 
          ($Is(LitInt(0), TInt) && Lit(0 < 0))
           || (exists y#1_1: int :: y#1_1 < 0);
        assume true;
        assume y#1_0 < 0;
        havoc y#1_2;
        assume true;
        assume true;
        assume y#1_2 < 0;
        assume true;
        assert Mul(y#1_0, LitInt(0)) == Mul(y#1_2, LitInt(0));
        assume $let#41$canCall();
        assume $let#41$canCall();
        x#0 := (var y#1_1 := $let#41_y(); Mul(y#1_1, LitInt(0)));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(325,30)"} true;
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(327,9)
        assume true;
        havoc w#0_0;
        if (true)
        {
        }

        assert ($Is(LitInt(0), TInt) && LitInt(0) == LitInt(Mul(LitInt(2), LitInt(0))))
           || (exists w#0_1: int :: w#0_1 == Mul(LitInt(2), w#0_1));
        assume true;
        assume w#0_0 == Mul(LitInt(2), w#0_0);
        havoc w#0_2;
        assume true;
        assume true;
        assume w#0_2 == Mul(LitInt(2), w#0_2);
        assume true;
        assert w#0_0 == w#0_2;
        assume $let#40$canCall();
        assume $let#40$canCall();
        x#0 := (var w#0_1 := $let#40_w(); w#0_1);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(327,31)"} true;
    }
    else
    {
        assume true;
        assume true;
        assume true;
        assume !Lit(true) && !Lit(true) && !Lit(true);
        assert false;
    }

    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(329,9)
    assume true;
    assume true;
    t#0 := Lit(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(LitInt(3))), $Box(LitInt(5))));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(329,17)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(330,9)
    assume true;
    havoc a#0;
    havoc b#0;
    if (true)
    {
        if (t#0[$Box(a#0)])
        {
        }

        if (t#0[$Box(a#0)] && t#0[$Box(b#0)])
        {
        }
    }

    assert (
        $Is(LitInt(0), TInt)
         && $Is(LitInt(0), TInt)
         && 
        t#0[$Box(LitInt(0))]
         && t#0[$Box(LitInt(0))]
         && 0 != 0)
       || 
      (exists a#1: int :: 
        $Is(LitInt(0), TInt) && t#0[$Box(a#1)] && t#0[$Box(LitInt(0))] && a#1 != 0)
       || 
      (exists b#1: int :: 
        $Is(LitInt(0), TInt) && t#0[$Box(LitInt(0))] && t#0[$Box(b#1)] && 0 != b#1)
       || (exists a#1: int, b#1: int :: t#0[$Box(a#1)] && t#0[$Box(b#1)] && a#1 != b#1);
    assume true;
    assume t#0[$Box(a#0)] && t#0[$Box(b#0)] && a#0 != b#0;
    assume $let#43$canCall(t#0);
    assume $let#43$canCall(t#0);
    s#0 := (var a#1, b#1 := $let#43_a(t#0), $let#43_b(t#0); 
      Set#Union(Set#UnionOne(Set#Empty(): Set Box, $Box(a#1)), 
        Set#UnionOne(Set#Empty(): Set Box, $Box(b#1))));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(330,60)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LetExpr.dfy(331,3)
    assume true;
    assert Set#Equal(s#0, t#0);
}



// Constructor function declaration
function #PatternsWithExplicitTypes.Tuple.Pair(Box, Box) : DatatypeType;

const unique ##PatternsWithExplicitTypes.Tuple.Pair: DtCtorId;

// Constructor identifier
axiom (forall a#0#0#0: Box, a#0#1#0: Box :: 
  { #PatternsWithExplicitTypes.Tuple.Pair(a#0#0#0, a#0#1#0) } 
  DatatypeCtorId(#PatternsWithExplicitTypes.Tuple.Pair(a#0#0#0, a#0#1#0))
     == ##PatternsWithExplicitTypes.Tuple.Pair);

function PatternsWithExplicitTypes.Tuple.Pair_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { PatternsWithExplicitTypes.Tuple.Pair_q(d) } 
  PatternsWithExplicitTypes.Tuple.Pair_q(d)
     <==> DatatypeCtorId(d) == ##PatternsWithExplicitTypes.Tuple.Pair);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { PatternsWithExplicitTypes.Tuple.Pair_q(d) } 
  PatternsWithExplicitTypes.Tuple.Pair_q(d)
     ==> (exists a#1#0#0: Box, a#1#1#0: Box :: 
      d == #PatternsWithExplicitTypes.Tuple.Pair(a#1#0#0, a#1#1#0)));

function Tclass.PatternsWithExplicitTypes.Tuple(Ty, Ty) : Ty;

const unique Tagclass.PatternsWithExplicitTypes.Tuple: TyTag;

// Tclass.PatternsWithExplicitTypes.Tuple Tag
axiom (forall PatternsWithExplicitTypes.Tuple$T: Ty, PatternsWithExplicitTypes.Tuple$U: Ty :: 
  { Tclass.PatternsWithExplicitTypes.Tuple(PatternsWithExplicitTypes.Tuple$T, PatternsWithExplicitTypes.Tuple$U) } 
  Tag(Tclass.PatternsWithExplicitTypes.Tuple(PatternsWithExplicitTypes.Tuple$T, PatternsWithExplicitTypes.Tuple$U))
       == Tagclass.PatternsWithExplicitTypes.Tuple
     && TagFamily(Tclass.PatternsWithExplicitTypes.Tuple(PatternsWithExplicitTypes.Tuple$T, PatternsWithExplicitTypes.Tuple$U))
       == tytagFamily$Tuple);

// Tclass.PatternsWithExplicitTypes.Tuple injectivity 0
axiom (forall PatternsWithExplicitTypes.Tuple$T: Ty, PatternsWithExplicitTypes.Tuple$U: Ty :: 
  { Tclass.PatternsWithExplicitTypes.Tuple(PatternsWithExplicitTypes.Tuple$T, PatternsWithExplicitTypes.Tuple$U) } 
  Tclass.PatternsWithExplicitTypes.Tuple_0(Tclass.PatternsWithExplicitTypes.Tuple(PatternsWithExplicitTypes.Tuple$T, PatternsWithExplicitTypes.Tuple$U))
     == PatternsWithExplicitTypes.Tuple$T);

function Tclass.PatternsWithExplicitTypes.Tuple_0(Ty) : Ty;

// Tclass.PatternsWithExplicitTypes.Tuple injectivity 1
axiom (forall PatternsWithExplicitTypes.Tuple$T: Ty, PatternsWithExplicitTypes.Tuple$U: Ty :: 
  { Tclass.PatternsWithExplicitTypes.Tuple(PatternsWithExplicitTypes.Tuple$T, PatternsWithExplicitTypes.Tuple$U) } 
  Tclass.PatternsWithExplicitTypes.Tuple_1(Tclass.PatternsWithExplicitTypes.Tuple(PatternsWithExplicitTypes.Tuple$T, PatternsWithExplicitTypes.Tuple$U))
     == PatternsWithExplicitTypes.Tuple$U);

function Tclass.PatternsWithExplicitTypes.Tuple_1(Ty) : Ty;

// Box/unbox axiom for Tclass.PatternsWithExplicitTypes.Tuple
axiom (forall PatternsWithExplicitTypes.Tuple$T: Ty, 
    PatternsWithExplicitTypes.Tuple$U: Ty, 
    bx: Box :: 
  { $IsBox(bx, 
      Tclass.PatternsWithExplicitTypes.Tuple(PatternsWithExplicitTypes.Tuple$T, PatternsWithExplicitTypes.Tuple$U)) } 
  $IsBox(bx, 
      Tclass.PatternsWithExplicitTypes.Tuple(PatternsWithExplicitTypes.Tuple$T, PatternsWithExplicitTypes.Tuple$U))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, 
        Tclass.PatternsWithExplicitTypes.Tuple(PatternsWithExplicitTypes.Tuple$T, PatternsWithExplicitTypes.Tuple$U)));

// Constructor $Is
axiom (forall PatternsWithExplicitTypes.Tuple$T: Ty, 
    PatternsWithExplicitTypes.Tuple$U: Ty, 
    a#2#0#0: Box, 
    a#2#1#0: Box :: 
  { $Is(#PatternsWithExplicitTypes.Tuple.Pair(a#2#0#0, a#2#1#0), 
      Tclass.PatternsWithExplicitTypes.Tuple(PatternsWithExplicitTypes.Tuple$T, PatternsWithExplicitTypes.Tuple$U)) } 
  $Is(#PatternsWithExplicitTypes.Tuple.Pair(a#2#0#0, a#2#1#0), 
      Tclass.PatternsWithExplicitTypes.Tuple(PatternsWithExplicitTypes.Tuple$T, PatternsWithExplicitTypes.Tuple$U))
     <==> $IsBox(a#2#0#0, PatternsWithExplicitTypes.Tuple$T)
       && $IsBox(a#2#1#0, PatternsWithExplicitTypes.Tuple$U));

// Constructor $IsAlloc
axiom (forall PatternsWithExplicitTypes.Tuple$T: Ty, 
    PatternsWithExplicitTypes.Tuple$U: Ty, 
    a#3#0#0: Box, 
    a#3#1#0: Box, 
    $h: Heap :: 
  { $IsAlloc(#PatternsWithExplicitTypes.Tuple.Pair(a#3#0#0, a#3#1#0), 
      Tclass.PatternsWithExplicitTypes.Tuple(PatternsWithExplicitTypes.Tuple$T, PatternsWithExplicitTypes.Tuple$U), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#PatternsWithExplicitTypes.Tuple.Pair(a#3#0#0, a#3#1#0), 
        Tclass.PatternsWithExplicitTypes.Tuple(PatternsWithExplicitTypes.Tuple$T, PatternsWithExplicitTypes.Tuple$U), 
        $h)
       <==> $IsAllocBox(a#3#0#0, PatternsWithExplicitTypes.Tuple$T, $h)
         && $IsAllocBox(a#3#1#0, PatternsWithExplicitTypes.Tuple$U, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, PatternsWithExplicitTypes.Tuple$T: Ty, $h: Heap :: 
  { $IsAllocBox(PatternsWithExplicitTypes.Tuple._0(d), PatternsWithExplicitTypes.Tuple$T, $h) } 
  $IsGoodHeap($h)
       && 
      PatternsWithExplicitTypes.Tuple.Pair_q(d)
       && (exists PatternsWithExplicitTypes.Tuple$U: Ty :: 
        { $IsAlloc(d, 
            Tclass.PatternsWithExplicitTypes.Tuple(PatternsWithExplicitTypes.Tuple$T, PatternsWithExplicitTypes.Tuple$U), 
            $h) } 
        $IsAlloc(d, 
          Tclass.PatternsWithExplicitTypes.Tuple(PatternsWithExplicitTypes.Tuple$T, PatternsWithExplicitTypes.Tuple$U), 
          $h))
     ==> $IsAllocBox(PatternsWithExplicitTypes.Tuple._0(d), PatternsWithExplicitTypes.Tuple$T, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, PatternsWithExplicitTypes.Tuple$U: Ty, $h: Heap :: 
  { $IsAllocBox(PatternsWithExplicitTypes.Tuple._1(d), PatternsWithExplicitTypes.Tuple$U, $h) } 
  $IsGoodHeap($h)
       && 
      PatternsWithExplicitTypes.Tuple.Pair_q(d)
       && (exists PatternsWithExplicitTypes.Tuple$T: Ty :: 
        { $IsAlloc(d, 
            Tclass.PatternsWithExplicitTypes.Tuple(PatternsWithExplicitTypes.Tuple$T, PatternsWithExplicitTypes.Tuple$U), 
            $h) } 
        $IsAlloc(d, 
          Tclass.PatternsWithExplicitTypes.Tuple(PatternsWithExplicitTypes.Tuple$T, PatternsWithExplicitTypes.Tuple$U), 
          $h))
     ==> $IsAllocBox(PatternsWithExplicitTypes.Tuple._1(d), PatternsWithExplicitTypes.Tuple$U, $h));

// Constructor literal
axiom (forall a#4#0#0: Box, a#4#1#0: Box :: 
  { #PatternsWithExplicitTypes.Tuple.Pair(Lit(a#4#0#0), Lit(a#4#1#0)) } 
  #PatternsWithExplicitTypes.Tuple.Pair(Lit(a#4#0#0), Lit(a#4#1#0))
     == Lit(#PatternsWithExplicitTypes.Tuple.Pair(a#4#0#0, a#4#1#0)));

function PatternsWithExplicitTypes.Tuple._0(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#5#0#0: Box, a#5#1#0: Box :: 
  { #PatternsWithExplicitTypes.Tuple.Pair(a#5#0#0, a#5#1#0) } 
  PatternsWithExplicitTypes.Tuple._0(#PatternsWithExplicitTypes.Tuple.Pair(a#5#0#0, a#5#1#0))
     == a#5#0#0);

// Inductive rank
axiom (forall a#6#0#0: Box, a#6#1#0: Box :: 
  { #PatternsWithExplicitTypes.Tuple.Pair(a#6#0#0, a#6#1#0) } 
  BoxRank(a#6#0#0)
     < DtRank(#PatternsWithExplicitTypes.Tuple.Pair(a#6#0#0, a#6#1#0)));

function PatternsWithExplicitTypes.Tuple._1(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#7#0#0: Box, a#7#1#0: Box :: 
  { #PatternsWithExplicitTypes.Tuple.Pair(a#7#0#0, a#7#1#0) } 
  PatternsWithExplicitTypes.Tuple._1(#PatternsWithExplicitTypes.Tuple.Pair(a#7#0#0, a#7#1#0))
     == a#7#1#0);

// Inductive rank
axiom (forall a#8#0#0: Box, a#8#1#0: Box :: 
  { #PatternsWithExplicitTypes.Tuple.Pair(a#8#0#0, a#8#1#0) } 
  BoxRank(a#8#1#0)
     < DtRank(#PatternsWithExplicitTypes.Tuple.Pair(a#8#0#0, a#8#1#0)));

// Depth-one case-split function
function $IsA#PatternsWithExplicitTypes.Tuple(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#PatternsWithExplicitTypes.Tuple(d) } 
  $IsA#PatternsWithExplicitTypes.Tuple(d)
     ==> PatternsWithExplicitTypes.Tuple.Pair_q(d));

// Questionmark data type disjunctivity
axiom (forall PatternsWithExplicitTypes.Tuple$T: Ty, 
    PatternsWithExplicitTypes.Tuple$U: Ty, 
    d: DatatypeType :: 
  { PatternsWithExplicitTypes.Tuple.Pair_q(d), $Is(d, 
      Tclass.PatternsWithExplicitTypes.Tuple(PatternsWithExplicitTypes.Tuple$T, PatternsWithExplicitTypes.Tuple$U)) } 
  $Is(d, 
      Tclass.PatternsWithExplicitTypes.Tuple(PatternsWithExplicitTypes.Tuple$T, PatternsWithExplicitTypes.Tuple$U))
     ==> PatternsWithExplicitTypes.Tuple.Pair_q(d));

// Datatype extensional equality declaration
function PatternsWithExplicitTypes.Tuple#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #PatternsWithExplicitTypes.Tuple.Pair
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { PatternsWithExplicitTypes.Tuple#Equal(a, b) } 
  true
     ==> (PatternsWithExplicitTypes.Tuple#Equal(a, b)
       <==> PatternsWithExplicitTypes.Tuple._0(a) == PatternsWithExplicitTypes.Tuple._0(b)
         && PatternsWithExplicitTypes.Tuple._1(a) == PatternsWithExplicitTypes.Tuple._1(b)));

// Datatype extensionality axiom: PatternsWithExplicitTypes.Tuple
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { PatternsWithExplicitTypes.Tuple#Equal(a, b) } 
  PatternsWithExplicitTypes.Tuple#Equal(a, b) <==> a == b);

const unique class.PatternsWithExplicitTypes.Tuple: ClassName;

const unique class.PatternsWithExplicitTypes.__default: ClassName;

function Tclass.PatternsWithExplicitTypes.__default() : Ty;

const unique Tagclass.PatternsWithExplicitTypes.__default: TyTag;

// Tclass.PatternsWithExplicitTypes.__default Tag
axiom Tag(Tclass.PatternsWithExplicitTypes.__default())
     == Tagclass.PatternsWithExplicitTypes.__default
   && TagFamily(Tclass.PatternsWithExplicitTypes.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.PatternsWithExplicitTypes.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.PatternsWithExplicitTypes.__default()) } 
  $IsBox(bx, Tclass.PatternsWithExplicitTypes.__default())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.PatternsWithExplicitTypes.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.PatternsWithExplicitTypes.__default()) } 
  $Is($o, Tclass.PatternsWithExplicitTypes.__default())
     <==> $o == null || dtype($o) == Tclass.PatternsWithExplicitTypes.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.PatternsWithExplicitTypes.__default(), $h) } 
  $IsAlloc($o, Tclass.PatternsWithExplicitTypes.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

const unique class.CanCallRegressionTests.C?: ClassName;

function Tclass.CanCallRegressionTests.C?() : Ty;

const unique Tagclass.CanCallRegressionTests.C?: TyTag;

// Tclass.CanCallRegressionTests.C? Tag
axiom Tag(Tclass.CanCallRegressionTests.C?()) == Tagclass.CanCallRegressionTests.C?
   && TagFamily(Tclass.CanCallRegressionTests.C?()) == tytagFamily$C;

// Box/unbox axiom for Tclass.CanCallRegressionTests.C?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.CanCallRegressionTests.C?()) } 
  $IsBox(bx, Tclass.CanCallRegressionTests.C?())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.CanCallRegressionTests.C?()));

// C: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.CanCallRegressionTests.C?()) } 
  $Is($o, Tclass.CanCallRegressionTests.C?())
     <==> $o == null || dtype($o) == Tclass.CanCallRegressionTests.C?());

// C: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.CanCallRegressionTests.C?(), $h) } 
  $IsAlloc($o, Tclass.CanCallRegressionTests.C?(), $h)
     <==> $o == null || read($h, $o, alloc));

axiom FDim(CanCallRegressionTests.C.x) == 0
   && FieldOfDecl(class.CanCallRegressionTests.C?, field$x)
     == CanCallRegressionTests.C.x
   && !$IsGhostField(CanCallRegressionTests.C.x);

const CanCallRegressionTests.C.x: Field int;

// C.x: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, CanCallRegressionTests.C.x) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass.CanCallRegressionTests.C?()
     ==> $Is(read($h, $o, CanCallRegressionTests.C.x), TInt));

// C.x: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, CanCallRegressionTests.C.x) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.CanCallRegressionTests.C?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, CanCallRegressionTests.C.x), TInt, $h));

// function declaration for CanCallRegressionTests.C.Id
function CanCallRegressionTests.C.Id(this: ref, c#0: ref) : ref;

function CanCallRegressionTests.C.Id#canCall(this: ref, c#0: ref) : bool;

function Tclass.CanCallRegressionTests.C() : Ty;

const unique Tagclass.CanCallRegressionTests.C: TyTag;

// Tclass.CanCallRegressionTests.C Tag
axiom Tag(Tclass.CanCallRegressionTests.C()) == Tagclass.CanCallRegressionTests.C
   && TagFamily(Tclass.CanCallRegressionTests.C()) == tytagFamily$C;

// Box/unbox axiom for Tclass.CanCallRegressionTests.C
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.CanCallRegressionTests.C()) } 
  $IsBox(bx, Tclass.CanCallRegressionTests.C())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.CanCallRegressionTests.C()));

// consequence axiom for CanCallRegressionTests.C.Id
axiom true
   ==> (forall this: ref, c#0: ref :: 
    { CanCallRegressionTests.C.Id(this, c#0) } 
    CanCallRegressionTests.C.Id#canCall(this, c#0)
         || (
          this != null
           && $Is(this, Tclass.CanCallRegressionTests.C())
           && $Is(c#0, Tclass.CanCallRegressionTests.C()))
       ==> $Is(CanCallRegressionTests.C.Id(this, c#0), Tclass.CanCallRegressionTests.C()));

function CanCallRegressionTests.C.Id#requires(ref, ref) : bool;

// #requires axiom for CanCallRegressionTests.C.Id
axiom (forall this: ref, c#0: ref :: 
  { CanCallRegressionTests.C.Id#requires(this, c#0) } 
  this != null
       && $Is(this, Tclass.CanCallRegressionTests.C())
       && $Is(c#0, Tclass.CanCallRegressionTests.C())
     ==> CanCallRegressionTests.C.Id#requires(this, c#0) == true);

// definition axiom for CanCallRegressionTests.C.Id (revealed)
axiom true
   ==> (forall this: ref, c#0: ref :: 
    { CanCallRegressionTests.C.Id(this, c#0) } 
    CanCallRegressionTests.C.Id#canCall(this, c#0)
         || (
          this != null
           && $Is(this, Tclass.CanCallRegressionTests.C())
           && $Is(c#0, Tclass.CanCallRegressionTests.C()))
       ==> CanCallRegressionTests.C.Id(this, c#0) == c#0);

// definition axiom for CanCallRegressionTests.C.Id for decreasing-related literals (revealed)
axiom true
   ==> (forall this: ref, c#0: ref :: 
    {:weight 3} { CanCallRegressionTests.C.Id(this, Lit(c#0)) } 
    CanCallRegressionTests.C.Id#canCall(this, Lit(c#0))
         || (
          this != null
           && $Is(this, Tclass.CanCallRegressionTests.C())
           && $Is(c#0, Tclass.CanCallRegressionTests.C()))
       ==> CanCallRegressionTests.C.Id(this, Lit(c#0)) == Lit(c#0));

// definition axiom for CanCallRegressionTests.C.Id for all literals (revealed)
axiom true
   ==> (forall this: ref, c#0: ref :: 
    {:weight 3} { CanCallRegressionTests.C.Id(Lit(this), Lit(c#0)) } 
    CanCallRegressionTests.C.Id#canCall(Lit(this), Lit(c#0))
         || (
          this != null
           && $Is(this, Tclass.CanCallRegressionTests.C())
           && $Is(c#0, Tclass.CanCallRegressionTests.C()))
       ==> CanCallRegressionTests.C.Id(Lit(this), Lit(c#0)) == Lit(c#0));

// CanCallRegressionTests.C: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass.CanCallRegressionTests.C()) } 
  $Is(c#0, Tclass.CanCallRegressionTests.C())
     <==> $Is(c#0, Tclass.CanCallRegressionTests.C?()) && c#0 != null);

// CanCallRegressionTests.C: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass.CanCallRegressionTests.C(), $h) } 
  $IsAlloc(c#0, Tclass.CanCallRegressionTests.C(), $h)
     <==> $IsAlloc(c#0, Tclass.CanCallRegressionTests.C?(), $h));

const unique class.CanCallRegressionTests.__default: ClassName;

function Tclass.CanCallRegressionTests.__default() : Ty;

const unique Tagclass.CanCallRegressionTests.__default: TyTag;

// Tclass.CanCallRegressionTests.__default Tag
axiom Tag(Tclass.CanCallRegressionTests.__default())
     == Tagclass.CanCallRegressionTests.__default
   && TagFamily(Tclass.CanCallRegressionTests.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.CanCallRegressionTests.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.CanCallRegressionTests.__default()) } 
  $IsBox(bx, Tclass.CanCallRegressionTests.__default())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.CanCallRegressionTests.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.CanCallRegressionTests.__default()) } 
  $Is($o, Tclass.CanCallRegressionTests.__default())
     <==> $o == null || dtype($o) == Tclass.CanCallRegressionTests.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.CanCallRegressionTests.__default(), $h) } 
  $IsAlloc($o, Tclass.CanCallRegressionTests.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

// Constructor function declaration
function #LitLet.Nat.O() : DatatypeType;

const unique ##LitLet.Nat.O: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#LitLet.Nat.O()) == ##LitLet.Nat.O;

function LitLet.Nat.O_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { LitLet.Nat.O_q(d) } 
  LitLet.Nat.O_q(d) <==> DatatypeCtorId(d) == ##LitLet.Nat.O);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { LitLet.Nat.O_q(d) } 
  LitLet.Nat.O_q(d) ==> d == #LitLet.Nat.O());

function Tclass.LitLet.Nat() : Ty;

const unique Tagclass.LitLet.Nat: TyTag;

// Tclass.LitLet.Nat Tag
axiom Tag(Tclass.LitLet.Nat()) == Tagclass.LitLet.Nat
   && TagFamily(Tclass.LitLet.Nat()) == tytagFamily$Nat;

// Box/unbox axiom for Tclass.LitLet.Nat
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.LitLet.Nat()) } 
  $IsBox(bx, Tclass.LitLet.Nat())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass.LitLet.Nat()));

// Constructor $Is
axiom $Is(#LitLet.Nat.O(), Tclass.LitLet.Nat());

// Constructor $IsAlloc
axiom (forall $h: Heap :: 
  { $IsAlloc(#LitLet.Nat.O(), Tclass.LitLet.Nat(), $h) } 
  $IsGoodHeap($h) ==> $IsAlloc(#LitLet.Nat.O(), Tclass.LitLet.Nat(), $h));

// Constructor literal
axiom #LitLet.Nat.O() == Lit(#LitLet.Nat.O());

// Constructor function declaration
function #LitLet.Nat.S(DatatypeType) : DatatypeType;

const unique ##LitLet.Nat.S: DtCtorId;

// Constructor identifier
axiom (forall a#5#0#0: DatatypeType :: 
  { #LitLet.Nat.S(a#5#0#0) } 
  DatatypeCtorId(#LitLet.Nat.S(a#5#0#0)) == ##LitLet.Nat.S);

function LitLet.Nat.S_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { LitLet.Nat.S_q(d) } 
  LitLet.Nat.S_q(d) <==> DatatypeCtorId(d) == ##LitLet.Nat.S);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { LitLet.Nat.S_q(d) } 
  LitLet.Nat.S_q(d)
     ==> (exists a#6#0#0: DatatypeType :: d == #LitLet.Nat.S(a#6#0#0)));

// Constructor $Is
axiom (forall a#7#0#0: DatatypeType :: 
  { $Is(#LitLet.Nat.S(a#7#0#0), Tclass.LitLet.Nat()) } 
  $Is(#LitLet.Nat.S(a#7#0#0), Tclass.LitLet.Nat())
     <==> $Is(a#7#0#0, Tclass.LitLet.Nat()));

// Constructor $IsAlloc
axiom (forall a#8#0#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#LitLet.Nat.S(a#8#0#0), Tclass.LitLet.Nat(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#LitLet.Nat.S(a#8#0#0), Tclass.LitLet.Nat(), $h)
       <==> $IsAlloc(a#8#0#0, Tclass.LitLet.Nat(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(LitLet.Nat.pred(d), Tclass.LitLet.Nat(), $h) } 
  $IsGoodHeap($h) && LitLet.Nat.S_q(d) && $IsAlloc(d, Tclass.LitLet.Nat(), $h)
     ==> $IsAlloc(LitLet.Nat.pred(d), Tclass.LitLet.Nat(), $h));

// Constructor literal
axiom (forall a#9#0#0: DatatypeType :: 
  { #LitLet.Nat.S(Lit(a#9#0#0)) } 
  #LitLet.Nat.S(Lit(a#9#0#0)) == Lit(#LitLet.Nat.S(a#9#0#0)));

function LitLet.Nat.pred(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#10#0#0: DatatypeType :: 
  { #LitLet.Nat.S(a#10#0#0) } 
  LitLet.Nat.pred(#LitLet.Nat.S(a#10#0#0)) == a#10#0#0);

// Inductive rank
axiom (forall a#11#0#0: DatatypeType :: 
  { #LitLet.Nat.S(a#11#0#0) } 
  DtRank(a#11#0#0) < DtRank(#LitLet.Nat.S(a#11#0#0)));

// Depth-one case-split function
function $IsA#LitLet.Nat(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#LitLet.Nat(d) } 
  $IsA#LitLet.Nat(d) ==> LitLet.Nat.O_q(d) || LitLet.Nat.S_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { LitLet.Nat.S_q(d), $Is(d, Tclass.LitLet.Nat()) } 
    { LitLet.Nat.O_q(d), $Is(d, Tclass.LitLet.Nat()) } 
  $Is(d, Tclass.LitLet.Nat()) ==> LitLet.Nat.O_q(d) || LitLet.Nat.S_q(d));

// Datatype extensional equality declaration
function LitLet.Nat#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #LitLet.Nat.O
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { LitLet.Nat#Equal(a, b), LitLet.Nat.O_q(a) } 
    { LitLet.Nat#Equal(a, b), LitLet.Nat.O_q(b) } 
  LitLet.Nat.O_q(a) && LitLet.Nat.O_q(b) ==> (LitLet.Nat#Equal(a, b) <==> true));

// Datatype extensional equality definition: #LitLet.Nat.S
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { LitLet.Nat#Equal(a, b), LitLet.Nat.S_q(a) } 
    { LitLet.Nat#Equal(a, b), LitLet.Nat.S_q(b) } 
  LitLet.Nat.S_q(a) && LitLet.Nat.S_q(b)
     ==> (LitLet.Nat#Equal(a, b)
       <==> LitLet.Nat#Equal(LitLet.Nat.pred(a), LitLet.Nat.pred(b))));

// Datatype extensionality axiom: LitLet.Nat
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { LitLet.Nat#Equal(a, b) } 
  LitLet.Nat#Equal(a, b) <==> a == b);

const unique class.LitLet.Nat: ClassName;

const unique class.LitLet.__default: ClassName;

function Tclass.LitLet.__default() : Ty;

const unique Tagclass.LitLet.__default: TyTag;

// Tclass.LitLet.__default Tag
axiom Tag(Tclass.LitLet.__default()) == Tagclass.LitLet.__default
   && TagFamily(Tclass.LitLet.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.LitLet.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.LitLet.__default()) } 
  $IsBox(bx, Tclass.LitLet.__default())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.LitLet.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.LitLet.__default()) } 
  $Is($o, Tclass.LitLet.__default())
     <==> $o == null || dtype($o) == Tclass.LitLet.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.LitLet.__default(), $h) } 
  $IsAlloc($o, Tclass.LitLet.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

// function declaration for LitLet._default.Gauss
function LitLet.__default.Gauss($ly: LayerType, n#0: int) : int;

function LitLet.__default.Gauss#canCall(n#0: int) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, n#0: int :: 
  { LitLet.__default.Gauss($LS($ly), n#0) } 
  LitLet.__default.Gauss($LS($ly), n#0) == LitLet.__default.Gauss($ly, n#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, n#0: int :: 
  { LitLet.__default.Gauss(AsFuelBottom($ly), n#0) } 
  LitLet.__default.Gauss($ly, n#0) == LitLet.__default.Gauss($LZ, n#0));

// consequence axiom for LitLet.__default.Gauss
axiom true
   ==> (forall $ly: LayerType, n#0: int :: 
    { LitLet.__default.Gauss($ly, n#0) } 
    LitLet.__default.Gauss#canCall(n#0) || LitInt(0) <= n#0
       ==> LitInt(0) <= LitLet.__default.Gauss($ly, n#0));

function LitLet.__default.Gauss#requires(LayerType, int) : bool;

// #requires axiom for LitLet.__default.Gauss
axiom (forall $ly: LayerType, n#0: int :: 
  { LitLet.__default.Gauss#requires($ly, n#0) } 
  LitInt(0) <= n#0 ==> LitLet.__default.Gauss#requires($ly, n#0) == true);

// definition axiom for LitLet.__default.Gauss (revealed)
axiom true
   ==> (forall $ly: LayerType, n#0: int :: 
    { LitLet.__default.Gauss($LS($ly), n#0) } 
    LitLet.__default.Gauss#canCall(n#0) || LitInt(0) <= n#0
       ==> (n#0 != LitInt(0) ==> LitLet.__default.Gauss#canCall(n#0 - 1))
         && LitLet.__default.Gauss($LS($ly), n#0)
           == (if n#0 == LitInt(0) then 0 else n#0 + LitLet.__default.Gauss($ly, n#0 - 1)));

// definition axiom for LitLet.__default.Gauss for all literals (revealed)
axiom true
   ==> (forall $ly: LayerType, n#0: int :: 
    {:weight 3} { LitLet.__default.Gauss($LS($ly), LitInt(n#0)) } 
    LitLet.__default.Gauss#canCall(LitInt(n#0)) || LitInt(0) <= n#0
       ==> (LitInt(n#0) != LitInt(0) ==> LitLet.__default.Gauss#canCall(LitInt(n#0 - 1)))
         && LitLet.__default.Gauss($LS($ly), LitInt(n#0))
           == (if LitInt(n#0) == LitInt(0)
             then 0
             else n#0 + LitLet.__default.Gauss($LS($ly), LitInt(n#0 - 1))));

// function declaration for LitLet._default.plus
function LitLet.__default.plus($ly: LayerType, n#0: DatatypeType, m#0: DatatypeType) : DatatypeType;

function LitLet.__default.plus#canCall(n#0: DatatypeType, m#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType :: 
  { LitLet.__default.plus($LS($ly), n#0, m#0) } 
  LitLet.__default.plus($LS($ly), n#0, m#0)
     == LitLet.__default.plus($ly, n#0, m#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType :: 
  { LitLet.__default.plus(AsFuelBottom($ly), n#0, m#0) } 
  LitLet.__default.plus($ly, n#0, m#0) == LitLet.__default.plus($LZ, n#0, m#0));

// consequence axiom for LitLet.__default.plus
axiom true
   ==> (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType :: 
    { LitLet.__default.plus($ly, n#0, m#0) } 
    LitLet.__default.plus#canCall(n#0, m#0)
         || ($Is(n#0, Tclass.LitLet.Nat()) && $Is(m#0, Tclass.LitLet.Nat()))
       ==> $Is(LitLet.__default.plus($ly, n#0, m#0), Tclass.LitLet.Nat()));

function LitLet.__default.plus#requires(LayerType, DatatypeType, DatatypeType) : bool;

// #requires axiom for LitLet.__default.plus
axiom (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType :: 
  { LitLet.__default.plus#requires($ly, n#0, m#0) } 
  $Is(n#0, Tclass.LitLet.Nat()) && $Is(m#0, Tclass.LitLet.Nat())
     ==> LitLet.__default.plus#requires($ly, n#0, m#0) == true);

// definition axiom for LitLet.__default.plus (revealed)
axiom true
   ==> (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType :: 
    { LitLet.__default.plus($LS($ly), n#0, m#0) } 
    LitLet.__default.plus#canCall(n#0, m#0)
         || ($Is(n#0, Tclass.LitLet.Nat()) && $Is(m#0, Tclass.LitLet.Nat()))
       ==> (!LitLet.Nat.O_q(n#0)
           ==> (var n'#5 := LitLet.Nat.pred(n#0); LitLet.__default.plus#canCall(n'#5, m#0)))
         && LitLet.__default.plus($LS($ly), n#0, m#0)
           == (if LitLet.Nat.O_q(n#0)
             then m#0
             else (var n'#4 := LitLet.Nat.pred(n#0); 
              #LitLet.Nat.S(LitLet.__default.plus($ly, n'#4, m#0)))));

// definition axiom for LitLet.__default.plus for all literals (revealed)
axiom true
   ==> (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType :: 
    {:weight 3} { LitLet.__default.plus($LS($ly), Lit(n#0), Lit(m#0)) } 
    LitLet.__default.plus#canCall(Lit(n#0), Lit(m#0))
         || ($Is(n#0, Tclass.LitLet.Nat()) && $Is(m#0, Tclass.LitLet.Nat()))
       ==> (!Lit(LitLet.Nat.O_q(Lit(n#0)))
           ==> (var n'#7 := Lit(LitLet.Nat.pred(Lit(n#0))); 
            LitLet.__default.plus#canCall(n'#7, Lit(m#0))))
         && LitLet.__default.plus($LS($ly), Lit(n#0), Lit(m#0))
           == (if LitLet.Nat.O_q(Lit(n#0))
             then m#0
             else (var n'#6 := Lit(LitLet.Nat.pred(Lit(n#0))); 
              Lit(#LitLet.Nat.S(Lit(LitLet.__default.plus($LS($ly), n'#6, Lit(m#0))))))));

// function declaration for LitLet._default.mult
function LitLet.__default.mult($ly: LayerType, n#0: DatatypeType, m#0: DatatypeType) : DatatypeType;

function LitLet.__default.mult#canCall(n#0: DatatypeType, m#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType :: 
  { LitLet.__default.mult($LS($ly), n#0, m#0) } 
  LitLet.__default.mult($LS($ly), n#0, m#0)
     == LitLet.__default.mult($ly, n#0, m#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType :: 
  { LitLet.__default.mult(AsFuelBottom($ly), n#0, m#0) } 
  LitLet.__default.mult($ly, n#0, m#0) == LitLet.__default.mult($LZ, n#0, m#0));

// consequence axiom for LitLet.__default.mult
axiom true
   ==> (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType :: 
    { LitLet.__default.mult($ly, n#0, m#0) } 
    LitLet.__default.mult#canCall(n#0, m#0)
         || ($Is(n#0, Tclass.LitLet.Nat()) && $Is(m#0, Tclass.LitLet.Nat()))
       ==> $Is(LitLet.__default.mult($ly, n#0, m#0), Tclass.LitLet.Nat()));

function LitLet.__default.mult#requires(LayerType, DatatypeType, DatatypeType) : bool;

// #requires axiom for LitLet.__default.mult
axiom (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType :: 
  { LitLet.__default.mult#requires($ly, n#0, m#0) } 
  $Is(n#0, Tclass.LitLet.Nat()) && $Is(m#0, Tclass.LitLet.Nat())
     ==> LitLet.__default.mult#requires($ly, n#0, m#0) == true);

// definition axiom for LitLet.__default.mult (revealed)
axiom true
   ==> (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType :: 
    { LitLet.__default.mult($LS($ly), n#0, m#0) } 
    LitLet.__default.mult#canCall(n#0, m#0)
         || ($Is(n#0, Tclass.LitLet.Nat()) && $Is(m#0, Tclass.LitLet.Nat()))
       ==> (!LitLet.Nat.O_q(n#0)
           ==> (var n'#2 := LitLet.Nat.pred(n#0); 
            LitLet.__default.mult#canCall(n'#2, m#0)
               && LitLet.__default.plus#canCall(m#0, LitLet.__default.mult($ly, n'#2, m#0))))
         && LitLet.__default.mult($LS($ly), n#0, m#0)
           == (if LitLet.Nat.O_q(n#0)
             then #LitLet.Nat.O()
             else (var n'#2 := LitLet.Nat.pred(n#0); 
              LitLet.__default.plus($LS($LZ), m#0, LitLet.__default.mult($ly, n'#2, m#0)))));

// definition axiom for LitLet.__default.mult for all literals (revealed)
axiom true
   ==> (forall $ly: LayerType, n#0: DatatypeType, m#0: DatatypeType :: 
    {:weight 3} { LitLet.__default.mult($LS($ly), Lit(n#0), Lit(m#0)) } 
    LitLet.__default.mult#canCall(Lit(n#0), Lit(m#0))
         || ($Is(n#0, Tclass.LitLet.Nat()) && $Is(m#0, Tclass.LitLet.Nat()))
       ==> (!Lit(LitLet.Nat.O_q(Lit(n#0)))
           ==> (var n'#3 := Lit(LitLet.Nat.pred(Lit(n#0))); 
            LitLet.__default.mult#canCall(n'#3, Lit(m#0))
               && LitLet.__default.plus#canCall(Lit(m#0), LitLet.__default.mult($LS($ly), n'#3, Lit(m#0)))))
         && LitLet.__default.mult($LS($ly), Lit(n#0), Lit(m#0))
           == (if LitLet.Nat.O_q(Lit(n#0))
             then #LitLet.Nat.O()
             else (var n'#3 := Lit(LitLet.Nat.pred(Lit(n#0))); 
              Lit(LitLet.__default.plus($LS($LZ), Lit(m#0), Lit(LitLet.__default.mult($LS($ly), n'#3, Lit(m#0))))))));

// function declaration for LitLet._default.factorial
function LitLet.__default.factorial($ly: LayerType, n#0: DatatypeType) : DatatypeType;

function LitLet.__default.factorial#canCall(n#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, n#0: DatatypeType :: 
  { LitLet.__default.factorial($LS($ly), n#0) } 
  LitLet.__default.factorial($LS($ly), n#0)
     == LitLet.__default.factorial($ly, n#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, n#0: DatatypeType :: 
  { LitLet.__default.factorial(AsFuelBottom($ly), n#0) } 
  LitLet.__default.factorial($ly, n#0) == LitLet.__default.factorial($LZ, n#0));

// consequence axiom for LitLet.__default.factorial
axiom true
   ==> (forall $ly: LayerType, n#0: DatatypeType :: 
    { LitLet.__default.factorial($ly, n#0) } 
    LitLet.__default.factorial#canCall(n#0) || $Is(n#0, Tclass.LitLet.Nat())
       ==> $Is(LitLet.__default.factorial($ly, n#0), Tclass.LitLet.Nat()));

function LitLet.__default.factorial#requires(LayerType, DatatypeType) : bool;

// #requires axiom for LitLet.__default.factorial
axiom (forall $ly: LayerType, n#0: DatatypeType :: 
  { LitLet.__default.factorial#requires($ly, n#0) } 
  $Is(n#0, Tclass.LitLet.Nat())
     ==> LitLet.__default.factorial#requires($ly, n#0) == true);

// definition axiom for LitLet.__default.factorial (revealed)
axiom true
   ==> (forall $ly: LayerType, n#0: DatatypeType :: 
    { LitLet.__default.factorial($LS($ly), n#0) } 
    LitLet.__default.factorial#canCall(n#0) || $Is(n#0, Tclass.LitLet.Nat())
       ==> (!LitLet.Nat.O_q(n#0)
           ==> (var n'#5 := LitLet.Nat.pred(n#0); 
            LitLet.__default.factorial#canCall(n'#5)
               && LitLet.__default.mult#canCall(n#0, LitLet.__default.factorial($ly, n'#5))))
         && LitLet.__default.factorial($LS($ly), n#0)
           == (if LitLet.Nat.O_q(n#0)
             then #LitLet.Nat.S(Lit(#LitLet.Nat.O()))
             else (var n'#4 := LitLet.Nat.pred(n#0); 
              LitLet.__default.mult($LS($LZ), n#0, LitLet.__default.factorial($ly, n'#4)))));

// definition axiom for LitLet.__default.factorial for all literals (revealed)
axiom true
   ==> (forall $ly: LayerType, n#0: DatatypeType :: 
    {:weight 3} { LitLet.__default.factorial($LS($ly), Lit(n#0)) } 
    LitLet.__default.factorial#canCall(Lit(n#0)) || $Is(n#0, Tclass.LitLet.Nat())
       ==> (!Lit(LitLet.Nat.O_q(Lit(n#0)))
           ==> (var n'#7 := Lit(LitLet.Nat.pred(Lit(n#0))); 
            LitLet.__default.factorial#canCall(n'#7)
               && LitLet.__default.mult#canCall(Lit(n#0), LitLet.__default.factorial($LS($ly), n'#7))))
         && LitLet.__default.factorial($LS($ly), Lit(n#0))
           == (if LitLet.Nat.O_q(Lit(n#0))
             then #LitLet.Nat.S(Lit(#LitLet.Nat.O()))
             else (var n'#6 := Lit(LitLet.Nat.pred(Lit(n#0))); 
              Lit(LitLet.__default.mult($LS($LZ), Lit(n#0), Lit(LitLet.__default.factorial($LS($ly), n'#6)))))));

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

const unique tytagFamily$AClass: TyTagFamily;

const unique tytagFamily$TrickySubstitution: TyTagFamily;

const unique tytagFamily$List: TyTagFamily;

const unique tytagFamily$Tuple: TyTagFamily;

const unique tytagFamily$Friend: TyTagFamily;

const unique tytagFamily$_default: TyTagFamily;

const unique tytagFamily$C: TyTagFamily;

const unique tytagFamily$Nat: TyTagFamily;

const unique field$index: NameFamily;

const unique field$v: NameFamily;

const unique field$w: NameFamily;

const unique field$x: NameFamily;
