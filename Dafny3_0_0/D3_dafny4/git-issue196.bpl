// Dafny 3.0.0.30204
// Command Line Options: -compile:0 -noVerify /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy -print:./git-issue196.bpl

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

const unique class._System.array2?: ClassName;

function Tclass._System.array2?(Ty) : Ty;

const unique Tagclass._System.array2?: TyTag;

// Tclass._System.array2? Tag
axiom (forall _System.array2$arg: Ty :: 
  { Tclass._System.array2?(_System.array2$arg) } 
  Tag(Tclass._System.array2?(_System.array2$arg)) == Tagclass._System.array2?
     && TagFamily(Tclass._System.array2?(_System.array2$arg)) == tytagFamily$array2);

// Tclass._System.array2? injectivity 0
axiom (forall _System.array2$arg: Ty :: 
  { Tclass._System.array2?(_System.array2$arg) } 
  Tclass._System.array2?_0(Tclass._System.array2?(_System.array2$arg))
     == _System.array2$arg);

function Tclass._System.array2?_0(Ty) : Ty;

// Box/unbox axiom for Tclass._System.array2?
axiom (forall _System.array2$arg: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.array2?(_System.array2$arg)) } 
  $IsBox(bx, Tclass._System.array2?(_System.array2$arg))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._System.array2?(_System.array2$arg)));

axiom (forall o: ref :: { _System.array2.Length0(o) } 0 <= _System.array2.Length0(o));

axiom (forall o: ref :: { _System.array2.Length1(o) } 0 <= _System.array2.Length1(o));

// array2.: Type axiom
axiom (forall _System.array2$arg: Ty, $h: Heap, $o: ref, $i0: int, $i1: int :: 
  { read($h, $o, MultiIndexField(IndexField($i0), $i1)), Tclass._System.array2?(_System.array2$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array2?(_System.array2$arg)
       && 
      0 <= $i0
       && $i0 < _System.array2.Length0($o)
       && 
      0 <= $i1
       && $i1 < _System.array2.Length1($o)
     ==> $IsBox(read($h, $o, MultiIndexField(IndexField($i0), $i1)), _System.array2$arg));

// array2.: Allocation axiom
axiom (forall _System.array2$arg: Ty, $h: Heap, $o: ref, $i0: int, $i1: int :: 
  { read($h, $o, MultiIndexField(IndexField($i0), $i1)), Tclass._System.array2?(_System.array2$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array2?(_System.array2$arg)
       && 
      0 <= $i0
       && $i0 < _System.array2.Length0($o)
       && 
      0 <= $i1
       && $i1 < _System.array2.Length1($o)
       && read($h, $o, alloc)
     ==> $IsAllocBox(read($h, $o, MultiIndexField(IndexField($i0), $i1)), _System.array2$arg, $h));

// array2: Class $Is
axiom (forall _System.array2$arg: Ty, $o: ref :: 
  { $Is($o, Tclass._System.array2?(_System.array2$arg)) } 
  $Is($o, Tclass._System.array2?(_System.array2$arg))
     <==> $o == null || dtype($o) == Tclass._System.array2?(_System.array2$arg));

// array2: Class $IsAlloc
axiom (forall _System.array2$arg: Ty, $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._System.array2?(_System.array2$arg), $h) } 
  $IsAlloc($o, Tclass._System.array2?(_System.array2$arg), $h)
     <==> $o == null || read($h, $o, alloc));

function _System.array2.Length0(ref) : int;

// array2.Length0: Type axiom
axiom (forall _System.array2$arg: Ty, $o: ref :: 
  { _System.array2.Length0($o), Tclass._System.array2?(_System.array2$arg) } 
  $o != null && dtype($o) == Tclass._System.array2?(_System.array2$arg)
     ==> $Is(_System.array2.Length0($o), TInt));

// array2.Length0: Allocation axiom
axiom (forall _System.array2$arg: Ty, $h: Heap, $o: ref :: 
  { _System.array2.Length0($o), read($h, $o, alloc), Tclass._System.array2?(_System.array2$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array2?(_System.array2$arg)
       && read($h, $o, alloc)
     ==> $IsAlloc(_System.array2.Length0($o), TInt, $h));

function _System.array2.Length1(ref) : int;

// array2.Length1: Type axiom
axiom (forall _System.array2$arg: Ty, $o: ref :: 
  { _System.array2.Length1($o), Tclass._System.array2?(_System.array2$arg) } 
  $o != null && dtype($o) == Tclass._System.array2?(_System.array2$arg)
     ==> $Is(_System.array2.Length1($o), TInt));

// array2.Length1: Allocation axiom
axiom (forall _System.array2$arg: Ty, $h: Heap, $o: ref :: 
  { _System.array2.Length1($o), read($h, $o, alloc), Tclass._System.array2?(_System.array2$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array2?(_System.array2$arg)
       && read($h, $o, alloc)
     ==> $IsAlloc(_System.array2.Length1($o), TInt, $h));

function Tclass._System.array2(Ty) : Ty;

const unique Tagclass._System.array2: TyTag;

// Tclass._System.array2 Tag
axiom (forall _System.array2$arg: Ty :: 
  { Tclass._System.array2(_System.array2$arg) } 
  Tag(Tclass._System.array2(_System.array2$arg)) == Tagclass._System.array2
     && TagFamily(Tclass._System.array2(_System.array2$arg)) == tytagFamily$array2);

// Tclass._System.array2 injectivity 0
axiom (forall _System.array2$arg: Ty :: 
  { Tclass._System.array2(_System.array2$arg) } 
  Tclass._System.array2_0(Tclass._System.array2(_System.array2$arg))
     == _System.array2$arg);

function Tclass._System.array2_0(Ty) : Ty;

// Box/unbox axiom for Tclass._System.array2
axiom (forall _System.array2$arg: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.array2(_System.array2$arg)) } 
  $IsBox(bx, Tclass._System.array2(_System.array2$arg))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._System.array2(_System.array2$arg)));

// _System.array2: subset type $Is
axiom (forall _System.array2$arg: Ty, c#0: ref :: 
  { $Is(c#0, Tclass._System.array2(_System.array2$arg)) } 
  $Is(c#0, Tclass._System.array2(_System.array2$arg))
     <==> $Is(c#0, Tclass._System.array2?(_System.array2$arg)) && c#0 != null);

// _System.array2: subset type $IsAlloc
axiom (forall _System.array2$arg: Ty, c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._System.array2(_System.array2$arg), $h) } 
  $IsAlloc(c#0, Tclass._System.array2(_System.array2$arg), $h)
     <==> $IsAlloc(c#0, Tclass._System.array2?(_System.array2$arg), $h));

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

const unique class._System.array3?: ClassName;

function Tclass._System.array3?(Ty) : Ty;

const unique Tagclass._System.array3?: TyTag;

// Tclass._System.array3? Tag
axiom (forall _System.array3$arg: Ty :: 
  { Tclass._System.array3?(_System.array3$arg) } 
  Tag(Tclass._System.array3?(_System.array3$arg)) == Tagclass._System.array3?
     && TagFamily(Tclass._System.array3?(_System.array3$arg)) == tytagFamily$array3);

// Tclass._System.array3? injectivity 0
axiom (forall _System.array3$arg: Ty :: 
  { Tclass._System.array3?(_System.array3$arg) } 
  Tclass._System.array3?_0(Tclass._System.array3?(_System.array3$arg))
     == _System.array3$arg);

function Tclass._System.array3?_0(Ty) : Ty;

// Box/unbox axiom for Tclass._System.array3?
axiom (forall _System.array3$arg: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.array3?(_System.array3$arg)) } 
  $IsBox(bx, Tclass._System.array3?(_System.array3$arg))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._System.array3?(_System.array3$arg)));

axiom (forall o: ref :: { _System.array3.Length0(o) } 0 <= _System.array3.Length0(o));

axiom (forall o: ref :: { _System.array3.Length1(o) } 0 <= _System.array3.Length1(o));

axiom (forall o: ref :: { _System.array3.Length2(o) } 0 <= _System.array3.Length2(o));

// array3.: Type axiom
axiom (forall _System.array3$arg: Ty, $h: Heap, $o: ref, $i0: int, $i1: int, $i2: int :: 
  { read($h, $o, MultiIndexField(MultiIndexField(IndexField($i0), $i1), $i2)), Tclass._System.array3?(_System.array3$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array3?(_System.array3$arg)
       && 
      0 <= $i0
       && $i0 < _System.array3.Length0($o)
       && 
      0 <= $i1
       && $i1 < _System.array3.Length1($o)
       && 
      0 <= $i2
       && $i2 < _System.array3.Length2($o)
     ==> $IsBox(read($h, $o, MultiIndexField(MultiIndexField(IndexField($i0), $i1), $i2)), 
      _System.array3$arg));

// array3.: Allocation axiom
axiom (forall _System.array3$arg: Ty, $h: Heap, $o: ref, $i0: int, $i1: int, $i2: int :: 
  { read($h, $o, MultiIndexField(MultiIndexField(IndexField($i0), $i1), $i2)), Tclass._System.array3?(_System.array3$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array3?(_System.array3$arg)
       && 
      0 <= $i0
       && $i0 < _System.array3.Length0($o)
       && 
      0 <= $i1
       && $i1 < _System.array3.Length1($o)
       && 
      0 <= $i2
       && $i2 < _System.array3.Length2($o)
       && read($h, $o, alloc)
     ==> $IsAllocBox(read($h, $o, MultiIndexField(MultiIndexField(IndexField($i0), $i1), $i2)), 
      _System.array3$arg, 
      $h));

// array3: Class $Is
axiom (forall _System.array3$arg: Ty, $o: ref :: 
  { $Is($o, Tclass._System.array3?(_System.array3$arg)) } 
  $Is($o, Tclass._System.array3?(_System.array3$arg))
     <==> $o == null || dtype($o) == Tclass._System.array3?(_System.array3$arg));

// array3: Class $IsAlloc
axiom (forall _System.array3$arg: Ty, $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._System.array3?(_System.array3$arg), $h) } 
  $IsAlloc($o, Tclass._System.array3?(_System.array3$arg), $h)
     <==> $o == null || read($h, $o, alloc));

function _System.array3.Length0(ref) : int;

// array3.Length0: Type axiom
axiom (forall _System.array3$arg: Ty, $o: ref :: 
  { _System.array3.Length0($o), Tclass._System.array3?(_System.array3$arg) } 
  $o != null && dtype($o) == Tclass._System.array3?(_System.array3$arg)
     ==> $Is(_System.array3.Length0($o), TInt));

// array3.Length0: Allocation axiom
axiom (forall _System.array3$arg: Ty, $h: Heap, $o: ref :: 
  { _System.array3.Length0($o), read($h, $o, alloc), Tclass._System.array3?(_System.array3$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array3?(_System.array3$arg)
       && read($h, $o, alloc)
     ==> $IsAlloc(_System.array3.Length0($o), TInt, $h));

function _System.array3.Length1(ref) : int;

// array3.Length1: Type axiom
axiom (forall _System.array3$arg: Ty, $o: ref :: 
  { _System.array3.Length1($o), Tclass._System.array3?(_System.array3$arg) } 
  $o != null && dtype($o) == Tclass._System.array3?(_System.array3$arg)
     ==> $Is(_System.array3.Length1($o), TInt));

// array3.Length1: Allocation axiom
axiom (forall _System.array3$arg: Ty, $h: Heap, $o: ref :: 
  { _System.array3.Length1($o), read($h, $o, alloc), Tclass._System.array3?(_System.array3$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array3?(_System.array3$arg)
       && read($h, $o, alloc)
     ==> $IsAlloc(_System.array3.Length1($o), TInt, $h));

function _System.array3.Length2(ref) : int;

// array3.Length2: Type axiom
axiom (forall _System.array3$arg: Ty, $o: ref :: 
  { _System.array3.Length2($o), Tclass._System.array3?(_System.array3$arg) } 
  $o != null && dtype($o) == Tclass._System.array3?(_System.array3$arg)
     ==> $Is(_System.array3.Length2($o), TInt));

// array3.Length2: Allocation axiom
axiom (forall _System.array3$arg: Ty, $h: Heap, $o: ref :: 
  { _System.array3.Length2($o), read($h, $o, alloc), Tclass._System.array3?(_System.array3$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array3?(_System.array3$arg)
       && read($h, $o, alloc)
     ==> $IsAlloc(_System.array3.Length2($o), TInt, $h));

function Tclass._System.array3(Ty) : Ty;

const unique Tagclass._System.array3: TyTag;

// Tclass._System.array3 Tag
axiom (forall _System.array3$arg: Ty :: 
  { Tclass._System.array3(_System.array3$arg) } 
  Tag(Tclass._System.array3(_System.array3$arg)) == Tagclass._System.array3
     && TagFamily(Tclass._System.array3(_System.array3$arg)) == tytagFamily$array3);

// Tclass._System.array3 injectivity 0
axiom (forall _System.array3$arg: Ty :: 
  { Tclass._System.array3(_System.array3$arg) } 
  Tclass._System.array3_0(Tclass._System.array3(_System.array3$arg))
     == _System.array3$arg);

function Tclass._System.array3_0(Ty) : Ty;

// Box/unbox axiom for Tclass._System.array3
axiom (forall _System.array3$arg: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.array3(_System.array3$arg)) } 
  $IsBox(bx, Tclass._System.array3(_System.array3$arg))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._System.array3(_System.array3$arg)));

// _System.array3: subset type $Is
axiom (forall _System.array3$arg: Ty, c#0: ref :: 
  { $Is(c#0, Tclass._System.array3(_System.array3$arg)) } 
  $Is(c#0, Tclass._System.array3(_System.array3$arg))
     <==> $Is(c#0, Tclass._System.array3?(_System.array3$arg)) && c#0 != null);

// _System.array3: subset type $IsAlloc
axiom (forall _System.array3$arg: Ty, c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._System.array3(_System.array3$arg), $h) } 
  $IsAlloc(c#0, Tclass._System.array3(_System.array3$arg), $h)
     <==> $IsAlloc(c#0, Tclass._System.array3?(_System.array3$arg), $h));

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

const unique class._System.array4?: ClassName;

function Tclass._System.array4?(Ty) : Ty;

const unique Tagclass._System.array4?: TyTag;

// Tclass._System.array4? Tag
axiom (forall _System.array4$arg: Ty :: 
  { Tclass._System.array4?(_System.array4$arg) } 
  Tag(Tclass._System.array4?(_System.array4$arg)) == Tagclass._System.array4?
     && TagFamily(Tclass._System.array4?(_System.array4$arg)) == tytagFamily$array4);

// Tclass._System.array4? injectivity 0
axiom (forall _System.array4$arg: Ty :: 
  { Tclass._System.array4?(_System.array4$arg) } 
  Tclass._System.array4?_0(Tclass._System.array4?(_System.array4$arg))
     == _System.array4$arg);

function Tclass._System.array4?_0(Ty) : Ty;

// Box/unbox axiom for Tclass._System.array4?
axiom (forall _System.array4$arg: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.array4?(_System.array4$arg)) } 
  $IsBox(bx, Tclass._System.array4?(_System.array4$arg))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._System.array4?(_System.array4$arg)));

axiom (forall o: ref :: { _System.array4.Length0(o) } 0 <= _System.array4.Length0(o));

axiom (forall o: ref :: { _System.array4.Length1(o) } 0 <= _System.array4.Length1(o));

axiom (forall o: ref :: { _System.array4.Length2(o) } 0 <= _System.array4.Length2(o));

axiom (forall o: ref :: { _System.array4.Length3(o) } 0 <= _System.array4.Length3(o));

// array4.: Type axiom
axiom (forall _System.array4$arg: Ty, 
    $h: Heap, 
    $o: ref, 
    $i0: int, 
    $i1: int, 
    $i2: int, 
    $i3: int :: 
  { read($h, 
      $o, 
      MultiIndexField(MultiIndexField(MultiIndexField(IndexField($i0), $i1), $i2), $i3)), Tclass._System.array4?(_System.array4$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array4?(_System.array4$arg)
       && 
      0 <= $i0
       && $i0 < _System.array4.Length0($o)
       && 
      0 <= $i1
       && $i1 < _System.array4.Length1($o)
       && 
      0 <= $i2
       && $i2 < _System.array4.Length2($o)
       && 
      0 <= $i3
       && $i3 < _System.array4.Length3($o)
     ==> $IsBox(read($h, 
        $o, 
        MultiIndexField(MultiIndexField(MultiIndexField(IndexField($i0), $i1), $i2), $i3)), 
      _System.array4$arg));

// array4.: Allocation axiom
axiom (forall _System.array4$arg: Ty, 
    $h: Heap, 
    $o: ref, 
    $i0: int, 
    $i1: int, 
    $i2: int, 
    $i3: int :: 
  { read($h, 
      $o, 
      MultiIndexField(MultiIndexField(MultiIndexField(IndexField($i0), $i1), $i2), $i3)), Tclass._System.array4?(_System.array4$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array4?(_System.array4$arg)
       && 
      0 <= $i0
       && $i0 < _System.array4.Length0($o)
       && 
      0 <= $i1
       && $i1 < _System.array4.Length1($o)
       && 
      0 <= $i2
       && $i2 < _System.array4.Length2($o)
       && 
      0 <= $i3
       && $i3 < _System.array4.Length3($o)
       && read($h, $o, alloc)
     ==> $IsAllocBox(read($h, 
        $o, 
        MultiIndexField(MultiIndexField(MultiIndexField(IndexField($i0), $i1), $i2), $i3)), 
      _System.array4$arg, 
      $h));

// array4: Class $Is
axiom (forall _System.array4$arg: Ty, $o: ref :: 
  { $Is($o, Tclass._System.array4?(_System.array4$arg)) } 
  $Is($o, Tclass._System.array4?(_System.array4$arg))
     <==> $o == null || dtype($o) == Tclass._System.array4?(_System.array4$arg));

// array4: Class $IsAlloc
axiom (forall _System.array4$arg: Ty, $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._System.array4?(_System.array4$arg), $h) } 
  $IsAlloc($o, Tclass._System.array4?(_System.array4$arg), $h)
     <==> $o == null || read($h, $o, alloc));

function _System.array4.Length0(ref) : int;

// array4.Length0: Type axiom
axiom (forall _System.array4$arg: Ty, $o: ref :: 
  { _System.array4.Length0($o), Tclass._System.array4?(_System.array4$arg) } 
  $o != null && dtype($o) == Tclass._System.array4?(_System.array4$arg)
     ==> $Is(_System.array4.Length0($o), TInt));

// array4.Length0: Allocation axiom
axiom (forall _System.array4$arg: Ty, $h: Heap, $o: ref :: 
  { _System.array4.Length0($o), read($h, $o, alloc), Tclass._System.array4?(_System.array4$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array4?(_System.array4$arg)
       && read($h, $o, alloc)
     ==> $IsAlloc(_System.array4.Length0($o), TInt, $h));

function _System.array4.Length1(ref) : int;

// array4.Length1: Type axiom
axiom (forall _System.array4$arg: Ty, $o: ref :: 
  { _System.array4.Length1($o), Tclass._System.array4?(_System.array4$arg) } 
  $o != null && dtype($o) == Tclass._System.array4?(_System.array4$arg)
     ==> $Is(_System.array4.Length1($o), TInt));

// array4.Length1: Allocation axiom
axiom (forall _System.array4$arg: Ty, $h: Heap, $o: ref :: 
  { _System.array4.Length1($o), read($h, $o, alloc), Tclass._System.array4?(_System.array4$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array4?(_System.array4$arg)
       && read($h, $o, alloc)
     ==> $IsAlloc(_System.array4.Length1($o), TInt, $h));

function _System.array4.Length2(ref) : int;

// array4.Length2: Type axiom
axiom (forall _System.array4$arg: Ty, $o: ref :: 
  { _System.array4.Length2($o), Tclass._System.array4?(_System.array4$arg) } 
  $o != null && dtype($o) == Tclass._System.array4?(_System.array4$arg)
     ==> $Is(_System.array4.Length2($o), TInt));

// array4.Length2: Allocation axiom
axiom (forall _System.array4$arg: Ty, $h: Heap, $o: ref :: 
  { _System.array4.Length2($o), read($h, $o, alloc), Tclass._System.array4?(_System.array4$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array4?(_System.array4$arg)
       && read($h, $o, alloc)
     ==> $IsAlloc(_System.array4.Length2($o), TInt, $h));

function _System.array4.Length3(ref) : int;

// array4.Length3: Type axiom
axiom (forall _System.array4$arg: Ty, $o: ref :: 
  { _System.array4.Length3($o), Tclass._System.array4?(_System.array4$arg) } 
  $o != null && dtype($o) == Tclass._System.array4?(_System.array4$arg)
     ==> $Is(_System.array4.Length3($o), TInt));

// array4.Length3: Allocation axiom
axiom (forall _System.array4$arg: Ty, $h: Heap, $o: ref :: 
  { _System.array4.Length3($o), read($h, $o, alloc), Tclass._System.array4?(_System.array4$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array4?(_System.array4$arg)
       && read($h, $o, alloc)
     ==> $IsAlloc(_System.array4.Length3($o), TInt, $h));

function Tclass._System.array4(Ty) : Ty;

const unique Tagclass._System.array4: TyTag;

// Tclass._System.array4 Tag
axiom (forall _System.array4$arg: Ty :: 
  { Tclass._System.array4(_System.array4$arg) } 
  Tag(Tclass._System.array4(_System.array4$arg)) == Tagclass._System.array4
     && TagFamily(Tclass._System.array4(_System.array4$arg)) == tytagFamily$array4);

// Tclass._System.array4 injectivity 0
axiom (forall _System.array4$arg: Ty :: 
  { Tclass._System.array4(_System.array4$arg) } 
  Tclass._System.array4_0(Tclass._System.array4(_System.array4$arg))
     == _System.array4$arg);

function Tclass._System.array4_0(Ty) : Ty;

// Box/unbox axiom for Tclass._System.array4
axiom (forall _System.array4$arg: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.array4(_System.array4$arg)) } 
  $IsBox(bx, Tclass._System.array4(_System.array4$arg))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._System.array4(_System.array4$arg)));

// _System.array4: subset type $Is
axiom (forall _System.array4$arg: Ty, c#0: ref :: 
  { $Is(c#0, Tclass._System.array4(_System.array4$arg)) } 
  $Is(c#0, Tclass._System.array4(_System.array4$arg))
     <==> $Is(c#0, Tclass._System.array4?(_System.array4$arg)) && c#0 != null);

// _System.array4: subset type $IsAlloc
axiom (forall _System.array4$arg: Ty, c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._System.array4(_System.array4$arg), $h) } 
  $IsAlloc(c#0, Tclass._System.array4(_System.array4$arg), $h)
     <==> $IsAlloc(c#0, Tclass._System.array4?(_System.array4$arg), $h));

function Tclass._System.___hFunc4(Ty, Ty, Ty, Ty, Ty) : Ty;

const unique Tagclass._System.___hFunc4: TyTag;

// Tclass._System.___hFunc4 Tag
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R) } 
  Tag(Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
       == Tagclass._System.___hFunc4
     && TagFamily(Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
       == tytagFamily$_#Func4);

// Tclass._System.___hFunc4 injectivity 0
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R) } 
  Tclass._System.___hFunc4_0(Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     == #$T0);

function Tclass._System.___hFunc4_0(Ty) : Ty;

// Tclass._System.___hFunc4 injectivity 1
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R) } 
  Tclass._System.___hFunc4_1(Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     == #$T1);

function Tclass._System.___hFunc4_1(Ty) : Ty;

// Tclass._System.___hFunc4 injectivity 2
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R) } 
  Tclass._System.___hFunc4_2(Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     == #$T2);

function Tclass._System.___hFunc4_2(Ty) : Ty;

// Tclass._System.___hFunc4 injectivity 3
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R) } 
  Tclass._System.___hFunc4_3(Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     == #$T3);

function Tclass._System.___hFunc4_3(Ty) : Ty;

// Tclass._System.___hFunc4 injectivity 4
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R) } 
  Tclass._System.___hFunc4_4(Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     == #$R);

function Tclass._System.___hFunc4_4(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hFunc4
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R)) } 
  $IsBox(bx, Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R)));

function Handle4([Heap,Box,Box,Box,Box]Box, 
    [Heap,Box,Box,Box,Box]bool, 
    [Heap,Box,Box,Box,Box]Set Box)
   : HandleType;

function Apply4(Ty, Ty, Ty, Ty, Ty, Heap, HandleType, Box, Box, Box, Box) : Box;

function Requires4(Ty, Ty, Ty, Ty, Ty, Heap, HandleType, Box, Box, Box, Box) : bool;

function Reads4(Ty, Ty, Ty, Ty, Ty, Heap, HandleType, Box, Box, Box, Box) : Set Box;

axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    heap: Heap, 
    h: [Heap,Box,Box,Box,Box]Box, 
    r: [Heap,Box,Box,Box,Box]bool, 
    rd: [Heap,Box,Box,Box,Box]Set Box, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box :: 
  { Apply4(t0, t1, t2, t3, t4, heap, Handle4(h, r, rd), bx0, bx1, bx2, bx3) } 
  Apply4(t0, t1, t2, t3, t4, heap, Handle4(h, r, rd), bx0, bx1, bx2, bx3)
     == h[heap, bx0, bx1, bx2, bx3]);

axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    heap: Heap, 
    h: [Heap,Box,Box,Box,Box]Box, 
    r: [Heap,Box,Box,Box,Box]bool, 
    rd: [Heap,Box,Box,Box,Box]Set Box, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box :: 
  { Requires4(t0, t1, t2, t3, t4, heap, Handle4(h, r, rd), bx0, bx1, bx2, bx3) } 
  r[heap, bx0, bx1, bx2, bx3]
     ==> Requires4(t0, t1, t2, t3, t4, heap, Handle4(h, r, rd), bx0, bx1, bx2, bx3));

axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    heap: Heap, 
    h: [Heap,Box,Box,Box,Box]Box, 
    r: [Heap,Box,Box,Box,Box]bool, 
    rd: [Heap,Box,Box,Box,Box]Set Box, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx: Box :: 
  { Reads4(t0, t1, t2, t3, t4, heap, Handle4(h, r, rd), bx0, bx1, bx2, bx3)[bx] } 
  Reads4(t0, t1, t2, t3, t4, heap, Handle4(h, r, rd), bx0, bx1, bx2, bx3)[bx]
     == rd[heap, bx0, bx1, bx2, bx3][bx]);

function {:inline} Requires4#canCall(t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    heap: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box)
   : bool
{
  true
}

function {:inline} Reads4#canCall(t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    heap: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box)
   : bool
{
  true
}

// frame axiom for Reads4
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box :: 
  { $HeapSucc(h0, h1), Reads4(t0, t1, t2, t3, t4, h1, f, bx0, bx1, bx2, bx3) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $Is(f, Tclass._System.___hFunc4(t0, t1, t2, t3, t4))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads4(t0, t1, t2, t3, t4, h0, f, bx0, bx1, bx2, bx3)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads4(t0, t1, t2, t3, t4, h0, f, bx0, bx1, bx2, bx3)
       == Reads4(t0, t1, t2, t3, t4, h1, f, bx0, bx1, bx2, bx3));

// frame axiom for Reads4
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box :: 
  { $HeapSucc(h0, h1), Reads4(t0, t1, t2, t3, t4, h1, f, bx0, bx1, bx2, bx3) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $Is(f, Tclass._System.___hFunc4(t0, t1, t2, t3, t4))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads4(t0, t1, t2, t3, t4, h1, f, bx0, bx1, bx2, bx3)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads4(t0, t1, t2, t3, t4, h0, f, bx0, bx1, bx2, bx3)
       == Reads4(t0, t1, t2, t3, t4, h1, f, bx0, bx1, bx2, bx3));

// frame axiom for Requires4
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box :: 
  { $HeapSucc(h0, h1), Requires4(t0, t1, t2, t3, t4, h1, f, bx0, bx1, bx2, bx3) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $Is(f, Tclass._System.___hFunc4(t0, t1, t2, t3, t4))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads4(t0, t1, t2, t3, t4, h0, f, bx0, bx1, bx2, bx3)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires4(t0, t1, t2, t3, t4, h0, f, bx0, bx1, bx2, bx3)
       == Requires4(t0, t1, t2, t3, t4, h1, f, bx0, bx1, bx2, bx3));

// frame axiom for Requires4
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box :: 
  { $HeapSucc(h0, h1), Requires4(t0, t1, t2, t3, t4, h1, f, bx0, bx1, bx2, bx3) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $Is(f, Tclass._System.___hFunc4(t0, t1, t2, t3, t4))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads4(t0, t1, t2, t3, t4, h1, f, bx0, bx1, bx2, bx3)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires4(t0, t1, t2, t3, t4, h0, f, bx0, bx1, bx2, bx3)
       == Requires4(t0, t1, t2, t3, t4, h1, f, bx0, bx1, bx2, bx3));

// frame axiom for Apply4
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box :: 
  { $HeapSucc(h0, h1), Apply4(t0, t1, t2, t3, t4, h1, f, bx0, bx1, bx2, bx3) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $Is(f, Tclass._System.___hFunc4(t0, t1, t2, t3, t4))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads4(t0, t1, t2, t3, t4, h0, f, bx0, bx1, bx2, bx3)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply4(t0, t1, t2, t3, t4, h0, f, bx0, bx1, bx2, bx3)
       == Apply4(t0, t1, t2, t3, t4, h1, f, bx0, bx1, bx2, bx3));

// frame axiom for Apply4
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box :: 
  { $HeapSucc(h0, h1), Apply4(t0, t1, t2, t3, t4, h1, f, bx0, bx1, bx2, bx3) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $Is(f, Tclass._System.___hFunc4(t0, t1, t2, t3, t4))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads4(t0, t1, t2, t3, t4, h1, f, bx0, bx1, bx2, bx3)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply4(t0, t1, t2, t3, t4, h0, f, bx0, bx1, bx2, bx3)
       == Apply4(t0, t1, t2, t3, t4, h1, f, bx0, bx1, bx2, bx3));

// empty-reads property for Reads4 
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    heap: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box :: 
  { Reads4(t0, t1, t2, t3, t4, $OneHeap, f, bx0, bx1, bx2, bx3), $IsGoodHeap(heap) } 
    { Reads4(t0, t1, t2, t3, t4, heap, f, bx0, bx1, bx2, bx3) } 
  $IsGoodHeap(heap)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $Is(f, Tclass._System.___hFunc4(t0, t1, t2, t3, t4))
     ==> (Set#Equal(Reads4(t0, t1, t2, t3, t4, $OneHeap, f, bx0, bx1, bx2, bx3), 
        Set#Empty(): Set Box)
       <==> Set#Equal(Reads4(t0, t1, t2, t3, t4, heap, f, bx0, bx1, bx2, bx3), Set#Empty(): Set Box)));

// empty-reads property for Requires4
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    heap: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box :: 
  { Requires4(t0, t1, t2, t3, t4, $OneHeap, f, bx0, bx1, bx2, bx3), $IsGoodHeap(heap) } 
    { Requires4(t0, t1, t2, t3, t4, heap, f, bx0, bx1, bx2, bx3) } 
  $IsGoodHeap(heap)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $Is(f, Tclass._System.___hFunc4(t0, t1, t2, t3, t4))
       && Set#Equal(Reads4(t0, t1, t2, t3, t4, $OneHeap, f, bx0, bx1, bx2, bx3), 
        Set#Empty(): Set Box)
     ==> Requires4(t0, t1, t2, t3, t4, $OneHeap, f, bx0, bx1, bx2, bx3)
       == Requires4(t0, t1, t2, t3, t4, heap, f, bx0, bx1, bx2, bx3));

axiom (forall f: HandleType, t0: Ty, t1: Ty, t2: Ty, t3: Ty, t4: Ty :: 
  { $Is(f, Tclass._System.___hFunc4(t0, t1, t2, t3, t4)) } 
  $Is(f, Tclass._System.___hFunc4(t0, t1, t2, t3, t4))
     <==> (forall h: Heap, bx0: Box, bx1: Box, bx2: Box, bx3: Box :: 
      { Apply4(t0, t1, t2, t3, t4, h, f, bx0, bx1, bx2, bx3) } 
      $IsGoodHeap(h)
           && 
          $IsBox(bx0, t0)
           && $IsBox(bx1, t1)
           && $IsBox(bx2, t2)
           && $IsBox(bx3, t3)
           && Requires4(t0, t1, t2, t3, t4, h, f, bx0, bx1, bx2, bx3)
         ==> $IsBox(Apply4(t0, t1, t2, t3, t4, h, f, bx0, bx1, bx2, bx3), t4)));

axiom (forall f: HandleType, 
    t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    u0: Ty, 
    u1: Ty, 
    u2: Ty, 
    u3: Ty, 
    u4: Ty :: 
  { $Is(f, Tclass._System.___hFunc4(t0, t1, t2, t3, t4)), $Is(f, Tclass._System.___hFunc4(u0, u1, u2, u3, u4)) } 
  $Is(f, Tclass._System.___hFunc4(t0, t1, t2, t3, t4))
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
        { $IsBox(bx, u3) } { $IsBox(bx, t3) } 
        $IsBox(bx, u3) ==> $IsBox(bx, t3))
       && (forall bx: Box :: 
        { $IsBox(bx, t4) } { $IsBox(bx, u4) } 
        $IsBox(bx, t4) ==> $IsBox(bx, u4))
     ==> $Is(f, Tclass._System.___hFunc4(u0, u1, u2, u3, u4)));

axiom (forall f: HandleType, t0: Ty, t1: Ty, t2: Ty, t3: Ty, t4: Ty, h: Heap :: 
  { $IsAlloc(f, Tclass._System.___hFunc4(t0, t1, t2, t3, t4), h) } 
  $IsGoodHeap(h)
     ==> ($IsAlloc(f, Tclass._System.___hFunc4(t0, t1, t2, t3, t4), h)
       <==> (forall bx0: Box, bx1: Box, bx2: Box, bx3: Box :: 
        { Apply4(t0, t1, t2, t3, t4, h, f, bx0, bx1, bx2, bx3) } 
          { Reads4(t0, t1, t2, t3, t4, h, f, bx0, bx1, bx2, bx3) } 
        $IsBox(bx0, t0)
             && $IsAllocBox(bx0, t0, h)
             && 
            $IsBox(bx1, t1)
             && $IsAllocBox(bx1, t1, h)
             && 
            $IsBox(bx2, t2)
             && $IsAllocBox(bx2, t2, h)
             && 
            $IsBox(bx3, t3)
             && $IsAllocBox(bx3, t3, h)
             && Requires4(t0, t1, t2, t3, t4, h, f, bx0, bx1, bx2, bx3)
           ==> (forall r: ref :: 
            { Reads4(t0, t1, t2, t3, t4, h, f, bx0, bx1, bx2, bx3)[$Box(r)] } 
            r != null && Reads4(t0, t1, t2, t3, t4, h, f, bx0, bx1, bx2, bx3)[$Box(r)]
               ==> read(h, r, alloc)))));

axiom (forall f: HandleType, t0: Ty, t1: Ty, t2: Ty, t3: Ty, t4: Ty, h: Heap :: 
  { $IsAlloc(f, Tclass._System.___hFunc4(t0, t1, t2, t3, t4), h) } 
  $IsGoodHeap(h) && $IsAlloc(f, Tclass._System.___hFunc4(t0, t1, t2, t3, t4), h)
     ==> (forall bx0: Box, bx1: Box, bx2: Box, bx3: Box :: 
      { Apply4(t0, t1, t2, t3, t4, h, f, bx0, bx1, bx2, bx3) } 
      $IsAllocBox(bx0, t0, h)
           && $IsAllocBox(bx1, t1, h)
           && $IsAllocBox(bx2, t2, h)
           && $IsAllocBox(bx3, t3, h)
           && Requires4(t0, t1, t2, t3, t4, h, f, bx0, bx1, bx2, bx3)
         ==> $IsAllocBox(Apply4(t0, t1, t2, t3, t4, h, f, bx0, bx1, bx2, bx3), t4, h)));

function Tclass._System.___hPartialFunc4(Ty, Ty, Ty, Ty, Ty) : Ty;

const unique Tagclass._System.___hPartialFunc4: TyTag;

// Tclass._System.___hPartialFunc4 Tag
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R) } 
  Tag(Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
       == Tagclass._System.___hPartialFunc4
     && TagFamily(Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
       == tytagFamily$_#PartialFunc4);

// Tclass._System.___hPartialFunc4 injectivity 0
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R) } 
  Tclass._System.___hPartialFunc4_0(Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     == #$T0);

function Tclass._System.___hPartialFunc4_0(Ty) : Ty;

// Tclass._System.___hPartialFunc4 injectivity 1
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R) } 
  Tclass._System.___hPartialFunc4_1(Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     == #$T1);

function Tclass._System.___hPartialFunc4_1(Ty) : Ty;

// Tclass._System.___hPartialFunc4 injectivity 2
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R) } 
  Tclass._System.___hPartialFunc4_2(Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     == #$T2);

function Tclass._System.___hPartialFunc4_2(Ty) : Ty;

// Tclass._System.___hPartialFunc4 injectivity 3
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R) } 
  Tclass._System.___hPartialFunc4_3(Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     == #$T3);

function Tclass._System.___hPartialFunc4_3(Ty) : Ty;

// Tclass._System.___hPartialFunc4 injectivity 4
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R) } 
  Tclass._System.___hPartialFunc4_4(Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     == #$R);

function Tclass._System.___hPartialFunc4_4(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hPartialFunc4
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R)) } 
  $IsBox(bx, Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, 
        Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R)));

// _System._#PartialFunc4: subset type $Is
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty, f#0: HandleType :: 
  { $Is(f#0, Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R)) } 
  $Is(f#0, Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     <==> $Is(f#0, Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
       && (forall x0#0: Box, x1#0: Box, x2#0: Box, x3#0: Box :: 
        $IsBox(x0#0, #$T0)
             && $IsBox(x1#0, #$T1)
             && $IsBox(x2#0, #$T2)
             && $IsBox(x3#0, #$T3)
           ==> Set#Equal(Reads4(#$T0, #$T1, #$T2, #$T3, #$R, $OneHeap, f#0, x0#0, x1#0, x2#0, x3#0), 
            Set#Empty(): Set Box)));

// _System._#PartialFunc4: subset type $IsAlloc
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty, f#0: HandleType, $h: Heap :: 
  { $IsAlloc(f#0, Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R), $h) } 
  $IsAlloc(f#0, Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R), $h));

function Tclass._System.___hTotalFunc4(Ty, Ty, Ty, Ty, Ty) : Ty;

const unique Tagclass._System.___hTotalFunc4: TyTag;

// Tclass._System.___hTotalFunc4 Tag
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R) } 
  Tag(Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
       == Tagclass._System.___hTotalFunc4
     && TagFamily(Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
       == tytagFamily$_#TotalFunc4);

// Tclass._System.___hTotalFunc4 injectivity 0
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R) } 
  Tclass._System.___hTotalFunc4_0(Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     == #$T0);

function Tclass._System.___hTotalFunc4_0(Ty) : Ty;

// Tclass._System.___hTotalFunc4 injectivity 1
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R) } 
  Tclass._System.___hTotalFunc4_1(Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     == #$T1);

function Tclass._System.___hTotalFunc4_1(Ty) : Ty;

// Tclass._System.___hTotalFunc4 injectivity 2
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R) } 
  Tclass._System.___hTotalFunc4_2(Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     == #$T2);

function Tclass._System.___hTotalFunc4_2(Ty) : Ty;

// Tclass._System.___hTotalFunc4 injectivity 3
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R) } 
  Tclass._System.___hTotalFunc4_3(Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     == #$T3);

function Tclass._System.___hTotalFunc4_3(Ty) : Ty;

// Tclass._System.___hTotalFunc4 injectivity 4
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R) } 
  Tclass._System.___hTotalFunc4_4(Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     == #$R);

function Tclass._System.___hTotalFunc4_4(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hTotalFunc4
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R)) } 
  $IsBox(bx, Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, 
        Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R)));

// _System._#TotalFunc4: subset type $Is
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty, f#0: HandleType :: 
  { $Is(f#0, Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R)) } 
  $Is(f#0, Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     <==> $Is(f#0, Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
       && (forall x0#0: Box, x1#0: Box, x2#0: Box, x3#0: Box :: 
        $IsBox(x0#0, #$T0)
             && $IsBox(x1#0, #$T1)
             && $IsBox(x2#0, #$T2)
             && $IsBox(x3#0, #$T3)
           ==> Requires4(#$T0, #$T1, #$T2, #$T3, #$R, $OneHeap, f#0, x0#0, x1#0, x2#0, x3#0)));

// _System._#TotalFunc4: subset type $IsAlloc
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty, f#0: HandleType, $h: Heap :: 
  { $IsAlloc(f#0, Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R), $h) } 
  $IsAlloc(f#0, Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R), $h));

const unique class._System.array15?: ClassName;

function Tclass._System.array15?(Ty) : Ty;

const unique Tagclass._System.array15?: TyTag;

// Tclass._System.array15? Tag
axiom (forall _System.array15$arg: Ty :: 
  { Tclass._System.array15?(_System.array15$arg) } 
  Tag(Tclass._System.array15?(_System.array15$arg)) == Tagclass._System.array15?
     && TagFamily(Tclass._System.array15?(_System.array15$arg)) == tytagFamily$array15);

// Tclass._System.array15? injectivity 0
axiom (forall _System.array15$arg: Ty :: 
  { Tclass._System.array15?(_System.array15$arg) } 
  Tclass._System.array15?_0(Tclass._System.array15?(_System.array15$arg))
     == _System.array15$arg);

function Tclass._System.array15?_0(Ty) : Ty;

// Box/unbox axiom for Tclass._System.array15?
axiom (forall _System.array15$arg: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.array15?(_System.array15$arg)) } 
  $IsBox(bx, Tclass._System.array15?(_System.array15$arg))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._System.array15?(_System.array15$arg)));

axiom (forall o: ref :: 
  { _System.array15.Length0(o) } 
  0 <= _System.array15.Length0(o));

axiom (forall o: ref :: 
  { _System.array15.Length1(o) } 
  0 <= _System.array15.Length1(o));

axiom (forall o: ref :: 
  { _System.array15.Length2(o) } 
  0 <= _System.array15.Length2(o));

axiom (forall o: ref :: 
  { _System.array15.Length3(o) } 
  0 <= _System.array15.Length3(o));

axiom (forall o: ref :: 
  { _System.array15.Length4(o) } 
  0 <= _System.array15.Length4(o));

axiom (forall o: ref :: 
  { _System.array15.Length5(o) } 
  0 <= _System.array15.Length5(o));

axiom (forall o: ref :: 
  { _System.array15.Length6(o) } 
  0 <= _System.array15.Length6(o));

axiom (forall o: ref :: 
  { _System.array15.Length7(o) } 
  0 <= _System.array15.Length7(o));

axiom (forall o: ref :: 
  { _System.array15.Length8(o) } 
  0 <= _System.array15.Length8(o));

axiom (forall o: ref :: 
  { _System.array15.Length9(o) } 
  0 <= _System.array15.Length9(o));

axiom (forall o: ref :: 
  { _System.array15.Length10(o) } 
  0 <= _System.array15.Length10(o));

axiom (forall o: ref :: 
  { _System.array15.Length11(o) } 
  0 <= _System.array15.Length11(o));

axiom (forall o: ref :: 
  { _System.array15.Length12(o) } 
  0 <= _System.array15.Length12(o));

axiom (forall o: ref :: 
  { _System.array15.Length13(o) } 
  0 <= _System.array15.Length13(o));

axiom (forall o: ref :: 
  { _System.array15.Length14(o) } 
  0 <= _System.array15.Length14(o));

// array15.: Type axiom
axiom (forall _System.array15$arg: Ty, 
    $h: Heap, 
    $o: ref, 
    $i0: int, 
    $i1: int, 
    $i2: int, 
    $i3: int, 
    $i4: int, 
    $i5: int, 
    $i6: int, 
    $i7: int, 
    $i8: int, 
    $i9: int, 
    $i10: int, 
    $i11: int, 
    $i12: int, 
    $i13: int, 
    $i14: int :: 
  { read($h, 
      $o, 
      MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(IndexField($i0), $i1), $i2), $i3), 
                            $i4), 
                          $i5), 
                        $i6), 
                      $i7), 
                    $i8), 
                  $i9), 
                $i10), 
              $i11), 
            $i12), 
          $i13), 
        $i14)), Tclass._System.array15?(_System.array15$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array15?(_System.array15$arg)
       && 
      0 <= $i0
       && $i0 < _System.array15.Length0($o)
       && 
      0 <= $i1
       && $i1 < _System.array15.Length1($o)
       && 
      0 <= $i2
       && $i2 < _System.array15.Length2($o)
       && 
      0 <= $i3
       && $i3 < _System.array15.Length3($o)
       && 
      0 <= $i4
       && $i4 < _System.array15.Length4($o)
       && 
      0 <= $i5
       && $i5 < _System.array15.Length5($o)
       && 
      0 <= $i6
       && $i6 < _System.array15.Length6($o)
       && 
      0 <= $i7
       && $i7 < _System.array15.Length7($o)
       && 
      0 <= $i8
       && $i8 < _System.array15.Length8($o)
       && 
      0 <= $i9
       && $i9 < _System.array15.Length9($o)
       && 
      0 <= $i10
       && $i10 < _System.array15.Length10($o)
       && 
      0 <= $i11
       && $i11 < _System.array15.Length11($o)
       && 
      0 <= $i12
       && $i12 < _System.array15.Length12($o)
       && 
      0 <= $i13
       && $i13 < _System.array15.Length13($o)
       && 
      0 <= $i14
       && $i14 < _System.array15.Length14($o)
     ==> $IsBox(read($h, 
        $o, 
        MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(IndexField($i0), $i1), $i2), $i3), 
                              $i4), 
                            $i5), 
                          $i6), 
                        $i7), 
                      $i8), 
                    $i9), 
                  $i10), 
                $i11), 
              $i12), 
            $i13), 
          $i14)), 
      _System.array15$arg));

// array15.: Allocation axiom
axiom (forall _System.array15$arg: Ty, 
    $h: Heap, 
    $o: ref, 
    $i0: int, 
    $i1: int, 
    $i2: int, 
    $i3: int, 
    $i4: int, 
    $i5: int, 
    $i6: int, 
    $i7: int, 
    $i8: int, 
    $i9: int, 
    $i10: int, 
    $i11: int, 
    $i12: int, 
    $i13: int, 
    $i14: int :: 
  { read($h, 
      $o, 
      MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(IndexField($i0), $i1), $i2), $i3), 
                            $i4), 
                          $i5), 
                        $i6), 
                      $i7), 
                    $i8), 
                  $i9), 
                $i10), 
              $i11), 
            $i12), 
          $i13), 
        $i14)), Tclass._System.array15?(_System.array15$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array15?(_System.array15$arg)
       && 
      0 <= $i0
       && $i0 < _System.array15.Length0($o)
       && 
      0 <= $i1
       && $i1 < _System.array15.Length1($o)
       && 
      0 <= $i2
       && $i2 < _System.array15.Length2($o)
       && 
      0 <= $i3
       && $i3 < _System.array15.Length3($o)
       && 
      0 <= $i4
       && $i4 < _System.array15.Length4($o)
       && 
      0 <= $i5
       && $i5 < _System.array15.Length5($o)
       && 
      0 <= $i6
       && $i6 < _System.array15.Length6($o)
       && 
      0 <= $i7
       && $i7 < _System.array15.Length7($o)
       && 
      0 <= $i8
       && $i8 < _System.array15.Length8($o)
       && 
      0 <= $i9
       && $i9 < _System.array15.Length9($o)
       && 
      0 <= $i10
       && $i10 < _System.array15.Length10($o)
       && 
      0 <= $i11
       && $i11 < _System.array15.Length11($o)
       && 
      0 <= $i12
       && $i12 < _System.array15.Length12($o)
       && 
      0 <= $i13
       && $i13 < _System.array15.Length13($o)
       && 
      0 <= $i14
       && $i14 < _System.array15.Length14($o)
       && read($h, $o, alloc)
     ==> $IsAllocBox(read($h, 
        $o, 
        MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(IndexField($i0), $i1), $i2), $i3), 
                              $i4), 
                            $i5), 
                          $i6), 
                        $i7), 
                      $i8), 
                    $i9), 
                  $i10), 
                $i11), 
              $i12), 
            $i13), 
          $i14)), 
      _System.array15$arg, 
      $h));

// array15: Class $Is
axiom (forall _System.array15$arg: Ty, $o: ref :: 
  { $Is($o, Tclass._System.array15?(_System.array15$arg)) } 
  $Is($o, Tclass._System.array15?(_System.array15$arg))
     <==> $o == null || dtype($o) == Tclass._System.array15?(_System.array15$arg));

// array15: Class $IsAlloc
axiom (forall _System.array15$arg: Ty, $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._System.array15?(_System.array15$arg), $h) } 
  $IsAlloc($o, Tclass._System.array15?(_System.array15$arg), $h)
     <==> $o == null || read($h, $o, alloc));

function _System.array15.Length0(ref) : int;

// array15.Length0: Type axiom
axiom (forall _System.array15$arg: Ty, $o: ref :: 
  { _System.array15.Length0($o), Tclass._System.array15?(_System.array15$arg) } 
  $o != null && dtype($o) == Tclass._System.array15?(_System.array15$arg)
     ==> $Is(_System.array15.Length0($o), TInt));

// array15.Length0: Allocation axiom
axiom (forall _System.array15$arg: Ty, $h: Heap, $o: ref :: 
  { _System.array15.Length0($o), read($h, $o, alloc), Tclass._System.array15?(_System.array15$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array15?(_System.array15$arg)
       && read($h, $o, alloc)
     ==> $IsAlloc(_System.array15.Length0($o), TInt, $h));

function _System.array15.Length1(ref) : int;

// array15.Length1: Type axiom
axiom (forall _System.array15$arg: Ty, $o: ref :: 
  { _System.array15.Length1($o), Tclass._System.array15?(_System.array15$arg) } 
  $o != null && dtype($o) == Tclass._System.array15?(_System.array15$arg)
     ==> $Is(_System.array15.Length1($o), TInt));

// array15.Length1: Allocation axiom
axiom (forall _System.array15$arg: Ty, $h: Heap, $o: ref :: 
  { _System.array15.Length1($o), read($h, $o, alloc), Tclass._System.array15?(_System.array15$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array15?(_System.array15$arg)
       && read($h, $o, alloc)
     ==> $IsAlloc(_System.array15.Length1($o), TInt, $h));

function _System.array15.Length2(ref) : int;

// array15.Length2: Type axiom
axiom (forall _System.array15$arg: Ty, $o: ref :: 
  { _System.array15.Length2($o), Tclass._System.array15?(_System.array15$arg) } 
  $o != null && dtype($o) == Tclass._System.array15?(_System.array15$arg)
     ==> $Is(_System.array15.Length2($o), TInt));

// array15.Length2: Allocation axiom
axiom (forall _System.array15$arg: Ty, $h: Heap, $o: ref :: 
  { _System.array15.Length2($o), read($h, $o, alloc), Tclass._System.array15?(_System.array15$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array15?(_System.array15$arg)
       && read($h, $o, alloc)
     ==> $IsAlloc(_System.array15.Length2($o), TInt, $h));

function _System.array15.Length3(ref) : int;

// array15.Length3: Type axiom
axiom (forall _System.array15$arg: Ty, $o: ref :: 
  { _System.array15.Length3($o), Tclass._System.array15?(_System.array15$arg) } 
  $o != null && dtype($o) == Tclass._System.array15?(_System.array15$arg)
     ==> $Is(_System.array15.Length3($o), TInt));

// array15.Length3: Allocation axiom
axiom (forall _System.array15$arg: Ty, $h: Heap, $o: ref :: 
  { _System.array15.Length3($o), read($h, $o, alloc), Tclass._System.array15?(_System.array15$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array15?(_System.array15$arg)
       && read($h, $o, alloc)
     ==> $IsAlloc(_System.array15.Length3($o), TInt, $h));

function _System.array15.Length4(ref) : int;

// array15.Length4: Type axiom
axiom (forall _System.array15$arg: Ty, $o: ref :: 
  { _System.array15.Length4($o), Tclass._System.array15?(_System.array15$arg) } 
  $o != null && dtype($o) == Tclass._System.array15?(_System.array15$arg)
     ==> $Is(_System.array15.Length4($o), TInt));

// array15.Length4: Allocation axiom
axiom (forall _System.array15$arg: Ty, $h: Heap, $o: ref :: 
  { _System.array15.Length4($o), read($h, $o, alloc), Tclass._System.array15?(_System.array15$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array15?(_System.array15$arg)
       && read($h, $o, alloc)
     ==> $IsAlloc(_System.array15.Length4($o), TInt, $h));

function _System.array15.Length5(ref) : int;

// array15.Length5: Type axiom
axiom (forall _System.array15$arg: Ty, $o: ref :: 
  { _System.array15.Length5($o), Tclass._System.array15?(_System.array15$arg) } 
  $o != null && dtype($o) == Tclass._System.array15?(_System.array15$arg)
     ==> $Is(_System.array15.Length5($o), TInt));

// array15.Length5: Allocation axiom
axiom (forall _System.array15$arg: Ty, $h: Heap, $o: ref :: 
  { _System.array15.Length5($o), read($h, $o, alloc), Tclass._System.array15?(_System.array15$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array15?(_System.array15$arg)
       && read($h, $o, alloc)
     ==> $IsAlloc(_System.array15.Length5($o), TInt, $h));

function _System.array15.Length6(ref) : int;

// array15.Length6: Type axiom
axiom (forall _System.array15$arg: Ty, $o: ref :: 
  { _System.array15.Length6($o), Tclass._System.array15?(_System.array15$arg) } 
  $o != null && dtype($o) == Tclass._System.array15?(_System.array15$arg)
     ==> $Is(_System.array15.Length6($o), TInt));

// array15.Length6: Allocation axiom
axiom (forall _System.array15$arg: Ty, $h: Heap, $o: ref :: 
  { _System.array15.Length6($o), read($h, $o, alloc), Tclass._System.array15?(_System.array15$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array15?(_System.array15$arg)
       && read($h, $o, alloc)
     ==> $IsAlloc(_System.array15.Length6($o), TInt, $h));

function _System.array15.Length7(ref) : int;

// array15.Length7: Type axiom
axiom (forall _System.array15$arg: Ty, $o: ref :: 
  { _System.array15.Length7($o), Tclass._System.array15?(_System.array15$arg) } 
  $o != null && dtype($o) == Tclass._System.array15?(_System.array15$arg)
     ==> $Is(_System.array15.Length7($o), TInt));

// array15.Length7: Allocation axiom
axiom (forall _System.array15$arg: Ty, $h: Heap, $o: ref :: 
  { _System.array15.Length7($o), read($h, $o, alloc), Tclass._System.array15?(_System.array15$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array15?(_System.array15$arg)
       && read($h, $o, alloc)
     ==> $IsAlloc(_System.array15.Length7($o), TInt, $h));

function _System.array15.Length8(ref) : int;

// array15.Length8: Type axiom
axiom (forall _System.array15$arg: Ty, $o: ref :: 
  { _System.array15.Length8($o), Tclass._System.array15?(_System.array15$arg) } 
  $o != null && dtype($o) == Tclass._System.array15?(_System.array15$arg)
     ==> $Is(_System.array15.Length8($o), TInt));

// array15.Length8: Allocation axiom
axiom (forall _System.array15$arg: Ty, $h: Heap, $o: ref :: 
  { _System.array15.Length8($o), read($h, $o, alloc), Tclass._System.array15?(_System.array15$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array15?(_System.array15$arg)
       && read($h, $o, alloc)
     ==> $IsAlloc(_System.array15.Length8($o), TInt, $h));

function _System.array15.Length9(ref) : int;

// array15.Length9: Type axiom
axiom (forall _System.array15$arg: Ty, $o: ref :: 
  { _System.array15.Length9($o), Tclass._System.array15?(_System.array15$arg) } 
  $o != null && dtype($o) == Tclass._System.array15?(_System.array15$arg)
     ==> $Is(_System.array15.Length9($o), TInt));

// array15.Length9: Allocation axiom
axiom (forall _System.array15$arg: Ty, $h: Heap, $o: ref :: 
  { _System.array15.Length9($o), read($h, $o, alloc), Tclass._System.array15?(_System.array15$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array15?(_System.array15$arg)
       && read($h, $o, alloc)
     ==> $IsAlloc(_System.array15.Length9($o), TInt, $h));

function _System.array15.Length10(ref) : int;

// array15.Length10: Type axiom
axiom (forall _System.array15$arg: Ty, $o: ref :: 
  { _System.array15.Length10($o), Tclass._System.array15?(_System.array15$arg) } 
  $o != null && dtype($o) == Tclass._System.array15?(_System.array15$arg)
     ==> $Is(_System.array15.Length10($o), TInt));

// array15.Length10: Allocation axiom
axiom (forall _System.array15$arg: Ty, $h: Heap, $o: ref :: 
  { _System.array15.Length10($o), read($h, $o, alloc), Tclass._System.array15?(_System.array15$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array15?(_System.array15$arg)
       && read($h, $o, alloc)
     ==> $IsAlloc(_System.array15.Length10($o), TInt, $h));

function _System.array15.Length11(ref) : int;

// array15.Length11: Type axiom
axiom (forall _System.array15$arg: Ty, $o: ref :: 
  { _System.array15.Length11($o), Tclass._System.array15?(_System.array15$arg) } 
  $o != null && dtype($o) == Tclass._System.array15?(_System.array15$arg)
     ==> $Is(_System.array15.Length11($o), TInt));

// array15.Length11: Allocation axiom
axiom (forall _System.array15$arg: Ty, $h: Heap, $o: ref :: 
  { _System.array15.Length11($o), read($h, $o, alloc), Tclass._System.array15?(_System.array15$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array15?(_System.array15$arg)
       && read($h, $o, alloc)
     ==> $IsAlloc(_System.array15.Length11($o), TInt, $h));

function _System.array15.Length12(ref) : int;

// array15.Length12: Type axiom
axiom (forall _System.array15$arg: Ty, $o: ref :: 
  { _System.array15.Length12($o), Tclass._System.array15?(_System.array15$arg) } 
  $o != null && dtype($o) == Tclass._System.array15?(_System.array15$arg)
     ==> $Is(_System.array15.Length12($o), TInt));

// array15.Length12: Allocation axiom
axiom (forall _System.array15$arg: Ty, $h: Heap, $o: ref :: 
  { _System.array15.Length12($o), read($h, $o, alloc), Tclass._System.array15?(_System.array15$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array15?(_System.array15$arg)
       && read($h, $o, alloc)
     ==> $IsAlloc(_System.array15.Length12($o), TInt, $h));

function _System.array15.Length13(ref) : int;

// array15.Length13: Type axiom
axiom (forall _System.array15$arg: Ty, $o: ref :: 
  { _System.array15.Length13($o), Tclass._System.array15?(_System.array15$arg) } 
  $o != null && dtype($o) == Tclass._System.array15?(_System.array15$arg)
     ==> $Is(_System.array15.Length13($o), TInt));

// array15.Length13: Allocation axiom
axiom (forall _System.array15$arg: Ty, $h: Heap, $o: ref :: 
  { _System.array15.Length13($o), read($h, $o, alloc), Tclass._System.array15?(_System.array15$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array15?(_System.array15$arg)
       && read($h, $o, alloc)
     ==> $IsAlloc(_System.array15.Length13($o), TInt, $h));

function _System.array15.Length14(ref) : int;

// array15.Length14: Type axiom
axiom (forall _System.array15$arg: Ty, $o: ref :: 
  { _System.array15.Length14($o), Tclass._System.array15?(_System.array15$arg) } 
  $o != null && dtype($o) == Tclass._System.array15?(_System.array15$arg)
     ==> $Is(_System.array15.Length14($o), TInt));

// array15.Length14: Allocation axiom
axiom (forall _System.array15$arg: Ty, $h: Heap, $o: ref :: 
  { _System.array15.Length14($o), read($h, $o, alloc), Tclass._System.array15?(_System.array15$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array15?(_System.array15$arg)
       && read($h, $o, alloc)
     ==> $IsAlloc(_System.array15.Length14($o), TInt, $h));

function Tclass._System.array15(Ty) : Ty;

const unique Tagclass._System.array15: TyTag;

// Tclass._System.array15 Tag
axiom (forall _System.array15$arg: Ty :: 
  { Tclass._System.array15(_System.array15$arg) } 
  Tag(Tclass._System.array15(_System.array15$arg)) == Tagclass._System.array15
     && TagFamily(Tclass._System.array15(_System.array15$arg)) == tytagFamily$array15);

// Tclass._System.array15 injectivity 0
axiom (forall _System.array15$arg: Ty :: 
  { Tclass._System.array15(_System.array15$arg) } 
  Tclass._System.array15_0(Tclass._System.array15(_System.array15$arg))
     == _System.array15$arg);

function Tclass._System.array15_0(Ty) : Ty;

// Box/unbox axiom for Tclass._System.array15
axiom (forall _System.array15$arg: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.array15(_System.array15$arg)) } 
  $IsBox(bx, Tclass._System.array15(_System.array15$arg))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._System.array15(_System.array15$arg)));

// _System.array15: subset type $Is
axiom (forall _System.array15$arg: Ty, c#0: ref :: 
  { $Is(c#0, Tclass._System.array15(_System.array15$arg)) } 
  $Is(c#0, Tclass._System.array15(_System.array15$arg))
     <==> $Is(c#0, Tclass._System.array15?(_System.array15$arg)) && c#0 != null);

// _System.array15: subset type $IsAlloc
axiom (forall _System.array15$arg: Ty, c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._System.array15(_System.array15$arg), $h) } 
  $IsAlloc(c#0, Tclass._System.array15(_System.array15$arg), $h)
     <==> $IsAlloc(c#0, Tclass._System.array15?(_System.array15$arg), $h));

function Tclass._System.___hFunc15(Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty) : Ty;

const unique Tagclass._System.___hFunc15: TyTag;

// Tclass._System.___hFunc15 Tag
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hFunc15(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$R) } 
  Tag(Tclass._System.___hFunc15(#$T0, 
          #$T1, 
          #$T2, 
          #$T3, 
          #$T4, 
          #$T5, 
          #$T6, 
          #$T7, 
          #$T8, 
          #$T9, 
          #$T10, 
          #$T11, 
          #$T12, 
          #$T13, 
          #$T14, 
          #$R))
       == Tagclass._System.___hFunc15
     && TagFamily(Tclass._System.___hFunc15(#$T0, 
          #$T1, 
          #$T2, 
          #$T3, 
          #$T4, 
          #$T5, 
          #$T6, 
          #$T7, 
          #$T8, 
          #$T9, 
          #$T10, 
          #$T11, 
          #$T12, 
          #$T13, 
          #$T14, 
          #$R))
       == tytagFamily$_#Func15);

// Tclass._System.___hFunc15 injectivity 0
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hFunc15(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$R) } 
  Tclass._System.___hFunc15_0(Tclass._System.___hFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     == #$T0);

function Tclass._System.___hFunc15_0(Ty) : Ty;

// Tclass._System.___hFunc15 injectivity 1
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hFunc15(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$R) } 
  Tclass._System.___hFunc15_1(Tclass._System.___hFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     == #$T1);

function Tclass._System.___hFunc15_1(Ty) : Ty;

// Tclass._System.___hFunc15 injectivity 2
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hFunc15(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$R) } 
  Tclass._System.___hFunc15_2(Tclass._System.___hFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     == #$T2);

function Tclass._System.___hFunc15_2(Ty) : Ty;

// Tclass._System.___hFunc15 injectivity 3
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hFunc15(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$R) } 
  Tclass._System.___hFunc15_3(Tclass._System.___hFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     == #$T3);

function Tclass._System.___hFunc15_3(Ty) : Ty;

// Tclass._System.___hFunc15 injectivity 4
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hFunc15(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$R) } 
  Tclass._System.___hFunc15_4(Tclass._System.___hFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     == #$T4);

function Tclass._System.___hFunc15_4(Ty) : Ty;

// Tclass._System.___hFunc15 injectivity 5
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hFunc15(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$R) } 
  Tclass._System.___hFunc15_5(Tclass._System.___hFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     == #$T5);

function Tclass._System.___hFunc15_5(Ty) : Ty;

// Tclass._System.___hFunc15 injectivity 6
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hFunc15(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$R) } 
  Tclass._System.___hFunc15_6(Tclass._System.___hFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     == #$T6);

function Tclass._System.___hFunc15_6(Ty) : Ty;

// Tclass._System.___hFunc15 injectivity 7
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hFunc15(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$R) } 
  Tclass._System.___hFunc15_7(Tclass._System.___hFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     == #$T7);

function Tclass._System.___hFunc15_7(Ty) : Ty;

// Tclass._System.___hFunc15 injectivity 8
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hFunc15(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$R) } 
  Tclass._System.___hFunc15_8(Tclass._System.___hFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     == #$T8);

function Tclass._System.___hFunc15_8(Ty) : Ty;

// Tclass._System.___hFunc15 injectivity 9
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hFunc15(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$R) } 
  Tclass._System.___hFunc15_9(Tclass._System.___hFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     == #$T9);

function Tclass._System.___hFunc15_9(Ty) : Ty;

// Tclass._System.___hFunc15 injectivity 10
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hFunc15(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$R) } 
  Tclass._System.___hFunc15_10(Tclass._System.___hFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     == #$T10);

function Tclass._System.___hFunc15_10(Ty) : Ty;

// Tclass._System.___hFunc15 injectivity 11
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hFunc15(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$R) } 
  Tclass._System.___hFunc15_11(Tclass._System.___hFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     == #$T11);

function Tclass._System.___hFunc15_11(Ty) : Ty;

// Tclass._System.___hFunc15 injectivity 12
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hFunc15(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$R) } 
  Tclass._System.___hFunc15_12(Tclass._System.___hFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     == #$T12);

function Tclass._System.___hFunc15_12(Ty) : Ty;

// Tclass._System.___hFunc15 injectivity 13
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hFunc15(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$R) } 
  Tclass._System.___hFunc15_13(Tclass._System.___hFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     == #$T13);

function Tclass._System.___hFunc15_13(Ty) : Ty;

// Tclass._System.___hFunc15 injectivity 14
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hFunc15(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$R) } 
  Tclass._System.___hFunc15_14(Tclass._System.___hFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     == #$T14);

function Tclass._System.___hFunc15_14(Ty) : Ty;

// Tclass._System.___hFunc15 injectivity 15
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hFunc15(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$R) } 
  Tclass._System.___hFunc15_15(Tclass._System.___hFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     == #$R);

function Tclass._System.___hFunc15_15(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hFunc15
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty, 
    bx: Box :: 
  { $IsBox(bx, 
      Tclass._System.___hFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R)) } 
  $IsBox(bx, 
      Tclass._System.___hFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, 
        Tclass._System.___hFunc15(#$T0, 
          #$T1, 
          #$T2, 
          #$T3, 
          #$T4, 
          #$T5, 
          #$T6, 
          #$T7, 
          #$T8, 
          #$T9, 
          #$T10, 
          #$T11, 
          #$T12, 
          #$T13, 
          #$T14, 
          #$R)));

function Handle15([Heap,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box]Box, 
    [Heap,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box]bool, 
    [Heap,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box]Set Box)
   : HandleType;

function Apply15(Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Heap, 
    HandleType, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box)
   : Box;

function Requires15(Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Heap, 
    HandleType, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box)
   : bool;

function Reads15(Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Heap, 
    HandleType, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box)
   : Set Box;

axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    t6: Ty, 
    t7: Ty, 
    t8: Ty, 
    t9: Ty, 
    t10: Ty, 
    t11: Ty, 
    t12: Ty, 
    t13: Ty, 
    t14: Ty, 
    t15: Ty, 
    heap: Heap, 
    h: [Heap,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box]Box, 
    r: [Heap,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box]bool, 
    rd: [Heap,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box]Set Box, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box, 
    bx5: Box, 
    bx6: Box, 
    bx7: Box, 
    bx8: Box, 
    bx9: Box, 
    bx10: Box, 
    bx11: Box, 
    bx12: Box, 
    bx13: Box, 
    bx14: Box :: 
  { Apply15(t0, 
      t1, 
      t2, 
      t3, 
      t4, 
      t5, 
      t6, 
      t7, 
      t8, 
      t9, 
      t10, 
      t11, 
      t12, 
      t13, 
      t14, 
      t15, 
      heap, 
      Handle15(h, r, rd), 
      bx0, 
      bx1, 
      bx2, 
      bx3, 
      bx4, 
      bx5, 
      bx6, 
      bx7, 
      bx8, 
      bx9, 
      bx10, 
      bx11, 
      bx12, 
      bx13, 
      bx14) } 
  Apply15(t0, 
      t1, 
      t2, 
      t3, 
      t4, 
      t5, 
      t6, 
      t7, 
      t8, 
      t9, 
      t10, 
      t11, 
      t12, 
      t13, 
      t14, 
      t15, 
      heap, 
      Handle15(h, r, rd), 
      bx0, 
      bx1, 
      bx2, 
      bx3, 
      bx4, 
      bx5, 
      bx6, 
      bx7, 
      bx8, 
      bx9, 
      bx10, 
      bx11, 
      bx12, 
      bx13, 
      bx14)
     == h[heap, bx0, bx1, bx2, bx3, bx4, bx5, bx6, bx7, bx8, bx9, bx10, bx11, bx12, bx13, bx14]);

axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    t6: Ty, 
    t7: Ty, 
    t8: Ty, 
    t9: Ty, 
    t10: Ty, 
    t11: Ty, 
    t12: Ty, 
    t13: Ty, 
    t14: Ty, 
    t15: Ty, 
    heap: Heap, 
    h: [Heap,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box]Box, 
    r: [Heap,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box]bool, 
    rd: [Heap,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box]Set Box, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box, 
    bx5: Box, 
    bx6: Box, 
    bx7: Box, 
    bx8: Box, 
    bx9: Box, 
    bx10: Box, 
    bx11: Box, 
    bx12: Box, 
    bx13: Box, 
    bx14: Box :: 
  { Requires15(t0, 
      t1, 
      t2, 
      t3, 
      t4, 
      t5, 
      t6, 
      t7, 
      t8, 
      t9, 
      t10, 
      t11, 
      t12, 
      t13, 
      t14, 
      t15, 
      heap, 
      Handle15(h, r, rd), 
      bx0, 
      bx1, 
      bx2, 
      bx3, 
      bx4, 
      bx5, 
      bx6, 
      bx7, 
      bx8, 
      bx9, 
      bx10, 
      bx11, 
      bx12, 
      bx13, 
      bx14) } 
  r[heap, bx0, bx1, bx2, bx3, bx4, bx5, bx6, bx7, bx8, bx9, bx10, bx11, bx12, bx13, bx14]
     ==> Requires15(t0, 
      t1, 
      t2, 
      t3, 
      t4, 
      t5, 
      t6, 
      t7, 
      t8, 
      t9, 
      t10, 
      t11, 
      t12, 
      t13, 
      t14, 
      t15, 
      heap, 
      Handle15(h, r, rd), 
      bx0, 
      bx1, 
      bx2, 
      bx3, 
      bx4, 
      bx5, 
      bx6, 
      bx7, 
      bx8, 
      bx9, 
      bx10, 
      bx11, 
      bx12, 
      bx13, 
      bx14));

axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    t6: Ty, 
    t7: Ty, 
    t8: Ty, 
    t9: Ty, 
    t10: Ty, 
    t11: Ty, 
    t12: Ty, 
    t13: Ty, 
    t14: Ty, 
    t15: Ty, 
    heap: Heap, 
    h: [Heap,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box]Box, 
    r: [Heap,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box]bool, 
    rd: [Heap,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box]Set Box, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box, 
    bx5: Box, 
    bx6: Box, 
    bx7: Box, 
    bx8: Box, 
    bx9: Box, 
    bx10: Box, 
    bx11: Box, 
    bx12: Box, 
    bx13: Box, 
    bx14: Box, 
    bx: Box :: 
  { Reads15(t0, 
      t1, 
      t2, 
      t3, 
      t4, 
      t5, 
      t6, 
      t7, 
      t8, 
      t9, 
      t10, 
      t11, 
      t12, 
      t13, 
      t14, 
      t15, 
      heap, 
      Handle15(h, r, rd), 
      bx0, 
      bx1, 
      bx2, 
      bx3, 
      bx4, 
      bx5, 
      bx6, 
      bx7, 
      bx8, 
      bx9, 
      bx10, 
      bx11, 
      bx12, 
      bx13, 
      bx14)[bx] } 
  Reads15(t0, 
      t1, 
      t2, 
      t3, 
      t4, 
      t5, 
      t6, 
      t7, 
      t8, 
      t9, 
      t10, 
      t11, 
      t12, 
      t13, 
      t14, 
      t15, 
      heap, 
      Handle15(h, r, rd), 
      bx0, 
      bx1, 
      bx2, 
      bx3, 
      bx4, 
      bx5, 
      bx6, 
      bx7, 
      bx8, 
      bx9, 
      bx10, 
      bx11, 
      bx12, 
      bx13, 
      bx14)[bx]
     == rd[heap, bx0, bx1, bx2, bx3, bx4, bx5, bx6, bx7, bx8, bx9, bx10, bx11, bx12, bx13, bx14][bx]);

function {:inline} Requires15#canCall(t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    t6: Ty, 
    t7: Ty, 
    t8: Ty, 
    t9: Ty, 
    t10: Ty, 
    t11: Ty, 
    t12: Ty, 
    t13: Ty, 
    t14: Ty, 
    t15: Ty, 
    heap: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box, 
    bx5: Box, 
    bx6: Box, 
    bx7: Box, 
    bx8: Box, 
    bx9: Box, 
    bx10: Box, 
    bx11: Box, 
    bx12: Box, 
    bx13: Box, 
    bx14: Box)
   : bool
{
  true
}

function {:inline} Reads15#canCall(t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    t6: Ty, 
    t7: Ty, 
    t8: Ty, 
    t9: Ty, 
    t10: Ty, 
    t11: Ty, 
    t12: Ty, 
    t13: Ty, 
    t14: Ty, 
    t15: Ty, 
    heap: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box, 
    bx5: Box, 
    bx6: Box, 
    bx7: Box, 
    bx8: Box, 
    bx9: Box, 
    bx10: Box, 
    bx11: Box, 
    bx12: Box, 
    bx13: Box, 
    bx14: Box)
   : bool
{
  true
}

// frame axiom for Reads15
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    t6: Ty, 
    t7: Ty, 
    t8: Ty, 
    t9: Ty, 
    t10: Ty, 
    t11: Ty, 
    t12: Ty, 
    t13: Ty, 
    t14: Ty, 
    t15: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box, 
    bx5: Box, 
    bx6: Box, 
    bx7: Box, 
    bx8: Box, 
    bx9: Box, 
    bx10: Box, 
    bx11: Box, 
    bx12: Box, 
    bx13: Box, 
    bx14: Box :: 
  { $HeapSucc(h0, h1), Reads15(t0, 
      t1, 
      t2, 
      t3, 
      t4, 
      t5, 
      t6, 
      t7, 
      t8, 
      t9, 
      t10, 
      t11, 
      t12, 
      t13, 
      t14, 
      t15, 
      h1, 
      f, 
      bx0, 
      bx1, 
      bx2, 
      bx3, 
      bx4, 
      bx5, 
      bx6, 
      bx7, 
      bx8, 
      bx9, 
      bx10, 
      bx11, 
      bx12, 
      bx13, 
      bx14) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $IsBox(bx4, t4)
       && $IsBox(bx5, t5)
       && $IsBox(bx6, t6)
       && $IsBox(bx7, t7)
       && $IsBox(bx8, t8)
       && $IsBox(bx9, t9)
       && $IsBox(bx10, t10)
       && $IsBox(bx11, t11)
       && $IsBox(bx12, t12)
       && $IsBox(bx13, t13)
       && $IsBox(bx14, t14)
       && $Is(f, 
        Tclass._System.___hFunc15(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15))
       && (forall<a> o: ref, fld: Field a :: 
        o != null
             && Reads15(t0, 
              t1, 
              t2, 
              t3, 
              t4, 
              t5, 
              t6, 
              t7, 
              t8, 
              t9, 
              t10, 
              t11, 
              t12, 
              t13, 
              t14, 
              t15, 
              h0, 
              f, 
              bx0, 
              bx1, 
              bx2, 
              bx3, 
              bx4, 
              bx5, 
              bx6, 
              bx7, 
              bx8, 
              bx9, 
              bx10, 
              bx11, 
              bx12, 
              bx13, 
              bx14)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads15(t0, 
        t1, 
        t2, 
        t3, 
        t4, 
        t5, 
        t6, 
        t7, 
        t8, 
        t9, 
        t10, 
        t11, 
        t12, 
        t13, 
        t14, 
        t15, 
        h0, 
        f, 
        bx0, 
        bx1, 
        bx2, 
        bx3, 
        bx4, 
        bx5, 
        bx6, 
        bx7, 
        bx8, 
        bx9, 
        bx10, 
        bx11, 
        bx12, 
        bx13, 
        bx14)
       == Reads15(t0, 
        t1, 
        t2, 
        t3, 
        t4, 
        t5, 
        t6, 
        t7, 
        t8, 
        t9, 
        t10, 
        t11, 
        t12, 
        t13, 
        t14, 
        t15, 
        h1, 
        f, 
        bx0, 
        bx1, 
        bx2, 
        bx3, 
        bx4, 
        bx5, 
        bx6, 
        bx7, 
        bx8, 
        bx9, 
        bx10, 
        bx11, 
        bx12, 
        bx13, 
        bx14));

// frame axiom for Reads15
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    t6: Ty, 
    t7: Ty, 
    t8: Ty, 
    t9: Ty, 
    t10: Ty, 
    t11: Ty, 
    t12: Ty, 
    t13: Ty, 
    t14: Ty, 
    t15: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box, 
    bx5: Box, 
    bx6: Box, 
    bx7: Box, 
    bx8: Box, 
    bx9: Box, 
    bx10: Box, 
    bx11: Box, 
    bx12: Box, 
    bx13: Box, 
    bx14: Box :: 
  { $HeapSucc(h0, h1), Reads15(t0, 
      t1, 
      t2, 
      t3, 
      t4, 
      t5, 
      t6, 
      t7, 
      t8, 
      t9, 
      t10, 
      t11, 
      t12, 
      t13, 
      t14, 
      t15, 
      h1, 
      f, 
      bx0, 
      bx1, 
      bx2, 
      bx3, 
      bx4, 
      bx5, 
      bx6, 
      bx7, 
      bx8, 
      bx9, 
      bx10, 
      bx11, 
      bx12, 
      bx13, 
      bx14) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $IsBox(bx4, t4)
       && $IsBox(bx5, t5)
       && $IsBox(bx6, t6)
       && $IsBox(bx7, t7)
       && $IsBox(bx8, t8)
       && $IsBox(bx9, t9)
       && $IsBox(bx10, t10)
       && $IsBox(bx11, t11)
       && $IsBox(bx12, t12)
       && $IsBox(bx13, t13)
       && $IsBox(bx14, t14)
       && $Is(f, 
        Tclass._System.___hFunc15(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15))
       && (forall<a> o: ref, fld: Field a :: 
        o != null
             && Reads15(t0, 
              t1, 
              t2, 
              t3, 
              t4, 
              t5, 
              t6, 
              t7, 
              t8, 
              t9, 
              t10, 
              t11, 
              t12, 
              t13, 
              t14, 
              t15, 
              h1, 
              f, 
              bx0, 
              bx1, 
              bx2, 
              bx3, 
              bx4, 
              bx5, 
              bx6, 
              bx7, 
              bx8, 
              bx9, 
              bx10, 
              bx11, 
              bx12, 
              bx13, 
              bx14)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads15(t0, 
        t1, 
        t2, 
        t3, 
        t4, 
        t5, 
        t6, 
        t7, 
        t8, 
        t9, 
        t10, 
        t11, 
        t12, 
        t13, 
        t14, 
        t15, 
        h0, 
        f, 
        bx0, 
        bx1, 
        bx2, 
        bx3, 
        bx4, 
        bx5, 
        bx6, 
        bx7, 
        bx8, 
        bx9, 
        bx10, 
        bx11, 
        bx12, 
        bx13, 
        bx14)
       == Reads15(t0, 
        t1, 
        t2, 
        t3, 
        t4, 
        t5, 
        t6, 
        t7, 
        t8, 
        t9, 
        t10, 
        t11, 
        t12, 
        t13, 
        t14, 
        t15, 
        h1, 
        f, 
        bx0, 
        bx1, 
        bx2, 
        bx3, 
        bx4, 
        bx5, 
        bx6, 
        bx7, 
        bx8, 
        bx9, 
        bx10, 
        bx11, 
        bx12, 
        bx13, 
        bx14));

// frame axiom for Requires15
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    t6: Ty, 
    t7: Ty, 
    t8: Ty, 
    t9: Ty, 
    t10: Ty, 
    t11: Ty, 
    t12: Ty, 
    t13: Ty, 
    t14: Ty, 
    t15: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box, 
    bx5: Box, 
    bx6: Box, 
    bx7: Box, 
    bx8: Box, 
    bx9: Box, 
    bx10: Box, 
    bx11: Box, 
    bx12: Box, 
    bx13: Box, 
    bx14: Box :: 
  { $HeapSucc(h0, h1), Requires15(t0, 
      t1, 
      t2, 
      t3, 
      t4, 
      t5, 
      t6, 
      t7, 
      t8, 
      t9, 
      t10, 
      t11, 
      t12, 
      t13, 
      t14, 
      t15, 
      h1, 
      f, 
      bx0, 
      bx1, 
      bx2, 
      bx3, 
      bx4, 
      bx5, 
      bx6, 
      bx7, 
      bx8, 
      bx9, 
      bx10, 
      bx11, 
      bx12, 
      bx13, 
      bx14) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $IsBox(bx4, t4)
       && $IsBox(bx5, t5)
       && $IsBox(bx6, t6)
       && $IsBox(bx7, t7)
       && $IsBox(bx8, t8)
       && $IsBox(bx9, t9)
       && $IsBox(bx10, t10)
       && $IsBox(bx11, t11)
       && $IsBox(bx12, t12)
       && $IsBox(bx13, t13)
       && $IsBox(bx14, t14)
       && $Is(f, 
        Tclass._System.___hFunc15(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15))
       && (forall<a> o: ref, fld: Field a :: 
        o != null
             && Reads15(t0, 
              t1, 
              t2, 
              t3, 
              t4, 
              t5, 
              t6, 
              t7, 
              t8, 
              t9, 
              t10, 
              t11, 
              t12, 
              t13, 
              t14, 
              t15, 
              h0, 
              f, 
              bx0, 
              bx1, 
              bx2, 
              bx3, 
              bx4, 
              bx5, 
              bx6, 
              bx7, 
              bx8, 
              bx9, 
              bx10, 
              bx11, 
              bx12, 
              bx13, 
              bx14)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires15(t0, 
        t1, 
        t2, 
        t3, 
        t4, 
        t5, 
        t6, 
        t7, 
        t8, 
        t9, 
        t10, 
        t11, 
        t12, 
        t13, 
        t14, 
        t15, 
        h0, 
        f, 
        bx0, 
        bx1, 
        bx2, 
        bx3, 
        bx4, 
        bx5, 
        bx6, 
        bx7, 
        bx8, 
        bx9, 
        bx10, 
        bx11, 
        bx12, 
        bx13, 
        bx14)
       == Requires15(t0, 
        t1, 
        t2, 
        t3, 
        t4, 
        t5, 
        t6, 
        t7, 
        t8, 
        t9, 
        t10, 
        t11, 
        t12, 
        t13, 
        t14, 
        t15, 
        h1, 
        f, 
        bx0, 
        bx1, 
        bx2, 
        bx3, 
        bx4, 
        bx5, 
        bx6, 
        bx7, 
        bx8, 
        bx9, 
        bx10, 
        bx11, 
        bx12, 
        bx13, 
        bx14));

// frame axiom for Requires15
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    t6: Ty, 
    t7: Ty, 
    t8: Ty, 
    t9: Ty, 
    t10: Ty, 
    t11: Ty, 
    t12: Ty, 
    t13: Ty, 
    t14: Ty, 
    t15: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box, 
    bx5: Box, 
    bx6: Box, 
    bx7: Box, 
    bx8: Box, 
    bx9: Box, 
    bx10: Box, 
    bx11: Box, 
    bx12: Box, 
    bx13: Box, 
    bx14: Box :: 
  { $HeapSucc(h0, h1), Requires15(t0, 
      t1, 
      t2, 
      t3, 
      t4, 
      t5, 
      t6, 
      t7, 
      t8, 
      t9, 
      t10, 
      t11, 
      t12, 
      t13, 
      t14, 
      t15, 
      h1, 
      f, 
      bx0, 
      bx1, 
      bx2, 
      bx3, 
      bx4, 
      bx5, 
      bx6, 
      bx7, 
      bx8, 
      bx9, 
      bx10, 
      bx11, 
      bx12, 
      bx13, 
      bx14) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $IsBox(bx4, t4)
       && $IsBox(bx5, t5)
       && $IsBox(bx6, t6)
       && $IsBox(bx7, t7)
       && $IsBox(bx8, t8)
       && $IsBox(bx9, t9)
       && $IsBox(bx10, t10)
       && $IsBox(bx11, t11)
       && $IsBox(bx12, t12)
       && $IsBox(bx13, t13)
       && $IsBox(bx14, t14)
       && $Is(f, 
        Tclass._System.___hFunc15(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15))
       && (forall<a> o: ref, fld: Field a :: 
        o != null
             && Reads15(t0, 
              t1, 
              t2, 
              t3, 
              t4, 
              t5, 
              t6, 
              t7, 
              t8, 
              t9, 
              t10, 
              t11, 
              t12, 
              t13, 
              t14, 
              t15, 
              h1, 
              f, 
              bx0, 
              bx1, 
              bx2, 
              bx3, 
              bx4, 
              bx5, 
              bx6, 
              bx7, 
              bx8, 
              bx9, 
              bx10, 
              bx11, 
              bx12, 
              bx13, 
              bx14)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires15(t0, 
        t1, 
        t2, 
        t3, 
        t4, 
        t5, 
        t6, 
        t7, 
        t8, 
        t9, 
        t10, 
        t11, 
        t12, 
        t13, 
        t14, 
        t15, 
        h0, 
        f, 
        bx0, 
        bx1, 
        bx2, 
        bx3, 
        bx4, 
        bx5, 
        bx6, 
        bx7, 
        bx8, 
        bx9, 
        bx10, 
        bx11, 
        bx12, 
        bx13, 
        bx14)
       == Requires15(t0, 
        t1, 
        t2, 
        t3, 
        t4, 
        t5, 
        t6, 
        t7, 
        t8, 
        t9, 
        t10, 
        t11, 
        t12, 
        t13, 
        t14, 
        t15, 
        h1, 
        f, 
        bx0, 
        bx1, 
        bx2, 
        bx3, 
        bx4, 
        bx5, 
        bx6, 
        bx7, 
        bx8, 
        bx9, 
        bx10, 
        bx11, 
        bx12, 
        bx13, 
        bx14));

// frame axiom for Apply15
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    t6: Ty, 
    t7: Ty, 
    t8: Ty, 
    t9: Ty, 
    t10: Ty, 
    t11: Ty, 
    t12: Ty, 
    t13: Ty, 
    t14: Ty, 
    t15: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box, 
    bx5: Box, 
    bx6: Box, 
    bx7: Box, 
    bx8: Box, 
    bx9: Box, 
    bx10: Box, 
    bx11: Box, 
    bx12: Box, 
    bx13: Box, 
    bx14: Box :: 
  { $HeapSucc(h0, h1), Apply15(t0, 
      t1, 
      t2, 
      t3, 
      t4, 
      t5, 
      t6, 
      t7, 
      t8, 
      t9, 
      t10, 
      t11, 
      t12, 
      t13, 
      t14, 
      t15, 
      h1, 
      f, 
      bx0, 
      bx1, 
      bx2, 
      bx3, 
      bx4, 
      bx5, 
      bx6, 
      bx7, 
      bx8, 
      bx9, 
      bx10, 
      bx11, 
      bx12, 
      bx13, 
      bx14) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $IsBox(bx4, t4)
       && $IsBox(bx5, t5)
       && $IsBox(bx6, t6)
       && $IsBox(bx7, t7)
       && $IsBox(bx8, t8)
       && $IsBox(bx9, t9)
       && $IsBox(bx10, t10)
       && $IsBox(bx11, t11)
       && $IsBox(bx12, t12)
       && $IsBox(bx13, t13)
       && $IsBox(bx14, t14)
       && $Is(f, 
        Tclass._System.___hFunc15(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15))
       && (forall<a> o: ref, fld: Field a :: 
        o != null
             && Reads15(t0, 
              t1, 
              t2, 
              t3, 
              t4, 
              t5, 
              t6, 
              t7, 
              t8, 
              t9, 
              t10, 
              t11, 
              t12, 
              t13, 
              t14, 
              t15, 
              h0, 
              f, 
              bx0, 
              bx1, 
              bx2, 
              bx3, 
              bx4, 
              bx5, 
              bx6, 
              bx7, 
              bx8, 
              bx9, 
              bx10, 
              bx11, 
              bx12, 
              bx13, 
              bx14)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply15(t0, 
        t1, 
        t2, 
        t3, 
        t4, 
        t5, 
        t6, 
        t7, 
        t8, 
        t9, 
        t10, 
        t11, 
        t12, 
        t13, 
        t14, 
        t15, 
        h0, 
        f, 
        bx0, 
        bx1, 
        bx2, 
        bx3, 
        bx4, 
        bx5, 
        bx6, 
        bx7, 
        bx8, 
        bx9, 
        bx10, 
        bx11, 
        bx12, 
        bx13, 
        bx14)
       == Apply15(t0, 
        t1, 
        t2, 
        t3, 
        t4, 
        t5, 
        t6, 
        t7, 
        t8, 
        t9, 
        t10, 
        t11, 
        t12, 
        t13, 
        t14, 
        t15, 
        h1, 
        f, 
        bx0, 
        bx1, 
        bx2, 
        bx3, 
        bx4, 
        bx5, 
        bx6, 
        bx7, 
        bx8, 
        bx9, 
        bx10, 
        bx11, 
        bx12, 
        bx13, 
        bx14));

// frame axiom for Apply15
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    t6: Ty, 
    t7: Ty, 
    t8: Ty, 
    t9: Ty, 
    t10: Ty, 
    t11: Ty, 
    t12: Ty, 
    t13: Ty, 
    t14: Ty, 
    t15: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box, 
    bx5: Box, 
    bx6: Box, 
    bx7: Box, 
    bx8: Box, 
    bx9: Box, 
    bx10: Box, 
    bx11: Box, 
    bx12: Box, 
    bx13: Box, 
    bx14: Box :: 
  { $HeapSucc(h0, h1), Apply15(t0, 
      t1, 
      t2, 
      t3, 
      t4, 
      t5, 
      t6, 
      t7, 
      t8, 
      t9, 
      t10, 
      t11, 
      t12, 
      t13, 
      t14, 
      t15, 
      h1, 
      f, 
      bx0, 
      bx1, 
      bx2, 
      bx3, 
      bx4, 
      bx5, 
      bx6, 
      bx7, 
      bx8, 
      bx9, 
      bx10, 
      bx11, 
      bx12, 
      bx13, 
      bx14) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $IsBox(bx4, t4)
       && $IsBox(bx5, t5)
       && $IsBox(bx6, t6)
       && $IsBox(bx7, t7)
       && $IsBox(bx8, t8)
       && $IsBox(bx9, t9)
       && $IsBox(bx10, t10)
       && $IsBox(bx11, t11)
       && $IsBox(bx12, t12)
       && $IsBox(bx13, t13)
       && $IsBox(bx14, t14)
       && $Is(f, 
        Tclass._System.___hFunc15(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15))
       && (forall<a> o: ref, fld: Field a :: 
        o != null
             && Reads15(t0, 
              t1, 
              t2, 
              t3, 
              t4, 
              t5, 
              t6, 
              t7, 
              t8, 
              t9, 
              t10, 
              t11, 
              t12, 
              t13, 
              t14, 
              t15, 
              h1, 
              f, 
              bx0, 
              bx1, 
              bx2, 
              bx3, 
              bx4, 
              bx5, 
              bx6, 
              bx7, 
              bx8, 
              bx9, 
              bx10, 
              bx11, 
              bx12, 
              bx13, 
              bx14)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply15(t0, 
        t1, 
        t2, 
        t3, 
        t4, 
        t5, 
        t6, 
        t7, 
        t8, 
        t9, 
        t10, 
        t11, 
        t12, 
        t13, 
        t14, 
        t15, 
        h0, 
        f, 
        bx0, 
        bx1, 
        bx2, 
        bx3, 
        bx4, 
        bx5, 
        bx6, 
        bx7, 
        bx8, 
        bx9, 
        bx10, 
        bx11, 
        bx12, 
        bx13, 
        bx14)
       == Apply15(t0, 
        t1, 
        t2, 
        t3, 
        t4, 
        t5, 
        t6, 
        t7, 
        t8, 
        t9, 
        t10, 
        t11, 
        t12, 
        t13, 
        t14, 
        t15, 
        h1, 
        f, 
        bx0, 
        bx1, 
        bx2, 
        bx3, 
        bx4, 
        bx5, 
        bx6, 
        bx7, 
        bx8, 
        bx9, 
        bx10, 
        bx11, 
        bx12, 
        bx13, 
        bx14));

// empty-reads property for Reads15 
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    t6: Ty, 
    t7: Ty, 
    t8: Ty, 
    t9: Ty, 
    t10: Ty, 
    t11: Ty, 
    t12: Ty, 
    t13: Ty, 
    t14: Ty, 
    t15: Ty, 
    heap: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box, 
    bx5: Box, 
    bx6: Box, 
    bx7: Box, 
    bx8: Box, 
    bx9: Box, 
    bx10: Box, 
    bx11: Box, 
    bx12: Box, 
    bx13: Box, 
    bx14: Box :: 
  { Reads15(t0, 
      t1, 
      t2, 
      t3, 
      t4, 
      t5, 
      t6, 
      t7, 
      t8, 
      t9, 
      t10, 
      t11, 
      t12, 
      t13, 
      t14, 
      t15, 
      $OneHeap, 
      f, 
      bx0, 
      bx1, 
      bx2, 
      bx3, 
      bx4, 
      bx5, 
      bx6, 
      bx7, 
      bx8, 
      bx9, 
      bx10, 
      bx11, 
      bx12, 
      bx13, 
      bx14), $IsGoodHeap(heap) } 
    { Reads15(t0, 
      t1, 
      t2, 
      t3, 
      t4, 
      t5, 
      t6, 
      t7, 
      t8, 
      t9, 
      t10, 
      t11, 
      t12, 
      t13, 
      t14, 
      t15, 
      heap, 
      f, 
      bx0, 
      bx1, 
      bx2, 
      bx3, 
      bx4, 
      bx5, 
      bx6, 
      bx7, 
      bx8, 
      bx9, 
      bx10, 
      bx11, 
      bx12, 
      bx13, 
      bx14) } 
  $IsGoodHeap(heap)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $IsBox(bx4, t4)
       && $IsBox(bx5, t5)
       && $IsBox(bx6, t6)
       && $IsBox(bx7, t7)
       && $IsBox(bx8, t8)
       && $IsBox(bx9, t9)
       && $IsBox(bx10, t10)
       && $IsBox(bx11, t11)
       && $IsBox(bx12, t12)
       && $IsBox(bx13, t13)
       && $IsBox(bx14, t14)
       && $Is(f, 
        Tclass._System.___hFunc15(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15))
     ==> (Set#Equal(Reads15(t0, 
          t1, 
          t2, 
          t3, 
          t4, 
          t5, 
          t6, 
          t7, 
          t8, 
          t9, 
          t10, 
          t11, 
          t12, 
          t13, 
          t14, 
          t15, 
          $OneHeap, 
          f, 
          bx0, 
          bx1, 
          bx2, 
          bx3, 
          bx4, 
          bx5, 
          bx6, 
          bx7, 
          bx8, 
          bx9, 
          bx10, 
          bx11, 
          bx12, 
          bx13, 
          bx14), 
        Set#Empty(): Set Box)
       <==> Set#Equal(Reads15(t0, 
          t1, 
          t2, 
          t3, 
          t4, 
          t5, 
          t6, 
          t7, 
          t8, 
          t9, 
          t10, 
          t11, 
          t12, 
          t13, 
          t14, 
          t15, 
          heap, 
          f, 
          bx0, 
          bx1, 
          bx2, 
          bx3, 
          bx4, 
          bx5, 
          bx6, 
          bx7, 
          bx8, 
          bx9, 
          bx10, 
          bx11, 
          bx12, 
          bx13, 
          bx14), 
        Set#Empty(): Set Box)));

// empty-reads property for Requires15
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    t6: Ty, 
    t7: Ty, 
    t8: Ty, 
    t9: Ty, 
    t10: Ty, 
    t11: Ty, 
    t12: Ty, 
    t13: Ty, 
    t14: Ty, 
    t15: Ty, 
    heap: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box, 
    bx5: Box, 
    bx6: Box, 
    bx7: Box, 
    bx8: Box, 
    bx9: Box, 
    bx10: Box, 
    bx11: Box, 
    bx12: Box, 
    bx13: Box, 
    bx14: Box :: 
  { Requires15(t0, 
      t1, 
      t2, 
      t3, 
      t4, 
      t5, 
      t6, 
      t7, 
      t8, 
      t9, 
      t10, 
      t11, 
      t12, 
      t13, 
      t14, 
      t15, 
      $OneHeap, 
      f, 
      bx0, 
      bx1, 
      bx2, 
      bx3, 
      bx4, 
      bx5, 
      bx6, 
      bx7, 
      bx8, 
      bx9, 
      bx10, 
      bx11, 
      bx12, 
      bx13, 
      bx14), $IsGoodHeap(heap) } 
    { Requires15(t0, 
      t1, 
      t2, 
      t3, 
      t4, 
      t5, 
      t6, 
      t7, 
      t8, 
      t9, 
      t10, 
      t11, 
      t12, 
      t13, 
      t14, 
      t15, 
      heap, 
      f, 
      bx0, 
      bx1, 
      bx2, 
      bx3, 
      bx4, 
      bx5, 
      bx6, 
      bx7, 
      bx8, 
      bx9, 
      bx10, 
      bx11, 
      bx12, 
      bx13, 
      bx14) } 
  $IsGoodHeap(heap)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $IsBox(bx4, t4)
       && $IsBox(bx5, t5)
       && $IsBox(bx6, t6)
       && $IsBox(bx7, t7)
       && $IsBox(bx8, t8)
       && $IsBox(bx9, t9)
       && $IsBox(bx10, t10)
       && $IsBox(bx11, t11)
       && $IsBox(bx12, t12)
       && $IsBox(bx13, t13)
       && $IsBox(bx14, t14)
       && $Is(f, 
        Tclass._System.___hFunc15(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15))
       && Set#Equal(Reads15(t0, 
          t1, 
          t2, 
          t3, 
          t4, 
          t5, 
          t6, 
          t7, 
          t8, 
          t9, 
          t10, 
          t11, 
          t12, 
          t13, 
          t14, 
          t15, 
          $OneHeap, 
          f, 
          bx0, 
          bx1, 
          bx2, 
          bx3, 
          bx4, 
          bx5, 
          bx6, 
          bx7, 
          bx8, 
          bx9, 
          bx10, 
          bx11, 
          bx12, 
          bx13, 
          bx14), 
        Set#Empty(): Set Box)
     ==> Requires15(t0, 
        t1, 
        t2, 
        t3, 
        t4, 
        t5, 
        t6, 
        t7, 
        t8, 
        t9, 
        t10, 
        t11, 
        t12, 
        t13, 
        t14, 
        t15, 
        $OneHeap, 
        f, 
        bx0, 
        bx1, 
        bx2, 
        bx3, 
        bx4, 
        bx5, 
        bx6, 
        bx7, 
        bx8, 
        bx9, 
        bx10, 
        bx11, 
        bx12, 
        bx13, 
        bx14)
       == Requires15(t0, 
        t1, 
        t2, 
        t3, 
        t4, 
        t5, 
        t6, 
        t7, 
        t8, 
        t9, 
        t10, 
        t11, 
        t12, 
        t13, 
        t14, 
        t15, 
        heap, 
        f, 
        bx0, 
        bx1, 
        bx2, 
        bx3, 
        bx4, 
        bx5, 
        bx6, 
        bx7, 
        bx8, 
        bx9, 
        bx10, 
        bx11, 
        bx12, 
        bx13, 
        bx14));

axiom (forall f: HandleType, 
    t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    t6: Ty, 
    t7: Ty, 
    t8: Ty, 
    t9: Ty, 
    t10: Ty, 
    t11: Ty, 
    t12: Ty, 
    t13: Ty, 
    t14: Ty, 
    t15: Ty :: 
  { $Is(f, 
      Tclass._System.___hFunc15(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15)) } 
  $Is(f, 
      Tclass._System.___hFunc15(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15))
     <==> (forall h: Heap, 
        bx0: Box, 
        bx1: Box, 
        bx2: Box, 
        bx3: Box, 
        bx4: Box, 
        bx5: Box, 
        bx6: Box, 
        bx7: Box, 
        bx8: Box, 
        bx9: Box, 
        bx10: Box, 
        bx11: Box, 
        bx12: Box, 
        bx13: Box, 
        bx14: Box :: 
      { Apply15(t0, 
          t1, 
          t2, 
          t3, 
          t4, 
          t5, 
          t6, 
          t7, 
          t8, 
          t9, 
          t10, 
          t11, 
          t12, 
          t13, 
          t14, 
          t15, 
          h, 
          f, 
          bx0, 
          bx1, 
          bx2, 
          bx3, 
          bx4, 
          bx5, 
          bx6, 
          bx7, 
          bx8, 
          bx9, 
          bx10, 
          bx11, 
          bx12, 
          bx13, 
          bx14) } 
      $IsGoodHeap(h)
           && 
          $IsBox(bx0, t0)
           && $IsBox(bx1, t1)
           && $IsBox(bx2, t2)
           && $IsBox(bx3, t3)
           && $IsBox(bx4, t4)
           && $IsBox(bx5, t5)
           && $IsBox(bx6, t6)
           && $IsBox(bx7, t7)
           && $IsBox(bx8, t8)
           && $IsBox(bx9, t9)
           && $IsBox(bx10, t10)
           && $IsBox(bx11, t11)
           && $IsBox(bx12, t12)
           && $IsBox(bx13, t13)
           && $IsBox(bx14, t14)
           && Requires15(t0, 
            t1, 
            t2, 
            t3, 
            t4, 
            t5, 
            t6, 
            t7, 
            t8, 
            t9, 
            t10, 
            t11, 
            t12, 
            t13, 
            t14, 
            t15, 
            h, 
            f, 
            bx0, 
            bx1, 
            bx2, 
            bx3, 
            bx4, 
            bx5, 
            bx6, 
            bx7, 
            bx8, 
            bx9, 
            bx10, 
            bx11, 
            bx12, 
            bx13, 
            bx14)
         ==> $IsBox(Apply15(t0, 
            t1, 
            t2, 
            t3, 
            t4, 
            t5, 
            t6, 
            t7, 
            t8, 
            t9, 
            t10, 
            t11, 
            t12, 
            t13, 
            t14, 
            t15, 
            h, 
            f, 
            bx0, 
            bx1, 
            bx2, 
            bx3, 
            bx4, 
            bx5, 
            bx6, 
            bx7, 
            bx8, 
            bx9, 
            bx10, 
            bx11, 
            bx12, 
            bx13, 
            bx14), 
          t15)));

axiom (forall f: HandleType, 
    t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    t6: Ty, 
    t7: Ty, 
    t8: Ty, 
    t9: Ty, 
    t10: Ty, 
    t11: Ty, 
    t12: Ty, 
    t13: Ty, 
    t14: Ty, 
    t15: Ty, 
    u0: Ty, 
    u1: Ty, 
    u2: Ty, 
    u3: Ty, 
    u4: Ty, 
    u5: Ty, 
    u6: Ty, 
    u7: Ty, 
    u8: Ty, 
    u9: Ty, 
    u10: Ty, 
    u11: Ty, 
    u12: Ty, 
    u13: Ty, 
    u14: Ty, 
    u15: Ty :: 
  { $Is(f, 
      Tclass._System.___hFunc15(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15)), $Is(f, 
      Tclass._System.___hFunc15(u0, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11, u12, u13, u14, u15)) } 
  $Is(f, 
        Tclass._System.___hFunc15(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15))
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
        { $IsBox(bx, u3) } { $IsBox(bx, t3) } 
        $IsBox(bx, u3) ==> $IsBox(bx, t3))
       && (forall bx: Box :: 
        { $IsBox(bx, u4) } { $IsBox(bx, t4) } 
        $IsBox(bx, u4) ==> $IsBox(bx, t4))
       && (forall bx: Box :: 
        { $IsBox(bx, u5) } { $IsBox(bx, t5) } 
        $IsBox(bx, u5) ==> $IsBox(bx, t5))
       && (forall bx: Box :: 
        { $IsBox(bx, u6) } { $IsBox(bx, t6) } 
        $IsBox(bx, u6) ==> $IsBox(bx, t6))
       && (forall bx: Box :: 
        { $IsBox(bx, u7) } { $IsBox(bx, t7) } 
        $IsBox(bx, u7) ==> $IsBox(bx, t7))
       && (forall bx: Box :: 
        { $IsBox(bx, u8) } { $IsBox(bx, t8) } 
        $IsBox(bx, u8) ==> $IsBox(bx, t8))
       && (forall bx: Box :: 
        { $IsBox(bx, u9) } { $IsBox(bx, t9) } 
        $IsBox(bx, u9) ==> $IsBox(bx, t9))
       && (forall bx: Box :: 
        { $IsBox(bx, u10) } { $IsBox(bx, t10) } 
        $IsBox(bx, u10) ==> $IsBox(bx, t10))
       && (forall bx: Box :: 
        { $IsBox(bx, u11) } { $IsBox(bx, t11) } 
        $IsBox(bx, u11) ==> $IsBox(bx, t11))
       && (forall bx: Box :: 
        { $IsBox(bx, u12) } { $IsBox(bx, t12) } 
        $IsBox(bx, u12) ==> $IsBox(bx, t12))
       && (forall bx: Box :: 
        { $IsBox(bx, u13) } { $IsBox(bx, t13) } 
        $IsBox(bx, u13) ==> $IsBox(bx, t13))
       && (forall bx: Box :: 
        { $IsBox(bx, u14) } { $IsBox(bx, t14) } 
        $IsBox(bx, u14) ==> $IsBox(bx, t14))
       && (forall bx: Box :: 
        { $IsBox(bx, t15) } { $IsBox(bx, u15) } 
        $IsBox(bx, t15) ==> $IsBox(bx, u15))
     ==> $Is(f, 
      Tclass._System.___hFunc15(u0, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11, u12, u13, u14, u15)));

axiom (forall f: HandleType, 
    t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    t6: Ty, 
    t7: Ty, 
    t8: Ty, 
    t9: Ty, 
    t10: Ty, 
    t11: Ty, 
    t12: Ty, 
    t13: Ty, 
    t14: Ty, 
    t15: Ty, 
    h: Heap :: 
  { $IsAlloc(f, 
      Tclass._System.___hFunc15(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15), 
      h) } 
  $IsGoodHeap(h)
     ==> ($IsAlloc(f, 
        Tclass._System.___hFunc15(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15), 
        h)
       <==> (forall bx0: Box, 
          bx1: Box, 
          bx2: Box, 
          bx3: Box, 
          bx4: Box, 
          bx5: Box, 
          bx6: Box, 
          bx7: Box, 
          bx8: Box, 
          bx9: Box, 
          bx10: Box, 
          bx11: Box, 
          bx12: Box, 
          bx13: Box, 
          bx14: Box :: 
        { Apply15(t0, 
            t1, 
            t2, 
            t3, 
            t4, 
            t5, 
            t6, 
            t7, 
            t8, 
            t9, 
            t10, 
            t11, 
            t12, 
            t13, 
            t14, 
            t15, 
            h, 
            f, 
            bx0, 
            bx1, 
            bx2, 
            bx3, 
            bx4, 
            bx5, 
            bx6, 
            bx7, 
            bx8, 
            bx9, 
            bx10, 
            bx11, 
            bx12, 
            bx13, 
            bx14) } 
          { Reads15(t0, 
            t1, 
            t2, 
            t3, 
            t4, 
            t5, 
            t6, 
            t7, 
            t8, 
            t9, 
            t10, 
            t11, 
            t12, 
            t13, 
            t14, 
            t15, 
            h, 
            f, 
            bx0, 
            bx1, 
            bx2, 
            bx3, 
            bx4, 
            bx5, 
            bx6, 
            bx7, 
            bx8, 
            bx9, 
            bx10, 
            bx11, 
            bx12, 
            bx13, 
            bx14) } 
        $IsBox(bx0, t0)
             && $IsAllocBox(bx0, t0, h)
             && 
            $IsBox(bx1, t1)
             && $IsAllocBox(bx1, t1, h)
             && 
            $IsBox(bx2, t2)
             && $IsAllocBox(bx2, t2, h)
             && 
            $IsBox(bx3, t3)
             && $IsAllocBox(bx3, t3, h)
             && 
            $IsBox(bx4, t4)
             && $IsAllocBox(bx4, t4, h)
             && 
            $IsBox(bx5, t5)
             && $IsAllocBox(bx5, t5, h)
             && 
            $IsBox(bx6, t6)
             && $IsAllocBox(bx6, t6, h)
             && 
            $IsBox(bx7, t7)
             && $IsAllocBox(bx7, t7, h)
             && 
            $IsBox(bx8, t8)
             && $IsAllocBox(bx8, t8, h)
             && 
            $IsBox(bx9, t9)
             && $IsAllocBox(bx9, t9, h)
             && 
            $IsBox(bx10, t10)
             && $IsAllocBox(bx10, t10, h)
             && 
            $IsBox(bx11, t11)
             && $IsAllocBox(bx11, t11, h)
             && 
            $IsBox(bx12, t12)
             && $IsAllocBox(bx12, t12, h)
             && 
            $IsBox(bx13, t13)
             && $IsAllocBox(bx13, t13, h)
             && 
            $IsBox(bx14, t14)
             && $IsAllocBox(bx14, t14, h)
             && Requires15(t0, 
              t1, 
              t2, 
              t3, 
              t4, 
              t5, 
              t6, 
              t7, 
              t8, 
              t9, 
              t10, 
              t11, 
              t12, 
              t13, 
              t14, 
              t15, 
              h, 
              f, 
              bx0, 
              bx1, 
              bx2, 
              bx3, 
              bx4, 
              bx5, 
              bx6, 
              bx7, 
              bx8, 
              bx9, 
              bx10, 
              bx11, 
              bx12, 
              bx13, 
              bx14)
           ==> (forall r: ref :: 
            { Reads15(t0, 
                t1, 
                t2, 
                t3, 
                t4, 
                t5, 
                t6, 
                t7, 
                t8, 
                t9, 
                t10, 
                t11, 
                t12, 
                t13, 
                t14, 
                t15, 
                h, 
                f, 
                bx0, 
                bx1, 
                bx2, 
                bx3, 
                bx4, 
                bx5, 
                bx6, 
                bx7, 
                bx8, 
                bx9, 
                bx10, 
                bx11, 
                bx12, 
                bx13, 
                bx14)[$Box(r)] } 
            r != null
                 && Reads15(t0, 
                  t1, 
                  t2, 
                  t3, 
                  t4, 
                  t5, 
                  t6, 
                  t7, 
                  t8, 
                  t9, 
                  t10, 
                  t11, 
                  t12, 
                  t13, 
                  t14, 
                  t15, 
                  h, 
                  f, 
                  bx0, 
                  bx1, 
                  bx2, 
                  bx3, 
                  bx4, 
                  bx5, 
                  bx6, 
                  bx7, 
                  bx8, 
                  bx9, 
                  bx10, 
                  bx11, 
                  bx12, 
                  bx13, 
                  bx14)[$Box(r)]
               ==> read(h, r, alloc)))));

axiom (forall f: HandleType, 
    t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    t6: Ty, 
    t7: Ty, 
    t8: Ty, 
    t9: Ty, 
    t10: Ty, 
    t11: Ty, 
    t12: Ty, 
    t13: Ty, 
    t14: Ty, 
    t15: Ty, 
    h: Heap :: 
  { $IsAlloc(f, 
      Tclass._System.___hFunc15(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15), 
      h) } 
  $IsGoodHeap(h)
       && $IsAlloc(f, 
        Tclass._System.___hFunc15(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15), 
        h)
     ==> (forall bx0: Box, 
        bx1: Box, 
        bx2: Box, 
        bx3: Box, 
        bx4: Box, 
        bx5: Box, 
        bx6: Box, 
        bx7: Box, 
        bx8: Box, 
        bx9: Box, 
        bx10: Box, 
        bx11: Box, 
        bx12: Box, 
        bx13: Box, 
        bx14: Box :: 
      { Apply15(t0, 
          t1, 
          t2, 
          t3, 
          t4, 
          t5, 
          t6, 
          t7, 
          t8, 
          t9, 
          t10, 
          t11, 
          t12, 
          t13, 
          t14, 
          t15, 
          h, 
          f, 
          bx0, 
          bx1, 
          bx2, 
          bx3, 
          bx4, 
          bx5, 
          bx6, 
          bx7, 
          bx8, 
          bx9, 
          bx10, 
          bx11, 
          bx12, 
          bx13, 
          bx14) } 
      $IsAllocBox(bx0, t0, h)
           && $IsAllocBox(bx1, t1, h)
           && $IsAllocBox(bx2, t2, h)
           && $IsAllocBox(bx3, t3, h)
           && $IsAllocBox(bx4, t4, h)
           && $IsAllocBox(bx5, t5, h)
           && $IsAllocBox(bx6, t6, h)
           && $IsAllocBox(bx7, t7, h)
           && $IsAllocBox(bx8, t8, h)
           && $IsAllocBox(bx9, t9, h)
           && $IsAllocBox(bx10, t10, h)
           && $IsAllocBox(bx11, t11, h)
           && $IsAllocBox(bx12, t12, h)
           && $IsAllocBox(bx13, t13, h)
           && $IsAllocBox(bx14, t14, h)
           && Requires15(t0, 
            t1, 
            t2, 
            t3, 
            t4, 
            t5, 
            t6, 
            t7, 
            t8, 
            t9, 
            t10, 
            t11, 
            t12, 
            t13, 
            t14, 
            t15, 
            h, 
            f, 
            bx0, 
            bx1, 
            bx2, 
            bx3, 
            bx4, 
            bx5, 
            bx6, 
            bx7, 
            bx8, 
            bx9, 
            bx10, 
            bx11, 
            bx12, 
            bx13, 
            bx14)
         ==> $IsAllocBox(Apply15(t0, 
            t1, 
            t2, 
            t3, 
            t4, 
            t5, 
            t6, 
            t7, 
            t8, 
            t9, 
            t10, 
            t11, 
            t12, 
            t13, 
            t14, 
            t15, 
            h, 
            f, 
            bx0, 
            bx1, 
            bx2, 
            bx3, 
            bx4, 
            bx5, 
            bx6, 
            bx7, 
            bx8, 
            bx9, 
            bx10, 
            bx11, 
            bx12, 
            bx13, 
            bx14), 
          t15, 
          h)));

function Tclass._System.___hPartialFunc15(Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty) : Ty;

const unique Tagclass._System.___hPartialFunc15: TyTag;

// Tclass._System.___hPartialFunc15 Tag
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hPartialFunc15(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$R) } 
  Tag(Tclass._System.___hPartialFunc15(#$T0, 
          #$T1, 
          #$T2, 
          #$T3, 
          #$T4, 
          #$T5, 
          #$T6, 
          #$T7, 
          #$T8, 
          #$T9, 
          #$T10, 
          #$T11, 
          #$T12, 
          #$T13, 
          #$T14, 
          #$R))
       == Tagclass._System.___hPartialFunc15
     && TagFamily(Tclass._System.___hPartialFunc15(#$T0, 
          #$T1, 
          #$T2, 
          #$T3, 
          #$T4, 
          #$T5, 
          #$T6, 
          #$T7, 
          #$T8, 
          #$T9, 
          #$T10, 
          #$T11, 
          #$T12, 
          #$T13, 
          #$T14, 
          #$R))
       == tytagFamily$_#PartialFunc15);

// Tclass._System.___hPartialFunc15 injectivity 0
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hPartialFunc15(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$R) } 
  Tclass._System.___hPartialFunc15_0(Tclass._System.___hPartialFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     == #$T0);

function Tclass._System.___hPartialFunc15_0(Ty) : Ty;

// Tclass._System.___hPartialFunc15 injectivity 1
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hPartialFunc15(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$R) } 
  Tclass._System.___hPartialFunc15_1(Tclass._System.___hPartialFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     == #$T1);

function Tclass._System.___hPartialFunc15_1(Ty) : Ty;

// Tclass._System.___hPartialFunc15 injectivity 2
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hPartialFunc15(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$R) } 
  Tclass._System.___hPartialFunc15_2(Tclass._System.___hPartialFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     == #$T2);

function Tclass._System.___hPartialFunc15_2(Ty) : Ty;

// Tclass._System.___hPartialFunc15 injectivity 3
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hPartialFunc15(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$R) } 
  Tclass._System.___hPartialFunc15_3(Tclass._System.___hPartialFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     == #$T3);

function Tclass._System.___hPartialFunc15_3(Ty) : Ty;

// Tclass._System.___hPartialFunc15 injectivity 4
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hPartialFunc15(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$R) } 
  Tclass._System.___hPartialFunc15_4(Tclass._System.___hPartialFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     == #$T4);

function Tclass._System.___hPartialFunc15_4(Ty) : Ty;

// Tclass._System.___hPartialFunc15 injectivity 5
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hPartialFunc15(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$R) } 
  Tclass._System.___hPartialFunc15_5(Tclass._System.___hPartialFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     == #$T5);

function Tclass._System.___hPartialFunc15_5(Ty) : Ty;

// Tclass._System.___hPartialFunc15 injectivity 6
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hPartialFunc15(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$R) } 
  Tclass._System.___hPartialFunc15_6(Tclass._System.___hPartialFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     == #$T6);

function Tclass._System.___hPartialFunc15_6(Ty) : Ty;

// Tclass._System.___hPartialFunc15 injectivity 7
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hPartialFunc15(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$R) } 
  Tclass._System.___hPartialFunc15_7(Tclass._System.___hPartialFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     == #$T7);

function Tclass._System.___hPartialFunc15_7(Ty) : Ty;

// Tclass._System.___hPartialFunc15 injectivity 8
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hPartialFunc15(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$R) } 
  Tclass._System.___hPartialFunc15_8(Tclass._System.___hPartialFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     == #$T8);

function Tclass._System.___hPartialFunc15_8(Ty) : Ty;

// Tclass._System.___hPartialFunc15 injectivity 9
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hPartialFunc15(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$R) } 
  Tclass._System.___hPartialFunc15_9(Tclass._System.___hPartialFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     == #$T9);

function Tclass._System.___hPartialFunc15_9(Ty) : Ty;

// Tclass._System.___hPartialFunc15 injectivity 10
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hPartialFunc15(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$R) } 
  Tclass._System.___hPartialFunc15_10(Tclass._System.___hPartialFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     == #$T10);

function Tclass._System.___hPartialFunc15_10(Ty) : Ty;

// Tclass._System.___hPartialFunc15 injectivity 11
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hPartialFunc15(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$R) } 
  Tclass._System.___hPartialFunc15_11(Tclass._System.___hPartialFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     == #$T11);

function Tclass._System.___hPartialFunc15_11(Ty) : Ty;

// Tclass._System.___hPartialFunc15 injectivity 12
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hPartialFunc15(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$R) } 
  Tclass._System.___hPartialFunc15_12(Tclass._System.___hPartialFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     == #$T12);

function Tclass._System.___hPartialFunc15_12(Ty) : Ty;

// Tclass._System.___hPartialFunc15 injectivity 13
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hPartialFunc15(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$R) } 
  Tclass._System.___hPartialFunc15_13(Tclass._System.___hPartialFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     == #$T13);

function Tclass._System.___hPartialFunc15_13(Ty) : Ty;

// Tclass._System.___hPartialFunc15 injectivity 14
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hPartialFunc15(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$R) } 
  Tclass._System.___hPartialFunc15_14(Tclass._System.___hPartialFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     == #$T14);

function Tclass._System.___hPartialFunc15_14(Ty) : Ty;

// Tclass._System.___hPartialFunc15 injectivity 15
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hPartialFunc15(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$R) } 
  Tclass._System.___hPartialFunc15_15(Tclass._System.___hPartialFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     == #$R);

function Tclass._System.___hPartialFunc15_15(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hPartialFunc15
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty, 
    bx: Box :: 
  { $IsBox(bx, 
      Tclass._System.___hPartialFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R)) } 
  $IsBox(bx, 
      Tclass._System.___hPartialFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, 
        Tclass._System.___hPartialFunc15(#$T0, 
          #$T1, 
          #$T2, 
          #$T3, 
          #$T4, 
          #$T5, 
          #$T6, 
          #$T7, 
          #$T8, 
          #$T9, 
          #$T10, 
          #$T11, 
          #$T12, 
          #$T13, 
          #$T14, 
          #$R)));

// _System._#PartialFunc15: subset type $Is
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty, 
    f#0: HandleType :: 
  { $Is(f#0, 
      Tclass._System.___hPartialFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R)) } 
  $Is(f#0, 
      Tclass._System.___hPartialFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     <==> $Is(f#0, 
        Tclass._System.___hFunc15(#$T0, 
          #$T1, 
          #$T2, 
          #$T3, 
          #$T4, 
          #$T5, 
          #$T6, 
          #$T7, 
          #$T8, 
          #$T9, 
          #$T10, 
          #$T11, 
          #$T12, 
          #$T13, 
          #$T14, 
          #$R))
       && (forall x0#0: Box, 
          x1#0: Box, 
          x2#0: Box, 
          x3#0: Box, 
          x4#0: Box, 
          x5#0: Box, 
          x6#0: Box, 
          x7#0: Box, 
          x8#0: Box, 
          x9#0: Box, 
          x10#0: Box, 
          x11#0: Box, 
          x12#0: Box, 
          x13#0: Box, 
          x14#0: Box :: 
        $IsBox(x0#0, #$T0)
             && $IsBox(x1#0, #$T1)
             && $IsBox(x2#0, #$T2)
             && $IsBox(x3#0, #$T3)
             && $IsBox(x4#0, #$T4)
             && $IsBox(x5#0, #$T5)
             && $IsBox(x6#0, #$T6)
             && $IsBox(x7#0, #$T7)
             && $IsBox(x8#0, #$T8)
             && $IsBox(x9#0, #$T9)
             && $IsBox(x10#0, #$T10)
             && $IsBox(x11#0, #$T11)
             && $IsBox(x12#0, #$T12)
             && $IsBox(x13#0, #$T13)
             && $IsBox(x14#0, #$T14)
           ==> Set#Equal(Reads15(#$T0, 
              #$T1, 
              #$T2, 
              #$T3, 
              #$T4, 
              #$T5, 
              #$T6, 
              #$T7, 
              #$T8, 
              #$T9, 
              #$T10, 
              #$T11, 
              #$T12, 
              #$T13, 
              #$T14, 
              #$R, 
              $OneHeap, 
              f#0, 
              x0#0, 
              x1#0, 
              x2#0, 
              x3#0, 
              x4#0, 
              x5#0, 
              x6#0, 
              x7#0, 
              x8#0, 
              x9#0, 
              x10#0, 
              x11#0, 
              x12#0, 
              x13#0, 
              x14#0), 
            Set#Empty(): Set Box)));

// _System._#PartialFunc15: subset type $IsAlloc
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty, 
    f#0: HandleType, 
    $h: Heap :: 
  { $IsAlloc(f#0, 
      Tclass._System.___hPartialFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R), 
      $h) } 
  $IsAlloc(f#0, 
      Tclass._System.___hPartialFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R), 
      $h)
     <==> $IsAlloc(f#0, 
      Tclass._System.___hFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R), 
      $h));

function Tclass._System.___hTotalFunc15(Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty) : Ty;

const unique Tagclass._System.___hTotalFunc15: TyTag;

// Tclass._System.___hTotalFunc15 Tag
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hTotalFunc15(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$R) } 
  Tag(Tclass._System.___hTotalFunc15(#$T0, 
          #$T1, 
          #$T2, 
          #$T3, 
          #$T4, 
          #$T5, 
          #$T6, 
          #$T7, 
          #$T8, 
          #$T9, 
          #$T10, 
          #$T11, 
          #$T12, 
          #$T13, 
          #$T14, 
          #$R))
       == Tagclass._System.___hTotalFunc15
     && TagFamily(Tclass._System.___hTotalFunc15(#$T0, 
          #$T1, 
          #$T2, 
          #$T3, 
          #$T4, 
          #$T5, 
          #$T6, 
          #$T7, 
          #$T8, 
          #$T9, 
          #$T10, 
          #$T11, 
          #$T12, 
          #$T13, 
          #$T14, 
          #$R))
       == tytagFamily$_#TotalFunc15);

// Tclass._System.___hTotalFunc15 injectivity 0
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hTotalFunc15(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$R) } 
  Tclass._System.___hTotalFunc15_0(Tclass._System.___hTotalFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     == #$T0);

function Tclass._System.___hTotalFunc15_0(Ty) : Ty;

// Tclass._System.___hTotalFunc15 injectivity 1
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hTotalFunc15(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$R) } 
  Tclass._System.___hTotalFunc15_1(Tclass._System.___hTotalFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     == #$T1);

function Tclass._System.___hTotalFunc15_1(Ty) : Ty;

// Tclass._System.___hTotalFunc15 injectivity 2
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hTotalFunc15(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$R) } 
  Tclass._System.___hTotalFunc15_2(Tclass._System.___hTotalFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     == #$T2);

function Tclass._System.___hTotalFunc15_2(Ty) : Ty;

// Tclass._System.___hTotalFunc15 injectivity 3
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hTotalFunc15(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$R) } 
  Tclass._System.___hTotalFunc15_3(Tclass._System.___hTotalFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     == #$T3);

function Tclass._System.___hTotalFunc15_3(Ty) : Ty;

// Tclass._System.___hTotalFunc15 injectivity 4
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hTotalFunc15(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$R) } 
  Tclass._System.___hTotalFunc15_4(Tclass._System.___hTotalFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     == #$T4);

function Tclass._System.___hTotalFunc15_4(Ty) : Ty;

// Tclass._System.___hTotalFunc15 injectivity 5
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hTotalFunc15(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$R) } 
  Tclass._System.___hTotalFunc15_5(Tclass._System.___hTotalFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     == #$T5);

function Tclass._System.___hTotalFunc15_5(Ty) : Ty;

// Tclass._System.___hTotalFunc15 injectivity 6
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hTotalFunc15(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$R) } 
  Tclass._System.___hTotalFunc15_6(Tclass._System.___hTotalFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     == #$T6);

function Tclass._System.___hTotalFunc15_6(Ty) : Ty;

// Tclass._System.___hTotalFunc15 injectivity 7
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hTotalFunc15(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$R) } 
  Tclass._System.___hTotalFunc15_7(Tclass._System.___hTotalFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     == #$T7);

function Tclass._System.___hTotalFunc15_7(Ty) : Ty;

// Tclass._System.___hTotalFunc15 injectivity 8
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hTotalFunc15(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$R) } 
  Tclass._System.___hTotalFunc15_8(Tclass._System.___hTotalFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     == #$T8);

function Tclass._System.___hTotalFunc15_8(Ty) : Ty;

// Tclass._System.___hTotalFunc15 injectivity 9
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hTotalFunc15(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$R) } 
  Tclass._System.___hTotalFunc15_9(Tclass._System.___hTotalFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     == #$T9);

function Tclass._System.___hTotalFunc15_9(Ty) : Ty;

// Tclass._System.___hTotalFunc15 injectivity 10
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hTotalFunc15(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$R) } 
  Tclass._System.___hTotalFunc15_10(Tclass._System.___hTotalFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     == #$T10);

function Tclass._System.___hTotalFunc15_10(Ty) : Ty;

// Tclass._System.___hTotalFunc15 injectivity 11
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hTotalFunc15(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$R) } 
  Tclass._System.___hTotalFunc15_11(Tclass._System.___hTotalFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     == #$T11);

function Tclass._System.___hTotalFunc15_11(Ty) : Ty;

// Tclass._System.___hTotalFunc15 injectivity 12
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hTotalFunc15(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$R) } 
  Tclass._System.___hTotalFunc15_12(Tclass._System.___hTotalFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     == #$T12);

function Tclass._System.___hTotalFunc15_12(Ty) : Ty;

// Tclass._System.___hTotalFunc15 injectivity 13
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hTotalFunc15(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$R) } 
  Tclass._System.___hTotalFunc15_13(Tclass._System.___hTotalFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     == #$T13);

function Tclass._System.___hTotalFunc15_13(Ty) : Ty;

// Tclass._System.___hTotalFunc15 injectivity 14
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hTotalFunc15(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$R) } 
  Tclass._System.___hTotalFunc15_14(Tclass._System.___hTotalFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     == #$T14);

function Tclass._System.___hTotalFunc15_14(Ty) : Ty;

// Tclass._System.___hTotalFunc15 injectivity 15
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hTotalFunc15(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$R) } 
  Tclass._System.___hTotalFunc15_15(Tclass._System.___hTotalFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     == #$R);

function Tclass._System.___hTotalFunc15_15(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hTotalFunc15
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty, 
    bx: Box :: 
  { $IsBox(bx, 
      Tclass._System.___hTotalFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R)) } 
  $IsBox(bx, 
      Tclass._System.___hTotalFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, 
        Tclass._System.___hTotalFunc15(#$T0, 
          #$T1, 
          #$T2, 
          #$T3, 
          #$T4, 
          #$T5, 
          #$T6, 
          #$T7, 
          #$T8, 
          #$T9, 
          #$T10, 
          #$T11, 
          #$T12, 
          #$T13, 
          #$T14, 
          #$R)));

// _System._#TotalFunc15: subset type $Is
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty, 
    f#0: HandleType :: 
  { $Is(f#0, 
      Tclass._System.___hTotalFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R)) } 
  $Is(f#0, 
      Tclass._System.___hTotalFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R))
     <==> $Is(f#0, 
        Tclass._System.___hPartialFunc15(#$T0, 
          #$T1, 
          #$T2, 
          #$T3, 
          #$T4, 
          #$T5, 
          #$T6, 
          #$T7, 
          #$T8, 
          #$T9, 
          #$T10, 
          #$T11, 
          #$T12, 
          #$T13, 
          #$T14, 
          #$R))
       && (forall x0#0: Box, 
          x1#0: Box, 
          x2#0: Box, 
          x3#0: Box, 
          x4#0: Box, 
          x5#0: Box, 
          x6#0: Box, 
          x7#0: Box, 
          x8#0: Box, 
          x9#0: Box, 
          x10#0: Box, 
          x11#0: Box, 
          x12#0: Box, 
          x13#0: Box, 
          x14#0: Box :: 
        $IsBox(x0#0, #$T0)
             && $IsBox(x1#0, #$T1)
             && $IsBox(x2#0, #$T2)
             && $IsBox(x3#0, #$T3)
             && $IsBox(x4#0, #$T4)
             && $IsBox(x5#0, #$T5)
             && $IsBox(x6#0, #$T6)
             && $IsBox(x7#0, #$T7)
             && $IsBox(x8#0, #$T8)
             && $IsBox(x9#0, #$T9)
             && $IsBox(x10#0, #$T10)
             && $IsBox(x11#0, #$T11)
             && $IsBox(x12#0, #$T12)
             && $IsBox(x13#0, #$T13)
             && $IsBox(x14#0, #$T14)
           ==> Requires15(#$T0, 
            #$T1, 
            #$T2, 
            #$T3, 
            #$T4, 
            #$T5, 
            #$T6, 
            #$T7, 
            #$T8, 
            #$T9, 
            #$T10, 
            #$T11, 
            #$T12, 
            #$T13, 
            #$T14, 
            #$R, 
            $OneHeap, 
            f#0, 
            x0#0, 
            x1#0, 
            x2#0, 
            x3#0, 
            x4#0, 
            x5#0, 
            x6#0, 
            x7#0, 
            x8#0, 
            x9#0, 
            x10#0, 
            x11#0, 
            x12#0, 
            x13#0, 
            x14#0)));

// _System._#TotalFunc15: subset type $IsAlloc
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$R: Ty, 
    f#0: HandleType, 
    $h: Heap :: 
  { $IsAlloc(f#0, 
      Tclass._System.___hTotalFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R), 
      $h) } 
  $IsAlloc(f#0, 
      Tclass._System.___hTotalFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R), 
      $h)
     <==> $IsAlloc(f#0, 
      Tclass._System.___hPartialFunc15(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$R), 
      $h));

const unique class._System.array16?: ClassName;

function Tclass._System.array16?(Ty) : Ty;

const unique Tagclass._System.array16?: TyTag;

// Tclass._System.array16? Tag
axiom (forall _System.array16$arg: Ty :: 
  { Tclass._System.array16?(_System.array16$arg) } 
  Tag(Tclass._System.array16?(_System.array16$arg)) == Tagclass._System.array16?
     && TagFamily(Tclass._System.array16?(_System.array16$arg)) == tytagFamily$array16);

// Tclass._System.array16? injectivity 0
axiom (forall _System.array16$arg: Ty :: 
  { Tclass._System.array16?(_System.array16$arg) } 
  Tclass._System.array16?_0(Tclass._System.array16?(_System.array16$arg))
     == _System.array16$arg);

function Tclass._System.array16?_0(Ty) : Ty;

// Box/unbox axiom for Tclass._System.array16?
axiom (forall _System.array16$arg: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.array16?(_System.array16$arg)) } 
  $IsBox(bx, Tclass._System.array16?(_System.array16$arg))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._System.array16?(_System.array16$arg)));

axiom (forall o: ref :: 
  { _System.array16.Length0(o) } 
  0 <= _System.array16.Length0(o));

axiom (forall o: ref :: 
  { _System.array16.Length1(o) } 
  0 <= _System.array16.Length1(o));

axiom (forall o: ref :: 
  { _System.array16.Length2(o) } 
  0 <= _System.array16.Length2(o));

axiom (forall o: ref :: 
  { _System.array16.Length3(o) } 
  0 <= _System.array16.Length3(o));

axiom (forall o: ref :: 
  { _System.array16.Length4(o) } 
  0 <= _System.array16.Length4(o));

axiom (forall o: ref :: 
  { _System.array16.Length5(o) } 
  0 <= _System.array16.Length5(o));

axiom (forall o: ref :: 
  { _System.array16.Length6(o) } 
  0 <= _System.array16.Length6(o));

axiom (forall o: ref :: 
  { _System.array16.Length7(o) } 
  0 <= _System.array16.Length7(o));

axiom (forall o: ref :: 
  { _System.array16.Length8(o) } 
  0 <= _System.array16.Length8(o));

axiom (forall o: ref :: 
  { _System.array16.Length9(o) } 
  0 <= _System.array16.Length9(o));

axiom (forall o: ref :: 
  { _System.array16.Length10(o) } 
  0 <= _System.array16.Length10(o));

axiom (forall o: ref :: 
  { _System.array16.Length11(o) } 
  0 <= _System.array16.Length11(o));

axiom (forall o: ref :: 
  { _System.array16.Length12(o) } 
  0 <= _System.array16.Length12(o));

axiom (forall o: ref :: 
  { _System.array16.Length13(o) } 
  0 <= _System.array16.Length13(o));

axiom (forall o: ref :: 
  { _System.array16.Length14(o) } 
  0 <= _System.array16.Length14(o));

axiom (forall o: ref :: 
  { _System.array16.Length15(o) } 
  0 <= _System.array16.Length15(o));

// array16.: Type axiom
axiom (forall _System.array16$arg: Ty, 
    $h: Heap, 
    $o: ref, 
    $i0: int, 
    $i1: int, 
    $i2: int, 
    $i3: int, 
    $i4: int, 
    $i5: int, 
    $i6: int, 
    $i7: int, 
    $i8: int, 
    $i9: int, 
    $i10: int, 
    $i11: int, 
    $i12: int, 
    $i13: int, 
    $i14: int, 
    $i15: int :: 
  { read($h, 
      $o, 
      MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(IndexField($i0), $i1), $i2), $i3), 
                              $i4), 
                            $i5), 
                          $i6), 
                        $i7), 
                      $i8), 
                    $i9), 
                  $i10), 
                $i11), 
              $i12), 
            $i13), 
          $i14), 
        $i15)), Tclass._System.array16?(_System.array16$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array16?(_System.array16$arg)
       && 
      0 <= $i0
       && $i0 < _System.array16.Length0($o)
       && 
      0 <= $i1
       && $i1 < _System.array16.Length1($o)
       && 
      0 <= $i2
       && $i2 < _System.array16.Length2($o)
       && 
      0 <= $i3
       && $i3 < _System.array16.Length3($o)
       && 
      0 <= $i4
       && $i4 < _System.array16.Length4($o)
       && 
      0 <= $i5
       && $i5 < _System.array16.Length5($o)
       && 
      0 <= $i6
       && $i6 < _System.array16.Length6($o)
       && 
      0 <= $i7
       && $i7 < _System.array16.Length7($o)
       && 
      0 <= $i8
       && $i8 < _System.array16.Length8($o)
       && 
      0 <= $i9
       && $i9 < _System.array16.Length9($o)
       && 
      0 <= $i10
       && $i10 < _System.array16.Length10($o)
       && 
      0 <= $i11
       && $i11 < _System.array16.Length11($o)
       && 
      0 <= $i12
       && $i12 < _System.array16.Length12($o)
       && 
      0 <= $i13
       && $i13 < _System.array16.Length13($o)
       && 
      0 <= $i14
       && $i14 < _System.array16.Length14($o)
       && 
      0 <= $i15
       && $i15 < _System.array16.Length15($o)
     ==> $IsBox(read($h, 
        $o, 
        MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(IndexField($i0), $i1), $i2), $i3), 
                                $i4), 
                              $i5), 
                            $i6), 
                          $i7), 
                        $i8), 
                      $i9), 
                    $i10), 
                  $i11), 
                $i12), 
              $i13), 
            $i14), 
          $i15)), 
      _System.array16$arg));

// array16.: Allocation axiom
axiom (forall _System.array16$arg: Ty, 
    $h: Heap, 
    $o: ref, 
    $i0: int, 
    $i1: int, 
    $i2: int, 
    $i3: int, 
    $i4: int, 
    $i5: int, 
    $i6: int, 
    $i7: int, 
    $i8: int, 
    $i9: int, 
    $i10: int, 
    $i11: int, 
    $i12: int, 
    $i13: int, 
    $i14: int, 
    $i15: int :: 
  { read($h, 
      $o, 
      MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(IndexField($i0), $i1), $i2), $i3), 
                              $i4), 
                            $i5), 
                          $i6), 
                        $i7), 
                      $i8), 
                    $i9), 
                  $i10), 
                $i11), 
              $i12), 
            $i13), 
          $i14), 
        $i15)), Tclass._System.array16?(_System.array16$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array16?(_System.array16$arg)
       && 
      0 <= $i0
       && $i0 < _System.array16.Length0($o)
       && 
      0 <= $i1
       && $i1 < _System.array16.Length1($o)
       && 
      0 <= $i2
       && $i2 < _System.array16.Length2($o)
       && 
      0 <= $i3
       && $i3 < _System.array16.Length3($o)
       && 
      0 <= $i4
       && $i4 < _System.array16.Length4($o)
       && 
      0 <= $i5
       && $i5 < _System.array16.Length5($o)
       && 
      0 <= $i6
       && $i6 < _System.array16.Length6($o)
       && 
      0 <= $i7
       && $i7 < _System.array16.Length7($o)
       && 
      0 <= $i8
       && $i8 < _System.array16.Length8($o)
       && 
      0 <= $i9
       && $i9 < _System.array16.Length9($o)
       && 
      0 <= $i10
       && $i10 < _System.array16.Length10($o)
       && 
      0 <= $i11
       && $i11 < _System.array16.Length11($o)
       && 
      0 <= $i12
       && $i12 < _System.array16.Length12($o)
       && 
      0 <= $i13
       && $i13 < _System.array16.Length13($o)
       && 
      0 <= $i14
       && $i14 < _System.array16.Length14($o)
       && 
      0 <= $i15
       && $i15 < _System.array16.Length15($o)
       && read($h, $o, alloc)
     ==> $IsAllocBox(read($h, 
        $o, 
        MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(MultiIndexField(IndexField($i0), $i1), $i2), $i3), 
                                $i4), 
                              $i5), 
                            $i6), 
                          $i7), 
                        $i8), 
                      $i9), 
                    $i10), 
                  $i11), 
                $i12), 
              $i13), 
            $i14), 
          $i15)), 
      _System.array16$arg, 
      $h));

// array16: Class $Is
axiom (forall _System.array16$arg: Ty, $o: ref :: 
  { $Is($o, Tclass._System.array16?(_System.array16$arg)) } 
  $Is($o, Tclass._System.array16?(_System.array16$arg))
     <==> $o == null || dtype($o) == Tclass._System.array16?(_System.array16$arg));

// array16: Class $IsAlloc
axiom (forall _System.array16$arg: Ty, $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._System.array16?(_System.array16$arg), $h) } 
  $IsAlloc($o, Tclass._System.array16?(_System.array16$arg), $h)
     <==> $o == null || read($h, $o, alloc));

function _System.array16.Length0(ref) : int;

// array16.Length0: Type axiom
axiom (forall _System.array16$arg: Ty, $o: ref :: 
  { _System.array16.Length0($o), Tclass._System.array16?(_System.array16$arg) } 
  $o != null && dtype($o) == Tclass._System.array16?(_System.array16$arg)
     ==> $Is(_System.array16.Length0($o), TInt));

// array16.Length0: Allocation axiom
axiom (forall _System.array16$arg: Ty, $h: Heap, $o: ref :: 
  { _System.array16.Length0($o), read($h, $o, alloc), Tclass._System.array16?(_System.array16$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array16?(_System.array16$arg)
       && read($h, $o, alloc)
     ==> $IsAlloc(_System.array16.Length0($o), TInt, $h));

function _System.array16.Length1(ref) : int;

// array16.Length1: Type axiom
axiom (forall _System.array16$arg: Ty, $o: ref :: 
  { _System.array16.Length1($o), Tclass._System.array16?(_System.array16$arg) } 
  $o != null && dtype($o) == Tclass._System.array16?(_System.array16$arg)
     ==> $Is(_System.array16.Length1($o), TInt));

// array16.Length1: Allocation axiom
axiom (forall _System.array16$arg: Ty, $h: Heap, $o: ref :: 
  { _System.array16.Length1($o), read($h, $o, alloc), Tclass._System.array16?(_System.array16$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array16?(_System.array16$arg)
       && read($h, $o, alloc)
     ==> $IsAlloc(_System.array16.Length1($o), TInt, $h));

function _System.array16.Length2(ref) : int;

// array16.Length2: Type axiom
axiom (forall _System.array16$arg: Ty, $o: ref :: 
  { _System.array16.Length2($o), Tclass._System.array16?(_System.array16$arg) } 
  $o != null && dtype($o) == Tclass._System.array16?(_System.array16$arg)
     ==> $Is(_System.array16.Length2($o), TInt));

// array16.Length2: Allocation axiom
axiom (forall _System.array16$arg: Ty, $h: Heap, $o: ref :: 
  { _System.array16.Length2($o), read($h, $o, alloc), Tclass._System.array16?(_System.array16$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array16?(_System.array16$arg)
       && read($h, $o, alloc)
     ==> $IsAlloc(_System.array16.Length2($o), TInt, $h));

function _System.array16.Length3(ref) : int;

// array16.Length3: Type axiom
axiom (forall _System.array16$arg: Ty, $o: ref :: 
  { _System.array16.Length3($o), Tclass._System.array16?(_System.array16$arg) } 
  $o != null && dtype($o) == Tclass._System.array16?(_System.array16$arg)
     ==> $Is(_System.array16.Length3($o), TInt));

// array16.Length3: Allocation axiom
axiom (forall _System.array16$arg: Ty, $h: Heap, $o: ref :: 
  { _System.array16.Length3($o), read($h, $o, alloc), Tclass._System.array16?(_System.array16$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array16?(_System.array16$arg)
       && read($h, $o, alloc)
     ==> $IsAlloc(_System.array16.Length3($o), TInt, $h));

function _System.array16.Length4(ref) : int;

// array16.Length4: Type axiom
axiom (forall _System.array16$arg: Ty, $o: ref :: 
  { _System.array16.Length4($o), Tclass._System.array16?(_System.array16$arg) } 
  $o != null && dtype($o) == Tclass._System.array16?(_System.array16$arg)
     ==> $Is(_System.array16.Length4($o), TInt));

// array16.Length4: Allocation axiom
axiom (forall _System.array16$arg: Ty, $h: Heap, $o: ref :: 
  { _System.array16.Length4($o), read($h, $o, alloc), Tclass._System.array16?(_System.array16$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array16?(_System.array16$arg)
       && read($h, $o, alloc)
     ==> $IsAlloc(_System.array16.Length4($o), TInt, $h));

function _System.array16.Length5(ref) : int;

// array16.Length5: Type axiom
axiom (forall _System.array16$arg: Ty, $o: ref :: 
  { _System.array16.Length5($o), Tclass._System.array16?(_System.array16$arg) } 
  $o != null && dtype($o) == Tclass._System.array16?(_System.array16$arg)
     ==> $Is(_System.array16.Length5($o), TInt));

// array16.Length5: Allocation axiom
axiom (forall _System.array16$arg: Ty, $h: Heap, $o: ref :: 
  { _System.array16.Length5($o), read($h, $o, alloc), Tclass._System.array16?(_System.array16$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array16?(_System.array16$arg)
       && read($h, $o, alloc)
     ==> $IsAlloc(_System.array16.Length5($o), TInt, $h));

function _System.array16.Length6(ref) : int;

// array16.Length6: Type axiom
axiom (forall _System.array16$arg: Ty, $o: ref :: 
  { _System.array16.Length6($o), Tclass._System.array16?(_System.array16$arg) } 
  $o != null && dtype($o) == Tclass._System.array16?(_System.array16$arg)
     ==> $Is(_System.array16.Length6($o), TInt));

// array16.Length6: Allocation axiom
axiom (forall _System.array16$arg: Ty, $h: Heap, $o: ref :: 
  { _System.array16.Length6($o), read($h, $o, alloc), Tclass._System.array16?(_System.array16$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array16?(_System.array16$arg)
       && read($h, $o, alloc)
     ==> $IsAlloc(_System.array16.Length6($o), TInt, $h));

function _System.array16.Length7(ref) : int;

// array16.Length7: Type axiom
axiom (forall _System.array16$arg: Ty, $o: ref :: 
  { _System.array16.Length7($o), Tclass._System.array16?(_System.array16$arg) } 
  $o != null && dtype($o) == Tclass._System.array16?(_System.array16$arg)
     ==> $Is(_System.array16.Length7($o), TInt));

// array16.Length7: Allocation axiom
axiom (forall _System.array16$arg: Ty, $h: Heap, $o: ref :: 
  { _System.array16.Length7($o), read($h, $o, alloc), Tclass._System.array16?(_System.array16$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array16?(_System.array16$arg)
       && read($h, $o, alloc)
     ==> $IsAlloc(_System.array16.Length7($o), TInt, $h));

function _System.array16.Length8(ref) : int;

// array16.Length8: Type axiom
axiom (forall _System.array16$arg: Ty, $o: ref :: 
  { _System.array16.Length8($o), Tclass._System.array16?(_System.array16$arg) } 
  $o != null && dtype($o) == Tclass._System.array16?(_System.array16$arg)
     ==> $Is(_System.array16.Length8($o), TInt));

// array16.Length8: Allocation axiom
axiom (forall _System.array16$arg: Ty, $h: Heap, $o: ref :: 
  { _System.array16.Length8($o), read($h, $o, alloc), Tclass._System.array16?(_System.array16$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array16?(_System.array16$arg)
       && read($h, $o, alloc)
     ==> $IsAlloc(_System.array16.Length8($o), TInt, $h));

function _System.array16.Length9(ref) : int;

// array16.Length9: Type axiom
axiom (forall _System.array16$arg: Ty, $o: ref :: 
  { _System.array16.Length9($o), Tclass._System.array16?(_System.array16$arg) } 
  $o != null && dtype($o) == Tclass._System.array16?(_System.array16$arg)
     ==> $Is(_System.array16.Length9($o), TInt));

// array16.Length9: Allocation axiom
axiom (forall _System.array16$arg: Ty, $h: Heap, $o: ref :: 
  { _System.array16.Length9($o), read($h, $o, alloc), Tclass._System.array16?(_System.array16$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array16?(_System.array16$arg)
       && read($h, $o, alloc)
     ==> $IsAlloc(_System.array16.Length9($o), TInt, $h));

function _System.array16.Length10(ref) : int;

// array16.Length10: Type axiom
axiom (forall _System.array16$arg: Ty, $o: ref :: 
  { _System.array16.Length10($o), Tclass._System.array16?(_System.array16$arg) } 
  $o != null && dtype($o) == Tclass._System.array16?(_System.array16$arg)
     ==> $Is(_System.array16.Length10($o), TInt));

// array16.Length10: Allocation axiom
axiom (forall _System.array16$arg: Ty, $h: Heap, $o: ref :: 
  { _System.array16.Length10($o), read($h, $o, alloc), Tclass._System.array16?(_System.array16$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array16?(_System.array16$arg)
       && read($h, $o, alloc)
     ==> $IsAlloc(_System.array16.Length10($o), TInt, $h));

function _System.array16.Length11(ref) : int;

// array16.Length11: Type axiom
axiom (forall _System.array16$arg: Ty, $o: ref :: 
  { _System.array16.Length11($o), Tclass._System.array16?(_System.array16$arg) } 
  $o != null && dtype($o) == Tclass._System.array16?(_System.array16$arg)
     ==> $Is(_System.array16.Length11($o), TInt));

// array16.Length11: Allocation axiom
axiom (forall _System.array16$arg: Ty, $h: Heap, $o: ref :: 
  { _System.array16.Length11($o), read($h, $o, alloc), Tclass._System.array16?(_System.array16$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array16?(_System.array16$arg)
       && read($h, $o, alloc)
     ==> $IsAlloc(_System.array16.Length11($o), TInt, $h));

function _System.array16.Length12(ref) : int;

// array16.Length12: Type axiom
axiom (forall _System.array16$arg: Ty, $o: ref :: 
  { _System.array16.Length12($o), Tclass._System.array16?(_System.array16$arg) } 
  $o != null && dtype($o) == Tclass._System.array16?(_System.array16$arg)
     ==> $Is(_System.array16.Length12($o), TInt));

// array16.Length12: Allocation axiom
axiom (forall _System.array16$arg: Ty, $h: Heap, $o: ref :: 
  { _System.array16.Length12($o), read($h, $o, alloc), Tclass._System.array16?(_System.array16$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array16?(_System.array16$arg)
       && read($h, $o, alloc)
     ==> $IsAlloc(_System.array16.Length12($o), TInt, $h));

function _System.array16.Length13(ref) : int;

// array16.Length13: Type axiom
axiom (forall _System.array16$arg: Ty, $o: ref :: 
  { _System.array16.Length13($o), Tclass._System.array16?(_System.array16$arg) } 
  $o != null && dtype($o) == Tclass._System.array16?(_System.array16$arg)
     ==> $Is(_System.array16.Length13($o), TInt));

// array16.Length13: Allocation axiom
axiom (forall _System.array16$arg: Ty, $h: Heap, $o: ref :: 
  { _System.array16.Length13($o), read($h, $o, alloc), Tclass._System.array16?(_System.array16$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array16?(_System.array16$arg)
       && read($h, $o, alloc)
     ==> $IsAlloc(_System.array16.Length13($o), TInt, $h));

function _System.array16.Length14(ref) : int;

// array16.Length14: Type axiom
axiom (forall _System.array16$arg: Ty, $o: ref :: 
  { _System.array16.Length14($o), Tclass._System.array16?(_System.array16$arg) } 
  $o != null && dtype($o) == Tclass._System.array16?(_System.array16$arg)
     ==> $Is(_System.array16.Length14($o), TInt));

// array16.Length14: Allocation axiom
axiom (forall _System.array16$arg: Ty, $h: Heap, $o: ref :: 
  { _System.array16.Length14($o), read($h, $o, alloc), Tclass._System.array16?(_System.array16$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array16?(_System.array16$arg)
       && read($h, $o, alloc)
     ==> $IsAlloc(_System.array16.Length14($o), TInt, $h));

function _System.array16.Length15(ref) : int;

// array16.Length15: Type axiom
axiom (forall _System.array16$arg: Ty, $o: ref :: 
  { _System.array16.Length15($o), Tclass._System.array16?(_System.array16$arg) } 
  $o != null && dtype($o) == Tclass._System.array16?(_System.array16$arg)
     ==> $Is(_System.array16.Length15($o), TInt));

// array16.Length15: Allocation axiom
axiom (forall _System.array16$arg: Ty, $h: Heap, $o: ref :: 
  { _System.array16.Length15($o), read($h, $o, alloc), Tclass._System.array16?(_System.array16$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array16?(_System.array16$arg)
       && read($h, $o, alloc)
     ==> $IsAlloc(_System.array16.Length15($o), TInt, $h));

function Tclass._System.array16(Ty) : Ty;

const unique Tagclass._System.array16: TyTag;

// Tclass._System.array16 Tag
axiom (forall _System.array16$arg: Ty :: 
  { Tclass._System.array16(_System.array16$arg) } 
  Tag(Tclass._System.array16(_System.array16$arg)) == Tagclass._System.array16
     && TagFamily(Tclass._System.array16(_System.array16$arg)) == tytagFamily$array16);

// Tclass._System.array16 injectivity 0
axiom (forall _System.array16$arg: Ty :: 
  { Tclass._System.array16(_System.array16$arg) } 
  Tclass._System.array16_0(Tclass._System.array16(_System.array16$arg))
     == _System.array16$arg);

function Tclass._System.array16_0(Ty) : Ty;

// Box/unbox axiom for Tclass._System.array16
axiom (forall _System.array16$arg: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.array16(_System.array16$arg)) } 
  $IsBox(bx, Tclass._System.array16(_System.array16$arg))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._System.array16(_System.array16$arg)));

// _System.array16: subset type $Is
axiom (forall _System.array16$arg: Ty, c#0: ref :: 
  { $Is(c#0, Tclass._System.array16(_System.array16$arg)) } 
  $Is(c#0, Tclass._System.array16(_System.array16$arg))
     <==> $Is(c#0, Tclass._System.array16?(_System.array16$arg)) && c#0 != null);

// _System.array16: subset type $IsAlloc
axiom (forall _System.array16$arg: Ty, c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._System.array16(_System.array16$arg), $h) } 
  $IsAlloc(c#0, Tclass._System.array16(_System.array16$arg), $h)
     <==> $IsAlloc(c#0, Tclass._System.array16?(_System.array16$arg), $h));

function Tclass._System.___hFunc16(Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty) : Ty;

const unique Tagclass._System.___hFunc16: TyTag;

// Tclass._System.___hFunc16 Tag
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tag(Tclass._System.___hFunc16(#$T0, 
          #$T1, 
          #$T2, 
          #$T3, 
          #$T4, 
          #$T5, 
          #$T6, 
          #$T7, 
          #$T8, 
          #$T9, 
          #$T10, 
          #$T11, 
          #$T12, 
          #$T13, 
          #$T14, 
          #$T15, 
          #$R))
       == Tagclass._System.___hFunc16
     && TagFamily(Tclass._System.___hFunc16(#$T0, 
          #$T1, 
          #$T2, 
          #$T3, 
          #$T4, 
          #$T5, 
          #$T6, 
          #$T7, 
          #$T8, 
          #$T9, 
          #$T10, 
          #$T11, 
          #$T12, 
          #$T13, 
          #$T14, 
          #$T15, 
          #$R))
       == tytagFamily$_#Func16);

// Tclass._System.___hFunc16 injectivity 0
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tclass._System.___hFunc16_0(Tclass._System.___hFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     == #$T0);

function Tclass._System.___hFunc16_0(Ty) : Ty;

// Tclass._System.___hFunc16 injectivity 1
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tclass._System.___hFunc16_1(Tclass._System.___hFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     == #$T1);

function Tclass._System.___hFunc16_1(Ty) : Ty;

// Tclass._System.___hFunc16 injectivity 2
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tclass._System.___hFunc16_2(Tclass._System.___hFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     == #$T2);

function Tclass._System.___hFunc16_2(Ty) : Ty;

// Tclass._System.___hFunc16 injectivity 3
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tclass._System.___hFunc16_3(Tclass._System.___hFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     == #$T3);

function Tclass._System.___hFunc16_3(Ty) : Ty;

// Tclass._System.___hFunc16 injectivity 4
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tclass._System.___hFunc16_4(Tclass._System.___hFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     == #$T4);

function Tclass._System.___hFunc16_4(Ty) : Ty;

// Tclass._System.___hFunc16 injectivity 5
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tclass._System.___hFunc16_5(Tclass._System.___hFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     == #$T5);

function Tclass._System.___hFunc16_5(Ty) : Ty;

// Tclass._System.___hFunc16 injectivity 6
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tclass._System.___hFunc16_6(Tclass._System.___hFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     == #$T6);

function Tclass._System.___hFunc16_6(Ty) : Ty;

// Tclass._System.___hFunc16 injectivity 7
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tclass._System.___hFunc16_7(Tclass._System.___hFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     == #$T7);

function Tclass._System.___hFunc16_7(Ty) : Ty;

// Tclass._System.___hFunc16 injectivity 8
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tclass._System.___hFunc16_8(Tclass._System.___hFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     == #$T8);

function Tclass._System.___hFunc16_8(Ty) : Ty;

// Tclass._System.___hFunc16 injectivity 9
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tclass._System.___hFunc16_9(Tclass._System.___hFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     == #$T9);

function Tclass._System.___hFunc16_9(Ty) : Ty;

// Tclass._System.___hFunc16 injectivity 10
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tclass._System.___hFunc16_10(Tclass._System.___hFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     == #$T10);

function Tclass._System.___hFunc16_10(Ty) : Ty;

// Tclass._System.___hFunc16 injectivity 11
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tclass._System.___hFunc16_11(Tclass._System.___hFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     == #$T11);

function Tclass._System.___hFunc16_11(Ty) : Ty;

// Tclass._System.___hFunc16 injectivity 12
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tclass._System.___hFunc16_12(Tclass._System.___hFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     == #$T12);

function Tclass._System.___hFunc16_12(Ty) : Ty;

// Tclass._System.___hFunc16 injectivity 13
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tclass._System.___hFunc16_13(Tclass._System.___hFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     == #$T13);

function Tclass._System.___hFunc16_13(Ty) : Ty;

// Tclass._System.___hFunc16 injectivity 14
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tclass._System.___hFunc16_14(Tclass._System.___hFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     == #$T14);

function Tclass._System.___hFunc16_14(Ty) : Ty;

// Tclass._System.___hFunc16 injectivity 15
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tclass._System.___hFunc16_15(Tclass._System.___hFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     == #$T15);

function Tclass._System.___hFunc16_15(Ty) : Ty;

// Tclass._System.___hFunc16 injectivity 16
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tclass._System.___hFunc16_16(Tclass._System.___hFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     == #$R);

function Tclass._System.___hFunc16_16(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hFunc16
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty, 
    bx: Box :: 
  { $IsBox(bx, 
      Tclass._System.___hFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R)) } 
  $IsBox(bx, 
      Tclass._System.___hFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, 
        Tclass._System.___hFunc16(#$T0, 
          #$T1, 
          #$T2, 
          #$T3, 
          #$T4, 
          #$T5, 
          #$T6, 
          #$T7, 
          #$T8, 
          #$T9, 
          #$T10, 
          #$T11, 
          #$T12, 
          #$T13, 
          #$T14, 
          #$T15, 
          #$R)));

function Handle16([Heap,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box]Box, 
    [Heap,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box]bool, 
    [Heap,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box]Set Box)
   : HandleType;

function Apply16(Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Heap, 
    HandleType, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box)
   : Box;

function Requires16(Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Heap, 
    HandleType, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box)
   : bool;

function Reads16(Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Ty, 
    Heap, 
    HandleType, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box, 
    Box)
   : Set Box;

axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    t6: Ty, 
    t7: Ty, 
    t8: Ty, 
    t9: Ty, 
    t10: Ty, 
    t11: Ty, 
    t12: Ty, 
    t13: Ty, 
    t14: Ty, 
    t15: Ty, 
    t16: Ty, 
    heap: Heap, 
    h: [Heap,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box]Box, 
    r: [Heap,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box]bool, 
    rd: [Heap,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box]Set Box, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box, 
    bx5: Box, 
    bx6: Box, 
    bx7: Box, 
    bx8: Box, 
    bx9: Box, 
    bx10: Box, 
    bx11: Box, 
    bx12: Box, 
    bx13: Box, 
    bx14: Box, 
    bx15: Box :: 
  { Apply16(t0, 
      t1, 
      t2, 
      t3, 
      t4, 
      t5, 
      t6, 
      t7, 
      t8, 
      t9, 
      t10, 
      t11, 
      t12, 
      t13, 
      t14, 
      t15, 
      t16, 
      heap, 
      Handle16(h, r, rd), 
      bx0, 
      bx1, 
      bx2, 
      bx3, 
      bx4, 
      bx5, 
      bx6, 
      bx7, 
      bx8, 
      bx9, 
      bx10, 
      bx11, 
      bx12, 
      bx13, 
      bx14, 
      bx15) } 
  Apply16(t0, 
      t1, 
      t2, 
      t3, 
      t4, 
      t5, 
      t6, 
      t7, 
      t8, 
      t9, 
      t10, 
      t11, 
      t12, 
      t13, 
      t14, 
      t15, 
      t16, 
      heap, 
      Handle16(h, r, rd), 
      bx0, 
      bx1, 
      bx2, 
      bx3, 
      bx4, 
      bx5, 
      bx6, 
      bx7, 
      bx8, 
      bx9, 
      bx10, 
      bx11, 
      bx12, 
      bx13, 
      bx14, 
      bx15)
     == h[heap, bx0, bx1, bx2, bx3, bx4, bx5, bx6, bx7, bx8, bx9, bx10, bx11, bx12, bx13, bx14, bx15]);

axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    t6: Ty, 
    t7: Ty, 
    t8: Ty, 
    t9: Ty, 
    t10: Ty, 
    t11: Ty, 
    t12: Ty, 
    t13: Ty, 
    t14: Ty, 
    t15: Ty, 
    t16: Ty, 
    heap: Heap, 
    h: [Heap,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box]Box, 
    r: [Heap,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box]bool, 
    rd: [Heap,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box]Set Box, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box, 
    bx5: Box, 
    bx6: Box, 
    bx7: Box, 
    bx8: Box, 
    bx9: Box, 
    bx10: Box, 
    bx11: Box, 
    bx12: Box, 
    bx13: Box, 
    bx14: Box, 
    bx15: Box :: 
  { Requires16(t0, 
      t1, 
      t2, 
      t3, 
      t4, 
      t5, 
      t6, 
      t7, 
      t8, 
      t9, 
      t10, 
      t11, 
      t12, 
      t13, 
      t14, 
      t15, 
      t16, 
      heap, 
      Handle16(h, r, rd), 
      bx0, 
      bx1, 
      bx2, 
      bx3, 
      bx4, 
      bx5, 
      bx6, 
      bx7, 
      bx8, 
      bx9, 
      bx10, 
      bx11, 
      bx12, 
      bx13, 
      bx14, 
      bx15) } 
  r[heap, bx0, bx1, bx2, bx3, bx4, bx5, bx6, bx7, bx8, bx9, bx10, bx11, bx12, bx13, bx14, bx15]
     ==> Requires16(t0, 
      t1, 
      t2, 
      t3, 
      t4, 
      t5, 
      t6, 
      t7, 
      t8, 
      t9, 
      t10, 
      t11, 
      t12, 
      t13, 
      t14, 
      t15, 
      t16, 
      heap, 
      Handle16(h, r, rd), 
      bx0, 
      bx1, 
      bx2, 
      bx3, 
      bx4, 
      bx5, 
      bx6, 
      bx7, 
      bx8, 
      bx9, 
      bx10, 
      bx11, 
      bx12, 
      bx13, 
      bx14, 
      bx15));

axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    t6: Ty, 
    t7: Ty, 
    t8: Ty, 
    t9: Ty, 
    t10: Ty, 
    t11: Ty, 
    t12: Ty, 
    t13: Ty, 
    t14: Ty, 
    t15: Ty, 
    t16: Ty, 
    heap: Heap, 
    h: [Heap,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box]Box, 
    r: [Heap,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box]bool, 
    rd: [Heap,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box,Box]Set Box, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box, 
    bx5: Box, 
    bx6: Box, 
    bx7: Box, 
    bx8: Box, 
    bx9: Box, 
    bx10: Box, 
    bx11: Box, 
    bx12: Box, 
    bx13: Box, 
    bx14: Box, 
    bx15: Box, 
    bx: Box :: 
  { Reads16(t0, 
      t1, 
      t2, 
      t3, 
      t4, 
      t5, 
      t6, 
      t7, 
      t8, 
      t9, 
      t10, 
      t11, 
      t12, 
      t13, 
      t14, 
      t15, 
      t16, 
      heap, 
      Handle16(h, r, rd), 
      bx0, 
      bx1, 
      bx2, 
      bx3, 
      bx4, 
      bx5, 
      bx6, 
      bx7, 
      bx8, 
      bx9, 
      bx10, 
      bx11, 
      bx12, 
      bx13, 
      bx14, 
      bx15)[bx] } 
  Reads16(t0, 
      t1, 
      t2, 
      t3, 
      t4, 
      t5, 
      t6, 
      t7, 
      t8, 
      t9, 
      t10, 
      t11, 
      t12, 
      t13, 
      t14, 
      t15, 
      t16, 
      heap, 
      Handle16(h, r, rd), 
      bx0, 
      bx1, 
      bx2, 
      bx3, 
      bx4, 
      bx5, 
      bx6, 
      bx7, 
      bx8, 
      bx9, 
      bx10, 
      bx11, 
      bx12, 
      bx13, 
      bx14, 
      bx15)[bx]
     == rd[heap, bx0, bx1, bx2, bx3, bx4, bx5, bx6, bx7, bx8, bx9, bx10, bx11, bx12, bx13, bx14, bx15][bx]);

function {:inline} Requires16#canCall(t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    t6: Ty, 
    t7: Ty, 
    t8: Ty, 
    t9: Ty, 
    t10: Ty, 
    t11: Ty, 
    t12: Ty, 
    t13: Ty, 
    t14: Ty, 
    t15: Ty, 
    t16: Ty, 
    heap: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box, 
    bx5: Box, 
    bx6: Box, 
    bx7: Box, 
    bx8: Box, 
    bx9: Box, 
    bx10: Box, 
    bx11: Box, 
    bx12: Box, 
    bx13: Box, 
    bx14: Box, 
    bx15: Box)
   : bool
{
  true
}

function {:inline} Reads16#canCall(t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    t6: Ty, 
    t7: Ty, 
    t8: Ty, 
    t9: Ty, 
    t10: Ty, 
    t11: Ty, 
    t12: Ty, 
    t13: Ty, 
    t14: Ty, 
    t15: Ty, 
    t16: Ty, 
    heap: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box, 
    bx5: Box, 
    bx6: Box, 
    bx7: Box, 
    bx8: Box, 
    bx9: Box, 
    bx10: Box, 
    bx11: Box, 
    bx12: Box, 
    bx13: Box, 
    bx14: Box, 
    bx15: Box)
   : bool
{
  true
}

// frame axiom for Reads16
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    t6: Ty, 
    t7: Ty, 
    t8: Ty, 
    t9: Ty, 
    t10: Ty, 
    t11: Ty, 
    t12: Ty, 
    t13: Ty, 
    t14: Ty, 
    t15: Ty, 
    t16: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box, 
    bx5: Box, 
    bx6: Box, 
    bx7: Box, 
    bx8: Box, 
    bx9: Box, 
    bx10: Box, 
    bx11: Box, 
    bx12: Box, 
    bx13: Box, 
    bx14: Box, 
    bx15: Box :: 
  { $HeapSucc(h0, h1), Reads16(t0, 
      t1, 
      t2, 
      t3, 
      t4, 
      t5, 
      t6, 
      t7, 
      t8, 
      t9, 
      t10, 
      t11, 
      t12, 
      t13, 
      t14, 
      t15, 
      t16, 
      h1, 
      f, 
      bx0, 
      bx1, 
      bx2, 
      bx3, 
      bx4, 
      bx5, 
      bx6, 
      bx7, 
      bx8, 
      bx9, 
      bx10, 
      bx11, 
      bx12, 
      bx13, 
      bx14, 
      bx15) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $IsBox(bx4, t4)
       && $IsBox(bx5, t5)
       && $IsBox(bx6, t6)
       && $IsBox(bx7, t7)
       && $IsBox(bx8, t8)
       && $IsBox(bx9, t9)
       && $IsBox(bx10, t10)
       && $IsBox(bx11, t11)
       && $IsBox(bx12, t12)
       && $IsBox(bx13, t13)
       && $IsBox(bx14, t14)
       && $IsBox(bx15, t15)
       && $Is(f, 
        Tclass._System.___hFunc16(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16))
       && (forall<a> o: ref, fld: Field a :: 
        o != null
             && Reads16(t0, 
              t1, 
              t2, 
              t3, 
              t4, 
              t5, 
              t6, 
              t7, 
              t8, 
              t9, 
              t10, 
              t11, 
              t12, 
              t13, 
              t14, 
              t15, 
              t16, 
              h0, 
              f, 
              bx0, 
              bx1, 
              bx2, 
              bx3, 
              bx4, 
              bx5, 
              bx6, 
              bx7, 
              bx8, 
              bx9, 
              bx10, 
              bx11, 
              bx12, 
              bx13, 
              bx14, 
              bx15)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads16(t0, 
        t1, 
        t2, 
        t3, 
        t4, 
        t5, 
        t6, 
        t7, 
        t8, 
        t9, 
        t10, 
        t11, 
        t12, 
        t13, 
        t14, 
        t15, 
        t16, 
        h0, 
        f, 
        bx0, 
        bx1, 
        bx2, 
        bx3, 
        bx4, 
        bx5, 
        bx6, 
        bx7, 
        bx8, 
        bx9, 
        bx10, 
        bx11, 
        bx12, 
        bx13, 
        bx14, 
        bx15)
       == Reads16(t0, 
        t1, 
        t2, 
        t3, 
        t4, 
        t5, 
        t6, 
        t7, 
        t8, 
        t9, 
        t10, 
        t11, 
        t12, 
        t13, 
        t14, 
        t15, 
        t16, 
        h1, 
        f, 
        bx0, 
        bx1, 
        bx2, 
        bx3, 
        bx4, 
        bx5, 
        bx6, 
        bx7, 
        bx8, 
        bx9, 
        bx10, 
        bx11, 
        bx12, 
        bx13, 
        bx14, 
        bx15));

// frame axiom for Reads16
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    t6: Ty, 
    t7: Ty, 
    t8: Ty, 
    t9: Ty, 
    t10: Ty, 
    t11: Ty, 
    t12: Ty, 
    t13: Ty, 
    t14: Ty, 
    t15: Ty, 
    t16: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box, 
    bx5: Box, 
    bx6: Box, 
    bx7: Box, 
    bx8: Box, 
    bx9: Box, 
    bx10: Box, 
    bx11: Box, 
    bx12: Box, 
    bx13: Box, 
    bx14: Box, 
    bx15: Box :: 
  { $HeapSucc(h0, h1), Reads16(t0, 
      t1, 
      t2, 
      t3, 
      t4, 
      t5, 
      t6, 
      t7, 
      t8, 
      t9, 
      t10, 
      t11, 
      t12, 
      t13, 
      t14, 
      t15, 
      t16, 
      h1, 
      f, 
      bx0, 
      bx1, 
      bx2, 
      bx3, 
      bx4, 
      bx5, 
      bx6, 
      bx7, 
      bx8, 
      bx9, 
      bx10, 
      bx11, 
      bx12, 
      bx13, 
      bx14, 
      bx15) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $IsBox(bx4, t4)
       && $IsBox(bx5, t5)
       && $IsBox(bx6, t6)
       && $IsBox(bx7, t7)
       && $IsBox(bx8, t8)
       && $IsBox(bx9, t9)
       && $IsBox(bx10, t10)
       && $IsBox(bx11, t11)
       && $IsBox(bx12, t12)
       && $IsBox(bx13, t13)
       && $IsBox(bx14, t14)
       && $IsBox(bx15, t15)
       && $Is(f, 
        Tclass._System.___hFunc16(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16))
       && (forall<a> o: ref, fld: Field a :: 
        o != null
             && Reads16(t0, 
              t1, 
              t2, 
              t3, 
              t4, 
              t5, 
              t6, 
              t7, 
              t8, 
              t9, 
              t10, 
              t11, 
              t12, 
              t13, 
              t14, 
              t15, 
              t16, 
              h1, 
              f, 
              bx0, 
              bx1, 
              bx2, 
              bx3, 
              bx4, 
              bx5, 
              bx6, 
              bx7, 
              bx8, 
              bx9, 
              bx10, 
              bx11, 
              bx12, 
              bx13, 
              bx14, 
              bx15)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads16(t0, 
        t1, 
        t2, 
        t3, 
        t4, 
        t5, 
        t6, 
        t7, 
        t8, 
        t9, 
        t10, 
        t11, 
        t12, 
        t13, 
        t14, 
        t15, 
        t16, 
        h0, 
        f, 
        bx0, 
        bx1, 
        bx2, 
        bx3, 
        bx4, 
        bx5, 
        bx6, 
        bx7, 
        bx8, 
        bx9, 
        bx10, 
        bx11, 
        bx12, 
        bx13, 
        bx14, 
        bx15)
       == Reads16(t0, 
        t1, 
        t2, 
        t3, 
        t4, 
        t5, 
        t6, 
        t7, 
        t8, 
        t9, 
        t10, 
        t11, 
        t12, 
        t13, 
        t14, 
        t15, 
        t16, 
        h1, 
        f, 
        bx0, 
        bx1, 
        bx2, 
        bx3, 
        bx4, 
        bx5, 
        bx6, 
        bx7, 
        bx8, 
        bx9, 
        bx10, 
        bx11, 
        bx12, 
        bx13, 
        bx14, 
        bx15));

// frame axiom for Requires16
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    t6: Ty, 
    t7: Ty, 
    t8: Ty, 
    t9: Ty, 
    t10: Ty, 
    t11: Ty, 
    t12: Ty, 
    t13: Ty, 
    t14: Ty, 
    t15: Ty, 
    t16: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box, 
    bx5: Box, 
    bx6: Box, 
    bx7: Box, 
    bx8: Box, 
    bx9: Box, 
    bx10: Box, 
    bx11: Box, 
    bx12: Box, 
    bx13: Box, 
    bx14: Box, 
    bx15: Box :: 
  { $HeapSucc(h0, h1), Requires16(t0, 
      t1, 
      t2, 
      t3, 
      t4, 
      t5, 
      t6, 
      t7, 
      t8, 
      t9, 
      t10, 
      t11, 
      t12, 
      t13, 
      t14, 
      t15, 
      t16, 
      h1, 
      f, 
      bx0, 
      bx1, 
      bx2, 
      bx3, 
      bx4, 
      bx5, 
      bx6, 
      bx7, 
      bx8, 
      bx9, 
      bx10, 
      bx11, 
      bx12, 
      bx13, 
      bx14, 
      bx15) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $IsBox(bx4, t4)
       && $IsBox(bx5, t5)
       && $IsBox(bx6, t6)
       && $IsBox(bx7, t7)
       && $IsBox(bx8, t8)
       && $IsBox(bx9, t9)
       && $IsBox(bx10, t10)
       && $IsBox(bx11, t11)
       && $IsBox(bx12, t12)
       && $IsBox(bx13, t13)
       && $IsBox(bx14, t14)
       && $IsBox(bx15, t15)
       && $Is(f, 
        Tclass._System.___hFunc16(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16))
       && (forall<a> o: ref, fld: Field a :: 
        o != null
             && Reads16(t0, 
              t1, 
              t2, 
              t3, 
              t4, 
              t5, 
              t6, 
              t7, 
              t8, 
              t9, 
              t10, 
              t11, 
              t12, 
              t13, 
              t14, 
              t15, 
              t16, 
              h0, 
              f, 
              bx0, 
              bx1, 
              bx2, 
              bx3, 
              bx4, 
              bx5, 
              bx6, 
              bx7, 
              bx8, 
              bx9, 
              bx10, 
              bx11, 
              bx12, 
              bx13, 
              bx14, 
              bx15)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires16(t0, 
        t1, 
        t2, 
        t3, 
        t4, 
        t5, 
        t6, 
        t7, 
        t8, 
        t9, 
        t10, 
        t11, 
        t12, 
        t13, 
        t14, 
        t15, 
        t16, 
        h0, 
        f, 
        bx0, 
        bx1, 
        bx2, 
        bx3, 
        bx4, 
        bx5, 
        bx6, 
        bx7, 
        bx8, 
        bx9, 
        bx10, 
        bx11, 
        bx12, 
        bx13, 
        bx14, 
        bx15)
       == Requires16(t0, 
        t1, 
        t2, 
        t3, 
        t4, 
        t5, 
        t6, 
        t7, 
        t8, 
        t9, 
        t10, 
        t11, 
        t12, 
        t13, 
        t14, 
        t15, 
        t16, 
        h1, 
        f, 
        bx0, 
        bx1, 
        bx2, 
        bx3, 
        bx4, 
        bx5, 
        bx6, 
        bx7, 
        bx8, 
        bx9, 
        bx10, 
        bx11, 
        bx12, 
        bx13, 
        bx14, 
        bx15));

// frame axiom for Requires16
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    t6: Ty, 
    t7: Ty, 
    t8: Ty, 
    t9: Ty, 
    t10: Ty, 
    t11: Ty, 
    t12: Ty, 
    t13: Ty, 
    t14: Ty, 
    t15: Ty, 
    t16: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box, 
    bx5: Box, 
    bx6: Box, 
    bx7: Box, 
    bx8: Box, 
    bx9: Box, 
    bx10: Box, 
    bx11: Box, 
    bx12: Box, 
    bx13: Box, 
    bx14: Box, 
    bx15: Box :: 
  { $HeapSucc(h0, h1), Requires16(t0, 
      t1, 
      t2, 
      t3, 
      t4, 
      t5, 
      t6, 
      t7, 
      t8, 
      t9, 
      t10, 
      t11, 
      t12, 
      t13, 
      t14, 
      t15, 
      t16, 
      h1, 
      f, 
      bx0, 
      bx1, 
      bx2, 
      bx3, 
      bx4, 
      bx5, 
      bx6, 
      bx7, 
      bx8, 
      bx9, 
      bx10, 
      bx11, 
      bx12, 
      bx13, 
      bx14, 
      bx15) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $IsBox(bx4, t4)
       && $IsBox(bx5, t5)
       && $IsBox(bx6, t6)
       && $IsBox(bx7, t7)
       && $IsBox(bx8, t8)
       && $IsBox(bx9, t9)
       && $IsBox(bx10, t10)
       && $IsBox(bx11, t11)
       && $IsBox(bx12, t12)
       && $IsBox(bx13, t13)
       && $IsBox(bx14, t14)
       && $IsBox(bx15, t15)
       && $Is(f, 
        Tclass._System.___hFunc16(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16))
       && (forall<a> o: ref, fld: Field a :: 
        o != null
             && Reads16(t0, 
              t1, 
              t2, 
              t3, 
              t4, 
              t5, 
              t6, 
              t7, 
              t8, 
              t9, 
              t10, 
              t11, 
              t12, 
              t13, 
              t14, 
              t15, 
              t16, 
              h1, 
              f, 
              bx0, 
              bx1, 
              bx2, 
              bx3, 
              bx4, 
              bx5, 
              bx6, 
              bx7, 
              bx8, 
              bx9, 
              bx10, 
              bx11, 
              bx12, 
              bx13, 
              bx14, 
              bx15)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires16(t0, 
        t1, 
        t2, 
        t3, 
        t4, 
        t5, 
        t6, 
        t7, 
        t8, 
        t9, 
        t10, 
        t11, 
        t12, 
        t13, 
        t14, 
        t15, 
        t16, 
        h0, 
        f, 
        bx0, 
        bx1, 
        bx2, 
        bx3, 
        bx4, 
        bx5, 
        bx6, 
        bx7, 
        bx8, 
        bx9, 
        bx10, 
        bx11, 
        bx12, 
        bx13, 
        bx14, 
        bx15)
       == Requires16(t0, 
        t1, 
        t2, 
        t3, 
        t4, 
        t5, 
        t6, 
        t7, 
        t8, 
        t9, 
        t10, 
        t11, 
        t12, 
        t13, 
        t14, 
        t15, 
        t16, 
        h1, 
        f, 
        bx0, 
        bx1, 
        bx2, 
        bx3, 
        bx4, 
        bx5, 
        bx6, 
        bx7, 
        bx8, 
        bx9, 
        bx10, 
        bx11, 
        bx12, 
        bx13, 
        bx14, 
        bx15));

// frame axiom for Apply16
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    t6: Ty, 
    t7: Ty, 
    t8: Ty, 
    t9: Ty, 
    t10: Ty, 
    t11: Ty, 
    t12: Ty, 
    t13: Ty, 
    t14: Ty, 
    t15: Ty, 
    t16: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box, 
    bx5: Box, 
    bx6: Box, 
    bx7: Box, 
    bx8: Box, 
    bx9: Box, 
    bx10: Box, 
    bx11: Box, 
    bx12: Box, 
    bx13: Box, 
    bx14: Box, 
    bx15: Box :: 
  { $HeapSucc(h0, h1), Apply16(t0, 
      t1, 
      t2, 
      t3, 
      t4, 
      t5, 
      t6, 
      t7, 
      t8, 
      t9, 
      t10, 
      t11, 
      t12, 
      t13, 
      t14, 
      t15, 
      t16, 
      h1, 
      f, 
      bx0, 
      bx1, 
      bx2, 
      bx3, 
      bx4, 
      bx5, 
      bx6, 
      bx7, 
      bx8, 
      bx9, 
      bx10, 
      bx11, 
      bx12, 
      bx13, 
      bx14, 
      bx15) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $IsBox(bx4, t4)
       && $IsBox(bx5, t5)
       && $IsBox(bx6, t6)
       && $IsBox(bx7, t7)
       && $IsBox(bx8, t8)
       && $IsBox(bx9, t9)
       && $IsBox(bx10, t10)
       && $IsBox(bx11, t11)
       && $IsBox(bx12, t12)
       && $IsBox(bx13, t13)
       && $IsBox(bx14, t14)
       && $IsBox(bx15, t15)
       && $Is(f, 
        Tclass._System.___hFunc16(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16))
       && (forall<a> o: ref, fld: Field a :: 
        o != null
             && Reads16(t0, 
              t1, 
              t2, 
              t3, 
              t4, 
              t5, 
              t6, 
              t7, 
              t8, 
              t9, 
              t10, 
              t11, 
              t12, 
              t13, 
              t14, 
              t15, 
              t16, 
              h0, 
              f, 
              bx0, 
              bx1, 
              bx2, 
              bx3, 
              bx4, 
              bx5, 
              bx6, 
              bx7, 
              bx8, 
              bx9, 
              bx10, 
              bx11, 
              bx12, 
              bx13, 
              bx14, 
              bx15)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply16(t0, 
        t1, 
        t2, 
        t3, 
        t4, 
        t5, 
        t6, 
        t7, 
        t8, 
        t9, 
        t10, 
        t11, 
        t12, 
        t13, 
        t14, 
        t15, 
        t16, 
        h0, 
        f, 
        bx0, 
        bx1, 
        bx2, 
        bx3, 
        bx4, 
        bx5, 
        bx6, 
        bx7, 
        bx8, 
        bx9, 
        bx10, 
        bx11, 
        bx12, 
        bx13, 
        bx14, 
        bx15)
       == Apply16(t0, 
        t1, 
        t2, 
        t3, 
        t4, 
        t5, 
        t6, 
        t7, 
        t8, 
        t9, 
        t10, 
        t11, 
        t12, 
        t13, 
        t14, 
        t15, 
        t16, 
        h1, 
        f, 
        bx0, 
        bx1, 
        bx2, 
        bx3, 
        bx4, 
        bx5, 
        bx6, 
        bx7, 
        bx8, 
        bx9, 
        bx10, 
        bx11, 
        bx12, 
        bx13, 
        bx14, 
        bx15));

// frame axiom for Apply16
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    t6: Ty, 
    t7: Ty, 
    t8: Ty, 
    t9: Ty, 
    t10: Ty, 
    t11: Ty, 
    t12: Ty, 
    t13: Ty, 
    t14: Ty, 
    t15: Ty, 
    t16: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box, 
    bx5: Box, 
    bx6: Box, 
    bx7: Box, 
    bx8: Box, 
    bx9: Box, 
    bx10: Box, 
    bx11: Box, 
    bx12: Box, 
    bx13: Box, 
    bx14: Box, 
    bx15: Box :: 
  { $HeapSucc(h0, h1), Apply16(t0, 
      t1, 
      t2, 
      t3, 
      t4, 
      t5, 
      t6, 
      t7, 
      t8, 
      t9, 
      t10, 
      t11, 
      t12, 
      t13, 
      t14, 
      t15, 
      t16, 
      h1, 
      f, 
      bx0, 
      bx1, 
      bx2, 
      bx3, 
      bx4, 
      bx5, 
      bx6, 
      bx7, 
      bx8, 
      bx9, 
      bx10, 
      bx11, 
      bx12, 
      bx13, 
      bx14, 
      bx15) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $IsBox(bx4, t4)
       && $IsBox(bx5, t5)
       && $IsBox(bx6, t6)
       && $IsBox(bx7, t7)
       && $IsBox(bx8, t8)
       && $IsBox(bx9, t9)
       && $IsBox(bx10, t10)
       && $IsBox(bx11, t11)
       && $IsBox(bx12, t12)
       && $IsBox(bx13, t13)
       && $IsBox(bx14, t14)
       && $IsBox(bx15, t15)
       && $Is(f, 
        Tclass._System.___hFunc16(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16))
       && (forall<a> o: ref, fld: Field a :: 
        o != null
             && Reads16(t0, 
              t1, 
              t2, 
              t3, 
              t4, 
              t5, 
              t6, 
              t7, 
              t8, 
              t9, 
              t10, 
              t11, 
              t12, 
              t13, 
              t14, 
              t15, 
              t16, 
              h1, 
              f, 
              bx0, 
              bx1, 
              bx2, 
              bx3, 
              bx4, 
              bx5, 
              bx6, 
              bx7, 
              bx8, 
              bx9, 
              bx10, 
              bx11, 
              bx12, 
              bx13, 
              bx14, 
              bx15)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply16(t0, 
        t1, 
        t2, 
        t3, 
        t4, 
        t5, 
        t6, 
        t7, 
        t8, 
        t9, 
        t10, 
        t11, 
        t12, 
        t13, 
        t14, 
        t15, 
        t16, 
        h0, 
        f, 
        bx0, 
        bx1, 
        bx2, 
        bx3, 
        bx4, 
        bx5, 
        bx6, 
        bx7, 
        bx8, 
        bx9, 
        bx10, 
        bx11, 
        bx12, 
        bx13, 
        bx14, 
        bx15)
       == Apply16(t0, 
        t1, 
        t2, 
        t3, 
        t4, 
        t5, 
        t6, 
        t7, 
        t8, 
        t9, 
        t10, 
        t11, 
        t12, 
        t13, 
        t14, 
        t15, 
        t16, 
        h1, 
        f, 
        bx0, 
        bx1, 
        bx2, 
        bx3, 
        bx4, 
        bx5, 
        bx6, 
        bx7, 
        bx8, 
        bx9, 
        bx10, 
        bx11, 
        bx12, 
        bx13, 
        bx14, 
        bx15));

// empty-reads property for Reads16 
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    t6: Ty, 
    t7: Ty, 
    t8: Ty, 
    t9: Ty, 
    t10: Ty, 
    t11: Ty, 
    t12: Ty, 
    t13: Ty, 
    t14: Ty, 
    t15: Ty, 
    t16: Ty, 
    heap: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box, 
    bx5: Box, 
    bx6: Box, 
    bx7: Box, 
    bx8: Box, 
    bx9: Box, 
    bx10: Box, 
    bx11: Box, 
    bx12: Box, 
    bx13: Box, 
    bx14: Box, 
    bx15: Box :: 
  { Reads16(t0, 
      t1, 
      t2, 
      t3, 
      t4, 
      t5, 
      t6, 
      t7, 
      t8, 
      t9, 
      t10, 
      t11, 
      t12, 
      t13, 
      t14, 
      t15, 
      t16, 
      $OneHeap, 
      f, 
      bx0, 
      bx1, 
      bx2, 
      bx3, 
      bx4, 
      bx5, 
      bx6, 
      bx7, 
      bx8, 
      bx9, 
      bx10, 
      bx11, 
      bx12, 
      bx13, 
      bx14, 
      bx15), $IsGoodHeap(heap) } 
    { Reads16(t0, 
      t1, 
      t2, 
      t3, 
      t4, 
      t5, 
      t6, 
      t7, 
      t8, 
      t9, 
      t10, 
      t11, 
      t12, 
      t13, 
      t14, 
      t15, 
      t16, 
      heap, 
      f, 
      bx0, 
      bx1, 
      bx2, 
      bx3, 
      bx4, 
      bx5, 
      bx6, 
      bx7, 
      bx8, 
      bx9, 
      bx10, 
      bx11, 
      bx12, 
      bx13, 
      bx14, 
      bx15) } 
  $IsGoodHeap(heap)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $IsBox(bx4, t4)
       && $IsBox(bx5, t5)
       && $IsBox(bx6, t6)
       && $IsBox(bx7, t7)
       && $IsBox(bx8, t8)
       && $IsBox(bx9, t9)
       && $IsBox(bx10, t10)
       && $IsBox(bx11, t11)
       && $IsBox(bx12, t12)
       && $IsBox(bx13, t13)
       && $IsBox(bx14, t14)
       && $IsBox(bx15, t15)
       && $Is(f, 
        Tclass._System.___hFunc16(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16))
     ==> (Set#Equal(Reads16(t0, 
          t1, 
          t2, 
          t3, 
          t4, 
          t5, 
          t6, 
          t7, 
          t8, 
          t9, 
          t10, 
          t11, 
          t12, 
          t13, 
          t14, 
          t15, 
          t16, 
          $OneHeap, 
          f, 
          bx0, 
          bx1, 
          bx2, 
          bx3, 
          bx4, 
          bx5, 
          bx6, 
          bx7, 
          bx8, 
          bx9, 
          bx10, 
          bx11, 
          bx12, 
          bx13, 
          bx14, 
          bx15), 
        Set#Empty(): Set Box)
       <==> Set#Equal(Reads16(t0, 
          t1, 
          t2, 
          t3, 
          t4, 
          t5, 
          t6, 
          t7, 
          t8, 
          t9, 
          t10, 
          t11, 
          t12, 
          t13, 
          t14, 
          t15, 
          t16, 
          heap, 
          f, 
          bx0, 
          bx1, 
          bx2, 
          bx3, 
          bx4, 
          bx5, 
          bx6, 
          bx7, 
          bx8, 
          bx9, 
          bx10, 
          bx11, 
          bx12, 
          bx13, 
          bx14, 
          bx15), 
        Set#Empty(): Set Box)));

// empty-reads property for Requires16
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    t6: Ty, 
    t7: Ty, 
    t8: Ty, 
    t9: Ty, 
    t10: Ty, 
    t11: Ty, 
    t12: Ty, 
    t13: Ty, 
    t14: Ty, 
    t15: Ty, 
    t16: Ty, 
    heap: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx4: Box, 
    bx5: Box, 
    bx6: Box, 
    bx7: Box, 
    bx8: Box, 
    bx9: Box, 
    bx10: Box, 
    bx11: Box, 
    bx12: Box, 
    bx13: Box, 
    bx14: Box, 
    bx15: Box :: 
  { Requires16(t0, 
      t1, 
      t2, 
      t3, 
      t4, 
      t5, 
      t6, 
      t7, 
      t8, 
      t9, 
      t10, 
      t11, 
      t12, 
      t13, 
      t14, 
      t15, 
      t16, 
      $OneHeap, 
      f, 
      bx0, 
      bx1, 
      bx2, 
      bx3, 
      bx4, 
      bx5, 
      bx6, 
      bx7, 
      bx8, 
      bx9, 
      bx10, 
      bx11, 
      bx12, 
      bx13, 
      bx14, 
      bx15), $IsGoodHeap(heap) } 
    { Requires16(t0, 
      t1, 
      t2, 
      t3, 
      t4, 
      t5, 
      t6, 
      t7, 
      t8, 
      t9, 
      t10, 
      t11, 
      t12, 
      t13, 
      t14, 
      t15, 
      t16, 
      heap, 
      f, 
      bx0, 
      bx1, 
      bx2, 
      bx3, 
      bx4, 
      bx5, 
      bx6, 
      bx7, 
      bx8, 
      bx9, 
      bx10, 
      bx11, 
      bx12, 
      bx13, 
      bx14, 
      bx15) } 
  $IsGoodHeap(heap)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $IsBox(bx4, t4)
       && $IsBox(bx5, t5)
       && $IsBox(bx6, t6)
       && $IsBox(bx7, t7)
       && $IsBox(bx8, t8)
       && $IsBox(bx9, t9)
       && $IsBox(bx10, t10)
       && $IsBox(bx11, t11)
       && $IsBox(bx12, t12)
       && $IsBox(bx13, t13)
       && $IsBox(bx14, t14)
       && $IsBox(bx15, t15)
       && $Is(f, 
        Tclass._System.___hFunc16(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16))
       && Set#Equal(Reads16(t0, 
          t1, 
          t2, 
          t3, 
          t4, 
          t5, 
          t6, 
          t7, 
          t8, 
          t9, 
          t10, 
          t11, 
          t12, 
          t13, 
          t14, 
          t15, 
          t16, 
          $OneHeap, 
          f, 
          bx0, 
          bx1, 
          bx2, 
          bx3, 
          bx4, 
          bx5, 
          bx6, 
          bx7, 
          bx8, 
          bx9, 
          bx10, 
          bx11, 
          bx12, 
          bx13, 
          bx14, 
          bx15), 
        Set#Empty(): Set Box)
     ==> Requires16(t0, 
        t1, 
        t2, 
        t3, 
        t4, 
        t5, 
        t6, 
        t7, 
        t8, 
        t9, 
        t10, 
        t11, 
        t12, 
        t13, 
        t14, 
        t15, 
        t16, 
        $OneHeap, 
        f, 
        bx0, 
        bx1, 
        bx2, 
        bx3, 
        bx4, 
        bx5, 
        bx6, 
        bx7, 
        bx8, 
        bx9, 
        bx10, 
        bx11, 
        bx12, 
        bx13, 
        bx14, 
        bx15)
       == Requires16(t0, 
        t1, 
        t2, 
        t3, 
        t4, 
        t5, 
        t6, 
        t7, 
        t8, 
        t9, 
        t10, 
        t11, 
        t12, 
        t13, 
        t14, 
        t15, 
        t16, 
        heap, 
        f, 
        bx0, 
        bx1, 
        bx2, 
        bx3, 
        bx4, 
        bx5, 
        bx6, 
        bx7, 
        bx8, 
        bx9, 
        bx10, 
        bx11, 
        bx12, 
        bx13, 
        bx14, 
        bx15));

axiom (forall f: HandleType, 
    t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    t6: Ty, 
    t7: Ty, 
    t8: Ty, 
    t9: Ty, 
    t10: Ty, 
    t11: Ty, 
    t12: Ty, 
    t13: Ty, 
    t14: Ty, 
    t15: Ty, 
    t16: Ty :: 
  { $Is(f, 
      Tclass._System.___hFunc16(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16)) } 
  $Is(f, 
      Tclass._System.___hFunc16(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16))
     <==> (forall h: Heap, 
        bx0: Box, 
        bx1: Box, 
        bx2: Box, 
        bx3: Box, 
        bx4: Box, 
        bx5: Box, 
        bx6: Box, 
        bx7: Box, 
        bx8: Box, 
        bx9: Box, 
        bx10: Box, 
        bx11: Box, 
        bx12: Box, 
        bx13: Box, 
        bx14: Box, 
        bx15: Box :: 
      { Apply16(t0, 
          t1, 
          t2, 
          t3, 
          t4, 
          t5, 
          t6, 
          t7, 
          t8, 
          t9, 
          t10, 
          t11, 
          t12, 
          t13, 
          t14, 
          t15, 
          t16, 
          h, 
          f, 
          bx0, 
          bx1, 
          bx2, 
          bx3, 
          bx4, 
          bx5, 
          bx6, 
          bx7, 
          bx8, 
          bx9, 
          bx10, 
          bx11, 
          bx12, 
          bx13, 
          bx14, 
          bx15) } 
      $IsGoodHeap(h)
           && 
          $IsBox(bx0, t0)
           && $IsBox(bx1, t1)
           && $IsBox(bx2, t2)
           && $IsBox(bx3, t3)
           && $IsBox(bx4, t4)
           && $IsBox(bx5, t5)
           && $IsBox(bx6, t6)
           && $IsBox(bx7, t7)
           && $IsBox(bx8, t8)
           && $IsBox(bx9, t9)
           && $IsBox(bx10, t10)
           && $IsBox(bx11, t11)
           && $IsBox(bx12, t12)
           && $IsBox(bx13, t13)
           && $IsBox(bx14, t14)
           && $IsBox(bx15, t15)
           && Requires16(t0, 
            t1, 
            t2, 
            t3, 
            t4, 
            t5, 
            t6, 
            t7, 
            t8, 
            t9, 
            t10, 
            t11, 
            t12, 
            t13, 
            t14, 
            t15, 
            t16, 
            h, 
            f, 
            bx0, 
            bx1, 
            bx2, 
            bx3, 
            bx4, 
            bx5, 
            bx6, 
            bx7, 
            bx8, 
            bx9, 
            bx10, 
            bx11, 
            bx12, 
            bx13, 
            bx14, 
            bx15)
         ==> $IsBox(Apply16(t0, 
            t1, 
            t2, 
            t3, 
            t4, 
            t5, 
            t6, 
            t7, 
            t8, 
            t9, 
            t10, 
            t11, 
            t12, 
            t13, 
            t14, 
            t15, 
            t16, 
            h, 
            f, 
            bx0, 
            bx1, 
            bx2, 
            bx3, 
            bx4, 
            bx5, 
            bx6, 
            bx7, 
            bx8, 
            bx9, 
            bx10, 
            bx11, 
            bx12, 
            bx13, 
            bx14, 
            bx15), 
          t16)));

axiom (forall f: HandleType, 
    t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    t6: Ty, 
    t7: Ty, 
    t8: Ty, 
    t9: Ty, 
    t10: Ty, 
    t11: Ty, 
    t12: Ty, 
    t13: Ty, 
    t14: Ty, 
    t15: Ty, 
    t16: Ty, 
    u0: Ty, 
    u1: Ty, 
    u2: Ty, 
    u3: Ty, 
    u4: Ty, 
    u5: Ty, 
    u6: Ty, 
    u7: Ty, 
    u8: Ty, 
    u9: Ty, 
    u10: Ty, 
    u11: Ty, 
    u12: Ty, 
    u13: Ty, 
    u14: Ty, 
    u15: Ty, 
    u16: Ty :: 
  { $Is(f, 
      Tclass._System.___hFunc16(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16)), $Is(f, 
      Tclass._System.___hFunc16(u0, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11, u12, u13, u14, u15, u16)) } 
  $Is(f, 
        Tclass._System.___hFunc16(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16))
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
        { $IsBox(bx, u3) } { $IsBox(bx, t3) } 
        $IsBox(bx, u3) ==> $IsBox(bx, t3))
       && (forall bx: Box :: 
        { $IsBox(bx, u4) } { $IsBox(bx, t4) } 
        $IsBox(bx, u4) ==> $IsBox(bx, t4))
       && (forall bx: Box :: 
        { $IsBox(bx, u5) } { $IsBox(bx, t5) } 
        $IsBox(bx, u5) ==> $IsBox(bx, t5))
       && (forall bx: Box :: 
        { $IsBox(bx, u6) } { $IsBox(bx, t6) } 
        $IsBox(bx, u6) ==> $IsBox(bx, t6))
       && (forall bx: Box :: 
        { $IsBox(bx, u7) } { $IsBox(bx, t7) } 
        $IsBox(bx, u7) ==> $IsBox(bx, t7))
       && (forall bx: Box :: 
        { $IsBox(bx, u8) } { $IsBox(bx, t8) } 
        $IsBox(bx, u8) ==> $IsBox(bx, t8))
       && (forall bx: Box :: 
        { $IsBox(bx, u9) } { $IsBox(bx, t9) } 
        $IsBox(bx, u9) ==> $IsBox(bx, t9))
       && (forall bx: Box :: 
        { $IsBox(bx, u10) } { $IsBox(bx, t10) } 
        $IsBox(bx, u10) ==> $IsBox(bx, t10))
       && (forall bx: Box :: 
        { $IsBox(bx, u11) } { $IsBox(bx, t11) } 
        $IsBox(bx, u11) ==> $IsBox(bx, t11))
       && (forall bx: Box :: 
        { $IsBox(bx, u12) } { $IsBox(bx, t12) } 
        $IsBox(bx, u12) ==> $IsBox(bx, t12))
       && (forall bx: Box :: 
        { $IsBox(bx, u13) } { $IsBox(bx, t13) } 
        $IsBox(bx, u13) ==> $IsBox(bx, t13))
       && (forall bx: Box :: 
        { $IsBox(bx, u14) } { $IsBox(bx, t14) } 
        $IsBox(bx, u14) ==> $IsBox(bx, t14))
       && (forall bx: Box :: 
        { $IsBox(bx, u15) } { $IsBox(bx, t15) } 
        $IsBox(bx, u15) ==> $IsBox(bx, t15))
       && (forall bx: Box :: 
        { $IsBox(bx, t16) } { $IsBox(bx, u16) } 
        $IsBox(bx, t16) ==> $IsBox(bx, u16))
     ==> $Is(f, 
      Tclass._System.___hFunc16(u0, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11, u12, u13, u14, u15, u16)));

axiom (forall f: HandleType, 
    t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    t6: Ty, 
    t7: Ty, 
    t8: Ty, 
    t9: Ty, 
    t10: Ty, 
    t11: Ty, 
    t12: Ty, 
    t13: Ty, 
    t14: Ty, 
    t15: Ty, 
    t16: Ty, 
    h: Heap :: 
  { $IsAlloc(f, 
      Tclass._System.___hFunc16(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16), 
      h) } 
  $IsGoodHeap(h)
     ==> ($IsAlloc(f, 
        Tclass._System.___hFunc16(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16), 
        h)
       <==> (forall bx0: Box, 
          bx1: Box, 
          bx2: Box, 
          bx3: Box, 
          bx4: Box, 
          bx5: Box, 
          bx6: Box, 
          bx7: Box, 
          bx8: Box, 
          bx9: Box, 
          bx10: Box, 
          bx11: Box, 
          bx12: Box, 
          bx13: Box, 
          bx14: Box, 
          bx15: Box :: 
        { Apply16(t0, 
            t1, 
            t2, 
            t3, 
            t4, 
            t5, 
            t6, 
            t7, 
            t8, 
            t9, 
            t10, 
            t11, 
            t12, 
            t13, 
            t14, 
            t15, 
            t16, 
            h, 
            f, 
            bx0, 
            bx1, 
            bx2, 
            bx3, 
            bx4, 
            bx5, 
            bx6, 
            bx7, 
            bx8, 
            bx9, 
            bx10, 
            bx11, 
            bx12, 
            bx13, 
            bx14, 
            bx15) } 
          { Reads16(t0, 
            t1, 
            t2, 
            t3, 
            t4, 
            t5, 
            t6, 
            t7, 
            t8, 
            t9, 
            t10, 
            t11, 
            t12, 
            t13, 
            t14, 
            t15, 
            t16, 
            h, 
            f, 
            bx0, 
            bx1, 
            bx2, 
            bx3, 
            bx4, 
            bx5, 
            bx6, 
            bx7, 
            bx8, 
            bx9, 
            bx10, 
            bx11, 
            bx12, 
            bx13, 
            bx14, 
            bx15) } 
        $IsBox(bx0, t0)
             && $IsAllocBox(bx0, t0, h)
             && 
            $IsBox(bx1, t1)
             && $IsAllocBox(bx1, t1, h)
             && 
            $IsBox(bx2, t2)
             && $IsAllocBox(bx2, t2, h)
             && 
            $IsBox(bx3, t3)
             && $IsAllocBox(bx3, t3, h)
             && 
            $IsBox(bx4, t4)
             && $IsAllocBox(bx4, t4, h)
             && 
            $IsBox(bx5, t5)
             && $IsAllocBox(bx5, t5, h)
             && 
            $IsBox(bx6, t6)
             && $IsAllocBox(bx6, t6, h)
             && 
            $IsBox(bx7, t7)
             && $IsAllocBox(bx7, t7, h)
             && 
            $IsBox(bx8, t8)
             && $IsAllocBox(bx8, t8, h)
             && 
            $IsBox(bx9, t9)
             && $IsAllocBox(bx9, t9, h)
             && 
            $IsBox(bx10, t10)
             && $IsAllocBox(bx10, t10, h)
             && 
            $IsBox(bx11, t11)
             && $IsAllocBox(bx11, t11, h)
             && 
            $IsBox(bx12, t12)
             && $IsAllocBox(bx12, t12, h)
             && 
            $IsBox(bx13, t13)
             && $IsAllocBox(bx13, t13, h)
             && 
            $IsBox(bx14, t14)
             && $IsAllocBox(bx14, t14, h)
             && 
            $IsBox(bx15, t15)
             && $IsAllocBox(bx15, t15, h)
             && Requires16(t0, 
              t1, 
              t2, 
              t3, 
              t4, 
              t5, 
              t6, 
              t7, 
              t8, 
              t9, 
              t10, 
              t11, 
              t12, 
              t13, 
              t14, 
              t15, 
              t16, 
              h, 
              f, 
              bx0, 
              bx1, 
              bx2, 
              bx3, 
              bx4, 
              bx5, 
              bx6, 
              bx7, 
              bx8, 
              bx9, 
              bx10, 
              bx11, 
              bx12, 
              bx13, 
              bx14, 
              bx15)
           ==> (forall r: ref :: 
            { Reads16(t0, 
                t1, 
                t2, 
                t3, 
                t4, 
                t5, 
                t6, 
                t7, 
                t8, 
                t9, 
                t10, 
                t11, 
                t12, 
                t13, 
                t14, 
                t15, 
                t16, 
                h, 
                f, 
                bx0, 
                bx1, 
                bx2, 
                bx3, 
                bx4, 
                bx5, 
                bx6, 
                bx7, 
                bx8, 
                bx9, 
                bx10, 
                bx11, 
                bx12, 
                bx13, 
                bx14, 
                bx15)[$Box(r)] } 
            r != null
                 && Reads16(t0, 
                  t1, 
                  t2, 
                  t3, 
                  t4, 
                  t5, 
                  t6, 
                  t7, 
                  t8, 
                  t9, 
                  t10, 
                  t11, 
                  t12, 
                  t13, 
                  t14, 
                  t15, 
                  t16, 
                  h, 
                  f, 
                  bx0, 
                  bx1, 
                  bx2, 
                  bx3, 
                  bx4, 
                  bx5, 
                  bx6, 
                  bx7, 
                  bx8, 
                  bx9, 
                  bx10, 
                  bx11, 
                  bx12, 
                  bx13, 
                  bx14, 
                  bx15)[$Box(r)]
               ==> read(h, r, alloc)))));

axiom (forall f: HandleType, 
    t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    t5: Ty, 
    t6: Ty, 
    t7: Ty, 
    t8: Ty, 
    t9: Ty, 
    t10: Ty, 
    t11: Ty, 
    t12: Ty, 
    t13: Ty, 
    t14: Ty, 
    t15: Ty, 
    t16: Ty, 
    h: Heap :: 
  { $IsAlloc(f, 
      Tclass._System.___hFunc16(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16), 
      h) } 
  $IsGoodHeap(h)
       && $IsAlloc(f, 
        Tclass._System.___hFunc16(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16), 
        h)
     ==> (forall bx0: Box, 
        bx1: Box, 
        bx2: Box, 
        bx3: Box, 
        bx4: Box, 
        bx5: Box, 
        bx6: Box, 
        bx7: Box, 
        bx8: Box, 
        bx9: Box, 
        bx10: Box, 
        bx11: Box, 
        bx12: Box, 
        bx13: Box, 
        bx14: Box, 
        bx15: Box :: 
      { Apply16(t0, 
          t1, 
          t2, 
          t3, 
          t4, 
          t5, 
          t6, 
          t7, 
          t8, 
          t9, 
          t10, 
          t11, 
          t12, 
          t13, 
          t14, 
          t15, 
          t16, 
          h, 
          f, 
          bx0, 
          bx1, 
          bx2, 
          bx3, 
          bx4, 
          bx5, 
          bx6, 
          bx7, 
          bx8, 
          bx9, 
          bx10, 
          bx11, 
          bx12, 
          bx13, 
          bx14, 
          bx15) } 
      $IsAllocBox(bx0, t0, h)
           && $IsAllocBox(bx1, t1, h)
           && $IsAllocBox(bx2, t2, h)
           && $IsAllocBox(bx3, t3, h)
           && $IsAllocBox(bx4, t4, h)
           && $IsAllocBox(bx5, t5, h)
           && $IsAllocBox(bx6, t6, h)
           && $IsAllocBox(bx7, t7, h)
           && $IsAllocBox(bx8, t8, h)
           && $IsAllocBox(bx9, t9, h)
           && $IsAllocBox(bx10, t10, h)
           && $IsAllocBox(bx11, t11, h)
           && $IsAllocBox(bx12, t12, h)
           && $IsAllocBox(bx13, t13, h)
           && $IsAllocBox(bx14, t14, h)
           && $IsAllocBox(bx15, t15, h)
           && Requires16(t0, 
            t1, 
            t2, 
            t3, 
            t4, 
            t5, 
            t6, 
            t7, 
            t8, 
            t9, 
            t10, 
            t11, 
            t12, 
            t13, 
            t14, 
            t15, 
            t16, 
            h, 
            f, 
            bx0, 
            bx1, 
            bx2, 
            bx3, 
            bx4, 
            bx5, 
            bx6, 
            bx7, 
            bx8, 
            bx9, 
            bx10, 
            bx11, 
            bx12, 
            bx13, 
            bx14, 
            bx15)
         ==> $IsAllocBox(Apply16(t0, 
            t1, 
            t2, 
            t3, 
            t4, 
            t5, 
            t6, 
            t7, 
            t8, 
            t9, 
            t10, 
            t11, 
            t12, 
            t13, 
            t14, 
            t15, 
            t16, 
            h, 
            f, 
            bx0, 
            bx1, 
            bx2, 
            bx3, 
            bx4, 
            bx5, 
            bx6, 
            bx7, 
            bx8, 
            bx9, 
            bx10, 
            bx11, 
            bx12, 
            bx13, 
            bx14, 
            bx15), 
          t16, 
          h)));

function Tclass._System.___hPartialFunc16(Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty) : Ty;

const unique Tagclass._System.___hPartialFunc16: TyTag;

// Tclass._System.___hPartialFunc16 Tag
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hPartialFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tag(Tclass._System.___hPartialFunc16(#$T0, 
          #$T1, 
          #$T2, 
          #$T3, 
          #$T4, 
          #$T5, 
          #$T6, 
          #$T7, 
          #$T8, 
          #$T9, 
          #$T10, 
          #$T11, 
          #$T12, 
          #$T13, 
          #$T14, 
          #$T15, 
          #$R))
       == Tagclass._System.___hPartialFunc16
     && TagFamily(Tclass._System.___hPartialFunc16(#$T0, 
          #$T1, 
          #$T2, 
          #$T3, 
          #$T4, 
          #$T5, 
          #$T6, 
          #$T7, 
          #$T8, 
          #$T9, 
          #$T10, 
          #$T11, 
          #$T12, 
          #$T13, 
          #$T14, 
          #$T15, 
          #$R))
       == tytagFamily$_#PartialFunc16);

// Tclass._System.___hPartialFunc16 injectivity 0
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hPartialFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tclass._System.___hPartialFunc16_0(Tclass._System.___hPartialFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     == #$T0);

function Tclass._System.___hPartialFunc16_0(Ty) : Ty;

// Tclass._System.___hPartialFunc16 injectivity 1
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hPartialFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tclass._System.___hPartialFunc16_1(Tclass._System.___hPartialFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     == #$T1);

function Tclass._System.___hPartialFunc16_1(Ty) : Ty;

// Tclass._System.___hPartialFunc16 injectivity 2
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hPartialFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tclass._System.___hPartialFunc16_2(Tclass._System.___hPartialFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     == #$T2);

function Tclass._System.___hPartialFunc16_2(Ty) : Ty;

// Tclass._System.___hPartialFunc16 injectivity 3
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hPartialFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tclass._System.___hPartialFunc16_3(Tclass._System.___hPartialFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     == #$T3);

function Tclass._System.___hPartialFunc16_3(Ty) : Ty;

// Tclass._System.___hPartialFunc16 injectivity 4
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hPartialFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tclass._System.___hPartialFunc16_4(Tclass._System.___hPartialFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     == #$T4);

function Tclass._System.___hPartialFunc16_4(Ty) : Ty;

// Tclass._System.___hPartialFunc16 injectivity 5
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hPartialFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tclass._System.___hPartialFunc16_5(Tclass._System.___hPartialFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     == #$T5);

function Tclass._System.___hPartialFunc16_5(Ty) : Ty;

// Tclass._System.___hPartialFunc16 injectivity 6
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hPartialFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tclass._System.___hPartialFunc16_6(Tclass._System.___hPartialFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     == #$T6);

function Tclass._System.___hPartialFunc16_6(Ty) : Ty;

// Tclass._System.___hPartialFunc16 injectivity 7
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hPartialFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tclass._System.___hPartialFunc16_7(Tclass._System.___hPartialFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     == #$T7);

function Tclass._System.___hPartialFunc16_7(Ty) : Ty;

// Tclass._System.___hPartialFunc16 injectivity 8
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hPartialFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tclass._System.___hPartialFunc16_8(Tclass._System.___hPartialFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     == #$T8);

function Tclass._System.___hPartialFunc16_8(Ty) : Ty;

// Tclass._System.___hPartialFunc16 injectivity 9
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hPartialFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tclass._System.___hPartialFunc16_9(Tclass._System.___hPartialFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     == #$T9);

function Tclass._System.___hPartialFunc16_9(Ty) : Ty;

// Tclass._System.___hPartialFunc16 injectivity 10
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hPartialFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tclass._System.___hPartialFunc16_10(Tclass._System.___hPartialFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     == #$T10);

function Tclass._System.___hPartialFunc16_10(Ty) : Ty;

// Tclass._System.___hPartialFunc16 injectivity 11
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hPartialFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tclass._System.___hPartialFunc16_11(Tclass._System.___hPartialFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     == #$T11);

function Tclass._System.___hPartialFunc16_11(Ty) : Ty;

// Tclass._System.___hPartialFunc16 injectivity 12
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hPartialFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tclass._System.___hPartialFunc16_12(Tclass._System.___hPartialFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     == #$T12);

function Tclass._System.___hPartialFunc16_12(Ty) : Ty;

// Tclass._System.___hPartialFunc16 injectivity 13
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hPartialFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tclass._System.___hPartialFunc16_13(Tclass._System.___hPartialFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     == #$T13);

function Tclass._System.___hPartialFunc16_13(Ty) : Ty;

// Tclass._System.___hPartialFunc16 injectivity 14
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hPartialFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tclass._System.___hPartialFunc16_14(Tclass._System.___hPartialFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     == #$T14);

function Tclass._System.___hPartialFunc16_14(Ty) : Ty;

// Tclass._System.___hPartialFunc16 injectivity 15
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hPartialFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tclass._System.___hPartialFunc16_15(Tclass._System.___hPartialFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     == #$T15);

function Tclass._System.___hPartialFunc16_15(Ty) : Ty;

// Tclass._System.___hPartialFunc16 injectivity 16
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hPartialFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tclass._System.___hPartialFunc16_16(Tclass._System.___hPartialFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     == #$R);

function Tclass._System.___hPartialFunc16_16(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hPartialFunc16
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty, 
    bx: Box :: 
  { $IsBox(bx, 
      Tclass._System.___hPartialFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R)) } 
  $IsBox(bx, 
      Tclass._System.___hPartialFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, 
        Tclass._System.___hPartialFunc16(#$T0, 
          #$T1, 
          #$T2, 
          #$T3, 
          #$T4, 
          #$T5, 
          #$T6, 
          #$T7, 
          #$T8, 
          #$T9, 
          #$T10, 
          #$T11, 
          #$T12, 
          #$T13, 
          #$T14, 
          #$T15, 
          #$R)));

// _System._#PartialFunc16: subset type $Is
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty, 
    f#0: HandleType :: 
  { $Is(f#0, 
      Tclass._System.___hPartialFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R)) } 
  $Is(f#0, 
      Tclass._System.___hPartialFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     <==> $Is(f#0, 
        Tclass._System.___hFunc16(#$T0, 
          #$T1, 
          #$T2, 
          #$T3, 
          #$T4, 
          #$T5, 
          #$T6, 
          #$T7, 
          #$T8, 
          #$T9, 
          #$T10, 
          #$T11, 
          #$T12, 
          #$T13, 
          #$T14, 
          #$T15, 
          #$R))
       && (forall x0#0: Box, 
          x1#0: Box, 
          x2#0: Box, 
          x3#0: Box, 
          x4#0: Box, 
          x5#0: Box, 
          x6#0: Box, 
          x7#0: Box, 
          x8#0: Box, 
          x9#0: Box, 
          x10#0: Box, 
          x11#0: Box, 
          x12#0: Box, 
          x13#0: Box, 
          x14#0: Box, 
          x15#0: Box :: 
        $IsBox(x0#0, #$T0)
             && $IsBox(x1#0, #$T1)
             && $IsBox(x2#0, #$T2)
             && $IsBox(x3#0, #$T3)
             && $IsBox(x4#0, #$T4)
             && $IsBox(x5#0, #$T5)
             && $IsBox(x6#0, #$T6)
             && $IsBox(x7#0, #$T7)
             && $IsBox(x8#0, #$T8)
             && $IsBox(x9#0, #$T9)
             && $IsBox(x10#0, #$T10)
             && $IsBox(x11#0, #$T11)
             && $IsBox(x12#0, #$T12)
             && $IsBox(x13#0, #$T13)
             && $IsBox(x14#0, #$T14)
             && $IsBox(x15#0, #$T15)
           ==> Set#Equal(Reads16(#$T0, 
              #$T1, 
              #$T2, 
              #$T3, 
              #$T4, 
              #$T5, 
              #$T6, 
              #$T7, 
              #$T8, 
              #$T9, 
              #$T10, 
              #$T11, 
              #$T12, 
              #$T13, 
              #$T14, 
              #$T15, 
              #$R, 
              $OneHeap, 
              f#0, 
              x0#0, 
              x1#0, 
              x2#0, 
              x3#0, 
              x4#0, 
              x5#0, 
              x6#0, 
              x7#0, 
              x8#0, 
              x9#0, 
              x10#0, 
              x11#0, 
              x12#0, 
              x13#0, 
              x14#0, 
              x15#0), 
            Set#Empty(): Set Box)));

// _System._#PartialFunc16: subset type $IsAlloc
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty, 
    f#0: HandleType, 
    $h: Heap :: 
  { $IsAlloc(f#0, 
      Tclass._System.___hPartialFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R), 
      $h) } 
  $IsAlloc(f#0, 
      Tclass._System.___hPartialFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R), 
      $h)
     <==> $IsAlloc(f#0, 
      Tclass._System.___hFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R), 
      $h));

function Tclass._System.___hTotalFunc16(Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty, Ty) : Ty;

const unique Tagclass._System.___hTotalFunc16: TyTag;

// Tclass._System.___hTotalFunc16 Tag
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hTotalFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tag(Tclass._System.___hTotalFunc16(#$T0, 
          #$T1, 
          #$T2, 
          #$T3, 
          #$T4, 
          #$T5, 
          #$T6, 
          #$T7, 
          #$T8, 
          #$T9, 
          #$T10, 
          #$T11, 
          #$T12, 
          #$T13, 
          #$T14, 
          #$T15, 
          #$R))
       == Tagclass._System.___hTotalFunc16
     && TagFamily(Tclass._System.___hTotalFunc16(#$T0, 
          #$T1, 
          #$T2, 
          #$T3, 
          #$T4, 
          #$T5, 
          #$T6, 
          #$T7, 
          #$T8, 
          #$T9, 
          #$T10, 
          #$T11, 
          #$T12, 
          #$T13, 
          #$T14, 
          #$T15, 
          #$R))
       == tytagFamily$_#TotalFunc16);

// Tclass._System.___hTotalFunc16 injectivity 0
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hTotalFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tclass._System.___hTotalFunc16_0(Tclass._System.___hTotalFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     == #$T0);

function Tclass._System.___hTotalFunc16_0(Ty) : Ty;

// Tclass._System.___hTotalFunc16 injectivity 1
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hTotalFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tclass._System.___hTotalFunc16_1(Tclass._System.___hTotalFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     == #$T1);

function Tclass._System.___hTotalFunc16_1(Ty) : Ty;

// Tclass._System.___hTotalFunc16 injectivity 2
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hTotalFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tclass._System.___hTotalFunc16_2(Tclass._System.___hTotalFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     == #$T2);

function Tclass._System.___hTotalFunc16_2(Ty) : Ty;

// Tclass._System.___hTotalFunc16 injectivity 3
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hTotalFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tclass._System.___hTotalFunc16_3(Tclass._System.___hTotalFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     == #$T3);

function Tclass._System.___hTotalFunc16_3(Ty) : Ty;

// Tclass._System.___hTotalFunc16 injectivity 4
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hTotalFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tclass._System.___hTotalFunc16_4(Tclass._System.___hTotalFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     == #$T4);

function Tclass._System.___hTotalFunc16_4(Ty) : Ty;

// Tclass._System.___hTotalFunc16 injectivity 5
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hTotalFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tclass._System.___hTotalFunc16_5(Tclass._System.___hTotalFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     == #$T5);

function Tclass._System.___hTotalFunc16_5(Ty) : Ty;

// Tclass._System.___hTotalFunc16 injectivity 6
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hTotalFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tclass._System.___hTotalFunc16_6(Tclass._System.___hTotalFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     == #$T6);

function Tclass._System.___hTotalFunc16_6(Ty) : Ty;

// Tclass._System.___hTotalFunc16 injectivity 7
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hTotalFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tclass._System.___hTotalFunc16_7(Tclass._System.___hTotalFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     == #$T7);

function Tclass._System.___hTotalFunc16_7(Ty) : Ty;

// Tclass._System.___hTotalFunc16 injectivity 8
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hTotalFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tclass._System.___hTotalFunc16_8(Tclass._System.___hTotalFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     == #$T8);

function Tclass._System.___hTotalFunc16_8(Ty) : Ty;

// Tclass._System.___hTotalFunc16 injectivity 9
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hTotalFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tclass._System.___hTotalFunc16_9(Tclass._System.___hTotalFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     == #$T9);

function Tclass._System.___hTotalFunc16_9(Ty) : Ty;

// Tclass._System.___hTotalFunc16 injectivity 10
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hTotalFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tclass._System.___hTotalFunc16_10(Tclass._System.___hTotalFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     == #$T10);

function Tclass._System.___hTotalFunc16_10(Ty) : Ty;

// Tclass._System.___hTotalFunc16 injectivity 11
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hTotalFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tclass._System.___hTotalFunc16_11(Tclass._System.___hTotalFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     == #$T11);

function Tclass._System.___hTotalFunc16_11(Ty) : Ty;

// Tclass._System.___hTotalFunc16 injectivity 12
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hTotalFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tclass._System.___hTotalFunc16_12(Tclass._System.___hTotalFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     == #$T12);

function Tclass._System.___hTotalFunc16_12(Ty) : Ty;

// Tclass._System.___hTotalFunc16 injectivity 13
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hTotalFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tclass._System.___hTotalFunc16_13(Tclass._System.___hTotalFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     == #$T13);

function Tclass._System.___hTotalFunc16_13(Ty) : Ty;

// Tclass._System.___hTotalFunc16 injectivity 14
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hTotalFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tclass._System.___hTotalFunc16_14(Tclass._System.___hTotalFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     == #$T14);

function Tclass._System.___hTotalFunc16_14(Ty) : Ty;

// Tclass._System.___hTotalFunc16 injectivity 15
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hTotalFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tclass._System.___hTotalFunc16_15(Tclass._System.___hTotalFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     == #$T15);

function Tclass._System.___hTotalFunc16_15(Ty) : Ty;

// Tclass._System.___hTotalFunc16 injectivity 16
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty :: 
  { Tclass._System.___hTotalFunc16(#$T0, 
      #$T1, 
      #$T2, 
      #$T3, 
      #$T4, 
      #$T5, 
      #$T6, 
      #$T7, 
      #$T8, 
      #$T9, 
      #$T10, 
      #$T11, 
      #$T12, 
      #$T13, 
      #$T14, 
      #$T15, 
      #$R) } 
  Tclass._System.___hTotalFunc16_16(Tclass._System.___hTotalFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     == #$R);

function Tclass._System.___hTotalFunc16_16(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hTotalFunc16
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty, 
    bx: Box :: 
  { $IsBox(bx, 
      Tclass._System.___hTotalFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R)) } 
  $IsBox(bx, 
      Tclass._System.___hTotalFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, 
        Tclass._System.___hTotalFunc16(#$T0, 
          #$T1, 
          #$T2, 
          #$T3, 
          #$T4, 
          #$T5, 
          #$T6, 
          #$T7, 
          #$T8, 
          #$T9, 
          #$T10, 
          #$T11, 
          #$T12, 
          #$T13, 
          #$T14, 
          #$T15, 
          #$R)));

// _System._#TotalFunc16: subset type $Is
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty, 
    f#0: HandleType :: 
  { $Is(f#0, 
      Tclass._System.___hTotalFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R)) } 
  $Is(f#0, 
      Tclass._System.___hTotalFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R))
     <==> $Is(f#0, 
        Tclass._System.___hPartialFunc16(#$T0, 
          #$T1, 
          #$T2, 
          #$T3, 
          #$T4, 
          #$T5, 
          #$T6, 
          #$T7, 
          #$T8, 
          #$T9, 
          #$T10, 
          #$T11, 
          #$T12, 
          #$T13, 
          #$T14, 
          #$T15, 
          #$R))
       && (forall x0#0: Box, 
          x1#0: Box, 
          x2#0: Box, 
          x3#0: Box, 
          x4#0: Box, 
          x5#0: Box, 
          x6#0: Box, 
          x7#0: Box, 
          x8#0: Box, 
          x9#0: Box, 
          x10#0: Box, 
          x11#0: Box, 
          x12#0: Box, 
          x13#0: Box, 
          x14#0: Box, 
          x15#0: Box :: 
        $IsBox(x0#0, #$T0)
             && $IsBox(x1#0, #$T1)
             && $IsBox(x2#0, #$T2)
             && $IsBox(x3#0, #$T3)
             && $IsBox(x4#0, #$T4)
             && $IsBox(x5#0, #$T5)
             && $IsBox(x6#0, #$T6)
             && $IsBox(x7#0, #$T7)
             && $IsBox(x8#0, #$T8)
             && $IsBox(x9#0, #$T9)
             && $IsBox(x10#0, #$T10)
             && $IsBox(x11#0, #$T11)
             && $IsBox(x12#0, #$T12)
             && $IsBox(x13#0, #$T13)
             && $IsBox(x14#0, #$T14)
             && $IsBox(x15#0, #$T15)
           ==> Requires16(#$T0, 
            #$T1, 
            #$T2, 
            #$T3, 
            #$T4, 
            #$T5, 
            #$T6, 
            #$T7, 
            #$T8, 
            #$T9, 
            #$T10, 
            #$T11, 
            #$T12, 
            #$T13, 
            #$T14, 
            #$T15, 
            #$R, 
            $OneHeap, 
            f#0, 
            x0#0, 
            x1#0, 
            x2#0, 
            x3#0, 
            x4#0, 
            x5#0, 
            x6#0, 
            x7#0, 
            x8#0, 
            x9#0, 
            x10#0, 
            x11#0, 
            x12#0, 
            x13#0, 
            x14#0, 
            x15#0)));

// _System._#TotalFunc16: subset type $IsAlloc
axiom (forall #$T0: Ty, 
    #$T1: Ty, 
    #$T2: Ty, 
    #$T3: Ty, 
    #$T4: Ty, 
    #$T5: Ty, 
    #$T6: Ty, 
    #$T7: Ty, 
    #$T8: Ty, 
    #$T9: Ty, 
    #$T10: Ty, 
    #$T11: Ty, 
    #$T12: Ty, 
    #$T13: Ty, 
    #$T14: Ty, 
    #$T15: Ty, 
    #$R: Ty, 
    f#0: HandleType, 
    $h: Heap :: 
  { $IsAlloc(f#0, 
      Tclass._System.___hTotalFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R), 
      $h) } 
  $IsAlloc(f#0, 
      Tclass._System.___hTotalFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R), 
      $h)
     <==> $IsAlloc(f#0, 
      Tclass._System.___hPartialFunc16(#$T0, 
        #$T1, 
        #$T2, 
        #$T3, 
        #$T4, 
        #$T5, 
        #$T6, 
        #$T7, 
        #$T8, 
        #$T9, 
        #$T10, 
        #$T11, 
        #$T12, 
        #$T13, 
        #$T14, 
        #$T15, 
        #$R), 
      $h));

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

const unique class._module.A?: ClassName;

function Tclass._module.A?() : Ty;

const unique Tagclass._module.A?: TyTag;

// Tclass._module.A? Tag
axiom Tag(Tclass._module.A?()) == Tagclass._module.A?
   && TagFamily(Tclass._module.A?()) == tytagFamily$A;

// Box/unbox axiom for Tclass._module.A?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.A?()) } 
  $IsBox(bx, Tclass._module.A?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.A?()));

// A: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.A?()) } 
  $Is($o, Tclass._module.A?()) <==> $o == null || dtype($o) == Tclass._module.A?());

// A: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.A?(), $h) } 
  $IsAlloc($o, Tclass._module.A?(), $h) <==> $o == null || read($h, $o, alloc));

axiom FDim(_module.A.a) == 0
   && FieldOfDecl(class._module.A?, field$a) == _module.A.a
   && !$IsGhostField(_module.A.a);

const _module.A.a: Field ref;

// A.a: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.A.a) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.A?()
     ==> $Is(read($h, $o, _module.A.a), Tclass._System.array(Tclass._System.array(TInt))));

// A.a: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.A.a) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.A?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.A.a), Tclass._System.array(Tclass._System.array(TInt)), $h));

function Tclass._module.A() : Ty;

const unique Tagclass._module.A: TyTag;

// Tclass._module.A Tag
axiom Tag(Tclass._module.A()) == Tagclass._module.A
   && TagFamily(Tclass._module.A()) == tytagFamily$A;

// Box/unbox axiom for Tclass._module.A
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.A()) } 
  $IsBox(bx, Tclass._module.A())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.A()));

procedure CheckWellformed$$_module.A.__ctor(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.A())
         && $IsAlloc(this, Tclass._module.A(), $Heap), 
    b#0: ref
       where $Is(b#0, Tclass._System.array(Tclass._System.array(TInt)))
         && $IsAlloc(b#0, Tclass._System.array(Tclass._System.array(TInt)), $Heap));
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.A.__ctor(b#0: ref
       where $Is(b#0, Tclass._System.array(Tclass._System.array(TInt)))
         && $IsAlloc(b#0, Tclass._System.array(Tclass._System.array(TInt)), $Heap))
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass._module.A())
         && $IsAlloc(this, Tclass._module.A(), $Heap));
  modifies $Heap, $Tick;
  // constructor allocates the object
  ensures !read(old($Heap), this, alloc);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.A.__ctor(b#0: ref
       where $Is(b#0, Tclass._System.array(Tclass._System.array(TInt)))
         && $IsAlloc(b#0, Tclass._System.array(Tclass._System.array(TInt)), $Heap))
   returns (this: ref where this != null && $Is(this, Tclass._module.A()), 
    $_reverifyPost: bool);
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



// _module.A: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.A()) } 
  $Is(c#0, Tclass._module.A()) <==> $Is(c#0, Tclass._module.A?()) && c#0 != null);

// _module.A: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.A(), $h) } 
  $IsAlloc(c#0, Tclass._module.A(), $h)
     <==> $IsAlloc(c#0, Tclass._module.A?(), $h));

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

procedure CheckWellformed$$_module.__default.sub(a#0: ref
       where $Is(a#0, Tclass._System.array(Tclass._System.array(TInt)))
         && $IsAlloc(a#0, Tclass._System.array(Tclass._System.array(TInt)), $Heap));
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.sub(a#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: sub, CheckWellformed$$_module.__default.sub
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(11,7): initial state"} true;
    assert a#0 != null;
    assume _System.array.Length(a#0) > 0;
    assert a#0 != null;
    assert 0 <= LitInt(0) && LitInt(0) < _System.array.Length(a#0);
    assert $Unbox(read($Heap, a#0, IndexField(LitInt(0)))): ref != null;
    assume _System.array.Length($Unbox(read($Heap, a#0, IndexField(LitInt(0)))): ref) > 0;
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
    assume $HeapSucc(old($Heap), $Heap);
}



procedure Call$$_module.__default.sub(a#0: ref
       where $Is(a#0, Tclass._System.array(Tclass._System.array(TInt)))
         && $IsAlloc(a#0, Tclass._System.array(Tclass._System.array(TInt)), $Heap));
  // user-defined preconditions
  requires _System.array.Length(a#0) > 0;
  requires _System.array.Length($Unbox(read($Heap, a#0, IndexField(LitInt(0)))): ref) > 0;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.sub(a#0: ref
       where $Is(a#0, Tclass._System.array(Tclass._System.array(TInt)))
         && $IsAlloc(a#0, Tclass._System.array(Tclass._System.array(TInt)), $Heap))
   returns ($_reverifyPost: bool);
  free requires 2 == $FunctionContextHeight;
  // user-defined preconditions
  requires _System.array.Length(a#0) > 0;
  requires _System.array.Length($Unbox(read($Heap, a#0, IndexField(LitInt(0)))): ref) > 0;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.sub(a#0: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b#0: ref
     where $Is(b#0, Tclass._System.array(Tclass._System.array(TInt)))
       && $IsAlloc(b#0, Tclass._System.array(Tclass._System.array(TInt)), $Heap);

    // AddMethodImpl: sub, Impl$$_module.__default.sub
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(14,0): initial state"} true;
    $_reverifyPost := false;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(15,3)
    assert a#0 != null;
    assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < _System.array.Length(a#0);
    assert $Unbox(read($Heap, a#0, IndexField(LitInt(0)))): ref != null;
    assert {:subsumption 0} 0 <= LitInt(0)
       && LitInt(0)
         < _System.array.Length($Unbox(read($Heap, a#0, IndexField(LitInt(0)))): ref);
    assume true;
    assume true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(16,9)
    assume true;
    assume true;
    b#0 := a#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(16,12)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(17,3)
    assert b#0 != null;
    assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < _System.array.Length(b#0);
    assert $Unbox(read($Heap, b#0, IndexField(LitInt(0)))): ref != null;
    assert {:subsumption 0} 0 <= LitInt(0)
       && LitInt(0)
         < _System.array.Length($Unbox(read($Heap, b#0, IndexField(LitInt(0)))): ref);
    assume true;
    assume true;
}



procedure CheckWellformed$$_module.__default._default_Main();
  free requires 14 == $FunctionContextHeight;
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
  free requires 14 == $FunctionContextHeight;
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
  var a#0: ref
     where $Is(a#0, Tclass._System.array(Tclass._System.array(TInt)))
       && $IsAlloc(a#0, Tclass._System.array(Tclass._System.array(TInt)), $Heap);
  var $nw: ref;
  var $rhs#0: ref where $Is($rhs#0, Tclass._System.array(TInt));
  var $rhs#1: int;
  var a##0: ref;
  var b#0: ref
     where $Is(b#0, Tclass._module.A()) && $IsAlloc(b#0, Tclass._module.A(), $Heap);
  var b##0: ref;

    // AddMethodImpl: Main, Impl$$_module.__default._default_Main
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(19,14): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(20,9)
    assume true;
    assert 0 <= LitInt(2);
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._System.array?(Tclass._System.array(TInt));
    assume !read($Heap, $nw, alloc);
    assume _System.array.Length($nw) == LitInt(2);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    a#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(20,28)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(21,8)
    assert a#0 != null;
    assert 0 <= LitInt(0) && LitInt(0) < _System.array.Length(a#0);
    assume true;
    assert $_Frame[a#0, IndexField(LitInt(0))];
    assert 0 <= LitInt(2);
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._System.array?(TInt);
    assume !read($Heap, $nw, alloc);
    assume _System.array.Length($nw) == LitInt(2);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    $rhs#0 := $nw;
    $Heap := update($Heap, a#0, IndexField(LitInt(0)), $Box($rhs#0));
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(21,20)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(22,11)
    assert a#0 != null;
    assert 0 <= LitInt(0) && LitInt(0) < _System.array.Length(a#0);
    assert $Unbox(read($Heap, a#0, IndexField(LitInt(0)))): ref != null;
    assert 0 <= LitInt(0)
       && LitInt(0)
         < _System.array.Length($Unbox(read($Heap, a#0, IndexField(LitInt(0)))): ref);
    assume true;
    assert $_Frame[$Unbox(read($Heap, a#0, IndexField(LitInt(0)))): ref, IndexField(LitInt(0))];
    assume true;
    $rhs#1 := LitInt(42);
    $Heap := update($Heap, 
      $Unbox(read($Heap, a#0, IndexField(LitInt(0)))): ref, 
      IndexField(LitInt(0)), 
      $Box($rhs#1));
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(22,15)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(23,3)
    assert a#0 != null;
    assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < _System.array.Length(a#0);
    assert $Unbox(read($Heap, a#0, IndexField(LitInt(0)))): ref != null;
    assert {:subsumption 0} 0 <= LitInt(0)
       && LitInt(0)
         < _System.array.Length($Unbox(read($Heap, a#0, IndexField(LitInt(0)))): ref);
    assume true;
    assume true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(24,6)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##0 := a#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.sub(a##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(24,8)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(25,9)
    assume true;
    // ----- init call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(25,12)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    b##0 := a#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $nw := Call$$_module.A.__ctor(b##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(25,19)"} true;
    b#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(25,19)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(26,12)
    // TrCallStmt: Before ProcessCallStmt
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.MoreTests();
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(26,13)"} true;
}



procedure CheckWellformed$$_module.__default.MoreTests();
  free requires 13 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.MoreTests();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.MoreTests() returns ($_reverifyPost: bool);
  free requires 13 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.MoreTests() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: MoreTests, Impl$$_module.__default.MoreTests
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(29,19): initial state"} true;
    $_reverifyPost := false;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(30,8)
    // TrCallStmt: Before ProcessCallStmt
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.TestA();
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(30,9)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(31,8)
    // TrCallStmt: Before ProcessCallStmt
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.TestB();
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(31,9)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(32,8)
    // TrCallStmt: Before ProcessCallStmt
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.TestC();
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(32,9)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(33,8)
    // TrCallStmt: Before ProcessCallStmt
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.TestD();
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(33,9)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(34,8)
    // TrCallStmt: Before ProcessCallStmt
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.TestE();
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(34,9)"} true;
}



procedure CheckWellformed$$_module.__default.TestA();
  free requires 7 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.TestA();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.TestA() returns ($_reverifyPost: bool);
  free requires 7 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.TestA() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var a#0: ref
     where $Is(a#0, Tclass._System.array(TInt))
       && $IsAlloc(a#0, Tclass._System.array(TInt), $Heap);
  var $nw: ref;
  var b#0: ref
     where $Is(b#0, Tclass._System.array(Tclass._System.array(TInt)))
       && $IsAlloc(b#0, Tclass._System.array(Tclass._System.array(TInt)), $Heap);
  var c#0: ref
     where $Is(c#0, Tclass._System.array(Tclass._System.array(Tclass._System.array2(TInt))))
       && $IsAlloc(c#0, 
        Tclass._System.array(Tclass._System.array(Tclass._System.array2(TInt))), 
        $Heap);
  var d#0: ref
     where $Is(d#0, Tclass._System.array(Tclass._System.array2(Tclass._System.array(TInt))))
       && $IsAlloc(d#0, 
        Tclass._System.array(Tclass._System.array2(Tclass._System.array(TInt))), 
        $Heap);
  var e#0: ref
     where $Is(e#0, Tclass._System.array(Tclass._System.array4(Tclass._System.array3(TInt))))
       && $IsAlloc(e#0, 
        Tclass._System.array(Tclass._System.array4(Tclass._System.array3(TInt))), 
        $Heap);
  var $rhs#0: int;
  var $rhs#1: ref where $Is($rhs#1, Tclass._System.array(TInt));
  var $rhs#2: int;
  var $rhs#3: ref where $Is($rhs#3, Tclass._System.array(Tclass._System.array2(TInt)));
  var $rhs#4: ref where $Is($rhs#4, Tclass._System.array2(TInt));
  var $rhs#5: int;
  var $rhs#6: ref where $Is($rhs#6, Tclass._System.array2(Tclass._System.array(TInt)));
  var $rhs#7: ref where $Is($rhs#7, Tclass._System.array(TInt));
  var $rhs#8: int;
  var $rhs#9: ref
     where $Is($rhs#9, Tclass._System.array4(Tclass._System.array3(TInt)));
  var $rhs#10: ref where $Is($rhs#10, Tclass._System.array3(TInt));
  var $rhs#11: int;

    // AddMethodImpl: TestA, Impl$$_module.__default.TestA
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(37,15): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(38,9)
    assume true;
    assert 0 <= LitInt(2);
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._System.array?(TInt);
    assume !read($Heap, $nw, alloc);
    assume _System.array.Length($nw) == LitInt(2);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    a#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(38,21)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(39,9)
    assume true;
    assert 0 <= LitInt(2);
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._System.array?(Tclass._System.array(TInt));
    assume !read($Heap, $nw, alloc);
    assume _System.array.Length($nw) == LitInt(2);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    b#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(39,28)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(40,9)
    assume true;
    assert 0 <= LitInt(2);
    havoc $nw;
    assume $nw != null
       && dtype($nw)
         == Tclass._System.array?(Tclass._System.array(Tclass._System.array2(TInt)));
    assume !read($Heap, $nw, alloc);
    assume _System.array.Length($nw) == LitInt(2);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    c#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(40,36)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(41,9)
    assume true;
    assert 0 <= LitInt(2);
    havoc $nw;
    assume $nw != null
       && dtype($nw)
         == Tclass._System.array?(Tclass._System.array2(Tclass._System.array(TInt)));
    assume !read($Heap, $nw, alloc);
    assume _System.array.Length($nw) == LitInt(2);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    d#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(41,36)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(42,9)
    assume true;
    assert 0 <= LitInt(2);
    havoc $nw;
    assume $nw != null
       && dtype($nw)
         == Tclass._System.array?(Tclass._System.array4(Tclass._System.array3(TInt)));
    assume !read($Heap, $nw, alloc);
    assume _System.array.Length($nw) == LitInt(2);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    e#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(42,37)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(43,8)
    assert a#0 != null;
    assert 0 <= LitInt(0) && LitInt(0) < _System.array.Length(a#0);
    assume true;
    assert $_Frame[a#0, IndexField(LitInt(0))];
    assume true;
    $rhs#0 := LitInt(5000);
    $Heap := update($Heap, a#0, IndexField(LitInt(0)), $Box($rhs#0));
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(43,14)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(44,8)
    assert b#0 != null;
    assert 0 <= LitInt(0) && LitInt(0) < _System.array.Length(b#0);
    assume true;
    assert $_Frame[b#0, IndexField(LitInt(0))];
    assert 0 <= LitInt(10);
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._System.array?(TInt);
    assume !read($Heap, $nw, alloc);
    assume _System.array.Length($nw) == LitInt(10);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    $rhs#1 := $nw;
    $Heap := update($Heap, b#0, IndexField(LitInt(0)), $Box($rhs#1));
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(44,21)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(45,11)
    assert b#0 != null;
    assert 0 <= LitInt(0) && LitInt(0) < _System.array.Length(b#0);
    assert $Unbox(read($Heap, b#0, IndexField(LitInt(0)))): ref != null;
    assert 0 <= LitInt(4)
       && LitInt(4)
         < _System.array.Length($Unbox(read($Heap, b#0, IndexField(LitInt(0)))): ref);
    assume true;
    assert $_Frame[$Unbox(read($Heap, b#0, IndexField(LitInt(0)))): ref, IndexField(LitInt(4))];
    assume true;
    $rhs#2 := LitInt(5000);
    $Heap := update($Heap, 
      $Unbox(read($Heap, b#0, IndexField(LitInt(0)))): ref, 
      IndexField(LitInt(4)), 
      $Box($rhs#2));
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(45,17)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(46,8)
    assert c#0 != null;
    assert 0 <= LitInt(0) && LitInt(0) < _System.array.Length(c#0);
    assume true;
    assert $_Frame[c#0, IndexField(LitInt(0))];
    assert 0 <= LitInt(10);
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._System.array?(Tclass._System.array2(TInt));
    assume !read($Heap, $nw, alloc);
    assume _System.array.Length($nw) == LitInt(10);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    $rhs#3 := $nw;
    $Heap := update($Heap, c#0, IndexField(LitInt(0)), $Box($rhs#3));
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(46,29)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(47,11)
    assert c#0 != null;
    assert 0 <= LitInt(0) && LitInt(0) < _System.array.Length(c#0);
    assert $Unbox(read($Heap, c#0, IndexField(LitInt(0)))): ref != null;
    assert 0 <= LitInt(4)
       && LitInt(4)
         < _System.array.Length($Unbox(read($Heap, c#0, IndexField(LitInt(0)))): ref);
    assume true;
    assert $_Frame[$Unbox(read($Heap, c#0, IndexField(LitInt(0)))): ref, IndexField(LitInt(4))];
    assert 0 <= LitInt(70);
    assert 0 <= LitInt(80);
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._System.array2?(TInt);
    assume !read($Heap, $nw, alloc);
    assume _System.array2.Length0($nw) == LitInt(70);
    assume _System.array2.Length1($nw) == LitInt(80);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    $rhs#4 := $nw;
    $Heap := update($Heap, 
      $Unbox(read($Heap, c#0, IndexField(LitInt(0)))): ref, 
      IndexField(LitInt(4)), 
      $Box($rhs#4));
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(47,27)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(48,18)
    assert c#0 != null;
    assert 0 <= LitInt(0) && LitInt(0) < _System.array.Length(c#0);
    assert $Unbox(read($Heap, c#0, IndexField(LitInt(0)))): ref != null;
    assert 0 <= LitInt(4)
       && LitInt(4)
         < _System.array.Length($Unbox(read($Heap, c#0, IndexField(LitInt(0)))): ref);
    assert $Unbox(read($Heap, 
          $Unbox(read($Heap, c#0, IndexField(LitInt(0)))): ref, 
          IndexField(LitInt(4)))): ref
       != null;
    assert 0 <= LitInt(63)
       && LitInt(63)
         < _System.array2.Length0($Unbox(read($Heap, 
              $Unbox(read($Heap, c#0, IndexField(LitInt(0)))): ref, 
              IndexField(LitInt(4)))): ref);
    assert 0 <= LitInt(73)
       && LitInt(73)
         < _System.array2.Length1($Unbox(read($Heap, 
              $Unbox(read($Heap, c#0, IndexField(LitInt(0)))): ref, 
              IndexField(LitInt(4)))): ref);
    assume true;
    assert $_Frame[$Unbox(read($Heap, 
        $Unbox(read($Heap, c#0, IndexField(LitInt(0)))): ref, 
        IndexField(LitInt(4)))): ref, MultiIndexField(IndexField(LitInt(63)), LitInt(73))];
    assume true;
    $rhs#5 := LitInt(5000);
    $Heap := update($Heap, 
      $Unbox(read($Heap, 
          $Unbox(read($Heap, c#0, IndexField(LitInt(0)))): ref, 
          IndexField(LitInt(4)))): ref, 
      MultiIndexField(IndexField(LitInt(63)), LitInt(73)), 
      $Box($rhs#5));
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(48,24)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(49,8)
    assert d#0 != null;
    assert 0 <= LitInt(0) && LitInt(0) < _System.array.Length(d#0);
    assume true;
    assert $_Frame[d#0, IndexField(LitInt(0))];
    assert 0 <= LitInt(70);
    assert 0 <= LitInt(80);
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._System.array2?(Tclass._System.array(TInt));
    assume !read($Heap, $nw, alloc);
    assume _System.array2.Length0($nw) == LitInt(70);
    assume _System.array2.Length1($nw) == LitInt(80);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    $rhs#6 := $nw;
    $Heap := update($Heap, d#0, IndexField(LitInt(0)), $Box($rhs#6));
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(49,31)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(50,15)
    assert d#0 != null;
    assert 0 <= LitInt(0) && LitInt(0) < _System.array.Length(d#0);
    assert $Unbox(read($Heap, d#0, IndexField(LitInt(0)))): ref != null;
    assert 0 <= LitInt(63)
       && LitInt(63)
         < _System.array2.Length0($Unbox(read($Heap, d#0, IndexField(LitInt(0)))): ref);
    assert 0 <= LitInt(73)
       && LitInt(73)
         < _System.array2.Length1($Unbox(read($Heap, d#0, IndexField(LitInt(0)))): ref);
    assume true;
    assert $_Frame[$Unbox(read($Heap, d#0, IndexField(LitInt(0)))): ref, MultiIndexField(IndexField(LitInt(63)), LitInt(73))];
    assert 0 <= LitInt(10);
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._System.array?(TInt);
    assume !read($Heap, $nw, alloc);
    assume _System.array.Length($nw) == LitInt(10);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    $rhs#7 := $nw;
    $Heap := update($Heap, 
      $Unbox(read($Heap, d#0, IndexField(LitInt(0)))): ref, 
      MultiIndexField(IndexField(LitInt(63)), LitInt(73)), 
      $Box($rhs#7));
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(50,28)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(51,18)
    assert d#0 != null;
    assert 0 <= LitInt(0) && LitInt(0) < _System.array.Length(d#0);
    assert $Unbox(read($Heap, d#0, IndexField(LitInt(0)))): ref != null;
    assert 0 <= LitInt(63)
       && LitInt(63)
         < _System.array2.Length0($Unbox(read($Heap, d#0, IndexField(LitInt(0)))): ref);
    assert 0 <= LitInt(73)
       && LitInt(73)
         < _System.array2.Length1($Unbox(read($Heap, d#0, IndexField(LitInt(0)))): ref);
    assert $Unbox(read($Heap, 
          $Unbox(read($Heap, d#0, IndexField(LitInt(0)))): ref, 
          MultiIndexField(IndexField(LitInt(63)), LitInt(73)))): ref
       != null;
    assert 0 <= LitInt(4)
       && LitInt(4)
         < _System.array.Length($Unbox(read($Heap, 
              $Unbox(read($Heap, d#0, IndexField(LitInt(0)))): ref, 
              MultiIndexField(IndexField(LitInt(63)), LitInt(73)))): ref);
    assume true;
    assert $_Frame[$Unbox(read($Heap, 
        $Unbox(read($Heap, d#0, IndexField(LitInt(0)))): ref, 
        MultiIndexField(IndexField(LitInt(63)), LitInt(73)))): ref, IndexField(LitInt(4))];
    assume true;
    $rhs#8 := LitInt(5000);
    $Heap := update($Heap, 
      $Unbox(read($Heap, 
          $Unbox(read($Heap, d#0, IndexField(LitInt(0)))): ref, 
          MultiIndexField(IndexField(LitInt(63)), LitInt(73)))): ref, 
      IndexField(LitInt(4)), 
      $Box($rhs#8));
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(51,24)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(52,8)
    assert e#0 != null;
    assert 0 <= LitInt(0) && LitInt(0) < _System.array.Length(e#0);
    assume true;
    assert $_Frame[e#0, IndexField(LitInt(0))];
    assert 0 <= LitInt(12);
    assert 0 <= LitInt(2);
    assert 0 <= LitInt(3);
    assert 0 <= LitInt(15);
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._System.array4?(Tclass._System.array3(TInt));
    assume !read($Heap, $nw, alloc);
    assume _System.array4.Length0($nw) == LitInt(12);
    assume _System.array4.Length1($nw) == LitInt(2);
    assume _System.array4.Length2($nw) == LitInt(3);
    assume _System.array4.Length3($nw) == LitInt(15);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    $rhs#9 := $nw;
    $Heap := update($Heap, e#0, IndexField(LitInt(0)), $Box($rhs#9));
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(52,36)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(53,19)
    assert e#0 != null;
    assert 0 <= LitInt(0) && LitInt(0) < _System.array.Length(e#0);
    assert $Unbox(read($Heap, e#0, IndexField(LitInt(0)))): ref != null;
    assert 0 <= LitInt(11)
       && LitInt(11)
         < _System.array4.Length0($Unbox(read($Heap, e#0, IndexField(LitInt(0)))): ref);
    assert 0 <= LitInt(1)
       && LitInt(1)
         < _System.array4.Length1($Unbox(read($Heap, e#0, IndexField(LitInt(0)))): ref);
    assert 0 <= LitInt(2)
       && LitInt(2)
         < _System.array4.Length2($Unbox(read($Heap, e#0, IndexField(LitInt(0)))): ref);
    assert 0 <= LitInt(14)
       && LitInt(14)
         < _System.array4.Length3($Unbox(read($Heap, e#0, IndexField(LitInt(0)))): ref);
    assume true;
    assert $_Frame[$Unbox(read($Heap, e#0, IndexField(LitInt(0)))): ref, MultiIndexField(MultiIndexField(MultiIndexField(IndexField(LitInt(11)), LitInt(1)), LitInt(2)), 
      LitInt(14))];
    assert 0 <= LitInt(20);
    assert 0 <= LitInt(1);
    assert 0 <= LitInt(1);
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._System.array3?(TInt);
    assume !read($Heap, $nw, alloc);
    assume _System.array3.Length0($nw) == LitInt(20);
    assume _System.array3.Length1($nw) == LitInt(1);
    assume _System.array3.Length2($nw) == LitInt(1);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    $rhs#10 := $nw;
    $Heap := update($Heap, 
      $Unbox(read($Heap, e#0, IndexField(LitInt(0)))): ref, 
      MultiIndexField(MultiIndexField(MultiIndexField(IndexField(LitInt(11)), LitInt(1)), LitInt(2)), 
        LitInt(14)), 
      $Box($rhs#10));
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(53,36)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(54,27)
    assert e#0 != null;
    assert 0 <= LitInt(0) && LitInt(0) < _System.array.Length(e#0);
    assert $Unbox(read($Heap, e#0, IndexField(LitInt(0)))): ref != null;
    assert 0 <= LitInt(11)
       && LitInt(11)
         < _System.array4.Length0($Unbox(read($Heap, e#0, IndexField(LitInt(0)))): ref);
    assert 0 <= LitInt(1)
       && LitInt(1)
         < _System.array4.Length1($Unbox(read($Heap, e#0, IndexField(LitInt(0)))): ref);
    assert 0 <= LitInt(2)
       && LitInt(2)
         < _System.array4.Length2($Unbox(read($Heap, e#0, IndexField(LitInt(0)))): ref);
    assert 0 <= LitInt(14)
       && LitInt(14)
         < _System.array4.Length3($Unbox(read($Heap, e#0, IndexField(LitInt(0)))): ref);
    assert $Unbox(read($Heap, 
          $Unbox(read($Heap, e#0, IndexField(LitInt(0)))): ref, 
          MultiIndexField(MultiIndexField(MultiIndexField(IndexField(LitInt(11)), LitInt(1)), LitInt(2)), 
            LitInt(14)))): ref
       != null;
    assert 0 <= LitInt(18)
       && LitInt(18)
         < _System.array3.Length0($Unbox(read($Heap, 
              $Unbox(read($Heap, e#0, IndexField(LitInt(0)))): ref, 
              MultiIndexField(MultiIndexField(MultiIndexField(IndexField(LitInt(11)), LitInt(1)), LitInt(2)), 
                LitInt(14)))): ref);
    assert 0 <= LitInt(0)
       && LitInt(0)
         < _System.array3.Length1($Unbox(read($Heap, 
              $Unbox(read($Heap, e#0, IndexField(LitInt(0)))): ref, 
              MultiIndexField(MultiIndexField(MultiIndexField(IndexField(LitInt(11)), LitInt(1)), LitInt(2)), 
                LitInt(14)))): ref);
    assert 0 <= LitInt(0)
       && LitInt(0)
         < _System.array3.Length2($Unbox(read($Heap, 
              $Unbox(read($Heap, e#0, IndexField(LitInt(0)))): ref, 
              MultiIndexField(MultiIndexField(MultiIndexField(IndexField(LitInt(11)), LitInt(1)), LitInt(2)), 
                LitInt(14)))): ref);
    assume true;
    assert $_Frame[$Unbox(read($Heap, 
        $Unbox(read($Heap, e#0, IndexField(LitInt(0)))): ref, 
        MultiIndexField(MultiIndexField(MultiIndexField(IndexField(LitInt(11)), LitInt(1)), LitInt(2)), 
          LitInt(14)))): ref, MultiIndexField(MultiIndexField(IndexField(LitInt(18)), LitInt(0)), LitInt(0))];
    assume true;
    $rhs#11 := LitInt(5000);
    $Heap := update($Heap, 
      $Unbox(read($Heap, 
          $Unbox(read($Heap, e#0, IndexField(LitInt(0)))): ref, 
          MultiIndexField(MultiIndexField(MultiIndexField(IndexField(LitInt(11)), LitInt(1)), LitInt(2)), 
            LitInt(14)))): ref, 
      MultiIndexField(MultiIndexField(IndexField(LitInt(18)), LitInt(0)), LitInt(0)), 
      $Box($rhs#11));
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(54,33)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(55,3)
    assert a#0 != null;
    assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < _System.array.Length(a#0);
    assume true;
    assume true;
    assert b#0 != null;
    assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < _System.array.Length(b#0);
    assert $Unbox(read($Heap, b#0, IndexField(LitInt(0)))): ref != null;
    assert {:subsumption 0} 0 <= LitInt(4)
       && LitInt(4)
         < _System.array.Length($Unbox(read($Heap, b#0, IndexField(LitInt(0)))): ref);
    assume true;
    assume true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(56,3)
    assert c#0 != null;
    assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < _System.array.Length(c#0);
    assert $Unbox(read($Heap, c#0, IndexField(LitInt(0)))): ref != null;
    assert {:subsumption 0} 0 <= LitInt(4)
       && LitInt(4)
         < _System.array.Length($Unbox(read($Heap, c#0, IndexField(LitInt(0)))): ref);
    assert $Unbox(read($Heap, 
          $Unbox(read($Heap, c#0, IndexField(LitInt(0)))): ref, 
          IndexField(LitInt(4)))): ref
       != null;
    assert {:subsumption 0} 0 <= LitInt(63)
       && LitInt(63)
         < _System.array2.Length0($Unbox(read($Heap, 
              $Unbox(read($Heap, c#0, IndexField(LitInt(0)))): ref, 
              IndexField(LitInt(4)))): ref);
    assert {:subsumption 0} 0 <= LitInt(73)
       && LitInt(73)
         < _System.array2.Length1($Unbox(read($Heap, 
              $Unbox(read($Heap, c#0, IndexField(LitInt(0)))): ref, 
              IndexField(LitInt(4)))): ref);
    assume true;
    assume true;
    assert d#0 != null;
    assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < _System.array.Length(d#0);
    assert $Unbox(read($Heap, d#0, IndexField(LitInt(0)))): ref != null;
    assert {:subsumption 0} 0 <= LitInt(63)
       && LitInt(63)
         < _System.array2.Length0($Unbox(read($Heap, d#0, IndexField(LitInt(0)))): ref);
    assert {:subsumption 0} 0 <= LitInt(73)
       && LitInt(73)
         < _System.array2.Length1($Unbox(read($Heap, d#0, IndexField(LitInt(0)))): ref);
    assert $Unbox(read($Heap, 
          $Unbox(read($Heap, d#0, IndexField(LitInt(0)))): ref, 
          MultiIndexField(IndexField(LitInt(63)), LitInt(73)))): ref
       != null;
    assert {:subsumption 0} 0 <= LitInt(4)
       && LitInt(4)
         < _System.array.Length($Unbox(read($Heap, 
              $Unbox(read($Heap, d#0, IndexField(LitInt(0)))): ref, 
              MultiIndexField(IndexField(LitInt(63)), LitInt(73)))): ref);
    assume true;
    assume true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(57,3)
    assert e#0 != null;
    assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < _System.array.Length(e#0);
    assert $Unbox(read($Heap, e#0, IndexField(LitInt(0)))): ref != null;
    assert {:subsumption 0} 0 <= LitInt(11)
       && LitInt(11)
         < _System.array4.Length0($Unbox(read($Heap, e#0, IndexField(LitInt(0)))): ref);
    assert {:subsumption 0} 0 <= LitInt(1)
       && LitInt(1)
         < _System.array4.Length1($Unbox(read($Heap, e#0, IndexField(LitInt(0)))): ref);
    assert {:subsumption 0} 0 <= LitInt(2)
       && LitInt(2)
         < _System.array4.Length2($Unbox(read($Heap, e#0, IndexField(LitInt(0)))): ref);
    assert {:subsumption 0} 0 <= LitInt(14)
       && LitInt(14)
         < _System.array4.Length3($Unbox(read($Heap, e#0, IndexField(LitInt(0)))): ref);
    assert $Unbox(read($Heap, 
          $Unbox(read($Heap, e#0, IndexField(LitInt(0)))): ref, 
          MultiIndexField(MultiIndexField(MultiIndexField(IndexField(LitInt(11)), LitInt(1)), LitInt(2)), 
            LitInt(14)))): ref
       != null;
    assert {:subsumption 0} 0 <= LitInt(18)
       && LitInt(18)
         < _System.array3.Length0($Unbox(read($Heap, 
              $Unbox(read($Heap, e#0, IndexField(LitInt(0)))): ref, 
              MultiIndexField(MultiIndexField(MultiIndexField(IndexField(LitInt(11)), LitInt(1)), LitInt(2)), 
                LitInt(14)))): ref);
    assert {:subsumption 0} 0 <= LitInt(0)
       && LitInt(0)
         < _System.array3.Length1($Unbox(read($Heap, 
              $Unbox(read($Heap, e#0, IndexField(LitInt(0)))): ref, 
              MultiIndexField(MultiIndexField(MultiIndexField(IndexField(LitInt(11)), LitInt(1)), LitInt(2)), 
                LitInt(14)))): ref);
    assert {:subsumption 0} 0 <= LitInt(0)
       && LitInt(0)
         < _System.array3.Length2($Unbox(read($Heap, 
              $Unbox(read($Heap, e#0, IndexField(LitInt(0)))): ref, 
              MultiIndexField(MultiIndexField(MultiIndexField(IndexField(LitInt(11)), LitInt(1)), LitInt(2)), 
                LitInt(14)))): ref);
    assume true;
    assume true;
}



procedure CheckWellformed$$_module.__default.TestB();
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.TestB();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.TestB() returns ($_reverifyPost: bool);
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.TestB() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var a#0: ref
     where $Is(a#0, Tclass._System.array2(TInt))
       && $IsAlloc(a#0, Tclass._System.array2(TInt), $Heap);
  var $nw: ref;
  var b#0: ref
     where $Is(b#0, Tclass._System.array2(Tclass._System.array(TInt)))
       && $IsAlloc(b#0, Tclass._System.array2(Tclass._System.array(TInt)), $Heap);
  var c#0: ref
     where $Is(c#0, Tclass._System.array2(Tclass._System.array(Tclass._System.array2(TInt))))
       && $IsAlloc(c#0, 
        Tclass._System.array2(Tclass._System.array(Tclass._System.array2(TInt))), 
        $Heap);
  var d#0: ref
     where $Is(d#0, Tclass._System.array2(Tclass._System.array2(Tclass._System.array(TInt))))
       && $IsAlloc(d#0, 
        Tclass._System.array2(Tclass._System.array2(Tclass._System.array(TInt))), 
        $Heap);
  var e#0: ref
     where $Is(e#0, Tclass._System.array2(Tclass._System.array4(Tclass._System.array3(TInt))))
       && $IsAlloc(e#0, 
        Tclass._System.array2(Tclass._System.array4(Tclass._System.array3(TInt))), 
        $Heap);

    // AddMethodImpl: TestB, Impl$$_module.__default.TestB
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(60,15): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(61,9)
    assume true;
    assert 0 <= LitInt(2);
    assert 0 <= LitInt(3);
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._System.array2?(TInt);
    assume !read($Heap, $nw, alloc);
    assume _System.array2.Length0($nw) == LitInt(2);
    assume _System.array2.Length1($nw) == LitInt(3);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    a#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(61,23)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(62,9)
    assume true;
    assert 0 <= LitInt(2);
    assert 0 <= LitInt(3);
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._System.array2?(Tclass._System.array(TInt));
    assume !read($Heap, $nw, alloc);
    assume _System.array2.Length0($nw) == LitInt(2);
    assume _System.array2.Length1($nw) == LitInt(3);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    b#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(62,30)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(63,9)
    assume true;
    assert 0 <= LitInt(2);
    assert 0 <= LitInt(3);
    havoc $nw;
    assume $nw != null
       && dtype($nw)
         == Tclass._System.array2?(Tclass._System.array(Tclass._System.array2(TInt)));
    assume !read($Heap, $nw, alloc);
    assume _System.array2.Length0($nw) == LitInt(2);
    assume _System.array2.Length1($nw) == LitInt(3);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    c#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(63,38)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(64,9)
    assume true;
    assert 0 <= LitInt(2);
    assert 0 <= LitInt(3);
    havoc $nw;
    assume $nw != null
       && dtype($nw)
         == Tclass._System.array2?(Tclass._System.array2(Tclass._System.array(TInt)));
    assume !read($Heap, $nw, alloc);
    assume _System.array2.Length0($nw) == LitInt(2);
    assume _System.array2.Length1($nw) == LitInt(3);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    d#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(64,38)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(65,9)
    assume true;
    assert 0 <= LitInt(2);
    assert 0 <= LitInt(3);
    havoc $nw;
    assume $nw != null
       && dtype($nw)
         == Tclass._System.array2?(Tclass._System.array4(Tclass._System.array3(TInt)));
    assume !read($Heap, $nw, alloc);
    assume _System.array2.Length0($nw) == LitInt(2);
    assume _System.array2.Length1($nw) == LitInt(3);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    e#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(65,39)"} true;
}



procedure CheckWellformed$$_module.__default.TestC();
  free requires 9 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.TestC();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.TestC() returns ($_reverifyPost: bool);
  free requires 9 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.TestC() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var a#0: ref
     where $Is(a#0, Tclass._System.array(TInt))
       && $IsAlloc(a#0, Tclass._System.array(TInt), $Heap);
  var $nw: ref;
  var b#0: ref
     where $Is(b#0, Tclass._System.array(Tclass._System.array?(TInt)))
       && $IsAlloc(b#0, Tclass._System.array(Tclass._System.array?(TInt)), $Heap);
  var c#0: ref
     where $Is(c#0, Tclass._System.array(Tclass._System.array?(Tclass._System.array2?(TInt))))
       && $IsAlloc(c#0, 
        Tclass._System.array(Tclass._System.array?(Tclass._System.array2?(TInt))), 
        $Heap);
  var d#0: ref
     where $Is(d#0, Tclass._System.array(Tclass._System.array2?(Tclass._System.array?(TInt))))
       && $IsAlloc(d#0, 
        Tclass._System.array(Tclass._System.array2?(Tclass._System.array?(TInt))), 
        $Heap);
  var e#0: ref
     where $Is(e#0, Tclass._System.array(Tclass._System.array4?(Tclass._System.array3?(TInt))))
       && $IsAlloc(e#0, 
        Tclass._System.array(Tclass._System.array4?(Tclass._System.array3?(TInt))), 
        $Heap);

    // AddMethodImpl: TestC, Impl$$_module.__default.TestC
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(68,15): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(69,9)
    assume true;
    assert 0 <= LitInt(2);
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._System.array?(TInt);
    assume !read($Heap, $nw, alloc);
    assume _System.array.Length($nw) == LitInt(2);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    a#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(69,21)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(70,9)
    assume true;
    assert 0 <= LitInt(2);
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._System.array?(Tclass._System.array?(TInt));
    assume !read($Heap, $nw, alloc);
    assume _System.array.Length($nw) == LitInt(2);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    b#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(70,29)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(71,9)
    assume true;
    assert 0 <= LitInt(2);
    havoc $nw;
    assume $nw != null
       && dtype($nw)
         == Tclass._System.array?(Tclass._System.array?(Tclass._System.array2?(TInt)));
    assume !read($Heap, $nw, alloc);
    assume _System.array.Length($nw) == LitInt(2);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    c#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(71,38)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(72,9)
    assume true;
    assert 0 <= LitInt(2);
    havoc $nw;
    assume $nw != null
       && dtype($nw)
         == Tclass._System.array?(Tclass._System.array2?(Tclass._System.array?(TInt)));
    assume !read($Heap, $nw, alloc);
    assume _System.array.Length($nw) == LitInt(2);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    d#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(72,38)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(73,9)
    assume true;
    assert 0 <= LitInt(2);
    havoc $nw;
    assume $nw != null
       && dtype($nw)
         == Tclass._System.array?(Tclass._System.array4?(Tclass._System.array3?(TInt)));
    assume !read($Heap, $nw, alloc);
    assume _System.array.Length($nw) == LitInt(2);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    e#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(73,39)"} true;
}



procedure CheckWellformed$$_module.__default.TestD();
  free requires 10 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.TestD();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.TestD() returns ($_reverifyPost: bool);
  free requires 10 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.TestD() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var a#0: ref
     where $Is(a#0, Tclass._System.array2(TInt))
       && $IsAlloc(a#0, Tclass._System.array2(TInt), $Heap);
  var $nw: ref;
  var b#0: ref
     where $Is(b#0, Tclass._System.array(Tclass._System.array2(TInt)))
       && $IsAlloc(b#0, Tclass._System.array(Tclass._System.array2(TInt)), $Heap);
  var _v0#0: int;
  var $oldHeap#0: Heap;
  var $_Frame#l0: <beta>[ref,Field beta]bool;
  var lambdaResult#0: ref;
  var c#0: ref
     where $Is(c#0, Tclass._System.array3(Tclass._System.array(Tclass._System.array2(TInt))))
       && $IsAlloc(c#0, 
        Tclass._System.array3(Tclass._System.array(Tclass._System.array2(TInt))), 
        $Heap);
  var _v1#0: int;
  var _v2#0: int;
  var _v3#0: int;
  var $oldHeap#1: Heap;
  var $_Frame#l1: <beta>[ref,Field beta]bool;
  var lambdaResult#1: ref;

    // AddMethodImpl: TestD, Impl$$_module.__default.TestD
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(76,15): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(77,22)
    assume true;
    assert 0 <= LitInt(3);
    assert 0 <= LitInt(2);
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._System.array2?(TInt);
    assume !read($Heap, $nw, alloc);
    assume _System.array2.Length0($nw) == LitInt(3);
    assume _System.array2.Length1($nw) == LitInt(2);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    a#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(77,36)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(78,29)
    assume true;
    assert 0 <= LitInt(5);
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._System.array?(Tclass._System.array2(TInt));
    assume !read($Heap, $nw, alloc);
    assume _System.array.Length($nw) == LitInt(5);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    b#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(78,49)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(79,5)
    assume true;
    assert 0 <= LitInt(5);
    assert LitInt(5) == 5;
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._System.array?(Tclass._System.array2(TInt));
    assume !read($Heap, $nw, alloc);
    assume _System.array.Length($nw) == LitInt(5);
    assume $Unbox(read($Heap, $nw, IndexField(0))): ref == a#0;
    assume $Unbox(read($Heap, $nw, IndexField(1))): ref == a#0;
    assume $Unbox(read($Heap, $nw, IndexField(2))): ref == a#0;
    assume $Unbox(read($Heap, $nw, IndexField(3))): ref == a#0;
    assume $Unbox(read($Heap, $nw, IndexField(4))): ref == a#0;
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    b#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(79,40)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(80,5)
    assume true;
    assert 0 <= LitInt(5);
    // Begin Comprehension WF check
    if (*)
    {
        havoc _v0#0;
        if (LitInt(0) <= _v0#0)
        {
            $oldHeap#0 := $Heap;
            havoc $Heap;
            assume $IsGoodHeap($Heap);
            assume $oldHeap#0 == $Heap || $HeapSucc($oldHeap#0, $Heap);
            $_Frame#l0 := (lambda<alpha> $o: ref, $f: Field alpha :: 
              $o != null && read($Heap, $o, alloc) ==> false);
            assume lambdaResult#0 == a#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(lambdaResult#0, Tclass._System.array2(TInt));
        }

        assume false;
    }

    // End Comprehension WF check
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._System.array?(Tclass._System.array2(TInt));
    assume !read($Heap, $nw, alloc);
    assume _System.array.Length($nw) == LitInt(5);
    assert {:subsumption 0} (forall arrayinit#0#i0#0: int :: 
      0 <= arrayinit#0#i0#0 && arrayinit#0#i0#0 < LitInt(5)
         ==> Requires1(Tclass._System.nat(), 
          Tclass._System.array2(TInt), 
          $Heap, 
          Lit(AtLayer((lambda $l#0#ly#0: LayerType :: 
                Handle1((lambda $l#0#heap#0: Heap, $l#0#_v0#0: Box :: $Box(a#0)), 
                  (lambda $l#0#heap#0: Heap, $l#0#_v0#0: Box :: 
                    $IsBox($l#0#_v0#0, Tclass._System.nat())), 
                  (lambda $l#0#heap#0: Heap, $l#0#_v0#0: Box :: 
                    SetRef_to_SetBox((lambda $l#0#o#0: ref :: false))))), 
              $LS($LZ))), 
          $Box(arrayinit#0#i0#0)));
    assume (forall arrayinit#0#i0#0: int :: 
      { read($Heap, $nw, IndexField(arrayinit#0#i0#0)) } 
      0 <= arrayinit#0#i0#0 && arrayinit#0#i0#0 < LitInt(5)
         ==> $Unbox(read($Heap, $nw, IndexField(arrayinit#0#i0#0))): ref
           == $Unbox(Apply1(Tclass._System.nat(), 
              Tclass._System.array2(TInt), 
              $Heap, 
              Lit(AtLayer((lambda $l#0#ly#0: LayerType :: 
                    Handle1((lambda $l#0#heap#0: Heap, $l#0#_v0#0: Box :: $Box(a#0)), 
                      (lambda $l#0#heap#0: Heap, $l#0#_v0#0: Box :: 
                        $IsBox($l#0#_v0#0, Tclass._System.nat())), 
                      (lambda $l#0#heap#0: Heap, $l#0#_v0#0: Box :: 
                        SetRef_to_SetBox((lambda $l#0#o#0: ref :: false))))), 
                  $LS($LZ))), 
              $Box(arrayinit#0#i0#0))): ref);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    b#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(80,33)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(81,37)
    assume true;
    assert 0 <= LitInt(5);
    assert 0 <= LitInt(4);
    assert 0 <= LitInt(3);
    havoc $nw;
    assume $nw != null
       && dtype($nw)
         == Tclass._System.array3?(Tclass._System.array(Tclass._System.array2(TInt)));
    assume !read($Heap, $nw, alloc);
    assume _System.array3.Length0($nw) == LitInt(5);
    assume _System.array3.Length1($nw) == LitInt(4);
    assume _System.array3.Length2($nw) == LitInt(3);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    c#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(81,68)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(82,5)
    assume true;
    assert 0 <= LitInt(5);
    assert 0 <= LitInt(4);
    assert 0 <= LitInt(3);
    // Begin Comprehension WF check
    if (*)
    {
        havoc _v1#0;
        havoc _v2#0;
        havoc _v3#0;
        if (LitInt(0) <= _v1#0)
        {
            $oldHeap#1 := $Heap;
            havoc $Heap;
            assume $IsGoodHeap($Heap);
            assume $oldHeap#1 == $Heap || $HeapSucc($oldHeap#1, $Heap);
            $_Frame#l1 := (lambda<alpha> $o: ref, $f: Field alpha :: 
              $o != null && read($Heap, $o, alloc) ==> false);
            assume lambdaResult#1 == b#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(lambdaResult#1, Tclass._System.array(Tclass._System.array2(TInt)));
        }

        assume false;
    }

    // End Comprehension WF check
    havoc $nw;
    assume $nw != null
       && dtype($nw)
         == Tclass._System.array3?(Tclass._System.array(Tclass._System.array2(TInt)));
    assume !read($Heap, $nw, alloc);
    assume _System.array3.Length0($nw) == LitInt(5);
    assume _System.array3.Length1($nw) == LitInt(4);
    assume _System.array3.Length2($nw) == LitInt(3);
    assert {:subsumption 0} (forall arrayinit#1#i0#0: int, arrayinit#1#i1#0: int, arrayinit#1#i2#0: int :: 
      0 <= arrayinit#1#i0#0
           && arrayinit#1#i0#0 < LitInt(5)
           && 
          0 <= arrayinit#1#i1#0
           && arrayinit#1#i1#0 < LitInt(4)
           && 
          0 <= arrayinit#1#i2#0
           && arrayinit#1#i2#0 < LitInt(3)
         ==> Requires3(Tclass._System.nat(), 
          TInt, 
          TInt, 
          Tclass._System.array(Tclass._System.array2(TInt)), 
          $Heap, 
          Lit(AtLayer((lambda $l#1#ly#0: LayerType :: 
                Handle3((lambda $l#1#heap#0: Heap, $l#1#_v1#0: Box, $l#1#_v2#0: Box, $l#1#_v3#0: Box :: 
                    $Box(b#0)), 
                  (lambda $l#1#heap#0: Heap, $l#1#_v1#0: Box, $l#1#_v2#0: Box, $l#1#_v3#0: Box :: 
                    $IsBox($l#1#_v1#0, Tclass._System.nat())
                       && $IsBox($l#1#_v2#0, TInt)
                       && $IsBox($l#1#_v3#0, TInt)), 
                  (lambda $l#1#heap#0: Heap, $l#1#_v1#0: Box, $l#1#_v2#0: Box, $l#1#_v3#0: Box :: 
                    SetRef_to_SetBox((lambda $l#1#o#0: ref :: false))))), 
              $LS($LZ))), 
          $Box(arrayinit#1#i0#0), 
          $Box(arrayinit#1#i1#0), 
          $Box(arrayinit#1#i2#0)));
    assume (forall arrayinit#1#i0#0: int, arrayinit#1#i1#0: int, arrayinit#1#i2#0: int :: 
      { read($Heap, 
          $nw, 
          MultiIndexField(MultiIndexField(IndexField(arrayinit#1#i0#0), arrayinit#1#i1#0), 
            arrayinit#1#i2#0)) } 
      0 <= arrayinit#1#i0#0
           && arrayinit#1#i0#0 < LitInt(5)
           && 
          0 <= arrayinit#1#i1#0
           && arrayinit#1#i1#0 < LitInt(4)
           && 
          0 <= arrayinit#1#i2#0
           && arrayinit#1#i2#0 < LitInt(3)
         ==> $Unbox(read($Heap, 
              $nw, 
              MultiIndexField(MultiIndexField(IndexField(arrayinit#1#i0#0), arrayinit#1#i1#0), 
                arrayinit#1#i2#0))): ref
           == $Unbox(Apply3(Tclass._System.nat(), 
              TInt, 
              TInt, 
              Tclass._System.array(Tclass._System.array2(TInt)), 
              $Heap, 
              Lit(AtLayer((lambda $l#1#ly#0: LayerType :: 
                    Handle3((lambda $l#1#heap#0: Heap, $l#1#_v1#0: Box, $l#1#_v2#0: Box, $l#1#_v3#0: Box :: 
                        $Box(b#0)), 
                      (lambda $l#1#heap#0: Heap, $l#1#_v1#0: Box, $l#1#_v2#0: Box, $l#1#_v3#0: Box :: 
                        $IsBox($l#1#_v1#0, Tclass._System.nat())
                           && $IsBox($l#1#_v2#0, TInt)
                           && $IsBox($l#1#_v3#0, TInt)), 
                      (lambda $l#1#heap#0: Heap, $l#1#_v1#0: Box, $l#1#_v2#0: Box, $l#1#_v3#0: Box :: 
                        SetRef_to_SetBox((lambda $l#1#o#0: ref :: false))))), 
                  $LS($LZ))), 
              $Box(arrayinit#1#i0#0), 
              $Box(arrayinit#1#i1#0), 
              $Box(arrayinit#1#i2#0))): ref);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    c#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(82,50)"} true;
}



procedure CheckWellformed$$_module.__default.TestE();
  free requires 12 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.TestE();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.TestE() returns ($_reverifyPost: bool);
  free requires 12 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.TestE() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var a#0: ref
     where $Is(a#0, Tclass._System.array2?(TInt))
       && $IsAlloc(a#0, Tclass._System.array2?(TInt), $Heap);
  var $nw: ref;
  var b#0: ref
     where $Is(b#0, Tclass._System.array?(Tclass._System.array2?(TInt)))
       && $IsAlloc(b#0, Tclass._System.array?(Tclass._System.array2?(TInt)), $Heap);
  var _v4#0: int;
  var $oldHeap#0: Heap;
  var $_Frame#l0: <beta>[ref,Field beta]bool;
  var lambdaResult#0: ref;
  var c#0: ref
     where $Is(c#0, Tclass._System.array3?(Tclass._System.array?(Tclass._System.array2?(TInt))))
       && $IsAlloc(c#0, 
        Tclass._System.array3?(Tclass._System.array?(Tclass._System.array2?(TInt))), 
        $Heap);
  var _v5#0: int;
  var _v6#0: int;
  var _v7#0: int;
  var $oldHeap#1: Heap;
  var $_Frame#l1: <beta>[ref,Field beta]bool;
  var lambdaResult#1: ref;
  var d#0: ref
     where $Is(d#0, Tclass._System.array15?(TInt))
       && $IsAlloc(d#0, Tclass._System.array15?(TInt), $Heap);
  var e#0: ref
     where $Is(e#0, Tclass._System.array16(TInt))
       && $IsAlloc(e#0, Tclass._System.array16(TInt), $Heap);

    // AddMethodImpl: TestE, Impl$$_module.__default.TestE
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(85,15): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(86,23)
    assume true;
    assert 0 <= LitInt(3);
    assert 0 <= LitInt(2);
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._System.array2?(TInt);
    assume !read($Heap, $nw, alloc);
    assume _System.array2.Length0($nw) == LitInt(3);
    assume _System.array2.Length1($nw) == LitInt(2);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    a#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(86,37)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(87,31)
    assume true;
    assert 0 <= LitInt(5);
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._System.array?(Tclass._System.array2?(TInt));
    assume !read($Heap, $nw, alloc);
    assume _System.array.Length($nw) == LitInt(5);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    b#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(87,52)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(88,5)
    assume true;
    assert 0 <= LitInt(5);
    assert LitInt(5) == 5;
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._System.array?(Tclass._System.array2?(TInt));
    assume !read($Heap, $nw, alloc);
    assume _System.array.Length($nw) == LitInt(5);
    assume $Unbox(read($Heap, $nw, IndexField(0))): ref == a#0;
    assume $Unbox(read($Heap, $nw, IndexField(1))): ref == a#0;
    assume $Unbox(read($Heap, $nw, IndexField(2))): ref == a#0;
    assume $Unbox(read($Heap, $nw, IndexField(3))): ref == a#0;
    assume $Unbox(read($Heap, $nw, IndexField(4))): ref == a#0;
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    b#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(88,41)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(89,5)
    assume true;
    assert 0 <= LitInt(5);
    // Begin Comprehension WF check
    if (*)
    {
        havoc _v4#0;
        if (LitInt(0) <= _v4#0)
        {
            $oldHeap#0 := $Heap;
            havoc $Heap;
            assume $IsGoodHeap($Heap);
            assume $oldHeap#0 == $Heap || $HeapSucc($oldHeap#0, $Heap);
            $_Frame#l0 := (lambda<alpha> $o: ref, $f: Field alpha :: 
              $o != null && read($Heap, $o, alloc) ==> false);
            assume lambdaResult#0 == a#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(lambdaResult#0, Tclass._System.array2?(TInt));
        }

        assume false;
    }

    // End Comprehension WF check
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._System.array?(Tclass._System.array2?(TInt));
    assume !read($Heap, $nw, alloc);
    assume _System.array.Length($nw) == LitInt(5);
    assert {:subsumption 0} (forall arrayinit#0#i0#0: int :: 
      0 <= arrayinit#0#i0#0 && arrayinit#0#i0#0 < LitInt(5)
         ==> Requires1(Tclass._System.nat(), 
          Tclass._System.array2?(TInt), 
          $Heap, 
          Lit(AtLayer((lambda $l#0#ly#0: LayerType :: 
                Handle1((lambda $l#0#heap#0: Heap, $l#0#_v4#0: Box :: $Box(a#0)), 
                  (lambda $l#0#heap#0: Heap, $l#0#_v4#0: Box :: 
                    $IsBox($l#0#_v4#0, Tclass._System.nat())), 
                  (lambda $l#0#heap#0: Heap, $l#0#_v4#0: Box :: 
                    SetRef_to_SetBox((lambda $l#0#o#0: ref :: false))))), 
              $LS($LZ))), 
          $Box(arrayinit#0#i0#0)));
    assume (forall arrayinit#0#i0#0: int :: 
      { read($Heap, $nw, IndexField(arrayinit#0#i0#0)) } 
      0 <= arrayinit#0#i0#0 && arrayinit#0#i0#0 < LitInt(5)
         ==> $Unbox(read($Heap, $nw, IndexField(arrayinit#0#i0#0))): ref
           == $Unbox(Apply1(Tclass._System.nat(), 
              Tclass._System.array2?(TInt), 
              $Heap, 
              Lit(AtLayer((lambda $l#0#ly#0: LayerType :: 
                    Handle1((lambda $l#0#heap#0: Heap, $l#0#_v4#0: Box :: $Box(a#0)), 
                      (lambda $l#0#heap#0: Heap, $l#0#_v4#0: Box :: 
                        $IsBox($l#0#_v4#0, Tclass._System.nat())), 
                      (lambda $l#0#heap#0: Heap, $l#0#_v4#0: Box :: 
                        SetRef_to_SetBox((lambda $l#0#o#0: ref :: false))))), 
                  $LS($LZ))), 
              $Box(arrayinit#0#i0#0))): ref);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    b#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(89,34)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(90,40)
    assume true;
    assert 0 <= LitInt(5);
    assert 0 <= LitInt(4);
    assert 0 <= LitInt(3);
    havoc $nw;
    assume $nw != null
       && dtype($nw)
         == Tclass._System.array3?(Tclass._System.array?(Tclass._System.array2?(TInt)));
    assume !read($Heap, $nw, alloc);
    assume _System.array3.Length0($nw) == LitInt(5);
    assume _System.array3.Length1($nw) == LitInt(4);
    assume _System.array3.Length2($nw) == LitInt(3);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    c#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(90,73)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(91,5)
    assume true;
    assert 0 <= LitInt(5);
    assert 0 <= LitInt(4);
    assert 0 <= LitInt(3);
    // Begin Comprehension WF check
    if (*)
    {
        havoc _v5#0;
        havoc _v6#0;
        havoc _v7#0;
        if (LitInt(0) <= _v5#0)
        {
            $oldHeap#1 := $Heap;
            havoc $Heap;
            assume $IsGoodHeap($Heap);
            assume $oldHeap#1 == $Heap || $HeapSucc($oldHeap#1, $Heap);
            $_Frame#l1 := (lambda<alpha> $o: ref, $f: Field alpha :: 
              $o != null && read($Heap, $o, alloc) ==> false);
            assume lambdaResult#1 == b#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(lambdaResult#1, Tclass._System.array?(Tclass._System.array2?(TInt)));
        }

        assume false;
    }

    // End Comprehension WF check
    havoc $nw;
    assume $nw != null
       && dtype($nw)
         == Tclass._System.array3?(Tclass._System.array?(Tclass._System.array2?(TInt)));
    assume !read($Heap, $nw, alloc);
    assume _System.array3.Length0($nw) == LitInt(5);
    assume _System.array3.Length1($nw) == LitInt(4);
    assume _System.array3.Length2($nw) == LitInt(3);
    assert {:subsumption 0} (forall arrayinit#1#i0#0: int, arrayinit#1#i1#0: int, arrayinit#1#i2#0: int :: 
      0 <= arrayinit#1#i0#0
           && arrayinit#1#i0#0 < LitInt(5)
           && 
          0 <= arrayinit#1#i1#0
           && arrayinit#1#i1#0 < LitInt(4)
           && 
          0 <= arrayinit#1#i2#0
           && arrayinit#1#i2#0 < LitInt(3)
         ==> Requires3(Tclass._System.nat(), 
          TInt, 
          TInt, 
          Tclass._System.array?(Tclass._System.array2?(TInt)), 
          $Heap, 
          Lit(AtLayer((lambda $l#1#ly#0: LayerType :: 
                Handle3((lambda $l#1#heap#0: Heap, $l#1#_v5#0: Box, $l#1#_v6#0: Box, $l#1#_v7#0: Box :: 
                    $Box(b#0)), 
                  (lambda $l#1#heap#0: Heap, $l#1#_v5#0: Box, $l#1#_v6#0: Box, $l#1#_v7#0: Box :: 
                    $IsBox($l#1#_v5#0, Tclass._System.nat())
                       && $IsBox($l#1#_v6#0, TInt)
                       && $IsBox($l#1#_v7#0, TInt)), 
                  (lambda $l#1#heap#0: Heap, $l#1#_v5#0: Box, $l#1#_v6#0: Box, $l#1#_v7#0: Box :: 
                    SetRef_to_SetBox((lambda $l#1#o#0: ref :: false))))), 
              $LS($LZ))), 
          $Box(arrayinit#1#i0#0), 
          $Box(arrayinit#1#i1#0), 
          $Box(arrayinit#1#i2#0)));
    assume (forall arrayinit#1#i0#0: int, arrayinit#1#i1#0: int, arrayinit#1#i2#0: int :: 
      { read($Heap, 
          $nw, 
          MultiIndexField(MultiIndexField(IndexField(arrayinit#1#i0#0), arrayinit#1#i1#0), 
            arrayinit#1#i2#0)) } 
      0 <= arrayinit#1#i0#0
           && arrayinit#1#i0#0 < LitInt(5)
           && 
          0 <= arrayinit#1#i1#0
           && arrayinit#1#i1#0 < LitInt(4)
           && 
          0 <= arrayinit#1#i2#0
           && arrayinit#1#i2#0 < LitInt(3)
         ==> $Unbox(read($Heap, 
              $nw, 
              MultiIndexField(MultiIndexField(IndexField(arrayinit#1#i0#0), arrayinit#1#i1#0), 
                arrayinit#1#i2#0))): ref
           == $Unbox(Apply3(Tclass._System.nat(), 
              TInt, 
              TInt, 
              Tclass._System.array?(Tclass._System.array2?(TInt)), 
              $Heap, 
              Lit(AtLayer((lambda $l#1#ly#0: LayerType :: 
                    Handle3((lambda $l#1#heap#0: Heap, $l#1#_v5#0: Box, $l#1#_v6#0: Box, $l#1#_v7#0: Box :: 
                        $Box(b#0)), 
                      (lambda $l#1#heap#0: Heap, $l#1#_v5#0: Box, $l#1#_v6#0: Box, $l#1#_v7#0: Box :: 
                        $IsBox($l#1#_v5#0, Tclass._System.nat())
                           && $IsBox($l#1#_v6#0, TInt)
                           && $IsBox($l#1#_v7#0, TInt)), 
                      (lambda $l#1#heap#0: Heap, $l#1#_v5#0: Box, $l#1#_v6#0: Box, $l#1#_v7#0: Box :: 
                        SetRef_to_SetBox((lambda $l#1#o#0: ref :: false))))), 
                  $LS($LZ))), 
              $Box(arrayinit#1#i0#0), 
              $Box(arrayinit#1#i1#0), 
              $Box(arrayinit#1#i2#0))): ref);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    c#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue196.dfy(91,52)"} true;
    havoc d#0 /* where $Is(d#0, Tclass._System.array15?(TInt))
       && $IsAlloc(d#0, Tclass._System.array15?(TInt), $Heap) */;
    havoc e#0 /* where $Is(e#0, Tclass._System.array16(TInt))
       && $IsAlloc(e#0, Tclass._System.array16(TInt), $Heap) */;
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

const unique tytagFamily$array2: TyTagFamily;

const unique tytagFamily$_#Func2: TyTagFamily;

const unique tytagFamily$_#PartialFunc2: TyTagFamily;

const unique tytagFamily$_#TotalFunc2: TyTagFamily;

const unique tytagFamily$array3: TyTagFamily;

const unique tytagFamily$_#Func3: TyTagFamily;

const unique tytagFamily$_#PartialFunc3: TyTagFamily;

const unique tytagFamily$_#TotalFunc3: TyTagFamily;

const unique tytagFamily$array4: TyTagFamily;

const unique tytagFamily$_#Func4: TyTagFamily;

const unique tytagFamily$_#PartialFunc4: TyTagFamily;

const unique tytagFamily$_#TotalFunc4: TyTagFamily;

const unique tytagFamily$array15: TyTagFamily;

const unique tytagFamily$_#Func15: TyTagFamily;

const unique tytagFamily$_#PartialFunc15: TyTagFamily;

const unique tytagFamily$_#TotalFunc15: TyTagFamily;

const unique tytagFamily$array16: TyTagFamily;

const unique tytagFamily$_#Func16: TyTagFamily;

const unique tytagFamily$_#PartialFunc16: TyTagFamily;

const unique tytagFamily$_#TotalFunc16: TyTagFamily;

const unique tytagFamily$_tuple#2: TyTagFamily;

const unique tytagFamily$_tuple#0: TyTagFamily;

const unique tytagFamily$A: TyTagFamily;

const unique tytagFamily$_default: TyTagFamily;

const unique field$a: NameFamily;
