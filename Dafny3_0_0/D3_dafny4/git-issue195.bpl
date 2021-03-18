// Dafny 3.0.0.30204
// Command Line Options: -compile:0 -noVerify /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue195.dfy -print:./git-issue195.bpl

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

// Box/unbox axiom for bv8
axiom (forall bx: Box :: 
  { $IsBox(bx, TBitvector(8)) } 
  $IsBox(bx, TBitvector(8))
     ==> $Box($Unbox(bx): bv8) == bx && $Is($Unbox(bx): bv8, TBitvector(8)));

axiom (forall v: bv8 :: { $Is(v, TBitvector(8)) } $Is(v, TBitvector(8)));

axiom (forall v: bv8, heap: Heap :: 
  { $IsAlloc(v, TBitvector(8), heap) } 
  $IsAlloc(v, TBitvector(8), heap));

function {:bvbuiltin "bvand"} and_bv8(bv8, bv8) : bv8;

function {:bvbuiltin "bvor"} or_bv8(bv8, bv8) : bv8;

function {:bvbuiltin "bvxor"} xor_bv8(bv8, bv8) : bv8;

function {:bvbuiltin "bvnot"} not_bv8(bv8) : bv8;

function {:bvbuiltin "bvadd"} add_bv8(bv8, bv8) : bv8;

function {:bvbuiltin "bvsub"} sub_bv8(bv8, bv8) : bv8;

function {:bvbuiltin "bvmul"} mul_bv8(bv8, bv8) : bv8;

function {:bvbuiltin "bvudiv"} div_bv8(bv8, bv8) : bv8;

function {:bvbuiltin "bvurem"} mod_bv8(bv8, bv8) : bv8;

function {:bvbuiltin "bvult"} lt_bv8(bv8, bv8) : bool;

function {:bvbuiltin "bvule"} le_bv8(bv8, bv8) : bool;

function {:bvbuiltin "bvuge"} ge_bv8(bv8, bv8) : bool;

function {:bvbuiltin "bvugt"} gt_bv8(bv8, bv8) : bool;

function {:bvbuiltin "bvshl"} LeftShift_bv8(bv8, bv8) : bv8;

function {:bvbuiltin "bvlshr"} RightShift_bv8(bv8, bv8) : bv8;

function {:bvbuiltin "ext_rotate_left"} LeftRotate_bv8(bv8, bv8) : bv8;

function {:bvbuiltin "ext_rotate_right"} RightRotate_bv8(bv8, bv8) : bv8;

function {:bvbuiltin "(_ int2bv 8)"} nat_to_bv8(int) : bv8;

function {:bvbuiltin "bv2int"} smt_nat_from_bv8(bv8) : int;

function nat_from_bv8(bv8) : int;

axiom (forall b: bv8 :: 
  { nat_from_bv8(b) } 
  0 <= nat_from_bv8(b)
     && nat_from_bv8(b) < 256
     && nat_from_bv8(b) == smt_nat_from_bv8(b));

// Box/unbox axiom for bv167
axiom (forall bx: Box :: 
  { $IsBox(bx, TBitvector(167)) } 
  $IsBox(bx, TBitvector(167))
     ==> $Box($Unbox(bx): bv167) == bx && $Is($Unbox(bx): bv167, TBitvector(167)));

axiom (forall v: bv167 :: { $Is(v, TBitvector(167)) } $Is(v, TBitvector(167)));

axiom (forall v: bv167, heap: Heap :: 
  { $IsAlloc(v, TBitvector(167), heap) } 
  $IsAlloc(v, TBitvector(167), heap));

function {:bvbuiltin "bvand"} and_bv167(bv167, bv167) : bv167;

function {:bvbuiltin "bvor"} or_bv167(bv167, bv167) : bv167;

function {:bvbuiltin "bvxor"} xor_bv167(bv167, bv167) : bv167;

function {:bvbuiltin "bvnot"} not_bv167(bv167) : bv167;

function {:bvbuiltin "bvadd"} add_bv167(bv167, bv167) : bv167;

function {:bvbuiltin "bvsub"} sub_bv167(bv167, bv167) : bv167;

function {:bvbuiltin "bvmul"} mul_bv167(bv167, bv167) : bv167;

function {:bvbuiltin "bvudiv"} div_bv167(bv167, bv167) : bv167;

function {:bvbuiltin "bvurem"} mod_bv167(bv167, bv167) : bv167;

function {:bvbuiltin "bvult"} lt_bv167(bv167, bv167) : bool;

function {:bvbuiltin "bvule"} le_bv167(bv167, bv167) : bool;

function {:bvbuiltin "bvuge"} ge_bv167(bv167, bv167) : bool;

function {:bvbuiltin "bvugt"} gt_bv167(bv167, bv167) : bool;

function {:bvbuiltin "bvshl"} LeftShift_bv167(bv167, bv167) : bv167;

function {:bvbuiltin "bvlshr"} RightShift_bv167(bv167, bv167) : bv167;

function {:bvbuiltin "ext_rotate_left"} LeftRotate_bv167(bv167, bv167) : bv167;

function {:bvbuiltin "ext_rotate_right"} RightRotate_bv167(bv167, bv167) : bv167;

function {:bvbuiltin "(_ int2bv 167)"} nat_to_bv167(int) : bv167;

function {:bvbuiltin "bv2int"} smt_nat_from_bv167(bv167) : int;

function nat_from_bv167(bv167) : int;

axiom (forall b: bv167 :: 
  { nat_from_bv167(b) } 
  0 <= nat_from_bv167(b)
     && nat_from_bv167(b) < 187072209578355573530071658587684226515959365500928
     && nat_from_bv167(b) == smt_nat_from_bv167(b));

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

// Constructor function declaration
function #_module.Block.Block(Box, Seq Box, Box) : DatatypeType;

const unique ##_module.Block.Block: DtCtorId;

// Constructor identifier
axiom (forall a#14#0#0: Box, a#14#1#0: Seq Box, a#14#2#0: Box :: 
  { #_module.Block.Block(a#14#0#0, a#14#1#0, a#14#2#0) } 
  DatatypeCtorId(#_module.Block.Block(a#14#0#0, a#14#1#0, a#14#2#0))
     == ##_module.Block.Block);

function _module.Block.Block_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Block.Block_q(d) } 
  _module.Block.Block_q(d) <==> DatatypeCtorId(d) == ##_module.Block.Block);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Block.Block_q(d) } 
  _module.Block.Block_q(d)
     ==> (exists a#15#0#0: Box, a#15#1#0: Seq Box, a#15#2#0: Box :: 
      d == #_module.Block.Block(a#15#0#0, a#15#1#0, a#15#2#0)));

function Tclass._module.Block(Ty, Ty, Ty) : Ty;

const unique Tagclass._module.Block: TyTag;

// Tclass._module.Block Tag
axiom (forall _module.Block$Hash: Ty, _module.Block$Transaction: Ty, _module.Block$VProof: Ty :: 
  { Tclass._module.Block(_module.Block$Hash, _module.Block$Transaction, _module.Block$VProof) } 
  Tag(Tclass._module.Block(_module.Block$Hash, _module.Block$Transaction, _module.Block$VProof))
       == Tagclass._module.Block
     && TagFamily(Tclass._module.Block(_module.Block$Hash, _module.Block$Transaction, _module.Block$VProof))
       == tytagFamily$Block);

// Tclass._module.Block injectivity 0
axiom (forall _module.Block$Hash: Ty, _module.Block$Transaction: Ty, _module.Block$VProof: Ty :: 
  { Tclass._module.Block(_module.Block$Hash, _module.Block$Transaction, _module.Block$VProof) } 
  Tclass._module.Block_0(Tclass._module.Block(_module.Block$Hash, _module.Block$Transaction, _module.Block$VProof))
     == _module.Block$Hash);

function Tclass._module.Block_0(Ty) : Ty;

// Tclass._module.Block injectivity 1
axiom (forall _module.Block$Hash: Ty, _module.Block$Transaction: Ty, _module.Block$VProof: Ty :: 
  { Tclass._module.Block(_module.Block$Hash, _module.Block$Transaction, _module.Block$VProof) } 
  Tclass._module.Block_1(Tclass._module.Block(_module.Block$Hash, _module.Block$Transaction, _module.Block$VProof))
     == _module.Block$Transaction);

function Tclass._module.Block_1(Ty) : Ty;

// Tclass._module.Block injectivity 2
axiom (forall _module.Block$Hash: Ty, _module.Block$Transaction: Ty, _module.Block$VProof: Ty :: 
  { Tclass._module.Block(_module.Block$Hash, _module.Block$Transaction, _module.Block$VProof) } 
  Tclass._module.Block_2(Tclass._module.Block(_module.Block$Hash, _module.Block$Transaction, _module.Block$VProof))
     == _module.Block$VProof);

function Tclass._module.Block_2(Ty) : Ty;

// Box/unbox axiom for Tclass._module.Block
axiom (forall _module.Block$Hash: Ty, 
    _module.Block$Transaction: Ty, 
    _module.Block$VProof: Ty, 
    bx: Box :: 
  { $IsBox(bx, 
      Tclass._module.Block(_module.Block$Hash, _module.Block$Transaction, _module.Block$VProof)) } 
  $IsBox(bx, 
      Tclass._module.Block(_module.Block$Hash, _module.Block$Transaction, _module.Block$VProof))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, 
        Tclass._module.Block(_module.Block$Hash, _module.Block$Transaction, _module.Block$VProof)));

// Constructor $Is
axiom (forall _module.Block$Hash: Ty, 
    _module.Block$Transaction: Ty, 
    _module.Block$VProof: Ty, 
    a#16#0#0: Box, 
    a#16#1#0: Seq Box, 
    a#16#2#0: Box :: 
  { $Is(#_module.Block.Block(a#16#0#0, a#16#1#0, a#16#2#0), 
      Tclass._module.Block(_module.Block$Hash, _module.Block$Transaction, _module.Block$VProof)) } 
  $Is(#_module.Block.Block(a#16#0#0, a#16#1#0, a#16#2#0), 
      Tclass._module.Block(_module.Block$Hash, _module.Block$Transaction, _module.Block$VProof))
     <==> $IsBox(a#16#0#0, _module.Block$Hash)
       && $Is(a#16#1#0, TSeq(_module.Block$Transaction))
       && $IsBox(a#16#2#0, _module.Block$VProof));

// Constructor $IsAlloc
axiom (forall _module.Block$Hash: Ty, 
    _module.Block$Transaction: Ty, 
    _module.Block$VProof: Ty, 
    a#17#0#0: Box, 
    a#17#1#0: Seq Box, 
    a#17#2#0: Box, 
    $h: Heap :: 
  { $IsAlloc(#_module.Block.Block(a#17#0#0, a#17#1#0, a#17#2#0), 
      Tclass._module.Block(_module.Block$Hash, _module.Block$Transaction, _module.Block$VProof), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Block.Block(a#17#0#0, a#17#1#0, a#17#2#0), 
        Tclass._module.Block(_module.Block$Hash, _module.Block$Transaction, _module.Block$VProof), 
        $h)
       <==> $IsAllocBox(a#17#0#0, _module.Block$Hash, $h)
         && $IsAlloc(a#17#1#0, TSeq(_module.Block$Transaction), $h)
         && $IsAllocBox(a#17#2#0, _module.Block$VProof, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _module.Block$Hash: Ty, $h: Heap :: 
  { $IsAllocBox(_module.Block.prevBlockHash(d), _module.Block$Hash, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Block.Block_q(d)
       && (exists _module.Block$Transaction: Ty, _module.Block$VProof: Ty :: 
        { $IsAlloc(d, 
            Tclass._module.Block(_module.Block$Hash, _module.Block$Transaction, _module.Block$VProof), 
            $h) } 
        $IsAlloc(d, 
          Tclass._module.Block(_module.Block$Hash, _module.Block$Transaction, _module.Block$VProof), 
          $h))
     ==> $IsAllocBox(_module.Block.prevBlockHash(d), _module.Block$Hash, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _module.Block$Transaction: Ty, $h: Heap :: 
  { $IsAlloc(_module.Block.txs(d), TSeq(_module.Block$Transaction), $h) } 
  $IsGoodHeap($h)
       && 
      _module.Block.Block_q(d)
       && (exists _module.Block$Hash: Ty, _module.Block$VProof: Ty :: 
        { $IsAlloc(d, 
            Tclass._module.Block(_module.Block$Hash, _module.Block$Transaction, _module.Block$VProof), 
            $h) } 
        $IsAlloc(d, 
          Tclass._module.Block(_module.Block$Hash, _module.Block$Transaction, _module.Block$VProof), 
          $h))
     ==> $IsAlloc(_module.Block.txs(d), TSeq(_module.Block$Transaction), $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _module.Block$VProof: Ty, $h: Heap :: 
  { $IsAllocBox(_module.Block.proof(d), _module.Block$VProof, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Block.Block_q(d)
       && (exists _module.Block$Hash: Ty, _module.Block$Transaction: Ty :: 
        { $IsAlloc(d, 
            Tclass._module.Block(_module.Block$Hash, _module.Block$Transaction, _module.Block$VProof), 
            $h) } 
        $IsAlloc(d, 
          Tclass._module.Block(_module.Block$Hash, _module.Block$Transaction, _module.Block$VProof), 
          $h))
     ==> $IsAllocBox(_module.Block.proof(d), _module.Block$VProof, $h));

// Constructor literal
axiom (forall a#18#0#0: Box, a#18#1#0: Seq Box, a#18#2#0: Box :: 
  { #_module.Block.Block(Lit(a#18#0#0), Lit(a#18#1#0), Lit(a#18#2#0)) } 
  #_module.Block.Block(Lit(a#18#0#0), Lit(a#18#1#0), Lit(a#18#2#0))
     == Lit(#_module.Block.Block(a#18#0#0, a#18#1#0, a#18#2#0)));

function _module.Block.prevBlockHash(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#19#0#0: Box, a#19#1#0: Seq Box, a#19#2#0: Box :: 
  { #_module.Block.Block(a#19#0#0, a#19#1#0, a#19#2#0) } 
  _module.Block.prevBlockHash(#_module.Block.Block(a#19#0#0, a#19#1#0, a#19#2#0))
     == a#19#0#0);

// Inductive rank
axiom (forall a#20#0#0: Box, a#20#1#0: Seq Box, a#20#2#0: Box :: 
  { #_module.Block.Block(a#20#0#0, a#20#1#0, a#20#2#0) } 
  BoxRank(a#20#0#0) < DtRank(#_module.Block.Block(a#20#0#0, a#20#1#0, a#20#2#0)));

function _module.Block.txs(DatatypeType) : Seq Box;

// Constructor injectivity
axiom (forall a#21#0#0: Box, a#21#1#0: Seq Box, a#21#2#0: Box :: 
  { #_module.Block.Block(a#21#0#0, a#21#1#0, a#21#2#0) } 
  _module.Block.txs(#_module.Block.Block(a#21#0#0, a#21#1#0, a#21#2#0))
     == a#21#1#0);

// Inductive seq element rank
axiom (forall a#22#0#0: Box, a#22#1#0: Seq Box, a#22#2#0: Box, i: int :: 
  { Seq#Index(a#22#1#0, i), #_module.Block.Block(a#22#0#0, a#22#1#0, a#22#2#0) } 
  0 <= i && i < Seq#Length(a#22#1#0)
     ==> DtRank($Unbox(Seq#Index(a#22#1#0, i)): DatatypeType)
       < DtRank(#_module.Block.Block(a#22#0#0, a#22#1#0, a#22#2#0)));

// Inductive seq rank
axiom (forall a#23#0#0: Box, a#23#1#0: Seq Box, a#23#2#0: Box :: 
  { #_module.Block.Block(a#23#0#0, a#23#1#0, a#23#2#0) } 
  Seq#Rank(a#23#1#0) < DtRank(#_module.Block.Block(a#23#0#0, a#23#1#0, a#23#2#0)));

function _module.Block.proof(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#24#0#0: Box, a#24#1#0: Seq Box, a#24#2#0: Box :: 
  { #_module.Block.Block(a#24#0#0, a#24#1#0, a#24#2#0) } 
  _module.Block.proof(#_module.Block.Block(a#24#0#0, a#24#1#0, a#24#2#0))
     == a#24#2#0);

// Inductive rank
axiom (forall a#25#0#0: Box, a#25#1#0: Seq Box, a#25#2#0: Box :: 
  { #_module.Block.Block(a#25#0#0, a#25#1#0, a#25#2#0) } 
  BoxRank(a#25#2#0) < DtRank(#_module.Block.Block(a#25#0#0, a#25#1#0, a#25#2#0)));

// Depth-one case-split function
function $IsA#_module.Block(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.Block(d) } 
  $IsA#_module.Block(d) ==> _module.Block.Block_q(d));

// Questionmark data type disjunctivity
axiom (forall _module.Block$Hash: Ty, 
    _module.Block$Transaction: Ty, 
    _module.Block$VProof: Ty, 
    d: DatatypeType :: 
  { _module.Block.Block_q(d), $Is(d, 
      Tclass._module.Block(_module.Block$Hash, _module.Block$Transaction, _module.Block$VProof)) } 
  $Is(d, 
      Tclass._module.Block(_module.Block$Hash, _module.Block$Transaction, _module.Block$VProof))
     ==> _module.Block.Block_q(d));

// Datatype extensional equality declaration
function _module.Block#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.Block.Block
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Block#Equal(a, b) } 
  true
     ==> (_module.Block#Equal(a, b)
       <==> _module.Block.prevBlockHash(a) == _module.Block.prevBlockHash(b)
         && Seq#Equal(_module.Block.txs(a), _module.Block.txs(b))
         && _module.Block.proof(a) == _module.Block.proof(b)));

// Datatype extensionality axiom: _module.Block
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Block#Equal(a, b) } 
  _module.Block#Equal(a, b) <==> a == b);

const unique class._module.Block: ClassName;

const unique class._module.nt: ClassName;

procedure CheckWellformed$$_module.ntNative(x#0: int);
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.ntNative(x#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;


    // AddWellformednessCheck for newtype ntNative
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue195.dfy(27,8): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        if (LitInt(-100) <= x#0)
        {
        }

        assume LitInt(-100) <= x#0 && x#0 < 100;
    }
    else
    {
        assume true;
        assert {:subsumption 0} LitInt(-100) <= LitInt(0);
        assert {:subsumption 0} 0 < 100;
    }
}



function Tclass._module.ntNative() : Ty;

const unique Tagclass._module.ntNative: TyTag;

// Tclass._module.ntNative Tag
axiom Tag(Tclass._module.ntNative()) == Tagclass._module.ntNative
   && TagFamily(Tclass._module.ntNative()) == tytagFamily$ntNative;

// Box/unbox axiom for Tclass._module.ntNative
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.ntNative()) } 
  $IsBox(bx, Tclass._module.ntNative())
     ==> $Box($Unbox(bx): int) == bx && $Is($Unbox(bx): int, Tclass._module.ntNative()));

// _module.ntNative: newtype $Is
axiom (forall x#0: int :: 
  { $Is(x#0, Tclass._module.ntNative()) } 
  $Is(x#0, Tclass._module.ntNative()) <==> LitInt(-100) <= x#0 && x#0 < 100);

// _module.ntNative: newtype $IsAlloc
axiom (forall x#0: int, $h: Heap :: 
  { $IsAlloc(x#0, Tclass._module.ntNative(), $h) } 
  $IsAlloc(x#0, Tclass._module.ntNative(), $h));

const unique class._module.ntNative: ClassName;

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

axiom FDim(_module.MyClass.u) == 0
   && FieldOfDecl(class._module.MyClass?, field$u) == _module.MyClass.u
   && !$IsGhostField(_module.MyClass.u);

const _module.MyClass.u: Field int;

// MyClass.u: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.MyClass.u) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.MyClass?()
     ==> $Is(read($h, $o, _module.MyClass.u), TInt));

// MyClass.u: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.MyClass.u) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.MyClass?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.MyClass.u), TInt, $h));

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
function #_module.X.X(bool, char, int, real, int, int, bv8, bv167, Box, ref) : DatatypeType;

const unique ##_module.X.X: DtCtorId;

// Constructor identifier
axiom (forall a#0#0#0: bool, 
    a#0#1#0: char, 
    a#0#2#0: int, 
    a#0#3#0: real, 
    a#0#4#0: int, 
    a#0#5#0: int, 
    a#0#6#0: bv8, 
    a#0#7#0: bv167, 
    a#0#8#0: Box, 
    a#0#9#0: ref :: 
  { #_module.X.X(a#0#0#0, 
      a#0#1#0, 
      a#0#2#0, 
      a#0#3#0, 
      a#0#4#0, 
      a#0#5#0, 
      a#0#6#0, 
      a#0#7#0, 
      a#0#8#0, 
      a#0#9#0) } 
  DatatypeCtorId(#_module.X.X(a#0#0#0, 
        a#0#1#0, 
        a#0#2#0, 
        a#0#3#0, 
        a#0#4#0, 
        a#0#5#0, 
        a#0#6#0, 
        a#0#7#0, 
        a#0#8#0, 
        a#0#9#0))
     == ##_module.X.X);

function _module.X.X_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.X.X_q(d) } 
  _module.X.X_q(d) <==> DatatypeCtorId(d) == ##_module.X.X);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.X.X_q(d) } 
  _module.X.X_q(d)
     ==> (exists a#1#0#0: bool, 
        a#1#1#0: char, 
        a#1#2#0: int, 
        a#1#3#0: real, 
        a#1#4#0: int, 
        a#1#5#0: int, 
        a#1#6#0: bv8, 
        a#1#7#0: bv167, 
        a#1#8#0: Box, 
        a#1#9#0: ref :: 
      d
         == #_module.X.X(a#1#0#0, 
          a#1#1#0, 
          a#1#2#0, 
          a#1#3#0, 
          a#1#4#0, 
          a#1#5#0, 
          a#1#6#0, 
          a#1#7#0, 
          a#1#8#0, 
          a#1#9#0)));

function Tclass._module.nt() : Ty;

const unique Tagclass._module.nt: TyTag;

// Tclass._module.nt Tag
axiom Tag(Tclass._module.nt()) == Tagclass._module.nt
   && TagFamily(Tclass._module.nt()) == tytagFamily$nt;

// Box/unbox axiom for Tclass._module.nt
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.nt()) } 
  $IsBox(bx, Tclass._module.nt())
     ==> $Box($Unbox(bx): int) == bx && $Is($Unbox(bx): int, Tclass._module.nt()));

function Tclass._module.X() : Ty;

const unique Tagclass._module.X: TyTag;

// Tclass._module.X Tag
axiom Tag(Tclass._module.X()) == Tagclass._module.X
   && TagFamily(Tclass._module.X()) == tytagFamily$X;

// Box/unbox axiom for Tclass._module.X
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.X()) } 
  $IsBox(bx, Tclass._module.X())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.X()));

// Constructor $Is
axiom (forall a#2#0#0: bool, 
    a#2#1#0: char, 
    a#2#2#0: int, 
    a#2#3#0: real, 
    a#2#4#0: int, 
    a#2#5#0: int, 
    a#2#6#0: bv8, 
    a#2#7#0: bv167, 
    a#2#8#0: Box, 
    a#2#9#0: ref :: 
  { $Is(#_module.X.X(a#2#0#0, 
        a#2#1#0, 
        a#2#2#0, 
        a#2#3#0, 
        a#2#4#0, 
        a#2#5#0, 
        a#2#6#0, 
        a#2#7#0, 
        a#2#8#0, 
        a#2#9#0), 
      Tclass._module.X()) } 
  $Is(#_module.X.X(a#2#0#0, 
        a#2#1#0, 
        a#2#2#0, 
        a#2#3#0, 
        a#2#4#0, 
        a#2#5#0, 
        a#2#6#0, 
        a#2#7#0, 
        a#2#8#0, 
        a#2#9#0), 
      Tclass._module.X())
     <==> $Is(a#2#0#0, TBool)
       && $Is(a#2#1#0, TChar)
       && $Is(a#2#2#0, TInt)
       && $Is(a#2#3#0, TReal)
       && $Is(a#2#4#0, Tclass._module.nt())
       && $Is(a#2#5#0, Tclass._module.ntNative())
       && $Is(a#2#6#0, TBitvector(8))
       && $Is(a#2#7#0, TBitvector(167))
       && $Is(a#2#8#0, TORDINAL)
       && $Is(a#2#9#0, Tclass._module.MyClass()));

// Constructor $IsAlloc
axiom (forall a#3#0#0: bool, 
    a#3#1#0: char, 
    a#3#2#0: int, 
    a#3#3#0: real, 
    a#3#4#0: int, 
    a#3#5#0: int, 
    a#3#6#0: bv8, 
    a#3#7#0: bv167, 
    a#3#8#0: Box, 
    a#3#9#0: ref, 
    $h: Heap :: 
  { $IsAlloc(#_module.X.X(a#3#0#0, 
        a#3#1#0, 
        a#3#2#0, 
        a#3#3#0, 
        a#3#4#0, 
        a#3#5#0, 
        a#3#6#0, 
        a#3#7#0, 
        a#3#8#0, 
        a#3#9#0), 
      Tclass._module.X(), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.X.X(a#3#0#0, 
          a#3#1#0, 
          a#3#2#0, 
          a#3#3#0, 
          a#3#4#0, 
          a#3#5#0, 
          a#3#6#0, 
          a#3#7#0, 
          a#3#8#0, 
          a#3#9#0), 
        Tclass._module.X(), 
        $h)
       <==> $IsAlloc(a#3#0#0, TBool, $h)
         && $IsAlloc(a#3#1#0, TChar, $h)
         && $IsAlloc(a#3#2#0, TInt, $h)
         && $IsAlloc(a#3#3#0, TReal, $h)
         && $IsAlloc(a#3#4#0, Tclass._module.nt(), $h)
         && $IsAlloc(a#3#5#0, Tclass._module.ntNative(), $h)
         && $IsAlloc(a#3#6#0, TBitvector(8), $h)
         && $IsAlloc(a#3#7#0, TBitvector(167), $h)
         && $IsAlloc(a#3#8#0, TORDINAL, $h)
         && $IsAlloc(a#3#9#0, Tclass._module.MyClass(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.X._h0(d), TBool, $h) } 
  $IsGoodHeap($h) && _module.X.X_q(d) && $IsAlloc(d, Tclass._module.X(), $h)
     ==> $IsAlloc(_module.X._h0(d), TBool, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.X._h1(d), TChar, $h) } 
  $IsGoodHeap($h) && _module.X.X_q(d) && $IsAlloc(d, Tclass._module.X(), $h)
     ==> $IsAlloc(_module.X._h1(d), TChar, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.X._h2(d), TInt, $h) } 
  $IsGoodHeap($h) && _module.X.X_q(d) && $IsAlloc(d, Tclass._module.X(), $h)
     ==> $IsAlloc(_module.X._h2(d), TInt, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.X._h3(d), TReal, $h) } 
  $IsGoodHeap($h) && _module.X.X_q(d) && $IsAlloc(d, Tclass._module.X(), $h)
     ==> $IsAlloc(_module.X._h3(d), TReal, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.X._h4(d), Tclass._module.nt(), $h) } 
  $IsGoodHeap($h) && _module.X.X_q(d) && $IsAlloc(d, Tclass._module.X(), $h)
     ==> $IsAlloc(_module.X._h4(d), Tclass._module.nt(), $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.X._h5(d), Tclass._module.ntNative(), $h) } 
  $IsGoodHeap($h) && _module.X.X_q(d) && $IsAlloc(d, Tclass._module.X(), $h)
     ==> $IsAlloc(_module.X._h5(d), Tclass._module.ntNative(), $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.X._h6(d), TBitvector(8), $h) } 
  $IsGoodHeap($h) && _module.X.X_q(d) && $IsAlloc(d, Tclass._module.X(), $h)
     ==> $IsAlloc(_module.X._h6(d), TBitvector(8), $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.X._h7(d), TBitvector(167), $h) } 
  $IsGoodHeap($h) && _module.X.X_q(d) && $IsAlloc(d, Tclass._module.X(), $h)
     ==> $IsAlloc(_module.X._h7(d), TBitvector(167), $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.X._h8(d), TORDINAL, $h) } 
  $IsGoodHeap($h) && _module.X.X_q(d) && $IsAlloc(d, Tclass._module.X(), $h)
     ==> $IsAlloc(_module.X._h8(d), TORDINAL, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.X._h9(d), Tclass._module.MyClass(), $h) } 
  $IsGoodHeap($h) && _module.X.X_q(d) && $IsAlloc(d, Tclass._module.X(), $h)
     ==> $IsAlloc(_module.X._h9(d), Tclass._module.MyClass(), $h));

// Constructor literal
axiom (forall a#4#0#0: bool, 
    a#4#1#0: char, 
    a#4#2#0: int, 
    a#4#3#0: real, 
    a#4#4#0: int, 
    a#4#5#0: int, 
    a#4#6#0: bv8, 
    a#4#7#0: bv167, 
    a#4#8#0: Box, 
    a#4#9#0: ref :: 
  { #_module.X.X(Lit(a#4#0#0), 
      Lit(a#4#1#0), 
      LitInt(a#4#2#0), 
      LitReal(a#4#3#0), 
      LitInt(a#4#4#0), 
      LitInt(a#4#5#0), 
      Lit(a#4#6#0), 
      Lit(a#4#7#0), 
      Lit(a#4#8#0), 
      Lit(a#4#9#0)) } 
  #_module.X.X(Lit(a#4#0#0), 
      Lit(a#4#1#0), 
      LitInt(a#4#2#0), 
      LitReal(a#4#3#0), 
      LitInt(a#4#4#0), 
      LitInt(a#4#5#0), 
      Lit(a#4#6#0), 
      Lit(a#4#7#0), 
      Lit(a#4#8#0), 
      Lit(a#4#9#0))
     == Lit(#_module.X.X(a#4#0#0, 
        a#4#1#0, 
        a#4#2#0, 
        a#4#3#0, 
        a#4#4#0, 
        a#4#5#0, 
        a#4#6#0, 
        a#4#7#0, 
        a#4#8#0, 
        a#4#9#0)));

function _module.X._h0(DatatypeType) : bool;

// Constructor injectivity
axiom (forall a#5#0#0: bool, 
    a#5#1#0: char, 
    a#5#2#0: int, 
    a#5#3#0: real, 
    a#5#4#0: int, 
    a#5#5#0: int, 
    a#5#6#0: bv8, 
    a#5#7#0: bv167, 
    a#5#8#0: Box, 
    a#5#9#0: ref :: 
  { #_module.X.X(a#5#0#0, 
      a#5#1#0, 
      a#5#2#0, 
      a#5#3#0, 
      a#5#4#0, 
      a#5#5#0, 
      a#5#6#0, 
      a#5#7#0, 
      a#5#8#0, 
      a#5#9#0) } 
  _module.X._h0(#_module.X.X(a#5#0#0, 
        a#5#1#0, 
        a#5#2#0, 
        a#5#3#0, 
        a#5#4#0, 
        a#5#5#0, 
        a#5#6#0, 
        a#5#7#0, 
        a#5#8#0, 
        a#5#9#0))
     == a#5#0#0);

function _module.X._h1(DatatypeType) : char;

// Constructor injectivity
axiom (forall a#6#0#0: bool, 
    a#6#1#0: char, 
    a#6#2#0: int, 
    a#6#3#0: real, 
    a#6#4#0: int, 
    a#6#5#0: int, 
    a#6#6#0: bv8, 
    a#6#7#0: bv167, 
    a#6#8#0: Box, 
    a#6#9#0: ref :: 
  { #_module.X.X(a#6#0#0, 
      a#6#1#0, 
      a#6#2#0, 
      a#6#3#0, 
      a#6#4#0, 
      a#6#5#0, 
      a#6#6#0, 
      a#6#7#0, 
      a#6#8#0, 
      a#6#9#0) } 
  _module.X._h1(#_module.X.X(a#6#0#0, 
        a#6#1#0, 
        a#6#2#0, 
        a#6#3#0, 
        a#6#4#0, 
        a#6#5#0, 
        a#6#6#0, 
        a#6#7#0, 
        a#6#8#0, 
        a#6#9#0))
     == a#6#1#0);

function _module.X._h2(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#7#0#0: bool, 
    a#7#1#0: char, 
    a#7#2#0: int, 
    a#7#3#0: real, 
    a#7#4#0: int, 
    a#7#5#0: int, 
    a#7#6#0: bv8, 
    a#7#7#0: bv167, 
    a#7#8#0: Box, 
    a#7#9#0: ref :: 
  { #_module.X.X(a#7#0#0, 
      a#7#1#0, 
      a#7#2#0, 
      a#7#3#0, 
      a#7#4#0, 
      a#7#5#0, 
      a#7#6#0, 
      a#7#7#0, 
      a#7#8#0, 
      a#7#9#0) } 
  _module.X._h2(#_module.X.X(a#7#0#0, 
        a#7#1#0, 
        a#7#2#0, 
        a#7#3#0, 
        a#7#4#0, 
        a#7#5#0, 
        a#7#6#0, 
        a#7#7#0, 
        a#7#8#0, 
        a#7#9#0))
     == a#7#2#0);

function _module.X._h3(DatatypeType) : real;

// Constructor injectivity
axiom (forall a#8#0#0: bool, 
    a#8#1#0: char, 
    a#8#2#0: int, 
    a#8#3#0: real, 
    a#8#4#0: int, 
    a#8#5#0: int, 
    a#8#6#0: bv8, 
    a#8#7#0: bv167, 
    a#8#8#0: Box, 
    a#8#9#0: ref :: 
  { #_module.X.X(a#8#0#0, 
      a#8#1#0, 
      a#8#2#0, 
      a#8#3#0, 
      a#8#4#0, 
      a#8#5#0, 
      a#8#6#0, 
      a#8#7#0, 
      a#8#8#0, 
      a#8#9#0) } 
  _module.X._h3(#_module.X.X(a#8#0#0, 
        a#8#1#0, 
        a#8#2#0, 
        a#8#3#0, 
        a#8#4#0, 
        a#8#5#0, 
        a#8#6#0, 
        a#8#7#0, 
        a#8#8#0, 
        a#8#9#0))
     == a#8#3#0);

function _module.X._h4(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#9#0#0: bool, 
    a#9#1#0: char, 
    a#9#2#0: int, 
    a#9#3#0: real, 
    a#9#4#0: int, 
    a#9#5#0: int, 
    a#9#6#0: bv8, 
    a#9#7#0: bv167, 
    a#9#8#0: Box, 
    a#9#9#0: ref :: 
  { #_module.X.X(a#9#0#0, 
      a#9#1#0, 
      a#9#2#0, 
      a#9#3#0, 
      a#9#4#0, 
      a#9#5#0, 
      a#9#6#0, 
      a#9#7#0, 
      a#9#8#0, 
      a#9#9#0) } 
  _module.X._h4(#_module.X.X(a#9#0#0, 
        a#9#1#0, 
        a#9#2#0, 
        a#9#3#0, 
        a#9#4#0, 
        a#9#5#0, 
        a#9#6#0, 
        a#9#7#0, 
        a#9#8#0, 
        a#9#9#0))
     == a#9#4#0);

function _module.X._h5(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#10#0#0: bool, 
    a#10#1#0: char, 
    a#10#2#0: int, 
    a#10#3#0: real, 
    a#10#4#0: int, 
    a#10#5#0: int, 
    a#10#6#0: bv8, 
    a#10#7#0: bv167, 
    a#10#8#0: Box, 
    a#10#9#0: ref :: 
  { #_module.X.X(a#10#0#0, 
      a#10#1#0, 
      a#10#2#0, 
      a#10#3#0, 
      a#10#4#0, 
      a#10#5#0, 
      a#10#6#0, 
      a#10#7#0, 
      a#10#8#0, 
      a#10#9#0) } 
  _module.X._h5(#_module.X.X(a#10#0#0, 
        a#10#1#0, 
        a#10#2#0, 
        a#10#3#0, 
        a#10#4#0, 
        a#10#5#0, 
        a#10#6#0, 
        a#10#7#0, 
        a#10#8#0, 
        a#10#9#0))
     == a#10#5#0);

function _module.X._h6(DatatypeType) : bv8;

// Constructor injectivity
axiom (forall a#11#0#0: bool, 
    a#11#1#0: char, 
    a#11#2#0: int, 
    a#11#3#0: real, 
    a#11#4#0: int, 
    a#11#5#0: int, 
    a#11#6#0: bv8, 
    a#11#7#0: bv167, 
    a#11#8#0: Box, 
    a#11#9#0: ref :: 
  { #_module.X.X(a#11#0#0, 
      a#11#1#0, 
      a#11#2#0, 
      a#11#3#0, 
      a#11#4#0, 
      a#11#5#0, 
      a#11#6#0, 
      a#11#7#0, 
      a#11#8#0, 
      a#11#9#0) } 
  _module.X._h6(#_module.X.X(a#11#0#0, 
        a#11#1#0, 
        a#11#2#0, 
        a#11#3#0, 
        a#11#4#0, 
        a#11#5#0, 
        a#11#6#0, 
        a#11#7#0, 
        a#11#8#0, 
        a#11#9#0))
     == a#11#6#0);

function _module.X._h7(DatatypeType) : bv167;

// Constructor injectivity
axiom (forall a#12#0#0: bool, 
    a#12#1#0: char, 
    a#12#2#0: int, 
    a#12#3#0: real, 
    a#12#4#0: int, 
    a#12#5#0: int, 
    a#12#6#0: bv8, 
    a#12#7#0: bv167, 
    a#12#8#0: Box, 
    a#12#9#0: ref :: 
  { #_module.X.X(a#12#0#0, 
      a#12#1#0, 
      a#12#2#0, 
      a#12#3#0, 
      a#12#4#0, 
      a#12#5#0, 
      a#12#6#0, 
      a#12#7#0, 
      a#12#8#0, 
      a#12#9#0) } 
  _module.X._h7(#_module.X.X(a#12#0#0, 
        a#12#1#0, 
        a#12#2#0, 
        a#12#3#0, 
        a#12#4#0, 
        a#12#5#0, 
        a#12#6#0, 
        a#12#7#0, 
        a#12#8#0, 
        a#12#9#0))
     == a#12#7#0);

function _module.X._h8(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#13#0#0: bool, 
    a#13#1#0: char, 
    a#13#2#0: int, 
    a#13#3#0: real, 
    a#13#4#0: int, 
    a#13#5#0: int, 
    a#13#6#0: bv8, 
    a#13#7#0: bv167, 
    a#13#8#0: Box, 
    a#13#9#0: ref :: 
  { #_module.X.X(a#13#0#0, 
      a#13#1#0, 
      a#13#2#0, 
      a#13#3#0, 
      a#13#4#0, 
      a#13#5#0, 
      a#13#6#0, 
      a#13#7#0, 
      a#13#8#0, 
      a#13#9#0) } 
  _module.X._h8(#_module.X.X(a#13#0#0, 
        a#13#1#0, 
        a#13#2#0, 
        a#13#3#0, 
        a#13#4#0, 
        a#13#5#0, 
        a#13#6#0, 
        a#13#7#0, 
        a#13#8#0, 
        a#13#9#0))
     == a#13#8#0);

function _module.X._h9(DatatypeType) : ref;

// Constructor injectivity
axiom (forall a#14#0#0: bool, 
    a#14#1#0: char, 
    a#14#2#0: int, 
    a#14#3#0: real, 
    a#14#4#0: int, 
    a#14#5#0: int, 
    a#14#6#0: bv8, 
    a#14#7#0: bv167, 
    a#14#8#0: Box, 
    a#14#9#0: ref :: 
  { #_module.X.X(a#14#0#0, 
      a#14#1#0, 
      a#14#2#0, 
      a#14#3#0, 
      a#14#4#0, 
      a#14#5#0, 
      a#14#6#0, 
      a#14#7#0, 
      a#14#8#0, 
      a#14#9#0) } 
  _module.X._h9(#_module.X.X(a#14#0#0, 
        a#14#1#0, 
        a#14#2#0, 
        a#14#3#0, 
        a#14#4#0, 
        a#14#5#0, 
        a#14#6#0, 
        a#14#7#0, 
        a#14#8#0, 
        a#14#9#0))
     == a#14#9#0);

// Depth-one case-split function
function $IsA#_module.X(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.X(d) } 
  $IsA#_module.X(d) ==> _module.X.X_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.X.X_q(d), $Is(d, Tclass._module.X()) } 
  $Is(d, Tclass._module.X()) ==> _module.X.X_q(d));

// Datatype extensional equality declaration
function _module.X#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.X.X
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.X#Equal(a, b) } 
  true
     ==> (_module.X#Equal(a, b)
       <==> _module.X._h0(a) == _module.X._h0(b)
         && _module.X._h1(a) == _module.X._h1(b)
         && _module.X._h2(a) == _module.X._h2(b)
         && _module.X._h3(a) == _module.X._h3(b)
         && _module.X._h4(a) == _module.X._h4(b)
         && _module.X._h5(a) == _module.X._h5(b)
         && _module.X._h6(a) == _module.X._h6(b)
         && _module.X._h7(a) == _module.X._h7(b)
         && _module.X._h8(a) == _module.X._h8(b)
         && _module.X._h9(a) == _module.X._h9(b)));

// Datatype extensionality axiom: _module.X
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.X#Equal(a, b) } 
  _module.X#Equal(a, b) <==> a == b);

const unique class._module.X: ClassName;

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

// function declaration for _module._default.GenesisBlock
function _module.__default.GenesisBlock() : DatatypeType;

function _module.__default.GenesisBlock#canCall() : bool;

// consequence axiom for _module.__default.GenesisBlock
axiom 5 <= $FunctionContextHeight
   ==> 
  _module.__default.GenesisBlock#canCall() || 5 != $FunctionContextHeight
   ==> $Is(_module.__default.GenesisBlock(), Tclass._module.Block(TInt, TInt, TInt));

function _module.__default.GenesisBlock#requires() : bool;

// #requires axiom for _module.__default.GenesisBlock
axiom _module.__default.GenesisBlock#requires() == true;

// definition axiom for _module.__default.GenesisBlock (revealed)
axiom 5 <= $FunctionContextHeight
   ==> 
  _module.__default.GenesisBlock#canCall() || 5 != $FunctionContextHeight
   ==> _module.__default.GenesisBlock()
     == Lit(#_module.Block.Block($Box(LitInt(0)), Lit(Seq#Empty(): Seq Box), $Box(LitInt(0))));

// definition axiom for _module.__default.GenesisBlock for all literals (revealed)
axiom 5 <= $FunctionContextHeight
   ==> 
  _module.__default.GenesisBlock#canCall() || 5 != $FunctionContextHeight
   ==> _module.__default.GenesisBlock()
     == Lit(#_module.Block.Block($Box(LitInt(0)), Lit(Seq#Empty(): Seq Box), $Box(LitInt(0))));

procedure CheckWellformed$$_module.__default.GenesisBlock();
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure CheckWellformed$$_module.__default.IsGenesisBlock(b#0: DatatypeType
       where $Is(b#0, Tclass._module.Block(TInt, TInt, TInt))
         && $IsAlloc(b#0, Tclass._module.Block(TInt, TInt, TInt), $Heap)
         && $IsA#_module.Block(b#0))
   returns (eq#0: bool);
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.IsGenesisBlock(b#0: DatatypeType
       where $Is(b#0, Tclass._module.Block(TInt, TInt, TInt))
         && $IsAlloc(b#0, Tclass._module.Block(TInt, TInt, TInt), $Heap)
         && $IsA#_module.Block(b#0))
   returns (eq#0: bool);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Block(b#0)
     && $IsA#_module.Block(Lit(_module.__default.GenesisBlock()))
     && _module.__default.GenesisBlock#canCall();
  ensures eq#0 <==> _module.Block#Equal(b#0, _module.__default.GenesisBlock());
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.IsGenesisBlock(b#0: DatatypeType
       where $Is(b#0, Tclass._module.Block(TInt, TInt, TInt))
         && $IsAlloc(b#0, Tclass._module.Block(TInt, TInt, TInt), $Heap)
         && $IsA#_module.Block(b#0))
   returns (eq#0: bool, $_reverifyPost: bool);
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Block(b#0)
     && $IsA#_module.Block(Lit(_module.__default.GenesisBlock()))
     && _module.__default.GenesisBlock#canCall();
  ensures eq#0 <==> _module.Block#Equal(b#0, _module.__default.GenesisBlock());
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.IsGenesisBlock(b#0: DatatypeType) returns (eq#0: bool, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var gb#0: DatatypeType
     where $Is(gb#0, Tclass._module.Block(TInt, TInt, TInt))
       && $IsAlloc(gb#0, Tclass._module.Block(TInt, TInt, TInt), $Heap);

    // AddMethodImpl: IsGenesisBlock, Impl$$_module.__default.IsGenesisBlock
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue195.dfy(13,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue195.dfy(14,10)
    assume true;
    assume _module.__default.GenesisBlock#canCall();
    assume _module.Block.Block_q(Lit(_module.__default.GenesisBlock()));
    assume _module.__default.GenesisBlock#canCall();
    gb#0 := Lit(_module.__default.GenesisBlock());
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue195.dfy(14,26)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue195.dfy(15,6)
    assume true;
    assume $IsA#_module.Block(b#0) && $IsA#_module.Block(gb#0);
    eq#0 := _module.Block#Equal(b#0, gb#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue195.dfy(15,15)"} true;
}



procedure CheckWellformed$$_module.__default._default_Main();
  free requires 9 == $FunctionContextHeight;
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
  free requires 9 == $FunctionContextHeight;
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
  var b#0: DatatypeType
     where $Is(b#0, Tclass._module.Block(TInt, TInt, TInt))
       && $IsAlloc(b#0, Tclass._module.Block(TInt, TInt, TInt), $Heap);
  var eq#0: bool;
  var $rhs##0: bool;
  var b##0: DatatypeType;

    // AddMethodImpl: Main, Impl$$_module.__default._default_Main
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue195.dfy(18,14): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue195.dfy(19,9)
    assume true;
    assume _module.__default.GenesisBlock#canCall();
    assume _module.Block.Block_q(Lit(_module.__default.GenesisBlock()));
    assume _module.__default.GenesisBlock#canCall();
    b#0 := Lit(_module.__default.GenesisBlock());
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue195.dfy(19,25)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue195.dfy(20,27)
    assume true;
    // TrCallStmt: Adding lhs with type bool
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    b##0 := b#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0 := Call$$_module.__default.IsGenesisBlock(b##0);
    // TrCallStmt: After ProcessCallStmt
    eq#0 := $rhs##0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue195.dfy(20,29)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue195.dfy(21,3)
    assume true;
    assert eq#0;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue195.dfy(22,3)
    assume true;
    assume true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue195.dfy(23,9)
    // TrCallStmt: Before ProcessCallStmt
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.TestEq();
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue195.dfy(23,10)"} true;
}



// function declaration for _module._default.TestAny
function _module.__default.TestAny(_module._default.TestAny$G: Ty, a#0: Box, b#0: Box) : bool;

function _module.__default.TestAny#canCall(_module._default.TestAny$G: Ty, a#0: Box, b#0: Box) : bool;

// consequence axiom for _module.__default.TestAny
axiom 7 <= $FunctionContextHeight
   ==> (forall _module._default.TestAny$G: Ty, a#0: Box, b#0: Box :: 
    { _module.__default.TestAny(_module._default.TestAny$G, a#0, b#0) } 
    _module.__default.TestAny#canCall(_module._default.TestAny$G, a#0, b#0)
         || (7 != $FunctionContextHeight
           && 
          $IsBox(a#0, _module._default.TestAny$G)
           && $IsBox(b#0, _module._default.TestAny$G)
           && a#0 == b#0)
       ==> true);

function _module.__default.TestAny#requires(Ty, Box, Box) : bool;

// #requires axiom for _module.__default.TestAny
axiom (forall _module._default.TestAny$G: Ty, a#0: Box, b#0: Box :: 
  { _module.__default.TestAny#requires(_module._default.TestAny$G, a#0, b#0) } 
  $IsBox(a#0, _module._default.TestAny$G)
       && $IsBox(b#0, _module._default.TestAny$G)
     ==> _module.__default.TestAny#requires(_module._default.TestAny$G, a#0, b#0)
       == 
      (a#0
       == b#0));

// definition axiom for _module.__default.TestAny (revealed)
axiom 7 <= $FunctionContextHeight
   ==> (forall _module._default.TestAny$G: Ty, a#0: Box, b#0: Box :: 
    { _module.__default.TestAny(_module._default.TestAny$G, a#0, b#0) } 
    _module.__default.TestAny#canCall(_module._default.TestAny$G, a#0, b#0)
         || (7 != $FunctionContextHeight
           && 
          $IsBox(a#0, _module._default.TestAny$G)
           && $IsBox(b#0, _module._default.TestAny$G)
           && a#0 == b#0)
       ==> _module.__default.TestAny(_module._default.TestAny$G, a#0, b#0) == (a#0 == b#0));

// definition axiom for _module.__default.TestAny for all literals (revealed)
axiom 7 <= $FunctionContextHeight
   ==> (forall _module._default.TestAny$G: Ty, a#0: Box, b#0: Box :: 
    {:weight 3} { _module.__default.TestAny(_module._default.TestAny$G, Lit(a#0), Lit(b#0)) } 
    _module.__default.TestAny#canCall(_module._default.TestAny$G, Lit(a#0), Lit(b#0))
         || (7 != $FunctionContextHeight
           && 
          $IsBox(a#0, _module._default.TestAny$G)
           && $IsBox(b#0, _module._default.TestAny$G)
           && Lit(a#0) == Lit(b#0))
       ==> _module.__default.TestAny(_module._default.TestAny$G, Lit(a#0), Lit(b#0))
         == 
        (Lit(a#0)
         == Lit(b#0)));

procedure CheckWellformed$$_module.__default.TestAny(_module._default.TestAny$G: Ty, 
    a#0: Box where $IsBox(a#0, _module._default.TestAny$G), 
    b#0: Box where $IsBox(b#0, _module._default.TestAny$G));
  free requires 7 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure CheckWellformed$$_module.__default.TestEq();
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.TestEq();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.TestEq() returns ($_reverifyPost: bool);
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.TestEq() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##a#0: bool;
  var ##b#0: bool;
  var ##a#1: char;
  var ##b#1: char;
  var ##a#2: int;
  var ##b#2: int;
  var ##a#3: real;
  var ##b#3: real;
  var m0#0: int where Lit(true);
  var m1#0: int where Lit(true);
  var $rhs#0: int where Lit(true);
  var newtype$check#0: int;
  var $rhs#1: int where Lit(true);
  var newtype$check#1: int;
  var ##a#4: int;
  var ##b#4: int;
  var n0#0: int where LitInt(-100) <= n0#0 && n0#0 < 100;
  var n1#0: int where LitInt(-100) <= n1#0 && n1#0 < 100;
  var $rhs#2: int where LitInt(-100) <= $rhs#2 && $rhs#2 < 100;
  var newtype$check#2: int;
  var $rhs#3: int where LitInt(-100) <= $rhs#3 && $rhs#3 < 100;
  var newtype$check#3: int;
  var ##a#5: int;
  var ##b#5: int;
  var b0#0: bv8;
  var b1#0: bv8;
  var $rhs#4: bv8;
  var $rhs#5: bv8;
  var ##a#6: bv8;
  var ##b#6: bv8;
  var c0#0: bv167;
  var c1#0: bv167;
  var $rhs#6: bv167;
  var $rhs#7: bv167;
  var ##a#7: bv167;
  var ##b#7: bv167;
  var o0#0: Box;
  var o1#0: Box;
  var $rhs#8: Box;
  var $rhs#9: Box;
  var obj#0: ref
     where $Is(obj#0, Tclass._module.MyClass())
       && $IsAlloc(obj#0, Tclass._module.MyClass(), $Heap);
  var $nw: ref;
  var ##a#8: ref;
  var ##b#8: ref;
  var x0#0: DatatypeType
     where $Is(x0#0, Tclass._module.X()) && $IsAlloc(x0#0, Tclass._module.X(), $Heap);
  var newtype$check#4: int;
  var newtype$check#5: int;
  var x1#0: DatatypeType
     where $Is(x1#0, Tclass._module.X()) && $IsAlloc(x1#0, Tclass._module.X(), $Heap);
  var newtype$check#6: int;
  var newtype$check#7: int;
  var ##a#9: Seq Box;
  var ##b#9: Seq Box;
  var ##a#10: Set Box;
  var ##b#10: Set Box;
  var ##a#11: MultiSet Box;
  var ##b#11: MultiSet Box;
  var ##a#12: Map Box Box;
  var ##b#12: Map Box Box;

    // AddMethodImpl: TestEq, Impl$$_module.__default.TestEq
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue195.dfy(38,0): initial state"} true;
    $_reverifyPost := false;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue195.dfy(39,3)
    assume true;
    assume true;
    ##a#0 := Lit(true);
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#0, TBool, $Heap);
    ##b#0 := Lit(true);
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#0, TBool, $Heap);
    assert {:subsumption 0} ##a#0 == ##b#0;
    assume _module.__default.TestAny#canCall(TBool, $Box(Lit(true)), $Box(Lit(true)));
    assume _module.__default.TestAny#canCall(TBool, $Box(Lit(true)), $Box(Lit(true)));
    assume true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue195.dfy(40,3)
    assume true;
    assume true;
    ##a#1 := Lit(char#FromInt(101));
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#1, TChar, $Heap);
    ##b#1 := Lit(char#FromInt(101));
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#1, TChar, $Heap);
    assert {:subsumption 0} ##a#1 == ##b#1;
    assume _module.__default.TestAny#canCall(TChar, $Box(Lit(char#FromInt(101))), $Box(Lit(char#FromInt(101))));
    assume _module.__default.TestAny#canCall(TChar, $Box(Lit(char#FromInt(101))), $Box(Lit(char#FromInt(101))));
    assume true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue195.dfy(41,3)
    assume true;
    assume true;
    ##a#2 := LitInt(12);
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#2, TInt, $Heap);
    ##b#2 := LitInt(12);
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#2, TInt, $Heap);
    assert {:subsumption 0} ##a#2 == ##b#2;
    assume _module.__default.TestAny#canCall(TInt, $Box(LitInt(12)), $Box(LitInt(12)));
    assume _module.__default.TestAny#canCall(TInt, $Box(LitInt(12)), $Box(LitInt(12)));
    assume true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue195.dfy(42,3)
    assume true;
    assume true;
    ##a#3 := LitReal(375e-1);
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#3, TReal, $Heap);
    ##b#3 := LitReal(375e-1);
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#3, TReal, $Heap);
    assert {:subsumption 0} ##a#3 == ##b#3;
    assume _module.__default.TestAny#canCall(TReal, $Box(LitReal(375e-1)), $Box(LitReal(375e-1)));
    assume _module.__default.TestAny#canCall(TReal, $Box(LitReal(375e-1)), $Box(LitReal(375e-1)));
    assume true;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue195.dfy(43,22)
    assume true;
    assume true;
    newtype$check#0 := LitInt(12);
    assume true;
    $rhs#0 := LitInt(12);
    newtype$check#1 := LitInt(12);
    assume true;
    $rhs#1 := LitInt(12);
    m0#0 := $rhs#0;
    m1#0 := $rhs#1;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue195.dfy(43,30)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue195.dfy(44,3)
    assume true;
    assume true;
    ##a#4 := m0#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#4, Tclass._module.nt(), $Heap);
    ##b#4 := m1#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#4, Tclass._module.nt(), $Heap);
    assert {:subsumption 0} ##a#4 == ##b#4;
    assume _module.__default.TestAny#canCall(Tclass._module.nt(), $Box(m0#0), $Box(m1#0));
    assume _module.__default.TestAny#canCall(Tclass._module.nt(), $Box(m0#0), $Box(m1#0));
    assume true;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue195.dfy(45,34)
    assume true;
    assume true;
    newtype$check#2 := LitInt(12);
    assert LitInt(-100) <= newtype$check#2 && newtype$check#2 < 100;
    assume true;
    $rhs#2 := LitInt(12);
    newtype$check#3 := LitInt(12);
    assert LitInt(-100) <= newtype$check#3 && newtype$check#3 < 100;
    assume true;
    $rhs#3 := LitInt(12);
    n0#0 := $rhs#2;
    n1#0 := $rhs#3;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue195.dfy(45,42)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue195.dfy(46,3)
    assume true;
    assume true;
    ##a#5 := n0#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#5, Tclass._module.ntNative(), $Heap);
    ##b#5 := n1#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#5, Tclass._module.ntNative(), $Heap);
    assert {:subsumption 0} ##a#5 == ##b#5;
    assume _module.__default.TestAny#canCall(Tclass._module.ntNative(), $Box(n0#0), $Box(n1#0));
    assume _module.__default.TestAny#canCall(Tclass._module.ntNative(), $Box(n0#0), $Box(n1#0));
    assume true;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue195.dfy(47,24)
    assume true;
    assume true;
    assume true;
    $rhs#4 := Lit(12bv8);
    assume true;
    $rhs#5 := Lit(12bv8);
    b0#0 := $rhs#4;
    b1#0 := $rhs#5;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue195.dfy(47,32)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue195.dfy(48,3)
    assume true;
    assume true;
    ##a#6 := b0#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#6, TBitvector(8), $Heap);
    ##b#6 := b1#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#6, TBitvector(8), $Heap);
    assert {:subsumption 0} ##a#6 == ##b#6;
    assume _module.__default.TestAny#canCall(TBitvector(8), $Box(b0#0), $Box(b1#0));
    assume _module.__default.TestAny#canCall(TBitvector(8), $Box(b0#0), $Box(b1#0));
    assume true;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue195.dfy(49,28)
    assume true;
    assume true;
    assume true;
    $rhs#6 := Lit(12bv167);
    assume true;
    $rhs#7 := Lit(12bv167);
    c0#0 := $rhs#6;
    c1#0 := $rhs#7;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue195.dfy(49,36)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue195.dfy(50,3)
    assume true;
    assume true;
    ##a#7 := c0#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#7, TBitvector(167), $Heap);
    ##b#7 := c1#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#7, TBitvector(167), $Heap);
    assert {:subsumption 0} ##a#7 == ##b#7;
    assume _module.__default.TestAny#canCall(TBitvector(167), $Box(c0#0), $Box(c1#0));
    assume _module.__default.TestAny#canCall(TBitvector(167), $Box(c0#0), $Box(c1#0));
    assume true;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue195.dfy(51,32)
    assume true;
    assume true;
    assume true;
    $rhs#8 := Lit(ORD#FromNat(12));
    assume true;
    $rhs#9 := Lit(ORD#FromNat(12));
    o0#0 := $rhs#8;
    o1#0 := $rhs#9;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue195.dfy(51,40)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue195.dfy(52,3)
    assume true;
    assume true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue195.dfy(53,11)
    assume true;
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._module.MyClass?();
    assume !read($Heap, $nw, alloc);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    obj#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue195.dfy(53,24)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue195.dfy(54,3)
    assume true;
    assume true;
    ##a#8 := obj#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#8, Tclass._module.MyClass(), $Heap);
    ##b#8 := obj#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#8, Tclass._module.MyClass(), $Heap);
    assert {:subsumption 0} ##a#8 == ##b#8;
    assume _module.__default.TestAny#canCall(Tclass._module.MyClass(), $Box(obj#0), $Box(obj#0));
    assume _module.__default.TestAny#canCall(Tclass._module.MyClass(), $Box(obj#0), $Box(obj#0));
    assume true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue195.dfy(56,10)
    assume true;
    newtype$check#4 := LitInt(12);
    newtype$check#5 := LitInt(12);
    assert LitInt(-100) <= newtype$check#5 && newtype$check#5 < 100;
    assume true;
    x0#0 := #_module.X.X(Lit(true), 
      Lit(char#FromInt(101)), 
      LitInt(12), 
      LitReal(375e-1), 
      LitInt(12), 
      LitInt(12), 
      Lit(12bv8), 
      Lit(12bv167), 
      Lit(ORD#FromNat(12)), 
      obj#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue195.dfy(56,59)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue195.dfy(57,10)
    assume true;
    newtype$check#6 := LitInt(12);
    newtype$check#7 := LitInt(12);
    assert LitInt(-100) <= newtype$check#7 && newtype$check#7 < 100;
    assume true;
    x1#0 := #_module.X.X(Lit(true), 
      Lit(char#FromInt(101)), 
      LitInt(12), 
      LitReal(375e-1), 
      LitInt(12), 
      LitInt(12), 
      Lit(12bv8), 
      Lit(12bv167), 
      Lit(ORD#FromNat(12)), 
      obj#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue195.dfy(57,59)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue195.dfy(58,3)
    assume true;
    assume true;
    ##a#9 := Seq#Build(Seq#Empty(): Seq Box, $Box(x0#0));
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#9, TSeq(Tclass._module.X()), $Heap);
    ##b#9 := Seq#Build(Seq#Empty(): Seq Box, $Box(x1#0));
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#9, TSeq(Tclass._module.X()), $Heap);
    assert {:subsumption 0} ##a#9 == ##b#9;
    assume _module.__default.TestAny#canCall(TSeq(Tclass._module.X()), 
      $Box(Seq#Build(Seq#Empty(): Seq Box, $Box(x0#0))), 
      $Box(Seq#Build(Seq#Empty(): Seq Box, $Box(x1#0))));
    assume _module.__default.TestAny#canCall(TSeq(Tclass._module.X()), 
      $Box(Seq#Build(Seq#Empty(): Seq Box, $Box(x0#0))), 
      $Box(Seq#Build(Seq#Empty(): Seq Box, $Box(x1#0))));
    assume true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue195.dfy(59,3)
    assume true;
    assume true;
    ##a#10 := Set#UnionOne(Set#Empty(): Set Box, $Box(x0#0));
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#10, TSet(Tclass._module.X()), $Heap);
    ##b#10 := Set#UnionOne(Set#Empty(): Set Box, $Box(x1#0));
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#10, TSet(Tclass._module.X()), $Heap);
    assert {:subsumption 0} ##a#10 == ##b#10;
    assume _module.__default.TestAny#canCall(TSet(Tclass._module.X()), 
      $Box(Set#UnionOne(Set#Empty(): Set Box, $Box(x0#0))), 
      $Box(Set#UnionOne(Set#Empty(): Set Box, $Box(x1#0))));
    assume _module.__default.TestAny#canCall(TSet(Tclass._module.X()), 
      $Box(Set#UnionOne(Set#Empty(): Set Box, $Box(x0#0))), 
      $Box(Set#UnionOne(Set#Empty(): Set Box, $Box(x1#0))));
    assume true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue195.dfy(60,3)
    assume true;
    assume true;
    ##a#11 := MultiSet#UnionOne(MultiSet#Empty(): MultiSet Box, $Box(x0#0));
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#11, TMultiSet(Tclass._module.X()), $Heap);
    ##b#11 := MultiSet#UnionOne(MultiSet#Empty(): MultiSet Box, $Box(x1#0));
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#11, TMultiSet(Tclass._module.X()), $Heap);
    assert {:subsumption 0} ##a#11 == ##b#11;
    assume _module.__default.TestAny#canCall(TMultiSet(Tclass._module.X()), 
      $Box(MultiSet#UnionOne(MultiSet#Empty(): MultiSet Box, $Box(x0#0))), 
      $Box(MultiSet#UnionOne(MultiSet#Empty(): MultiSet Box, $Box(x1#0))));
    assume _module.__default.TestAny#canCall(TMultiSet(Tclass._module.X()), 
      $Box(MultiSet#UnionOne(MultiSet#Empty(): MultiSet Box, $Box(x0#0))), 
      $Box(MultiSet#UnionOne(MultiSet#Empty(): MultiSet Box, $Box(x1#0))));
    assume true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/git-issue195.dfy(61,3)
    assume true;
    assume true;
    ##a#12 := Map#Build(Map#Empty(): Map Box Box, $Box(x0#0), $Box(n0#0));
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#12, TMap(Tclass._module.X(), Tclass._module.ntNative()), $Heap);
    ##b#12 := Map#Build(Map#Empty(): Map Box Box, $Box(x0#0), $Box(n1#0));
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#12, TMap(Tclass._module.X(), Tclass._module.ntNative()), $Heap);
    assert {:subsumption 0} ##a#12 == ##b#12;
    assume _module.__default.TestAny#canCall(TMap(Tclass._module.X(), Tclass._module.ntNative()), 
      $Box(Map#Build(Map#Empty(): Map Box Box, $Box(x0#0), $Box(n0#0))), 
      $Box(Map#Build(Map#Empty(): Map Box Box, $Box(x0#0), $Box(n1#0))));
    assume _module.__default.TestAny#canCall(TMap(Tclass._module.X(), Tclass._module.ntNative()), 
      $Box(Map#Build(Map#Empty(): Map Box Box, $Box(x0#0), $Box(n0#0))), 
      $Box(Map#Build(Map#Empty(): Map Box Box, $Box(x0#0), $Box(n1#0))));
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

const unique tytagFamily$_#Func2: TyTagFamily;

const unique tytagFamily$_#PartialFunc2: TyTagFamily;

const unique tytagFamily$_#TotalFunc2: TyTagFamily;

const unique tytagFamily$_tuple#2: TyTagFamily;

const unique tytagFamily$_tuple#0: TyTagFamily;

const unique tytagFamily$Block: TyTagFamily;

const unique tytagFamily$ntNative: TyTagFamily;

const unique tytagFamily$MyClass: TyTagFamily;

const unique tytagFamily$nt: TyTagFamily;

const unique tytagFamily$X: TyTagFamily;

const unique tytagFamily$_default: TyTagFamily;

const unique field$u: NameFamily;
