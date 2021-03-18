// Dafny 3.0.0.30204
// Command Line Options: -compile:0 -noVerify /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy -print:./TypeMembers.bpl

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

// Box/unbox axiom for bv11
axiom (forall bx: Box :: 
  { $IsBox(bx, TBitvector(11)) } 
  $IsBox(bx, TBitvector(11))
     ==> $Box($Unbox(bx): bv11) == bx && $Is($Unbox(bx): bv11, TBitvector(11)));

axiom (forall v: bv11 :: { $Is(v, TBitvector(11)) } $Is(v, TBitvector(11)));

axiom (forall v: bv11, heap: Heap :: 
  { $IsAlloc(v, TBitvector(11), heap) } 
  $IsAlloc(v, TBitvector(11), heap));

function {:bvbuiltin "bvand"} and_bv11(bv11, bv11) : bv11;

function {:bvbuiltin "bvor"} or_bv11(bv11, bv11) : bv11;

function {:bvbuiltin "bvxor"} xor_bv11(bv11, bv11) : bv11;

function {:bvbuiltin "bvnot"} not_bv11(bv11) : bv11;

function {:bvbuiltin "bvadd"} add_bv11(bv11, bv11) : bv11;

function {:bvbuiltin "bvsub"} sub_bv11(bv11, bv11) : bv11;

function {:bvbuiltin "bvmul"} mul_bv11(bv11, bv11) : bv11;

function {:bvbuiltin "bvudiv"} div_bv11(bv11, bv11) : bv11;

function {:bvbuiltin "bvurem"} mod_bv11(bv11, bv11) : bv11;

function {:bvbuiltin "bvult"} lt_bv11(bv11, bv11) : bool;

function {:bvbuiltin "bvule"} le_bv11(bv11, bv11) : bool;

function {:bvbuiltin "bvuge"} ge_bv11(bv11, bv11) : bool;

function {:bvbuiltin "bvugt"} gt_bv11(bv11, bv11) : bool;

function {:bvbuiltin "bvshl"} LeftShift_bv11(bv11, bv11) : bv11;

function {:bvbuiltin "bvlshr"} RightShift_bv11(bv11, bv11) : bv11;

function {:bvbuiltin "ext_rotate_left"} LeftRotate_bv11(bv11, bv11) : bv11;

function {:bvbuiltin "ext_rotate_right"} RightRotate_bv11(bv11, bv11) : bv11;

function {:bvbuiltin "(_ int2bv 11)"} nat_to_bv11(int) : bv11;

function {:bvbuiltin "bv2int"} smt_nat_from_bv11(bv11) : int;

function nat_from_bv11(bv11) : int;

axiom (forall b: bv11 :: 
  { nat_from_bv11(b) } 
  0 <= nat_from_bv11(b)
     && nat_from_bv11(b) < 2048
     && nat_from_bv11(b) == smt_nat_from_bv11(b));

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
function #_module.DaTy.Yes() : DatatypeType;

const unique ##_module.DaTy.Yes: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#_module.DaTy.Yes()) == ##_module.DaTy.Yes;

function _module.DaTy.Yes_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.DaTy.Yes_q(d) } 
  _module.DaTy.Yes_q(d) <==> DatatypeCtorId(d) == ##_module.DaTy.Yes);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.DaTy.Yes_q(d) } 
  _module.DaTy.Yes_q(d) ==> d == #_module.DaTy.Yes());

function Tclass._module.DaTy() : Ty;

const unique Tagclass._module.DaTy: TyTag;

// Tclass._module.DaTy Tag
axiom Tag(Tclass._module.DaTy()) == Tagclass._module.DaTy
   && TagFamily(Tclass._module.DaTy()) == tytagFamily$DaTy;

// Box/unbox axiom for Tclass._module.DaTy
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.DaTy()) } 
  $IsBox(bx, Tclass._module.DaTy())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.DaTy()));

// Constructor $Is
axiom $Is(#_module.DaTy.Yes(), Tclass._module.DaTy());

// Constructor $IsAlloc
axiom (forall $h: Heap :: 
  { $IsAlloc(#_module.DaTy.Yes(), Tclass._module.DaTy(), $h) } 
  $IsGoodHeap($h) ==> $IsAlloc(#_module.DaTy.Yes(), Tclass._module.DaTy(), $h));

// Constructor literal
axiom #_module.DaTy.Yes() == Lit(#_module.DaTy.Yes());

// Depth-one case-split function
function $IsA#_module.DaTy(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.DaTy(d) } 
  $IsA#_module.DaTy(d) ==> _module.DaTy.Yes_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.DaTy.Yes_q(d), $Is(d, Tclass._module.DaTy()) } 
  $Is(d, Tclass._module.DaTy()) ==> _module.DaTy.Yes_q(d));

// Datatype extensional equality declaration
function _module.DaTy#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.DaTy.Yes
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.DaTy#Equal(a, b) } 
  true ==> (_module.DaTy#Equal(a, b) <==> true));

// Datatype extensionality axiom: _module.DaTy
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.DaTy#Equal(a, b) } 
  _module.DaTy#Equal(a, b) <==> a == b);

const unique class._module.DaTy: ClassName;

// function declaration for _module.DaTy.W
function _module.DaTy.W(this: DatatypeType) : int;

function _module.DaTy.W#canCall(this: DatatypeType) : bool;

// consequence axiom for _module.DaTy.W
axiom 27 <= $FunctionContextHeight
   ==> (forall this: DatatypeType :: 
    { _module.DaTy.W(this) } 
    _module.DaTy.W#canCall(this)
         || (27 != $FunctionContextHeight && $Is(this, Tclass._module.DaTy()))
       ==> true);

function _module.DaTy.W#requires(DatatypeType) : bool;

// #requires axiom for _module.DaTy.W
axiom (forall this: DatatypeType :: 
  { _module.DaTy.W#requires(this) } 
  $Is(this, Tclass._module.DaTy()) ==> _module.DaTy.W#requires(this) == true);

// definition axiom for _module.DaTy.W (revealed)
axiom 27 <= $FunctionContextHeight
   ==> (forall this: DatatypeType :: 
    { _module.DaTy.W(this) } 
    _module.DaTy.W#canCall(this)
         || (27 != $FunctionContextHeight && $Is(this, Tclass._module.DaTy()))
       ==> _module.DaTy.W(this) == LitInt(10));

// definition axiom for _module.DaTy.W for all literals (revealed)
axiom 27 <= $FunctionContextHeight
   ==> (forall this: DatatypeType :: 
    {:weight 3} { _module.DaTy.W(Lit(this)) } 
    _module.DaTy.W#canCall(Lit(this))
         || (27 != $FunctionContextHeight && $Is(this, Tclass._module.DaTy()))
       ==> _module.DaTy.W(Lit(this)) == LitInt(10));

procedure CheckWellformed$$_module.DaTy.W(this: DatatypeType
       where $Is(this, Tclass._module.DaTy()) && $IsAlloc(this, Tclass._module.DaTy(), $Heap));
  free requires 27 == $FunctionContextHeight;
  modifies $Heap, $Tick;



// function declaration for _module.DaTy.Q
function _module.DaTy.Q() : int;

function _module.DaTy.Q#canCall() : bool;

// consequence axiom for _module.DaTy.Q
axiom 28 <= $FunctionContextHeight
   ==> 
  _module.DaTy.Q#canCall() || 28 != $FunctionContextHeight
   ==> true;

function _module.DaTy.Q#requires() : bool;

// #requires axiom for _module.DaTy.Q
axiom _module.DaTy.Q#requires() == true;

// definition axiom for _module.DaTy.Q (revealed)
axiom 28 <= $FunctionContextHeight
   ==> 
  _module.DaTy.Q#canCall() || 28 != $FunctionContextHeight
   ==> _module.DaTy.Q() == LitInt(13);

// definition axiom for _module.DaTy.Q for all literals (revealed)
axiom 28 <= $FunctionContextHeight
   ==> 
  _module.DaTy.Q#canCall() || 28 != $FunctionContextHeight
   ==> _module.DaTy.Q() == LitInt(13);

procedure CheckWellformed$$_module.DaTy.Q();
  free requires 28 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure CheckWellformed$$_module.Pos(x#0: int);
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Pos(x#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;


    // AddWellformednessCheck for newtype Pos
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(30,8): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume 0 < x#0;
    }
    else
    {
        assume true;
        assert 0 < 1;
    }
}



function Tclass._module.Pos() : Ty;

const unique Tagclass._module.Pos: TyTag;

// Tclass._module.Pos Tag
axiom Tag(Tclass._module.Pos()) == Tagclass._module.Pos
   && TagFamily(Tclass._module.Pos()) == tytagFamily$Pos;

// Box/unbox axiom for Tclass._module.Pos
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Pos()) } 
  $IsBox(bx, Tclass._module.Pos())
     ==> $Box($Unbox(bx): int) == bx && $Is($Unbox(bx): int, Tclass._module.Pos()));

// _module.Pos: newtype $Is
axiom (forall x#0: int :: 
  { $Is(x#0, Tclass._module.Pos()) } 
  $Is(x#0, Tclass._module.Pos()) <==> 0 < x#0);

// _module.Pos: newtype $IsAlloc
axiom (forall x#0: int, $h: Heap :: 
  { $IsAlloc(x#0, Tclass._module.Pos(), $h) } 
  $IsAlloc(x#0, Tclass._module.Pos(), $h));

const unique class._module.Pos: ClassName;

// function declaration for _module.Pos.Func
function _module.Pos.Func(y#0: int) : int;

function _module.Pos.Func#canCall(y#0: int) : bool;

// consequence axiom for _module.Pos.Func
axiom 5 <= $FunctionContextHeight
   ==> (forall y#0: int :: 
    { _module.Pos.Func(y#0) } 
    _module.Pos.Func#canCall(y#0) || (5 != $FunctionContextHeight && 0 < y#0)
       ==> true);

function _module.Pos.Func#requires(int) : bool;

// #requires axiom for _module.Pos.Func
axiom (forall y#0: int :: 
  { _module.Pos.Func#requires(y#0) } 
  0 < y#0 ==> _module.Pos.Func#requires(y#0) == true);

// definition axiom for _module.Pos.Func (revealed)
axiom 5 <= $FunctionContextHeight
   ==> (forall y#0: int :: 
    { _module.Pos.Func(y#0) } 
    _module.Pos.Func#canCall(y#0) || (5 != $FunctionContextHeight && 0 < y#0)
       ==> _module.Pos.Func(y#0) == y#0 + 3);

// definition axiom for _module.Pos.Func for all literals (revealed)
axiom 5 <= $FunctionContextHeight
   ==> (forall y#0: int :: 
    {:weight 3} { _module.Pos.Func(LitInt(y#0)) } 
    _module.Pos.Func#canCall(LitInt(y#0))
         || (5 != $FunctionContextHeight && 0 < y#0)
       ==> _module.Pos.Func(LitInt(y#0)) == LitInt(y#0 + 3));

procedure CheckWellformed$$_module.Pos.Func(y#0: int where 0 < y#0);
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Pos.Func(y#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var newtype$check#0: int;
  var newtype$check#1: int;


    // AddWellformednessCheck for function Func
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(32,25): initial state"} true;
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
        newtype$check#0 := LitInt(3);
        assert 0 < newtype$check#0;
        newtype$check#1 := y#0 + 3;
        assert 0 < newtype$check#1;
        assume _module.Pos.Func(y#0) == y#0 + 3;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.Pos.Func(y#0), TInt);
    }
}



// function declaration for _module.Pos.Gittit
function _module.Pos.Gittit(this: int) : int;

function _module.Pos.Gittit#canCall(this: int) : bool;

// consequence axiom for _module.Pos.Gittit
axiom 29 <= $FunctionContextHeight
   ==> (forall this: int :: 
    { _module.Pos.Gittit(this) } 
    _module.Pos.Gittit#canCall(this) || (29 != $FunctionContextHeight && 0 < this)
       ==> true);

function _module.Pos.Gittit#requires(int) : bool;

// #requires axiom for _module.Pos.Gittit
axiom (forall $Heap: Heap, this: int :: 
  { _module.Pos.Gittit#requires(this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap) && 0 < this ==> _module.Pos.Gittit#requires(this) == true);

// definition axiom for _module.Pos.Gittit (revealed)
axiom 29 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: int :: 
    { _module.Pos.Gittit(this), $IsGoodHeap($Heap) } 
    _module.Pos.Gittit#canCall(this)
         || (29 != $FunctionContextHeight && $IsGoodHeap($Heap) && 0 < this)
       ==> _module.Pos.Gittit(this) == this + 2);

// definition axiom for _module.Pos.Gittit for all literals (revealed)
axiom 29 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: int :: 
    {:weight 3} { _module.Pos.Gittit(LitInt(this)), $IsGoodHeap($Heap) } 
    _module.Pos.Gittit#canCall(LitInt(this))
         || (29 != $FunctionContextHeight && $IsGoodHeap($Heap) && 0 < this)
       ==> _module.Pos.Gittit(LitInt(this)) == LitInt(this + 2));

procedure CheckWellformed$$_module.Pos.Gittit(this: int where 0 < this);
  free requires 29 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Pos.Gittit(this: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var newtype$check#0: int;
  var newtype$check#1: int;


    // AddWellformednessCheck for function Gittit
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(33,18): initial state"} true;
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
        newtype$check#0 := LitInt(2);
        assert 0 < newtype$check#0;
        newtype$check#1 := this + 2;
        assert 0 < newtype$check#1;
        assume _module.Pos.Gittit(this) == this + 2;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.Pos.Gittit(this), TInt);
    }
}



procedure CheckWellformed$$_module.Pos.Method(y#0: int where 0 < y#0) returns (r#0: int);
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Pos.Method(y#0: int) returns (r#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var newtype$check#0: int;
  var newtype$check#1: int;

    // AddMethodImpl: Method, CheckWellformed$$_module.Pos.Method
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(34,16): initial state"} true;
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
    assume $HeapSucc(old($Heap), $Heap);
    havoc r#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(34,58): post-state"} true;
    newtype$check#0 := LitInt(3);
    assert 0 < newtype$check#0;
    newtype$check#1 := y#0 + 3;
    assert 0 < newtype$check#1;
    assume r#0 == y#0 + 3;
}



procedure Call$$_module.Pos.Method(y#0: int where 0 < y#0) returns (r#0: int);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures r#0 == y#0 + 3;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Pos.Method(y#0: int where 0 < y#0) returns (r#0: int, $_reverifyPost: bool);
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures r#0 == y#0 + 3;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Pos.Method(y#0: int) returns (r#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var newtype$check#2: int;
  var newtype$check#3: int;

    // AddMethodImpl: Method, Impl$$_module.Pos.Method
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(34,76): initial state"} true;
    $_reverifyPost := false;
    // ----- return statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(34,79)
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(34,79)
    assume true;
    newtype$check#2 := LitInt(3);
    assert 0 < newtype$check#2;
    newtype$check#3 := y#0 + 3;
    assert 0 < newtype$check#3;
    assume true;
    r#0 := y#0 + 3;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(34,99)"} true;
    return;
}



procedure CheckWellformed$$_module.Pos.Collect(this: int where 0 < this) returns (r#0: int);
  free requires 30 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Pos.Collect(this: int) returns (r#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var newtype$check#0: int;
  var newtype$check#1: int;

    // AddMethodImpl: Collect, CheckWellformed$$_module.Pos.Collect
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(35,9): initial state"} true;
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
    assume $HeapSucc(old($Heap), $Heap);
    havoc r#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(35,46): post-state"} true;
    newtype$check#0 := LitInt(2);
    assert 0 < newtype$check#0;
    newtype$check#1 := this + 2;
    assert 0 < newtype$check#1;
    assume r#0 == this + 2;
}



procedure Call$$_module.Pos.Collect(this: int where 0 < this) returns (r#0: int);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures r#0 == this + 2;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Pos.Collect(this: int where 0 < this) returns (r#0: int, $_reverifyPost: bool);
  free requires 30 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures r#0 == this + 2;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Pos.Collect(this: int) returns (r#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var newtype$check#2: int;
  var newtype$check#3: int;

    // AddMethodImpl: Collect, Impl$$_module.Pos.Collect
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(35,67): initial state"} true;
    $_reverifyPost := false;
    // ----- return statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(35,70)
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(35,70)
    assume true;
    newtype$check#2 := LitInt(2);
    assert 0 < newtype$check#2;
    newtype$check#3 := this + 2;
    assert 0 < newtype$check#3;
    assume true;
    r#0 := this + 2;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(35,93)"} true;
    return;
}



// Constructor function declaration
function #_module.Dt.Blue() : DatatypeType;

const unique ##_module.Dt.Blue: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#_module.Dt.Blue()) == ##_module.Dt.Blue;

function _module.Dt.Blue_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Dt.Blue_q(d) } 
  _module.Dt.Blue_q(d) <==> DatatypeCtorId(d) == ##_module.Dt.Blue);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Dt.Blue_q(d) } 
  _module.Dt.Blue_q(d) ==> d == #_module.Dt.Blue());

function Tclass._module.Dt(Ty) : Ty;

const unique Tagclass._module.Dt: TyTag;

// Tclass._module.Dt Tag
axiom (forall _module.Dt$A: Ty :: 
  { Tclass._module.Dt(_module.Dt$A) } 
  Tag(Tclass._module.Dt(_module.Dt$A)) == Tagclass._module.Dt
     && TagFamily(Tclass._module.Dt(_module.Dt$A)) == tytagFamily$Dt);

// Tclass._module.Dt injectivity 0
axiom (forall _module.Dt$A: Ty :: 
  { Tclass._module.Dt(_module.Dt$A) } 
  Tclass._module.Dt_0(Tclass._module.Dt(_module.Dt$A)) == _module.Dt$A);

function Tclass._module.Dt_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.Dt
axiom (forall _module.Dt$A: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.Dt(_module.Dt$A)) } 
  $IsBox(bx, Tclass._module.Dt(_module.Dt$A))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Dt(_module.Dt$A)));

// Constructor $Is
axiom (forall _module.Dt$A: Ty :: 
  { $Is(#_module.Dt.Blue(), Tclass._module.Dt(_module.Dt$A)) } 
  $Is(#_module.Dt.Blue(), Tclass._module.Dt(_module.Dt$A)));

// Constructor $IsAlloc
axiom (forall _module.Dt$A: Ty, $h: Heap :: 
  { $IsAlloc(#_module.Dt.Blue(), Tclass._module.Dt(_module.Dt$A), $h) } 
  $IsGoodHeap($h)
     ==> $IsAlloc(#_module.Dt.Blue(), Tclass._module.Dt(_module.Dt$A), $h));

// Constructor literal
axiom #_module.Dt.Blue() == Lit(#_module.Dt.Blue());

// Constructor function declaration
function #_module.Dt.Bucket(real) : DatatypeType;

const unique ##_module.Dt.Bucket: DtCtorId;

// Constructor identifier
axiom (forall a#5#0#0: real :: 
  { #_module.Dt.Bucket(a#5#0#0) } 
  DatatypeCtorId(#_module.Dt.Bucket(a#5#0#0)) == ##_module.Dt.Bucket);

function _module.Dt.Bucket_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Dt.Bucket_q(d) } 
  _module.Dt.Bucket_q(d) <==> DatatypeCtorId(d) == ##_module.Dt.Bucket);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Dt.Bucket_q(d) } 
  _module.Dt.Bucket_q(d)
     ==> (exists a#6#0#0: real :: d == #_module.Dt.Bucket(a#6#0#0)));

// Constructor $Is
axiom (forall _module.Dt$A: Ty, a#7#0#0: real :: 
  { $Is(#_module.Dt.Bucket(a#7#0#0), Tclass._module.Dt(_module.Dt$A)) } 
  $Is(#_module.Dt.Bucket(a#7#0#0), Tclass._module.Dt(_module.Dt$A))
     <==> $Is(a#7#0#0, TReal));

// Constructor $IsAlloc
axiom (forall _module.Dt$A: Ty, a#8#0#0: real, $h: Heap :: 
  { $IsAlloc(#_module.Dt.Bucket(a#8#0#0), Tclass._module.Dt(_module.Dt$A), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Dt.Bucket(a#8#0#0), Tclass._module.Dt(_module.Dt$A), $h)
       <==> $IsAlloc(a#8#0#0, TReal, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Dt.diameter(d), TReal, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Dt.Bucket_q(d)
       && (exists _module.Dt$A: Ty :: 
        { $IsAlloc(d, Tclass._module.Dt(_module.Dt$A), $h) } 
        $IsAlloc(d, Tclass._module.Dt(_module.Dt$A), $h))
     ==> $IsAlloc(_module.Dt.diameter(d), TReal, $h));

// Constructor literal
axiom (forall a#9#0#0: real :: 
  { #_module.Dt.Bucket(LitReal(a#9#0#0)) } 
  #_module.Dt.Bucket(LitReal(a#9#0#0)) == Lit(#_module.Dt.Bucket(a#9#0#0)));

function _module.Dt.diameter(DatatypeType) : real;

// Constructor injectivity
axiom (forall a#10#0#0: real :: 
  { #_module.Dt.Bucket(a#10#0#0) } 
  _module.Dt.diameter(#_module.Dt.Bucket(a#10#0#0)) == a#10#0#0);

// Constructor function declaration
function #_module.Dt.Business(bool, Box) : DatatypeType;

const unique ##_module.Dt.Business: DtCtorId;

// Constructor identifier
axiom (forall a#11#0#0: bool, a#11#1#0: Box :: 
  { #_module.Dt.Business(a#11#0#0, a#11#1#0) } 
  DatatypeCtorId(#_module.Dt.Business(a#11#0#0, a#11#1#0))
     == ##_module.Dt.Business);

function _module.Dt.Business_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Dt.Business_q(d) } 
  _module.Dt.Business_q(d) <==> DatatypeCtorId(d) == ##_module.Dt.Business);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Dt.Business_q(d) } 
  _module.Dt.Business_q(d)
     ==> (exists a#12#0#0: bool, a#12#1#0: Box :: 
      d == #_module.Dt.Business(a#12#0#0, a#12#1#0)));

// Constructor $Is
axiom (forall _module.Dt$A: Ty, a#13#0#0: bool, a#13#1#0: Box :: 
  { $Is(#_module.Dt.Business(a#13#0#0, a#13#1#0), Tclass._module.Dt(_module.Dt$A)) } 
  $Is(#_module.Dt.Business(a#13#0#0, a#13#1#0), Tclass._module.Dt(_module.Dt$A))
     <==> $Is(a#13#0#0, TBool) && $IsBox(a#13#1#0, _module.Dt$A));

// Constructor $IsAlloc
axiom (forall _module.Dt$A: Ty, a#14#0#0: bool, a#14#1#0: Box, $h: Heap :: 
  { $IsAlloc(#_module.Dt.Business(a#14#0#0, a#14#1#0), Tclass._module.Dt(_module.Dt$A), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Dt.Business(a#14#0#0, a#14#1#0), Tclass._module.Dt(_module.Dt$A), $h)
       <==> $IsAlloc(a#14#0#0, TBool, $h) && $IsAllocBox(a#14#1#0, _module.Dt$A, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Dt.trendy(d), TBool, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Dt.Business_q(d)
       && (exists _module.Dt$A: Ty :: 
        { $IsAlloc(d, Tclass._module.Dt(_module.Dt$A), $h) } 
        $IsAlloc(d, Tclass._module.Dt(_module.Dt$A), $h))
     ==> $IsAlloc(_module.Dt.trendy(d), TBool, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _module.Dt$A: Ty, $h: Heap :: 
  { $IsAllocBox(_module.Dt.a(d), _module.Dt$A, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Dt.Business_q(d)
       && $IsAlloc(d, Tclass._module.Dt(_module.Dt$A), $h)
     ==> $IsAllocBox(_module.Dt.a(d), _module.Dt$A, $h));

// Constructor literal
axiom (forall a#15#0#0: bool, a#15#1#0: Box :: 
  { #_module.Dt.Business(Lit(a#15#0#0), Lit(a#15#1#0)) } 
  #_module.Dt.Business(Lit(a#15#0#0), Lit(a#15#1#0))
     == Lit(#_module.Dt.Business(a#15#0#0, a#15#1#0)));

function _module.Dt.trendy(DatatypeType) : bool;

// Constructor injectivity
axiom (forall a#16#0#0: bool, a#16#1#0: Box :: 
  { #_module.Dt.Business(a#16#0#0, a#16#1#0) } 
  _module.Dt.trendy(#_module.Dt.Business(a#16#0#0, a#16#1#0)) == a#16#0#0);

function _module.Dt.a(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#17#0#0: bool, a#17#1#0: Box :: 
  { #_module.Dt.Business(a#17#0#0, a#17#1#0) } 
  _module.Dt.a(#_module.Dt.Business(a#17#0#0, a#17#1#0)) == a#17#1#0);

// Inductive rank
axiom (forall a#18#0#0: bool, a#18#1#0: Box :: 
  { #_module.Dt.Business(a#18#0#0, a#18#1#0) } 
  BoxRank(a#18#1#0) < DtRank(#_module.Dt.Business(a#18#0#0, a#18#1#0)));

// Depth-one case-split function
function $IsA#_module.Dt(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.Dt(d) } 
  $IsA#_module.Dt(d)
     ==> _module.Dt.Blue_q(d) || _module.Dt.Bucket_q(d) || _module.Dt.Business_q(d));

// Questionmark data type disjunctivity
axiom (forall _module.Dt$A: Ty, d: DatatypeType :: 
  { _module.Dt.Business_q(d), $Is(d, Tclass._module.Dt(_module.Dt$A)) } 
    { _module.Dt.Bucket_q(d), $Is(d, Tclass._module.Dt(_module.Dt$A)) } 
    { _module.Dt.Blue_q(d), $Is(d, Tclass._module.Dt(_module.Dt$A)) } 
  $Is(d, Tclass._module.Dt(_module.Dt$A))
     ==> _module.Dt.Blue_q(d) || _module.Dt.Bucket_q(d) || _module.Dt.Business_q(d));

// Datatype extensional equality declaration
function _module.Dt#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.Dt.Blue
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Dt#Equal(a, b), _module.Dt.Blue_q(a) } 
    { _module.Dt#Equal(a, b), _module.Dt.Blue_q(b) } 
  _module.Dt.Blue_q(a) && _module.Dt.Blue_q(b)
     ==> (_module.Dt#Equal(a, b) <==> true));

// Datatype extensional equality definition: #_module.Dt.Bucket
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Dt#Equal(a, b), _module.Dt.Bucket_q(a) } 
    { _module.Dt#Equal(a, b), _module.Dt.Bucket_q(b) } 
  _module.Dt.Bucket_q(a) && _module.Dt.Bucket_q(b)
     ==> (_module.Dt#Equal(a, b) <==> _module.Dt.diameter(a) == _module.Dt.diameter(b)));

// Datatype extensional equality definition: #_module.Dt.Business
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Dt#Equal(a, b), _module.Dt.Business_q(a) } 
    { _module.Dt#Equal(a, b), _module.Dt.Business_q(b) } 
  _module.Dt.Business_q(a) && _module.Dt.Business_q(b)
     ==> (_module.Dt#Equal(a, b)
       <==> _module.Dt.trendy(a) == _module.Dt.trendy(b)
         && _module.Dt.a(a) == _module.Dt.a(b)));

// Datatype extensionality axiom: _module.Dt
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Dt#Equal(a, b) } 
  _module.Dt#Equal(a, b) <==> a == b);

const unique class._module.Dt: ClassName;

function {:inline} _module.Dt.c(_module.Dt$A: Ty, this: DatatypeType) : int
{
  (if _module.Dt.Blue_q(this) then 18 else 19)
}

procedure CheckWellformed$$_module.Dt.c(_module.Dt$A: Ty, 
    this: DatatypeType
       where $Is(this, Tclass._module.Dt(_module.Dt$A))
         && $IsAlloc(this, Tclass._module.Dt(_module.Dt$A), $Heap));
  free requires 34 == $FunctionContextHeight;
  modifies $Heap;



// Dt.c: Type axiom
axiom 34 < $FunctionContextHeight
   ==> (forall _module.Dt$A: Ty, $o: DatatypeType :: 
    { _module.Dt.c(_module.Dt$A, $o) } 
    $Is(_module.Dt.c(_module.Dt$A, $o), TInt));

// Dt.c: Allocation axiom
axiom 34 < $FunctionContextHeight
   ==> (forall _module.Dt$A: Ty, $h: Heap, $o: DatatypeType :: 
    { _module.Dt.c(_module.Dt$A, $o), $IsAlloc($o, Tclass._module.Dt(_module.Dt$A), $h) } 
    $IsGoodHeap($h) && $IsAlloc($o, Tclass._module.Dt(_module.Dt$A), $h)
       ==> $IsAlloc(_module.Dt.c(_module.Dt$A, $o), TInt, $h));

function {:inline} _module.Dt.g(_module.Dt$A: Ty) : int
{
  LitInt(22)
}

procedure CheckWellformed$$_module.Dt.g(_module.Dt$A: Ty);
  free requires 21 == $FunctionContextHeight;
  modifies $Heap;



// Dt.g: Type axiom
axiom 21 < $FunctionContextHeight
   ==> (forall _module.Dt$A: Ty :: 
    { _module.Dt.g(_module.Dt$A) } 
    $Is(_module.Dt.g(_module.Dt$A), TInt));

// Dt.g: Allocation axiom
axiom 21 < $FunctionContextHeight
   ==> (forall _module.Dt$A: Ty, $h: Heap :: 
    { $IsAlloc(_module.Dt.g(_module.Dt$A), TInt, $h) } 
    $IsGoodHeap($h) ==> $IsAlloc(_module.Dt.g(_module.Dt$A), TInt, $h));

// function declaration for _module.Dt.F
function _module.Dt.F(_module.Dt$A: Ty, this: DatatypeType, x#0: int) : int;

function _module.Dt.F#canCall(_module.Dt$A: Ty, this: DatatypeType, x#0: int) : bool;

// consequence axiom for _module.Dt.F
axiom 33 <= $FunctionContextHeight
   ==> (forall _module.Dt$A: Ty, this: DatatypeType, x#0: int :: 
    { _module.Dt.F(_module.Dt$A, this, x#0) } 
    _module.Dt.F#canCall(_module.Dt$A, this, x#0)
         || (33 != $FunctionContextHeight && $Is(this, Tclass._module.Dt(_module.Dt$A)))
       ==> true);

function _module.Dt.F#requires(Ty, DatatypeType, int) : bool;

// #requires axiom for _module.Dt.F
axiom (forall _module.Dt$A: Ty, $Heap: Heap, this: DatatypeType, x#0: int :: 
  { _module.Dt.F#requires(_module.Dt$A, this, x#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      $Is(this, Tclass._module.Dt(_module.Dt$A))
       && $IsAlloc(this, Tclass._module.Dt(_module.Dt$A), $Heap)
     ==> _module.Dt.F#requires(_module.Dt$A, this, x#0) == true);

// definition axiom for _module.Dt.F (revealed)
axiom 33 <= $FunctionContextHeight
   ==> (forall _module.Dt$A: Ty, $Heap: Heap, this: DatatypeType, x#0: int :: 
    { _module.Dt.F(_module.Dt$A, this, x#0), $IsGoodHeap($Heap) } 
    _module.Dt.F#canCall(_module.Dt$A, this, x#0)
         || (33 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          $Is(this, Tclass._module.Dt(_module.Dt$A))
           && $IsAlloc(this, Tclass._module.Dt(_module.Dt$A), $Heap))
       ==> _module.Dt.F(_module.Dt$A, this, x#0)
         == x#0
           + (if _module.Dt.Bucket_q(this)
             then _System.real.Floor(_module.Dt.diameter(this))
             else 25));

// definition axiom for _module.Dt.F for all literals (revealed)
axiom 33 <= $FunctionContextHeight
   ==> (forall _module.Dt$A: Ty, $Heap: Heap, this: DatatypeType, x#0: int :: 
    {:weight 3} { _module.Dt.F(_module.Dt$A, Lit(this), LitInt(x#0)), $IsGoodHeap($Heap) } 
    _module.Dt.F#canCall(_module.Dt$A, Lit(this), LitInt(x#0))
         || (33 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          $Is(this, Tclass._module.Dt(_module.Dt$A))
           && $IsAlloc(this, Tclass._module.Dt(_module.Dt$A), $Heap))
       ==> _module.Dt.F(_module.Dt$A, Lit(this), LitInt(x#0))
         == x#0
           + (if _module.Dt.Bucket_q(Lit(this))
             then _System.real.Floor(LitReal(_module.Dt.diameter(Lit(this))))
             else 25));

procedure CheckWellformed$$_module.Dt.F(_module.Dt$A: Ty, 
    this: DatatypeType
       where $Is(this, Tclass._module.Dt(_module.Dt$A))
         && $IsAlloc(this, Tclass._module.Dt(_module.Dt$A), $Heap), 
    x#0: int);
  free requires 33 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Dt.F(_module.Dt$A: Ty, this: DatatypeType, x#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;


    // AddWellformednessCheck for function F
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(87,18): initial state"} true;
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
        if (_module.Dt.Bucket_q(this))
        {
            assert _module.Dt.Bucket_q(this);
        }
        else
        {
        }

        assume _module.Dt.F(_module.Dt$A, this, x#0)
           == x#0
             + (if _module.Dt.Bucket_q(this)
               then _System.real.Floor(_module.Dt.diameter(this))
               else 25);
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.Dt.F(_module.Dt$A, this, x#0), TInt);
    }
}



// function declaration for _module.Dt.G
function _module.Dt.G(_module.Dt$A: Ty, x#0: int) : int;

function _module.Dt.G#canCall(_module.Dt$A: Ty, x#0: int) : bool;

// consequence axiom for _module.Dt.G
axiom 32 <= $FunctionContextHeight
   ==> (forall _module.Dt$A: Ty, x#0: int :: 
    { _module.Dt.G(_module.Dt$A, x#0) } 
    _module.Dt.G#canCall(_module.Dt$A, x#0) || 32 != $FunctionContextHeight ==> true);

function _module.Dt.G#requires(Ty, int) : bool;

// #requires axiom for _module.Dt.G
axiom (forall _module.Dt$A: Ty, x#0: int :: 
  { _module.Dt.G#requires(_module.Dt$A, x#0) } 
  _module.Dt.G#requires(_module.Dt$A, x#0) == true);

// definition axiom for _module.Dt.G (revealed)
axiom 32 <= $FunctionContextHeight
   ==> (forall _module.Dt$A: Ty, x#0: int :: 
    { _module.Dt.G(_module.Dt$A, x#0) } 
    _module.Dt.G#canCall(_module.Dt$A, x#0) || 32 != $FunctionContextHeight
       ==> _module.Dt.G(_module.Dt$A, x#0) == Mul(LitInt(2), x#0));

// definition axiom for _module.Dt.G for all literals (revealed)
axiom 32 <= $FunctionContextHeight
   ==> (forall _module.Dt$A: Ty, x#0: int :: 
    {:weight 3} { _module.Dt.G(_module.Dt$A, LitInt(x#0)) } 
    _module.Dt.G#canCall(_module.Dt$A, LitInt(x#0)) || 32 != $FunctionContextHeight
       ==> _module.Dt.G(_module.Dt$A, LitInt(x#0)) == LitInt(Mul(LitInt(2), LitInt(x#0))));

procedure CheckWellformed$$_module.Dt.G(_module.Dt$A: Ty, x#0: int);
  free requires 32 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure CheckWellformed$$_module.Dt.M(_module.Dt$A: Ty, 
    this: DatatypeType
       where $Is(this, Tclass._module.Dt(_module.Dt$A))
         && $IsAlloc(this, Tclass._module.Dt(_module.Dt$A), $Heap), 
    x#0: int)
   returns (y#0: int, 
    d#0: DatatypeType
       where $Is(d#0, Tclass._module.Dt(_module.Dt$A))
         && $IsAlloc(d#0, Tclass._module.Dt(_module.Dt$A), $Heap));
  free requires 10 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Dt.M(_module.Dt$A: Ty, 
    this: DatatypeType
       where $Is(this, Tclass._module.Dt(_module.Dt$A))
         && $IsAlloc(this, Tclass._module.Dt(_module.Dt$A), $Heap), 
    x#0: int)
   returns (y#0: int, 
    d#0: DatatypeType
       where $Is(d#0, Tclass._module.Dt(_module.Dt$A))
         && $IsAlloc(d#0, Tclass._module.Dt(_module.Dt$A), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Dt.M(_module.Dt$A: Ty, 
    this: DatatypeType
       where $Is(this, Tclass._module.Dt(_module.Dt$A))
         && $IsAlloc(this, Tclass._module.Dt(_module.Dt$A), $Heap), 
    x#0: int)
   returns (y#0: int, 
    d#0: DatatypeType
       where $Is(d#0, Tclass._module.Dt(_module.Dt$A))
         && $IsAlloc(d#0, Tclass._module.Dt(_module.Dt$A), $Heap), 
    $_reverifyPost: bool);
  free requires 10 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Dt.M(_module.Dt$A: Ty, this: DatatypeType, x#0: int)
   returns (y#0: int, d#0: DatatypeType, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var z#0: int;
  var $rhs##0: int;
  var x##0: int;
  var $rhs##1: int;
  var x##1: int;
  var _mcc#1#1_0: bool;
  var _mcc#2#1_0: Box;
  var a#1_0: Box;
  var let#1_0#0#0: Box;
  var t#1_0: bool;
  var let#1_1#0#0: bool;
  var dt_update_tmp#1#Z#1_0: DatatypeType;
  var let#1_2#0#0: DatatypeType;
  var dt_update#trendy#0#Z#1_0: bool;
  var let#1_3#0#0: bool;
  var _mcc#0#2_0: real;
  var dm#2_0: real;
  var let#2_0#0#0: real;
  var dt_update_tmp#0#Z#2_0: DatatypeType;
  var let#2_1#0#0: DatatypeType;
  var dt_update#diameter#0#Z#2_0: real;
  var let#2_2#0#0: real;

    // AddMethodImpl: M, Impl$$_module.Dt.M
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(93,46): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(94,5)
    assume $IsA#_module.Dt(this);
    if (_module.Dt#Equal(this, #_module.Dt.Blue()))
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(95,9)
        assume true;
        assume true;
        y#0 := x#0;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(95,12)"} true;
    }
    else
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(97,9)
        assume true;
        assume true;
        y#0 := LitInt(9);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(97,12)"} true;
    }

    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(99,27)
    assume true;
    // TrCallStmt: Adding lhs with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##0 := LitInt(3);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0 := Call$$_module.Dt.RecursiveZero(_module.Dt$A, this, x##0);
    // TrCallStmt: After ProcessCallStmt
    z#0 := $rhs##0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(99,29)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(100,7)
    assume true;
    assume true;
    y#0 := y#0 + z#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(100,14)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(101,29)
    assume true;
    // TrCallStmt: Adding lhs with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##1 := LitInt(3);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##1 := Call$$_module.Dt.StaticRecursiveZero(_module.Dt$A, x##1);
    // TrCallStmt: After ProcessCallStmt
    z#0 := $rhs##1;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(101,31)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(102,7)
    assume true;
    assume true;
    y#0 := y#0 + z#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(102,14)"} true;
    assume true;
    havoc _mcc#1#1_0, _mcc#2#1_0;
    havoc _mcc#0#2_0;
    if (this == #_module.Dt.Blue())
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(105,7)
        assume true;
        assert y#0 == x#0;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(106,9)
        assume true;
        assume true;
        d#0 := Lit(#_module.Dt.Bucket(LitReal(0e0)));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(106,22)"} true;
    }
    else if (this == #_module.Dt.Bucket(_mcc#0#2_0))
    {
        havoc dm#2_0;
        assume let#2_0#0#0 == _mcc#0#2_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#2_0#0#0, TReal);
        assume dm#2_0 == let#2_0#0#0;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(108,9)
        assume true;
        assert _module.Dt.Bucket_q(this);
        havoc dt_update_tmp#0#Z#2_0;
        assume $Is(dt_update_tmp#0#Z#2_0, Tclass._module.Dt(_module.Dt$A));
        assume let#2_1#0#0 == this;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#2_1#0#0, Tclass._module.Dt(_module.Dt$A));
        assume dt_update_tmp#0#Z#2_0 == let#2_1#0#0;
        havoc dt_update#diameter#0#Z#2_0;
        assume true;
        assert _module.Dt.Bucket_q(this);
        assume let#2_2#0#0 == _module.Dt.diameter(this) + 2e0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#2_2#0#0, TReal);
        assume dt_update#diameter#0#Z#2_0 == let#2_2#0#0;
        assume true;
        d#0 := (var dt_update_tmp#0#2_0 := this; 
          (var dt_update#diameter#0#2_0 := _module.Dt.diameter(this) + 2e0; 
            #_module.Dt.Bucket(dt_update#diameter#0#2_0)));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(108,49)"} true;
    }
    else if (this == #_module.Dt.Business(_mcc#1#1_0, _mcc#2#1_0))
    {
        assume $IsBox(_mcc#2#1_0, _module.Dt$A) && $IsAllocBox(_mcc#2#1_0, _module.Dt$A, $Heap);
        havoc a#1_0;
        assume $IsBox(a#1_0, _module.Dt$A) && $IsAllocBox(a#1_0, _module.Dt$A, $Heap);
        assume let#1_0#0#0 == _mcc#2#1_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $IsBox(let#1_0#0#0, _module.Dt$A);
        assume a#1_0 == let#1_0#0#0;
        havoc t#1_0;
        assume let#1_1#0#0 == _mcc#1#1_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#1_1#0#0, TBool);
        assume t#1_0 == let#1_1#0#0;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(110,9)
        assume true;
        assert _module.Dt.Business_q(this);
        havoc dt_update_tmp#1#Z#1_0;
        assume $Is(dt_update_tmp#1#Z#1_0, Tclass._module.Dt(_module.Dt$A));
        assume let#1_2#0#0 == this;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#1_2#0#0, Tclass._module.Dt(_module.Dt$A));
        assume dt_update_tmp#1#Z#1_0 == let#1_2#0#0;
        havoc dt_update#trendy#0#Z#1_0;
        assume true;
        assume let#1_3#0#0 == !t#1_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#1_3#0#0, TBool);
        assume dt_update#trendy#0#Z#1_0 == let#1_3#0#0;
        assert _module.Dt.Business_q(dt_update_tmp#1#Z#1_0);
        assume true;
        d#0 := (var dt_update_tmp#1#1_0 := this; 
          (var dt_update#trendy#0#1_0 := !t#1_0; 
            #_module.Dt.Business(dt_update#trendy#0#1_0, _module.Dt.a(dt_update_tmp#1#1_0))));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(110,30)"} true;
    }
    else
    {
        assume false;
    }
}



procedure CheckWellformed$$_module.Dt.P(_module.Dt$A: Ty, x#0: int) returns (y#0: int);
  free requires 22 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Dt.P(_module.Dt$A: Ty, x#0: int) returns (y#0: int);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Dt.P(_module.Dt$A: Ty, x#0: int) returns (y#0: int, $_reverifyPost: bool);
  free requires 22 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



// function declaration for _module.Dt.Toop
function _module.Dt.Toop(_module.Dt$A: Ty, $prevHeap: Heap, $heap: Heap, this: DatatypeType) : bool;

function _module.Dt.Toop#canCall(_module.Dt$A: Ty, $prevHeap: Heap, $heap: Heap, this: DatatypeType) : bool;

// frame axiom for _module.Dt.Toop
axiom (forall _module.Dt$A: Ty, $prevHeap: Heap, $h0: Heap, $h1: Heap, this: DatatypeType :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.Dt.Toop(_module.Dt$A, $prevHeap, $h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && $Is(this, Tclass._module.Dt(_module.Dt$A))
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      false ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.Dt.Toop(_module.Dt$A, $prevHeap, $h0, this)
       == _module.Dt.Toop(_module.Dt$A, $prevHeap, $h1, this));

// consequence axiom for _module.Dt.Toop
axiom 50 <= $FunctionContextHeight
   ==> (forall _module.Dt$A: Ty, $prevHeap: Heap, $Heap: Heap, this: DatatypeType :: 
    { _module.Dt.Toop(_module.Dt$A, $prevHeap, $Heap, this) } 
    _module.Dt.Toop#canCall(_module.Dt$A, $prevHeap, $Heap, this)
         || (50 != $FunctionContextHeight
           && 
          $IsGoodHeap($prevHeap)
           && $IsGoodHeap($Heap)
           && $HeapSucc($prevHeap, $Heap)
           && 
          $Is(this, Tclass._module.Dt(_module.Dt$A))
           && $IsAlloc(this, Tclass._module.Dt(_module.Dt$A), $prevHeap))
       ==> true);

function _module.Dt.Toop#requires(Ty, Heap, Heap, DatatypeType) : bool;

// #requires axiom for _module.Dt.Toop
axiom (forall _module.Dt$A: Ty, $prevHeap: Heap, $Heap: Heap, this: DatatypeType :: 
  { _module.Dt.Toop#requires(_module.Dt$A, $prevHeap, $Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($prevHeap)
       && $IsGoodHeap($Heap)
       && $HeapSucc($prevHeap, $Heap)
       && 
      $Is(this, Tclass._module.Dt(_module.Dt$A))
       && $IsAlloc(this, Tclass._module.Dt(_module.Dt$A), $prevHeap)
     ==> _module.Dt.Toop#requires(_module.Dt$A, $prevHeap, $Heap, this) == true);

// definition axiom for _module.Dt.Toop (revealed)
axiom 50 <= $FunctionContextHeight
   ==> (forall _module.Dt$A: Ty, $prevHeap: Heap, $Heap: Heap, this: DatatypeType :: 
    { _module.Dt.Toop(_module.Dt$A, $prevHeap, $Heap, this), $IsGoodHeap($Heap) } 
    _module.Dt.Toop#canCall(_module.Dt$A, $prevHeap, $Heap, this)
         || (50 != $FunctionContextHeight
           && 
          $IsGoodHeap($prevHeap)
           && $IsGoodHeap($Heap)
           && $HeapSucc($prevHeap, $Heap)
           && 
          $Is(this, Tclass._module.Dt(_module.Dt$A))
           && $IsAlloc(this, Tclass._module.Dt(_module.Dt$A), $prevHeap))
       ==> $IsA#_module.Dt(this)
         && $IsA#_module.Dt(this)
         && _module.Dt.Toop(_module.Dt$A, $prevHeap, $Heap, this)
           == _module.Dt#Equal(this, this));

// definition axiom for _module.Dt.Toop for all literals (revealed)
axiom 50 <= $FunctionContextHeight
   ==> (forall _module.Dt$A: Ty, $prevHeap: Heap, $Heap: Heap, this: DatatypeType :: 
    {:weight 3} { _module.Dt.Toop(_module.Dt$A, $prevHeap, $Heap, Lit(this)), $IsGoodHeap($Heap) } 
    _module.Dt.Toop#canCall(_module.Dt$A, $prevHeap, $Heap, Lit(this))
         || (50 != $FunctionContextHeight
           && 
          $IsGoodHeap($prevHeap)
           && $IsGoodHeap($Heap)
           && $HeapSucc($prevHeap, $Heap)
           && 
          $Is(this, Tclass._module.Dt(_module.Dt$A))
           && $IsAlloc(this, Tclass._module.Dt(_module.Dt$A), $prevHeap))
       ==> $IsA#_module.Dt(Lit(this))
         && $IsA#_module.Dt(Lit(this))
         && _module.Dt.Toop(_module.Dt$A, $prevHeap, $Heap, Lit(this))
           == _module.Dt#Equal(this, this));

procedure CheckWellformed$$_module.Dt.Toop(_module.Dt$A: Ty, 
    previous$Heap: Heap, 
    current$Heap: Heap, 
    this: DatatypeType
       where $Is(this, Tclass._module.Dt(_module.Dt$A))
         && $IsAlloc(this, Tclass._module.Dt(_module.Dt$A), previous$Heap));
  free requires 50 == $FunctionContextHeight;
  free requires previous$Heap == $Heap
     && 
    $HeapSucc(previous$Heap, current$Heap)
     && $IsGoodHeap(current$Heap);
  modifies $Heap, $Tick;



procedure CheckWellformed$$_module.Dt.Tool(previous$Heap: Heap, 
    current$Heap: Heap, 
    _module.Dt$A: Ty, 
    this: DatatypeType
       where $Is(this, Tclass._module.Dt(_module.Dt$A))
         && $IsAlloc(this, Tclass._module.Dt(_module.Dt$A), previous$Heap));
  free requires 51 == $FunctionContextHeight;
  free requires previous$Heap == $Heap
     && 
    $HeapSucc(previous$Heap, current$Heap)
     && $IsGoodHeap(current$Heap);
  modifies $Heap, $Tick;



procedure Call$$_module.Dt.Tool(previous$Heap: Heap, 
    current$Heap: Heap, 
    _module.Dt$A: Ty, 
    this: DatatypeType
       where $Is(this, Tclass._module.Dt(_module.Dt$A))
         && $IsAlloc(this, Tclass._module.Dt(_module.Dt$A), previous$Heap));
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.Dt.Tool(previous$Heap: Heap, 
    current$Heap: Heap, 
    _module.Dt$A: Ty, 
    this: DatatypeType
       where $Is(this, Tclass._module.Dt(_module.Dt$A))
         && $IsAlloc(this, Tclass._module.Dt(_module.Dt$A), previous$Heap))
   returns ($_reverifyPost: bool);
  free requires 51 == $FunctionContextHeight;
  free requires previous$Heap == $Heap
     && 
    $HeapSucc(previous$Heap, current$Heap)
     && $IsGoodHeap(current$Heap);
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;



// function declaration for _module.Dt.IndP
function _module.Dt.IndP(_module.Dt$A: Ty, this: DatatypeType) : bool;

function _module.Dt.IndP#canCall(_module.Dt$A: Ty, this: DatatypeType) : bool;

// consequence axiom for _module.Dt.IndP
axiom 0 <= $FunctionContextHeight
   ==> (forall _module.Dt$A: Ty, this: DatatypeType :: 
    { _module.Dt.IndP(_module.Dt$A, this) } 
    _module.Dt.IndP#canCall(_module.Dt$A, this)
         || (0 != $FunctionContextHeight && $Is(this, Tclass._module.Dt(_module.Dt$A)))
       ==> true);

function _module.Dt.IndP#requires(Ty, DatatypeType) : bool;

// #requires axiom for _module.Dt.IndP
axiom (forall _module.Dt$A: Ty, this: DatatypeType :: 
  { _module.Dt.IndP#requires(_module.Dt$A, this) } 
  $Is(this, Tclass._module.Dt(_module.Dt$A))
     ==> _module.Dt.IndP#requires(_module.Dt$A, this) == true);

// definition axiom for _module.Dt.IndP (revealed)
axiom 0 <= $FunctionContextHeight
   ==> (forall _module.Dt$A: Ty, this: DatatypeType :: 
    { _module.Dt.IndP(_module.Dt$A, this) } 
    _module.Dt.IndP#canCall(_module.Dt$A, this)
         || (0 != $FunctionContextHeight && $Is(this, Tclass._module.Dt(_module.Dt$A)))
       ==> _module.Dt.IndP(_module.Dt$A, this) == Lit(true));

// 1st prefix predicate axiom for _module.Dt.IndP_h
axiom 1 <= $FunctionContextHeight
   ==> (forall _module.Dt$A: Ty, this: DatatypeType :: 
    { _module.Dt.IndP(_module.Dt$A, this) } 
    $Is(this, Tclass._module.Dt(_module.Dt$A))
         && _module.Dt.IndP(_module.Dt$A, this)
       ==> (exists _k#0: Box :: 
        { _module.Dt.IndP_h(_module.Dt$A, this, _k#0) } 
        _module.Dt.IndP_h(_module.Dt$A, this, _k#0)));

// 2nd prefix predicate axiom
axiom 1 <= $FunctionContextHeight
   ==> (forall _module.Dt$A: Ty, this: DatatypeType :: 
    { _module.Dt.IndP(_module.Dt$A, this) } 
    $Is(this, Tclass._module.Dt(_module.Dt$A))
         && (exists _k#0: Box :: 
          { _module.Dt.IndP_h(_module.Dt$A, this, _k#0) } 
          _module.Dt.IndP_h(_module.Dt$A, this, _k#0))
       ==> _module.Dt.IndP(_module.Dt$A, this));

// 3rd prefix predicate axiom
axiom 1 <= $FunctionContextHeight
   ==> (forall _module.Dt$A: Ty, this: DatatypeType, _k#0: Box :: 
    { _module.Dt.IndP_h(_module.Dt$A, this, _k#0) } 
    $Is(this, Tclass._module.Dt(_module.Dt$A)) && _k#0 == ORD#FromNat(0)
       ==> !_module.Dt.IndP_h(_module.Dt$A, this, _k#0));

// targeted prefix predicate monotonicity axiom
axiom 1 <= $FunctionContextHeight
   ==> (forall _module.Dt$A: Ty, this: DatatypeType, _k#0: Box, _m: Box, _limit: Box :: 
    { _module.Dt.IndP_h(_module.Dt$A, this, _k#0), ORD#LessThanLimit(_k#0, _limit), ORD#LessThanLimit(_m, _limit) } 
    ORD#Less(_k#0, _m)
       ==> 
      _module.Dt.IndP_h(_module.Dt$A, this, _k#0)
       ==> _module.Dt.IndP_h(_module.Dt$A, this, _m));

procedure CheckWellformed$$_module.Dt.IndP(_module.Dt$A: Ty, 
    this: DatatypeType
       where $Is(this, Tclass._module.Dt(_module.Dt$A))
         && $IsAlloc(this, Tclass._module.Dt(_module.Dt$A), $Heap));
  free requires 0 == $FunctionContextHeight;
  modifies $Heap, $Tick;



// function declaration for _module.Dt.IndP#
function _module.Dt.IndP_h(_module.Dt$A: Ty, this: DatatypeType, _k#0: Box) : bool;

function _module.Dt.IndP_h#canCall(_module.Dt$A: Ty, this: DatatypeType, _k#0: Box) : bool;

// consequence axiom for _module.Dt.IndP_h
axiom 1 <= $FunctionContextHeight
   ==> (forall _module.Dt$A: Ty, this: DatatypeType, _k#0: Box :: 
    { _module.Dt.IndP_h(_module.Dt$A, this, _k#0) } 
    _module.Dt.IndP_h#canCall(_module.Dt$A, this, _k#0)
         || (1 != $FunctionContextHeight && $Is(this, Tclass._module.Dt(_module.Dt$A)))
       ==> true);

function _module.Dt.IndP_h#requires(Ty, DatatypeType, Box) : bool;

// #requires axiom for _module.Dt.IndP_h
axiom (forall _module.Dt$A: Ty, this: DatatypeType, _k#0: Box :: 
  { _module.Dt.IndP_h#requires(_module.Dt$A, this, _k#0) } 
  $Is(this, Tclass._module.Dt(_module.Dt$A))
     ==> _module.Dt.IndP_h#requires(_module.Dt$A, this, _k#0) == true);

// definition axiom for _module.Dt.IndP_h (revealed)
axiom 1 <= $FunctionContextHeight
   ==> (forall _module.Dt$A: Ty, this: DatatypeType, _k#0: Box :: 
    { _module.Dt.IndP_h(_module.Dt$A, this, _k#0) } 
    _module.Dt.IndP_h#canCall(_module.Dt$A, this, _k#0)
         || (1 != $FunctionContextHeight && $Is(this, Tclass._module.Dt(_module.Dt$A)))
       ==> (LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#0: Box :: 
            { _module.Dt.IndP_h(_module.Dt$A, this, _k'#0) } 
            ORD#LessThanLimit(_k'#0, _k#0)
               ==> _module.Dt.IndP_h#canCall(_module.Dt$A, this, _k'#0)))
         && _module.Dt.IndP_h(_module.Dt$A, this, _k#0)
           == (LitInt(0) == ORD#Offset(_k#0)
             ==> (exists _k'#0: Box :: 
              { _module.Dt.IndP_h(_module.Dt$A, this, _k'#0) } 
              ORD#LessThanLimit(_k'#0, _k#0) && _module.Dt.IndP_h(_module.Dt$A, this, _k'#0))));

// definition axiom for _module.Dt.IndP_h for decreasing-related literals (revealed)
axiom 1 <= $FunctionContextHeight
   ==> (forall _module.Dt$A: Ty, this: DatatypeType, _k#0: Box :: 
    {:weight 3} { _module.Dt.IndP_h(_module.Dt$A, this, Lit(_k#0)) } 
    _module.Dt.IndP_h#canCall(_module.Dt$A, this, Lit(_k#0))
         || (1 != $FunctionContextHeight && $Is(this, Tclass._module.Dt(_module.Dt$A)))
       ==> (LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#1: Box :: 
            { _module.Dt.IndP_h(_module.Dt$A, this, _k'#1) } 
            ORD#LessThanLimit(_k'#1, _k#0)
               ==> _module.Dt.IndP_h#canCall(_module.Dt$A, this, _k'#1)))
         && _module.Dt.IndP_h(_module.Dt$A, this, Lit(_k#0))
           == (LitInt(0) == ORD#Offset(_k#0)
             ==> (exists _k'#1: Box :: 
              { _module.Dt.IndP_h(_module.Dt$A, this, _k'#1) } 
              ORD#LessThanLimit(_k'#1, _k#0) && _module.Dt.IndP_h(_module.Dt$A, this, _k'#1))));

// definition axiom for _module.Dt.IndP_h for all literals (revealed)
axiom 1 <= $FunctionContextHeight
   ==> (forall _module.Dt$A: Ty, this: DatatypeType, _k#0: Box :: 
    {:weight 3} { _module.Dt.IndP_h(_module.Dt$A, Lit(this), Lit(_k#0)) } 
    _module.Dt.IndP_h#canCall(_module.Dt$A, Lit(this), Lit(_k#0))
         || (1 != $FunctionContextHeight && $Is(this, Tclass._module.Dt(_module.Dt$A)))
       ==> (LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#2: Box :: 
            { _module.Dt.IndP_h(_module.Dt$A, this, _k'#2) } 
            ORD#LessThanLimit(_k'#2, _k#0)
               ==> _module.Dt.IndP_h#canCall(_module.Dt$A, this, _k'#2)))
         && _module.Dt.IndP_h(_module.Dt$A, Lit(this), Lit(_k#0))
           == (LitInt(0) == ORD#Offset(_k#0)
             ==> (exists _k'#2: Box :: 
              { _module.Dt.IndP_h(_module.Dt$A, this, _k'#2) } 
              ORD#LessThanLimit(_k'#2, _k#0) && _module.Dt.IndP_h(_module.Dt$A, this, _k'#2))));

// function declaration for _module.Dt.CoP
function _module.Dt.CoP(_module.Dt$A: Ty, this: DatatypeType) : bool;

function _module.Dt.CoP#canCall(_module.Dt$A: Ty, this: DatatypeType) : bool;

// consequence axiom for _module.Dt.CoP
axiom 2 <= $FunctionContextHeight
   ==> (forall _module.Dt$A: Ty, this: DatatypeType :: 
    { _module.Dt.CoP(_module.Dt$A, this) } 
    _module.Dt.CoP#canCall(_module.Dt$A, this)
         || (2 != $FunctionContextHeight && $Is(this, Tclass._module.Dt(_module.Dt$A)))
       ==> true);

function _module.Dt.CoP#requires(Ty, DatatypeType) : bool;

// #requires axiom for _module.Dt.CoP
axiom (forall _module.Dt$A: Ty, this: DatatypeType :: 
  { _module.Dt.CoP#requires(_module.Dt$A, this) } 
  $Is(this, Tclass._module.Dt(_module.Dt$A))
     ==> _module.Dt.CoP#requires(_module.Dt$A, this) == true);

// definition axiom for _module.Dt.CoP (revealed)
axiom 2 <= $FunctionContextHeight
   ==> (forall _module.Dt$A: Ty, this: DatatypeType :: 
    { _module.Dt.CoP(_module.Dt$A, this) } 
    _module.Dt.CoP#canCall(_module.Dt$A, this)
         || (2 != $FunctionContextHeight && $Is(this, Tclass._module.Dt(_module.Dt$A)))
       ==> _module.Dt.CoP(_module.Dt$A, this) == Lit(true));

// 1st prefix predicate axiom for _module.Dt.CoP_h
axiom 3 <= $FunctionContextHeight
   ==> (forall _module.Dt$A: Ty, this: DatatypeType :: 
    { _module.Dt.CoP(_module.Dt$A, this) } 
    $Is(this, Tclass._module.Dt(_module.Dt$A)) && _module.Dt.CoP(_module.Dt$A, this)
       ==> (forall _k#0: Box :: 
        { _module.Dt.CoP_h(_module.Dt$A, this, _k#0) } 
        _module.Dt.CoP_h(_module.Dt$A, this, _k#0)));

// 2nd prefix predicate axiom
axiom 3 <= $FunctionContextHeight
   ==> (forall _module.Dt$A: Ty, this: DatatypeType :: 
    { _module.Dt.CoP(_module.Dt$A, this) } 
    $Is(this, Tclass._module.Dt(_module.Dt$A))
         && (forall _k#0: Box :: 
          { _module.Dt.CoP_h(_module.Dt$A, this, _k#0) } 
          _module.Dt.CoP_h(_module.Dt$A, this, _k#0))
       ==> _module.Dt.CoP(_module.Dt$A, this));

// 3rd prefix predicate axiom
axiom 3 <= $FunctionContextHeight
   ==> (forall _module.Dt$A: Ty, this: DatatypeType, _k#0: Box :: 
    { _module.Dt.CoP_h(_module.Dt$A, this, _k#0) } 
    $Is(this, Tclass._module.Dt(_module.Dt$A)) && _k#0 == ORD#FromNat(0)
       ==> _module.Dt.CoP_h(_module.Dt$A, this, _k#0));

procedure CheckWellformed$$_module.Dt.CoP(_module.Dt$A: Ty, 
    this: DatatypeType
       where $Is(this, Tclass._module.Dt(_module.Dt$A))
         && $IsAlloc(this, Tclass._module.Dt(_module.Dt$A), $Heap));
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;



// function declaration for _module.Dt.CoP#
function _module.Dt.CoP_h(_module.Dt$A: Ty, this: DatatypeType, _k#0: Box) : bool;

function _module.Dt.CoP_h#canCall(_module.Dt$A: Ty, this: DatatypeType, _k#0: Box) : bool;

// consequence axiom for _module.Dt.CoP_h
axiom 3 <= $FunctionContextHeight
   ==> (forall _module.Dt$A: Ty, this: DatatypeType, _k#0: Box :: 
    { _module.Dt.CoP_h(_module.Dt$A, this, _k#0) } 
    _module.Dt.CoP_h#canCall(_module.Dt$A, this, _k#0)
         || (3 != $FunctionContextHeight && $Is(this, Tclass._module.Dt(_module.Dt$A)))
       ==> true);

function _module.Dt.CoP_h#requires(Ty, DatatypeType, Box) : bool;

// #requires axiom for _module.Dt.CoP_h
axiom (forall _module.Dt$A: Ty, this: DatatypeType, _k#0: Box :: 
  { _module.Dt.CoP_h#requires(_module.Dt$A, this, _k#0) } 
  $Is(this, Tclass._module.Dt(_module.Dt$A))
     ==> _module.Dt.CoP_h#requires(_module.Dt$A, this, _k#0) == true);

// definition axiom for _module.Dt.CoP_h (revealed)
axiom 3 <= $FunctionContextHeight
   ==> (forall _module.Dt$A: Ty, this: DatatypeType, _k#0: Box :: 
    { _module.Dt.CoP_h(_module.Dt$A, this, _k#0) } 
    _module.Dt.CoP_h#canCall(_module.Dt$A, this, _k#0)
         || (3 != $FunctionContextHeight && $Is(this, Tclass._module.Dt(_module.Dt$A)))
       ==> (LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#0: Box :: 
            { _module.Dt.CoP_h(_module.Dt$A, this, _k'#0) } 
            ORD#Less(_k'#0, _k#0) ==> _module.Dt.CoP_h#canCall(_module.Dt$A, this, _k'#0)))
         && _module.Dt.CoP_h(_module.Dt$A, this, _k#0)
           == (LitInt(0) == ORD#Offset(_k#0)
             ==> (forall _k'#0: Box :: 
              { _module.Dt.CoP_h(_module.Dt$A, this, _k'#0) } 
              ORD#Less(_k'#0, _k#0) ==> _module.Dt.CoP_h(_module.Dt$A, this, _k'#0))));

// definition axiom for _module.Dt.CoP_h for decreasing-related literals (revealed)
axiom 3 <= $FunctionContextHeight
   ==> (forall _module.Dt$A: Ty, this: DatatypeType, _k#0: Box :: 
    {:weight 3} { _module.Dt.CoP_h(_module.Dt$A, this, Lit(_k#0)) } 
    _module.Dt.CoP_h#canCall(_module.Dt$A, this, Lit(_k#0))
         || (3 != $FunctionContextHeight && $Is(this, Tclass._module.Dt(_module.Dt$A)))
       ==> (LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#1: Box :: 
            { _module.Dt.CoP_h(_module.Dt$A, this, _k'#1) } 
            ORD#Less(_k'#1, _k#0) ==> _module.Dt.CoP_h#canCall(_module.Dt$A, this, _k'#1)))
         && _module.Dt.CoP_h(_module.Dt$A, this, Lit(_k#0))
           == (LitInt(0) == ORD#Offset(_k#0)
             ==> (forall _k'#1: Box :: 
              { _module.Dt.CoP_h(_module.Dt$A, this, _k'#1) } 
              ORD#Less(_k'#1, _k#0) ==> _module.Dt.CoP_h(_module.Dt$A, this, _k'#1))));

// definition axiom for _module.Dt.CoP_h for all literals (revealed)
axiom 3 <= $FunctionContextHeight
   ==> (forall _module.Dt$A: Ty, this: DatatypeType, _k#0: Box :: 
    {:weight 3} { _module.Dt.CoP_h(_module.Dt$A, Lit(this), Lit(_k#0)) } 
    _module.Dt.CoP_h#canCall(_module.Dt$A, Lit(this), Lit(_k#0))
         || (3 != $FunctionContextHeight && $Is(this, Tclass._module.Dt(_module.Dt$A)))
       ==> (LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#2: Box :: 
            { _module.Dt.CoP_h(_module.Dt$A, this, _k'#2) } 
            ORD#Less(_k'#2, _k#0) ==> _module.Dt.CoP_h#canCall(_module.Dt$A, this, _k'#2)))
         && _module.Dt.CoP_h(_module.Dt$A, Lit(this), Lit(_k#0))
           == (LitInt(0) == ORD#Offset(_k#0)
             ==> (forall _k'#2: Box :: 
              { _module.Dt.CoP_h(_module.Dt$A, this, _k'#2) } 
              ORD#Less(_k'#2, _k#0) ==> _module.Dt.CoP_h(_module.Dt$A, this, _k'#2))));

procedure CheckWellformed$$_module.Dt.RecursiveZero(_module.Dt$A: Ty, 
    this: DatatypeType
       where $Is(this, Tclass._module.Dt(_module.Dt$A))
         && $IsAlloc(this, Tclass._module.Dt(_module.Dt$A), $Heap), 
    x#0: int)
   returns (z#0: int);
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Dt.RecursiveZero(_module.Dt$A: Ty, 
    this: DatatypeType
       where $Is(this, Tclass._module.Dt(_module.Dt$A))
         && $IsAlloc(this, Tclass._module.Dt(_module.Dt$A), $Heap), 
    x#0: int)
   returns (z#0: int);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures z#0 == LitInt(0);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Dt.RecursiveZero(_module.Dt$A: Ty, 
    this: DatatypeType
       where $Is(this, Tclass._module.Dt(_module.Dt$A))
         && $IsAlloc(this, Tclass._module.Dt(_module.Dt$A), $Heap), 
    x#0: int)
   returns (z#0: int, $_reverifyPost: bool);
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures z#0 == LitInt(0);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Dt.RecursiveZero(_module.Dt$A: Ty, this: DatatypeType, x#0: int)
   returns (z#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs##0: int;
  var x##0: int;

    // AddMethodImpl: RecursiveZero, Impl$$_module.Dt.RecursiveZero
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(119,80): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(120,5)
    assume true;
    if (x#0 == LitInt(0))
    {
        // ----- return statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(120,17)
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(120,17)
        assume true;
        assume true;
        z#0 := LitInt(0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(120,24)"} true;
        return;
    }
    else
    {
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(120,54)
        assume true;
        // TrCallStmt: Adding lhs with type int
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        assume true;
        // ProcessCallStmt: CheckSubrange
        x##0 := LitInt(0);
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assert x##0 == 0 && x#0 != 0;
        // ProcessCallStmt: Make the call
        call $rhs##0 := Call$$_module.Dt.RecursiveZero(_module.Dt$A, this, x##0);
        // TrCallStmt: After ProcessCallStmt
        z#0 := $rhs##0;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(120,56)"} true;
    }
}



procedure CheckWellformed$$_module.Dt.StaticRecursiveZero(_module.Dt$A: Ty, x#0: int) returns (z#0: int);
  free requires 9 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Dt.StaticRecursiveZero(_module.Dt$A: Ty, x#0: int) returns (z#0: int);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures z#0 == LitInt(0);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Dt.StaticRecursiveZero(_module.Dt$A: Ty, x#0: int) returns (z#0: int, $_reverifyPost: bool);
  free requires 9 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures z#0 == LitInt(0);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Dt.StaticRecursiveZero(_module.Dt$A: Ty, x#0: int) returns (z#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs##0: int;
  var x##0: int;

    // AddMethodImpl: StaticRecursiveZero, Impl$$_module.Dt.StaticRecursiveZero
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(122,93): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(123,5)
    assume true;
    if (x#0 == LitInt(0))
    {
        // ----- return statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(123,17)
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(123,17)
        assume true;
        assume true;
        z#0 := LitInt(0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(123,24)"} true;
        return;
    }
    else
    {
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(123,60)
        assume true;
        // TrCallStmt: Adding lhs with type int
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        x##0 := LitInt(0);
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assert x##0 == 0 && x#0 != 0;
        // ProcessCallStmt: Make the call
        call $rhs##0 := Call$$_module.Dt.StaticRecursiveZero(_module.Dt$A, x##0);
        // TrCallStmt: After ProcessCallStmt
        z#0 := $rhs##0;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(123,62)"} true;
    }
}



// Constructor function declaration
function #_module.Co.Cobalt() : DatatypeType;

const unique ##_module.Co.Cobalt: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#_module.Co.Cobalt()) == ##_module.Co.Cobalt;

function _module.Co.Cobalt_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Co.Cobalt_q(d) } 
  _module.Co.Cobalt_q(d) <==> DatatypeCtorId(d) == ##_module.Co.Cobalt);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Co.Cobalt_q(d) } 
  _module.Co.Cobalt_q(d) ==> d == #_module.Co.Cobalt());

function Tclass._module.Co(Ty) : Ty;

const unique Tagclass._module.Co: TyTag;

// Tclass._module.Co Tag
axiom (forall _module.Co$A: Ty :: 
  { Tclass._module.Co(_module.Co$A) } 
  Tag(Tclass._module.Co(_module.Co$A)) == Tagclass._module.Co
     && TagFamily(Tclass._module.Co(_module.Co$A)) == tytagFamily$Co);

// Tclass._module.Co injectivity 0
axiom (forall _module.Co$A: Ty :: 
  { Tclass._module.Co(_module.Co$A) } 
  Tclass._module.Co_0(Tclass._module.Co(_module.Co$A)) == _module.Co$A);

function Tclass._module.Co_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.Co
axiom (forall _module.Co$A: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.Co(_module.Co$A)) } 
  $IsBox(bx, Tclass._module.Co(_module.Co$A))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Co(_module.Co$A)));

// Constructor $Is
axiom (forall _module.Co$A: Ty :: 
  { $Is(#_module.Co.Cobalt(), Tclass._module.Co(_module.Co$A)) } 
  $Is(#_module.Co.Cobalt(), Tclass._module.Co(_module.Co$A)));

// Constructor $IsAlloc
axiom (forall _module.Co$A: Ty, $h: Heap :: 
  { $IsAlloc(#_module.Co.Cobalt(), Tclass._module.Co(_module.Co$A), $h) } 
  $IsGoodHeap($h)
     ==> $IsAlloc(#_module.Co.Cobalt(), Tclass._module.Co(_module.Co$A), $h));

// Constructor function declaration
function #_module.Co.Continues(DatatypeType) : DatatypeType;

const unique ##_module.Co.Continues: DtCtorId;

// Constructor identifier
axiom (forall a#4#0#0: DatatypeType :: 
  { #_module.Co.Continues(a#4#0#0) } 
  DatatypeCtorId(#_module.Co.Continues(a#4#0#0)) == ##_module.Co.Continues);

function _module.Co.Continues_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Co.Continues_q(d) } 
  _module.Co.Continues_q(d) <==> DatatypeCtorId(d) == ##_module.Co.Continues);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Co.Continues_q(d) } 
  _module.Co.Continues_q(d)
     ==> (exists a#5#0#0: DatatypeType :: d == #_module.Co.Continues(a#5#0#0)));

// Constructor $Is
axiom (forall _module.Co$A: Ty, a#6#0#0: DatatypeType :: 
  { $Is(#_module.Co.Continues(a#6#0#0), Tclass._module.Co(_module.Co$A)) } 
  $Is(#_module.Co.Continues(a#6#0#0), Tclass._module.Co(_module.Co$A))
     <==> $Is(a#6#0#0, Tclass._module.Co(_module.Co$A)));

// Constructor $IsAlloc
axiom (forall _module.Co$A: Ty, a#7#0#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#_module.Co.Continues(a#7#0#0), Tclass._module.Co(_module.Co$A), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Co.Continues(a#7#0#0), Tclass._module.Co(_module.Co$A), $h)
       <==> $IsAlloc(a#7#0#0, Tclass._module.Co(_module.Co$A), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _module.Co$A: Ty, $h: Heap :: 
  { $IsAlloc(_module.Co.next(d), Tclass._module.Co(_module.Co$A), $h) } 
  $IsGoodHeap($h)
       && 
      _module.Co.Continues_q(d)
       && $IsAlloc(d, Tclass._module.Co(_module.Co$A), $h)
     ==> $IsAlloc(_module.Co.next(d), Tclass._module.Co(_module.Co$A), $h));

function _module.Co.next(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#8#0#0: DatatypeType :: 
  { #_module.Co.Continues(a#8#0#0) } 
  _module.Co.next(#_module.Co.Continues(a#8#0#0)) == a#8#0#0);

// Depth-one case-split function
function $IsA#_module.Co(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.Co(d) } 
  $IsA#_module.Co(d) ==> _module.Co.Cobalt_q(d) || _module.Co.Continues_q(d));

// Questionmark data type disjunctivity
axiom (forall _module.Co$A: Ty, d: DatatypeType :: 
  { _module.Co.Continues_q(d), $Is(d, Tclass._module.Co(_module.Co$A)) } 
    { _module.Co.Cobalt_q(d), $Is(d, Tclass._module.Co(_module.Co$A)) } 
  $Is(d, Tclass._module.Co(_module.Co$A))
     ==> _module.Co.Cobalt_q(d) || _module.Co.Continues_q(d));

function $Eq#_module.Co(Ty, Ty, LayerType, DatatypeType, DatatypeType) : bool;

// Layered co-equality axiom
axiom (forall _module.Co$A#l: Ty, 
    _module.Co$A#r: Ty, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType :: 
  { $Eq#_module.Co(_module.Co$A#l, _module.Co$A#r, $LS(ly), d0, d1) } 
  $Is(d0, Tclass._module.Co(_module.Co$A#l))
       && $Is(d1, Tclass._module.Co(_module.Co$A#r))
     ==> ($Eq#_module.Co(_module.Co$A#l, _module.Co$A#r, $LS(ly), d0, d1)
       <==> (_module.Co.Cobalt_q(d0) && _module.Co.Cobalt_q(d1))
         || (
          _module.Co.Continues_q(d0)
           && _module.Co.Continues_q(d1)
           && (_module.Co.Continues_q(d0) && _module.Co.Continues_q(d1)
             ==> $Eq#_module.Co(_module.Co$A#l, _module.Co$A#r, ly, _module.Co.next(d0), _module.Co.next(d1))))));

// Unbump layer co-equality axiom
axiom (forall _module.Co$A#l: Ty, 
    _module.Co$A#r: Ty, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType :: 
  { $Eq#_module.Co(_module.Co$A#l, _module.Co$A#r, $LS(ly), d0, d1) } 
  $Eq#_module.Co(_module.Co$A#l, _module.Co$A#r, $LS(ly), d0, d1)
     <==> $Eq#_module.Co(_module.Co$A#l, _module.Co$A#r, ly, d0, d1));

// Equality for codatatypes
axiom (forall _module.Co$A#l: Ty, 
    _module.Co$A#r: Ty, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType :: 
  { $Eq#_module.Co(_module.Co$A#l, _module.Co$A#r, $LS(ly), d0, d1) } 
  $Eq#_module.Co(_module.Co$A#l, _module.Co$A#r, $LS(ly), d0, d1) <==> d0 == d1);

function $PrefixEq#_module.Co(Ty, Ty, Box, LayerType, DatatypeType, DatatypeType) : bool;

// Layered co-equality axiom
axiom (forall _module.Co$A#l: Ty, 
    _module.Co$A#r: Ty, 
    k: Box, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType :: 
  { $PrefixEq#_module.Co(_module.Co$A#l, _module.Co$A#r, k, $LS(ly), d0, d1) } 
  $Is(d0, Tclass._module.Co(_module.Co$A#l))
       && $Is(d1, Tclass._module.Co(_module.Co$A#r))
     ==> ($PrefixEq#_module.Co(_module.Co$A#l, _module.Co$A#r, k, $LS(ly), d0, d1)
       <==> (0 < ORD#Offset(k)
           ==> (_module.Co.Cobalt_q(d0) && _module.Co.Cobalt_q(d1))
             || (
              _module.Co.Continues_q(d0)
               && _module.Co.Continues_q(d1)
               && (_module.Co.Continues_q(d0) && _module.Co.Continues_q(d1)
                 ==> $PrefixEq#_module.Co(_module.Co$A#l, 
                  _module.Co$A#r, 
                  ORD#Minus(k, ORD#FromNat(1)), 
                  ly, 
                  _module.Co.next(d0), 
                  _module.Co.next(d1)))))
         && (k != ORD#FromNat(0) && ORD#IsLimit(k)
           ==> $Eq#_module.Co(_module.Co$A#l, _module.Co$A#r, ly, d0, d1))));

// Unbump layer co-equality axiom
axiom (forall _module.Co$A#l: Ty, 
    _module.Co$A#r: Ty, 
    k: Box, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType :: 
  { $PrefixEq#_module.Co(_module.Co$A#l, _module.Co$A#r, k, $LS(ly), d0, d1) } 
  k != ORD#FromNat(0)
     ==> ($PrefixEq#_module.Co(_module.Co$A#l, _module.Co$A#r, k, $LS(ly), d0, d1)
       <==> $PrefixEq#_module.Co(_module.Co$A#l, _module.Co$A#r, k, ly, d0, d1)));

// Coequality and prefix equality connection
axiom (forall _module.Co$A#l: Ty, 
    _module.Co$A#r: Ty, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType :: 
  { $Eq#_module.Co(_module.Co$A#l, _module.Co$A#r, $LS(ly), d0, d1) } 
  $Eq#_module.Co(_module.Co$A#l, _module.Co$A#r, $LS(ly), d0, d1)
     <==> (forall k: Box :: 
      { $PrefixEq#_module.Co(_module.Co$A#l, _module.Co$A#r, k, $LS(ly), d0, d1) } 
      $PrefixEq#_module.Co(_module.Co$A#l, _module.Co$A#r, k, $LS(ly), d0, d1)));

// Coequality and prefix equality connection
axiom (forall _module.Co$A#l: Ty, 
    _module.Co$A#r: Ty, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType :: 
  { $Eq#_module.Co(_module.Co$A#l, _module.Co$A#r, $LS(ly), d0, d1) } 
  (forall k: int :: 
      { $PrefixEq#_module.Co(_module.Co$A#l, _module.Co$A#r, ORD#FromNat(k), $LS(ly), d0, d1) } 
      0 <= k
         ==> $PrefixEq#_module.Co(_module.Co$A#l, _module.Co$A#r, ORD#FromNat(k), $LS(ly), d0, d1))
     ==> $Eq#_module.Co(_module.Co$A#l, _module.Co$A#r, $LS(ly), d0, d1));

// Prefix equality consequence
axiom (forall _module.Co$A#l: Ty, 
    _module.Co$A#r: Ty, 
    k: Box, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType, 
    m: Box :: 
  { $PrefixEq#_module.Co(_module.Co$A#l, _module.Co$A#r, k, $LS(ly), d0, d1), $PrefixEq#_module.Co(_module.Co$A#l, _module.Co$A#r, m, $LS(ly), d0, d1) } 
  ORD#Less(k, m)
       && $PrefixEq#_module.Co(_module.Co$A#l, _module.Co$A#r, m, $LS(ly), d0, d1)
     ==> $PrefixEq#_module.Co(_module.Co$A#l, _module.Co$A#r, k, $LS(ly), d0, d1));

// Prefix equality shortcut
axiom (forall _module.Co$A#l: Ty, 
    _module.Co$A#r: Ty, 
    k: Box, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType :: 
  { $PrefixEq#_module.Co(_module.Co$A#l, _module.Co$A#r, k, $LS(ly), d0, d1) } 
  d0 == d1
     ==> $PrefixEq#_module.Co(_module.Co$A#l, _module.Co$A#r, k, $LS(ly), d0, d1));

const unique class._module.Co: ClassName;

function {:inline} _module.Co.c(_module.Co$A: Ty, this: DatatypeType) : int
{
  (if _module.Co.Cobalt_q(this) then 18 else 19)
}

procedure CheckWellformed$$_module.Co.c(_module.Co$A: Ty, 
    this: DatatypeType
       where $Is(this, Tclass._module.Co(_module.Co$A))
         && $IsAlloc(this, Tclass._module.Co(_module.Co$A), $Heap));
  free requires 39 == $FunctionContextHeight;
  modifies $Heap;



// Co.c: Type axiom
axiom 39 < $FunctionContextHeight
   ==> (forall _module.Co$A: Ty, $o: DatatypeType :: 
    { _module.Co.c(_module.Co$A, $o) } 
    $Is(_module.Co.c(_module.Co$A, $o), TInt));

// Co.c: Allocation axiom
axiom 39 < $FunctionContextHeight
   ==> (forall _module.Co$A: Ty, $h: Heap, $o: DatatypeType :: 
    { _module.Co.c(_module.Co$A, $o), $IsAlloc($o, Tclass._module.Co(_module.Co$A), $h) } 
    $IsGoodHeap($h) && $IsAlloc($o, Tclass._module.Co(_module.Co$A), $h)
       ==> $IsAlloc(_module.Co.c(_module.Co$A, $o), TInt, $h));

function _module.Co.g(_module.Co$A: Ty) : int;

// Co.g: Type axiom
axiom 35 < $FunctionContextHeight
   ==> (forall _module.Co$A: Ty :: 
    { _module.Co.g(_module.Co$A) } 
    $Is(_module.Co.g(_module.Co$A), TInt));

// Co.g: Allocation axiom
axiom 35 < $FunctionContextHeight
   ==> (forall _module.Co$A: Ty, $h: Heap :: 
    { $IsAlloc(_module.Co.g(_module.Co$A), TInt, $h) } 
    $IsGoodHeap($h) ==> $IsAlloc(_module.Co.g(_module.Co$A), TInt, $h));

// function declaration for _module.Co.F
function _module.Co.F(_module.Co$A: Ty, this: DatatypeType, x#0: int) : int;

function _module.Co.F#canCall(_module.Co$A: Ty, this: DatatypeType, x#0: int) : bool;

// consequence axiom for _module.Co.F
axiom 36 <= $FunctionContextHeight
   ==> (forall _module.Co$A: Ty, this: DatatypeType, x#0: int :: 
    { _module.Co.F(_module.Co$A, this, x#0) } 
    _module.Co.F#canCall(_module.Co$A, this, x#0)
         || (36 != $FunctionContextHeight && $Is(this, Tclass._module.Co(_module.Co$A)))
       ==> true);

function _module.Co.F#requires(Ty, DatatypeType, int) : bool;

// #requires axiom for _module.Co.F
axiom (forall _module.Co$A: Ty, this: DatatypeType, x#0: int :: 
  { _module.Co.F#requires(_module.Co$A, this, x#0) } 
  $Is(this, Tclass._module.Co(_module.Co$A))
     ==> _module.Co.F#requires(_module.Co$A, this, x#0) == true);

// definition axiom for _module.Co.F (revealed)
axiom 36 <= $FunctionContextHeight
   ==> (forall _module.Co$A: Ty, this: DatatypeType, x#0: int :: 
    { _module.Co.F(_module.Co$A, this, x#0) } 
    _module.Co.F#canCall(_module.Co$A, this, x#0)
         || (36 != $FunctionContextHeight && $Is(this, Tclass._module.Co(_module.Co$A)))
       ==> _module.Co.F(_module.Co$A, this, x#0) == LitInt(19));

// definition axiom for _module.Co.F for decreasing-related literals (revealed)
axiom 36 <= $FunctionContextHeight
   ==> (forall _module.Co$A: Ty, this: DatatypeType, x#0: int :: 
    {:weight 3} { _module.Co.F(_module.Co$A, this, LitInt(x#0)) } 
    _module.Co.F#canCall(_module.Co$A, this, LitInt(x#0))
         || (36 != $FunctionContextHeight && $Is(this, Tclass._module.Co(_module.Co$A)))
       ==> _module.Co.F(_module.Co$A, this, LitInt(x#0)) == LitInt(19));

// definition axiom for _module.Co.F for all literals (revealed)
axiom 36 <= $FunctionContextHeight
   ==> (forall _module.Co$A: Ty, this: DatatypeType, x#0: int :: 
    {:weight 3} { _module.Co.F(_module.Co$A, Lit(this), LitInt(x#0)) } 
    _module.Co.F#canCall(_module.Co$A, Lit(this), LitInt(x#0))
         || (36 != $FunctionContextHeight && $Is(this, Tclass._module.Co(_module.Co$A)))
       ==> _module.Co.F(_module.Co$A, Lit(this), LitInt(x#0)) == LitInt(19));

procedure CheckWellformed$$_module.Co.F(_module.Co$A: Ty, 
    this: DatatypeType
       where $Is(this, Tclass._module.Co(_module.Co$A))
         && $IsAlloc(this, Tclass._module.Co(_module.Co$A), $Heap), 
    x#0: int);
  free requires 36 == $FunctionContextHeight;
  modifies $Heap, $Tick;



// function declaration for _module.Co.G
function _module.Co.G(_module.Co$A: Ty, x#0: int) : int;

function _module.Co.G#canCall(_module.Co$A: Ty, x#0: int) : bool;

// consequence axiom for _module.Co.G
axiom 37 <= $FunctionContextHeight
   ==> (forall _module.Co$A: Ty, x#0: int :: 
    { _module.Co.G(_module.Co$A, x#0) } 
    _module.Co.G#canCall(_module.Co$A, x#0) || 37 != $FunctionContextHeight ==> true);

function _module.Co.G#requires(Ty, int) : bool;

// #requires axiom for _module.Co.G
axiom (forall _module.Co$A: Ty, x#0: int :: 
  { _module.Co.G#requires(_module.Co$A, x#0) } 
  _module.Co.G#requires(_module.Co$A, x#0) == true);

// definition axiom for _module.Co.G (revealed)
axiom 37 <= $FunctionContextHeight
   ==> (forall _module.Co$A: Ty, x#0: int :: 
    { _module.Co.G(_module.Co$A, x#0) } 
    _module.Co.G#canCall(_module.Co$A, x#0) || 37 != $FunctionContextHeight
       ==> _module.Co.G(_module.Co$A, x#0) == x#0 + 12);

// definition axiom for _module.Co.G for all literals (revealed)
axiom 37 <= $FunctionContextHeight
   ==> (forall _module.Co$A: Ty, x#0: int :: 
    {:weight 3} { _module.Co.G(_module.Co$A, LitInt(x#0)) } 
    _module.Co.G#canCall(_module.Co$A, LitInt(x#0)) || 37 != $FunctionContextHeight
       ==> _module.Co.G(_module.Co$A, LitInt(x#0)) == LitInt(x#0 + 12));

procedure CheckWellformed$$_module.Co.G(_module.Co$A: Ty, x#0: int);
  free requires 37 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure CheckWellformed$$_module.Co.M(_module.Co$A: Ty, 
    this: DatatypeType
       where $Is(this, Tclass._module.Co(_module.Co$A))
         && $IsAlloc(this, Tclass._module.Co(_module.Co$A), $Heap), 
    x#0: int)
   returns (y#0: int, 
    d#0: DatatypeType
       where $Is(d#0, Tclass._module.Co(TInt))
         && $IsAlloc(d#0, Tclass._module.Co(TInt), $Heap));
  free requires 14 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Co.M(_module.Co$A: Ty, 
    this: DatatypeType
       where $Is(this, Tclass._module.Co(_module.Co$A))
         && $IsAlloc(this, Tclass._module.Co(_module.Co$A), $Heap), 
    x#0: int)
   returns (y#0: int, 
    d#0: DatatypeType
       where $Is(d#0, Tclass._module.Co(TInt))
         && $IsAlloc(d#0, Tclass._module.Co(TInt), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Co.M(_module.Co$A: Ty, 
    this: DatatypeType
       where $Is(this, Tclass._module.Co(_module.Co$A))
         && $IsAlloc(this, Tclass._module.Co(_module.Co$A), $Heap), 
    x#0: int)
   returns (y#0: int, 
    d#0: DatatypeType
       where $Is(d#0, Tclass._module.Co(TInt))
         && $IsAlloc(d#0, Tclass._module.Co(TInt), $Heap), 
    $_reverifyPost: bool);
  free requires 14 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Co.M(_module.Co$A: Ty, this: DatatypeType, x#0: int)
   returns (y#0: int, d#0: DatatypeType, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var z#0: int;
  var $rhs##0: int;
  var x##0: int;
  var $rhs##1: int;
  var x##1: int;

    // AddMethodImpl: M, Impl$$_module.Co.M
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(132,48): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(133,5)
    assume $IsA#_module.Co(this);
    if ($Eq#_module.Co(_module.Co$A, _module.Co$A, $LS($LS($LZ)), this, #_module.Co.Cobalt()))
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(134,9)
        assume true;
        assume true;
        y#0 := x#0;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(134,12)"} true;
    }
    else
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(136,9)
        assume true;
        assume true;
        y#0 := LitInt(9);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(136,12)"} true;
    }

    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(138,27)
    assume true;
    // TrCallStmt: Adding lhs with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##0 := LitInt(3);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0 := Call$$_module.Co.RecursiveZero(_module.Co$A, this, x##0);
    // TrCallStmt: After ProcessCallStmt
    z#0 := $rhs##0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(138,29)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(139,7)
    assume true;
    assume true;
    y#0 := y#0 + z#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(139,14)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(140,29)
    assume true;
    // TrCallStmt: Adding lhs with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##1 := LitInt(3);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##1 := Call$$_module.Co.StaticRecursiveZero(_module.Co$A, x##1);
    // TrCallStmt: After ProcessCallStmt
    z#0 := $rhs##1;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(140,31)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(141,7)
    assume true;
    assume true;
    y#0 := y#0 + z#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(141,14)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(142,7)
    assume true;
    assume true;
    d#0 := Lit(#_module.Co.Cobalt());
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(142,15)"} true;
}



procedure CheckWellformed$$_module.Co.P(_module.Co$A: Ty, x#0: int) returns (y#0: int);
  free requires 38 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Co.P(_module.Co$A: Ty, x#0: int) returns (y#0: int);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Co.P(_module.Co$A: Ty, x#0: int) returns (y#0: int, $_reverifyPost: bool);
  free requires 38 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Co.P(_module.Co$A: Ty, x#0: int) returns (y#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: P, Impl$$_module.Co.P
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(144,43): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(145,7)
    assume true;
    assert LitInt(2) != 0;
    assume true;
    y#0 := Div(x#0, LitInt(2));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(145,14)"} true;
}



procedure CheckWellformed$$_module.Co.RecursiveZero(_module.Co$A: Ty, 
    this: DatatypeType
       where $Is(this, Tclass._module.Co(_module.Co$A))
         && $IsAlloc(this, Tclass._module.Co(_module.Co$A), $Heap), 
    x#0: int)
   returns (z#0: int);
  free requires 12 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Co.RecursiveZero(_module.Co$A: Ty, 
    this: DatatypeType
       where $Is(this, Tclass._module.Co(_module.Co$A))
         && $IsAlloc(this, Tclass._module.Co(_module.Co$A), $Heap), 
    x#0: int)
   returns (z#0: int);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures z#0 == LitInt(0);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Co.RecursiveZero(_module.Co$A: Ty, 
    this: DatatypeType
       where $Is(this, Tclass._module.Co(_module.Co$A))
         && $IsAlloc(this, Tclass._module.Co(_module.Co$A), $Heap), 
    x#0: int)
   returns (z#0: int, $_reverifyPost: bool);
  free requires 12 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures z#0 == LitInt(0);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Co.RecursiveZero(_module.Co$A: Ty, this: DatatypeType, x#0: int)
   returns (z#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs##0: int;
  var x##0: int;

    // AddMethodImpl: RecursiveZero, Impl$$_module.Co.RecursiveZero
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(147,80): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(148,5)
    assume true;
    if (x#0 == LitInt(0))
    {
        // ----- return statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(148,17)
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(148,17)
        assume true;
        assume true;
        z#0 := LitInt(0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(148,24)"} true;
        return;
    }
    else
    {
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(148,54)
        assume true;
        // TrCallStmt: Adding lhs with type int
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        assume true;
        // ProcessCallStmt: CheckSubrange
        x##0 := LitInt(0);
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assert x##0 == 0 && x#0 != 0;
        // ProcessCallStmt: Make the call
        call $rhs##0 := Call$$_module.Co.RecursiveZero(_module.Co$A, this, x##0);
        // TrCallStmt: After ProcessCallStmt
        z#0 := $rhs##0;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(148,56)"} true;
    }
}



procedure CheckWellformed$$_module.Co.StaticRecursiveZero(_module.Co$A: Ty, x#0: int) returns (z#0: int);
  free requires 13 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Co.StaticRecursiveZero(_module.Co$A: Ty, x#0: int) returns (z#0: int);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures z#0 == LitInt(0);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Co.StaticRecursiveZero(_module.Co$A: Ty, x#0: int) returns (z#0: int, $_reverifyPost: bool);
  free requires 13 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures z#0 == LitInt(0);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Co.StaticRecursiveZero(_module.Co$A: Ty, x#0: int) returns (z#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs##0: int;
  var x##0: int;

    // AddMethodImpl: StaticRecursiveZero, Impl$$_module.Co.StaticRecursiveZero
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(150,93): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(151,5)
    assume true;
    if (x#0 == LitInt(0))
    {
        // ----- return statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(151,17)
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(151,17)
        assume true;
        assume true;
        z#0 := LitInt(0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(151,24)"} true;
        return;
    }
    else
    {
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(151,60)
        assume true;
        // TrCallStmt: Adding lhs with type int
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        x##0 := LitInt(0);
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assert x##0 == 0 && x#0 != 0;
        // ProcessCallStmt: Make the call
        call $rhs##0 := Call$$_module.Co.StaticRecursiveZero(_module.Co$A, x##0);
        // TrCallStmt: After ProcessCallStmt
        z#0 := $rhs##0;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(151,62)"} true;
    }
}



procedure CheckWellformed$$_module.Primes(x#0: int);
  free requires 15 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Primes(x#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var y#0: int;


    // AddWellformednessCheck for newtype Primes
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(155,8): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume LitInt(2) <= x#0;
        havoc y#0;
        assume true;
        if (*)
        {
            assume LitInt(2) <= y#0;
            assume y#0 < x#0;
            assert y#0 != 0;
            assume Mod(x#0, y#0) != 0;
        }
        else
        {
            assume LitInt(2) <= y#0 && y#0 < x#0 ==> Mod(x#0, y#0) != 0;
        }

        assume (forall y#1: int :: 
          true ==> LitInt(2) <= y#1 && y#1 < x#0 ==> Mod(x#0, y#1) != 0);
    }
    else
    {
        assume true;
        assert {:subsumption 0} LitInt(2) <= LitInt(2);
        assert {:subsumption 0} (forall y#2: int :: true ==> LitInt(2) <= y#2 && y#2 < 2 ==> Mod(2, y#2) != 0);
    }
}



function Tclass._module.Primes() : Ty;

const unique Tagclass._module.Primes: TyTag;

// Tclass._module.Primes Tag
axiom Tag(Tclass._module.Primes()) == Tagclass._module.Primes
   && TagFamily(Tclass._module.Primes()) == tytagFamily$Primes;

// Box/unbox axiom for Tclass._module.Primes
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Primes()) } 
  $IsBox(bx, Tclass._module.Primes())
     ==> $Box($Unbox(bx): int) == bx && $Is($Unbox(bx): int, Tclass._module.Primes()));

// _module.Primes: newtype $Is
axiom (forall x#0: int :: 
  { $Is(x#0, Tclass._module.Primes()) } 
  $Is(x#0, Tclass._module.Primes())
     <==> LitInt(2) <= x#0
       && (forall y#3: int :: 
        true ==> LitInt(2) <= y#3 && y#3 < x#0 ==> Mod(x#0, y#3) != 0));

// _module.Primes: newtype $IsAlloc
axiom (forall x#0: int, $h: Heap :: 
  { $IsAlloc(x#0, Tclass._module.Primes(), $h) } 
  $IsAlloc(x#0, Tclass._module.Primes(), $h));

const unique class._module.Primes: ClassName;

function {:inline} _module.Primes.c(this: int) : int
{
  Mul(this, LitInt(2))
}

procedure CheckWellformed$$_module.Primes.c(this: int
       where LitInt(2) <= this
         && (forall y#0: int :: 
          true ==> LitInt(2) <= y#0 && y#0 < this ==> Mod(this, y#0) != 0));
  free requires 41 == $FunctionContextHeight;
  modifies $Heap;



// Primes.c: Type axiom
axiom 41 < $FunctionContextHeight
   ==> (forall $o: int :: { _module.Primes.c($o) } $Is(_module.Primes.c($o), TInt));

// Primes.c: Allocation axiom
axiom 41 < $FunctionContextHeight
   ==> (forall $h: Heap, $o: int :: 
    { _module.Primes.c($o), $IsAlloc($o, Tclass._module.Primes(), $h) } 
    $IsGoodHeap($h) && $IsAlloc($o, Tclass._module.Primes(), $h)
       ==> $IsAlloc(_module.Primes.c($o), TInt, $h));

function {:inline} _module.Primes.g() : int
{
  LitInt(18)
}

procedure CheckWellformed$$_module.Primes.g();
  free requires 40 == $FunctionContextHeight;
  modifies $Heap;



// Primes.g: Type axiom
axiom 40 < $FunctionContextHeight ==> $Is(_module.Primes.g(), TInt);

// Primes.g: Allocation axiom
axiom 40 < $FunctionContextHeight
   ==> (forall $h: Heap :: 
    { $IsAlloc(_module.Primes.g(), TInt, $h) } 
    $IsGoodHeap($h) ==> $IsAlloc(_module.Primes.g(), TInt, $h));

// function declaration for _module.Primes.F
function _module.Primes.F(this: int, x#0: int) : int;

function _module.Primes.F#canCall(this: int, x#0: int) : bool;

// consequence axiom for _module.Primes.F
axiom 42 <= $FunctionContextHeight
   ==> (forall this: int, x#0: int :: 
    { _module.Primes.F(this, x#0) } 
    _module.Primes.F#canCall(this, x#0)
         || (42 != $FunctionContextHeight
           && 
          LitInt(2) <= this
           && (forall y#0: int :: 
            true ==> LitInt(2) <= y#0 && y#0 < this ==> Mod(this, y#0) != 0))
       ==> true);

function _module.Primes.F#requires(int, int) : bool;

// #requires axiom for _module.Primes.F
axiom (forall $Heap: Heap, this: int, x#0: int :: 
  { _module.Primes.F#requires(this, x#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      LitInt(2) <= this
       && (forall y#1: int :: 
        true ==> LitInt(2) <= y#1 && y#1 < this ==> Mod(this, y#1) != 0)
     ==> _module.Primes.F#requires(this, x#0) == true);

// definition axiom for _module.Primes.F (revealed)
axiom 42 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: int, x#0: int :: 
    { _module.Primes.F(this, x#0), $IsGoodHeap($Heap) } 
    _module.Primes.F#canCall(this, x#0)
         || (42 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          LitInt(2) <= this
           && (forall y#1: int :: 
            true ==> LitInt(2) <= y#1 && y#1 < this ==> Mod(this, y#1) != 0))
       ==> _module.Primes.F(this, x#0) == Mul(LitInt(2), x#0) + this);

// definition axiom for _module.Primes.F for all literals (revealed)
axiom 42 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: int, x#0: int :: 
    {:weight 3} { _module.Primes.F(LitInt(this), LitInt(x#0)), $IsGoodHeap($Heap) } 
    _module.Primes.F#canCall(LitInt(this), LitInt(x#0))
         || (42 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          LitInt(2) <= this
           && (forall y#2: int :: 
            true ==> LitInt(2) <= y#2 && y#2 < this ==> Mod(this, y#2) != 0))
       ==> _module.Primes.F(LitInt(this), LitInt(x#0))
         == LitInt(Mul(LitInt(2), LitInt(x#0)) + this));

procedure CheckWellformed$$_module.Primes.F(this: int
       where LitInt(2) <= this
         && (forall y#3: int :: 
          true ==> LitInt(2) <= y#3 && y#3 < this ==> Mod(this, y#3) != 0), 
    x#0: int);
  free requires 42 == $FunctionContextHeight;
  modifies $Heap, $Tick;



// function declaration for _module.Primes.G
function _module.Primes.G(x#0: int) : int;

function _module.Primes.G#canCall(x#0: int) : bool;

// consequence axiom for _module.Primes.G
axiom 43 <= $FunctionContextHeight
   ==> (forall x#0: int :: 
    { _module.Primes.G(x#0) } 
    _module.Primes.G#canCall(x#0) || 43 != $FunctionContextHeight ==> true);

function _module.Primes.G#requires(int) : bool;

// #requires axiom for _module.Primes.G
axiom (forall x#0: int :: 
  { _module.Primes.G#requires(x#0) } 
  _module.Primes.G#requires(x#0) == true);

// definition axiom for _module.Primes.G (revealed)
axiom 43 <= $FunctionContextHeight
   ==> (forall x#0: int :: 
    { _module.Primes.G(x#0) } 
    _module.Primes.G#canCall(x#0) || 43 != $FunctionContextHeight
       ==> _module.Primes.G(x#0) == 100 - x#0);

// definition axiom for _module.Primes.G for all literals (revealed)
axiom 43 <= $FunctionContextHeight
   ==> (forall x#0: int :: 
    {:weight 3} { _module.Primes.G(LitInt(x#0)) } 
    _module.Primes.G#canCall(LitInt(x#0)) || 43 != $FunctionContextHeight
       ==> _module.Primes.G(LitInt(x#0)) == LitInt(100 - x#0));

procedure CheckWellformed$$_module.Primes.G(x#0: int);
  free requires 43 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure CheckWellformed$$_module.Primes.M(this: int
       where LitInt(2) <= this
         && (forall y#0: int :: 
          true ==> LitInt(2) <= y#0 && y#0 < this ==> Mod(this, y#0) != 0), 
    x#0: int)
   returns (y#1: int, 
    d#0: int
       where LitInt(2) <= d#0
         && (forall y#2: int :: 
          true ==> LitInt(2) <= y#2 && y#2 < d#0 ==> Mod(d#0, y#2) != 0));
  free requires 17 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Primes.M(this: int
       where LitInt(2) <= this
         && (forall y#3: int :: 
          true ==> LitInt(2) <= y#3 && y#3 < this ==> Mod(this, y#3) != 0), 
    x#0: int)
   returns (y#1: int, 
    d#0: int
       where LitInt(2) <= d#0
         && (forall y#4: int :: 
          true ==> LitInt(2) <= y#4 && y#4 < d#0 ==> Mod(d#0, y#4) != 0));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Primes.M(this: int
       where LitInt(2) <= this
         && (forall y#5: int :: 
          true ==> LitInt(2) <= y#5 && y#5 < this ==> Mod(this, y#5) != 0), 
    x#0: int)
   returns (y#1: int, 
    d#0: int
       where LitInt(2) <= d#0
         && (forall y#6: int :: 
          true ==> LitInt(2) <= y#6 && y#6 < d#0 ==> Mod(d#0, y#6) != 0), 
    $_reverifyPost: bool);
  free requires 17 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Primes.M(this: int, x#0: int) returns (y#1: int, d#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var z#0: int;
  var $rhs##0: int;
  var x##0: int;
  var $rhs#0: int;
  var $rhs#1: int
     where LitInt(2) <= $rhs#1
       && (forall y#7: int :: 
        true ==> LitInt(2) <= y#7 && y#7 < $rhs#1 ==> Mod($rhs#1, y#7) != 0);

    // AddMethodImpl: M, Impl$$_module.Primes.M
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(161,47): initial state"} true;
    $_reverifyPost := false;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(162,27)
    assume true;
    // TrCallStmt: Adding lhs with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##0 := LitInt(3);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0 := Call$$_module.Primes.RecursiveZero(this, x##0);
    // TrCallStmt: After ProcessCallStmt
    z#0 := $rhs##0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(162,29)"} true;
    // ----- return statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(163,5)
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(163,5)
    assume true;
    assume true;
    assume true;
    $rhs#0 := x#0 + z#0;
    assume true;
    $rhs#1 := this;
    y#1 := $rhs#0;
    d#0 := $rhs#1;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(163,22)"} true;
    return;
}



procedure CheckWellformed$$_module.Primes.P(x#0: int) returns (y#0: int);
  free requires 24 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Primes.P(x#0: int) returns (y#0: int);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Primes.P(x#0: int) returns (y#0: int, $_reverifyPost: bool);
  free requires 24 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Primes.P(x#0: int) returns (y#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var z#0: int;
  var $rhs##0: int;
  var x##0: int;

    // AddMethodImpl: P, Impl$$_module.Primes.P
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(165,43): initial state"} true;
    $_reverifyPost := false;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(166,33)
    assume true;
    // TrCallStmt: Adding lhs with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##0 := LitInt(3);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0 := Call$$_module.Primes.StaticRecursiveZero(x##0);
    // TrCallStmt: After ProcessCallStmt
    z#0 := $rhs##0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(166,35)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(167,7)
    assume true;
    assume true;
    y#0 := Mul(LitInt(3), x#0) + z#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(167,16)"} true;
}



procedure CheckWellformed$$_module.Primes.RecursiveZero(this: int
       where LitInt(2) <= this
         && (forall y#0: int :: 
          true ==> LitInt(2) <= y#0 && y#0 < this ==> Mod(this, y#0) != 0), 
    x#0: int)
   returns (z#0: int);
  free requires 16 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Primes.RecursiveZero(this: int
       where LitInt(2) <= this
         && (forall y#1: int :: 
          true ==> LitInt(2) <= y#1 && y#1 < this ==> Mod(this, y#1) != 0), 
    x#0: int)
   returns (z#0: int);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures z#0 == LitInt(0);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Primes.RecursiveZero(this: int
       where LitInt(2) <= this
         && (forall y#2: int :: 
          true ==> LitInt(2) <= y#2 && y#2 < this ==> Mod(this, y#2) != 0), 
    x#0: int)
   returns (z#0: int, $_reverifyPost: bool);
  free requires 16 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures z#0 == LitInt(0);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Primes.RecursiveZero(this: int, x#0: int) returns (z#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs##0: int;
  var x##0: int;

    // AddMethodImpl: RecursiveZero, Impl$$_module.Primes.RecursiveZero
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(169,80): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(170,5)
    assume true;
    if (x#0 == LitInt(0))
    {
        // ----- return statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(170,17)
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(170,17)
        assume true;
        assume true;
        z#0 := LitInt(0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(170,24)"} true;
        return;
    }
    else
    {
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(170,54)
        assume true;
        // TrCallStmt: Adding lhs with type int
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        assume true;
        // ProcessCallStmt: CheckSubrange
        x##0 := LitInt(0);
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assert x##0 == 0 && x#0 != 0;
        // ProcessCallStmt: Make the call
        call $rhs##0 := Call$$_module.Primes.RecursiveZero(this, x##0);
        // TrCallStmt: After ProcessCallStmt
        z#0 := $rhs##0;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(170,56)"} true;
    }
}



procedure CheckWellformed$$_module.Primes.StaticRecursiveZero(x#0: int) returns (z#0: int);
  free requires 23 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Primes.StaticRecursiveZero(x#0: int) returns (z#0: int);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures z#0 == LitInt(0);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Primes.StaticRecursiveZero(x#0: int) returns (z#0: int, $_reverifyPost: bool);
  free requires 23 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures z#0 == LitInt(0);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Primes.StaticRecursiveZero(x#0: int) returns (z#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs##0: int;
  var x##0: int;

    // AddMethodImpl: StaticRecursiveZero, Impl$$_module.Primes.StaticRecursiveZero
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(172,93): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(173,5)
    assume true;
    if (x#0 == LitInt(0))
    {
        // ----- return statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(173,17)
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(173,17)
        assume true;
        assume true;
        z#0 := LitInt(0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(173,24)"} true;
        return;
    }
    else
    {
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(173,60)
        assume true;
        // TrCallStmt: Adding lhs with type int
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        x##0 := LitInt(0);
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assert x##0 == 0 && x#0 != 0;
        // ProcessCallStmt: Make the call
        call $rhs##0 := Call$$_module.Primes.StaticRecursiveZero(x##0);
        // TrCallStmt: After ProcessCallStmt
        z#0 := $rhs##0;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(173,62)"} true;
    }
}



procedure CheckWellformed$$_module.Small(x#0: int);
  free requires 18 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Small(x#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;


    // AddWellformednessCheck for newtype Small
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(177,8): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        if (LitInt(0) <= x#0)
        {
        }

        assume LitInt(0) <= x#0 && x#0 < 25;
    }
    else
    {
        assume true;
        assert {:subsumption 0} LitInt(0) <= LitInt(0);
        assert {:subsumption 0} 0 < 25;
    }
}



function Tclass._module.Small() : Ty;

const unique Tagclass._module.Small: TyTag;

// Tclass._module.Small Tag
axiom Tag(Tclass._module.Small()) == Tagclass._module.Small
   && TagFamily(Tclass._module.Small()) == tytagFamily$Small;

// Box/unbox axiom for Tclass._module.Small
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Small()) } 
  $IsBox(bx, Tclass._module.Small())
     ==> $Box($Unbox(bx): int) == bx && $Is($Unbox(bx): int, Tclass._module.Small()));

// _module.Small: newtype $Is
axiom (forall x#0: int :: 
  { $Is(x#0, Tclass._module.Small()) } 
  $Is(x#0, Tclass._module.Small()) <==> LitInt(0) <= x#0 && x#0 < 25);

// _module.Small: newtype $IsAlloc
axiom (forall x#0: int, $h: Heap :: 
  { $IsAlloc(x#0, Tclass._module.Small(), $h) } 
  $IsAlloc(x#0, Tclass._module.Small(), $h));

const unique class._module.Small: ClassName;

function {:inline} _module.Small.c(this: int) : int
{
  Mod(this, LitInt(4))
}

procedure CheckWellformed$$_module.Small.c(this: int where LitInt(0) <= this && this < 25);
  free requires 45 == $FunctionContextHeight;
  modifies $Heap;



implementation CheckWellformed$$_module.Small.c(this: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddWellformednessCheck for const field c
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(179,8): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assert LitInt(4) != 0;
    assume true;
}



// Small.c: Type axiom
axiom 45 < $FunctionContextHeight
   ==> (forall $o: int :: { _module.Small.c($o) } $Is(_module.Small.c($o), TInt));

// Small.c: Allocation axiom
axiom 45 < $FunctionContextHeight
   ==> (forall $h: Heap, $o: int :: 
    { _module.Small.c($o), $IsAlloc($o, Tclass._module.Small(), $h) } 
    $IsGoodHeap($h) && $IsAlloc($o, Tclass._module.Small(), $h)
       ==> $IsAlloc(_module.Small.c($o), TInt, $h));

function {:inline} _module.Small.g() : int
{
  LitInt(18)
}

procedure CheckWellformed$$_module.Small.g();
  free requires 44 == $FunctionContextHeight;
  modifies $Heap;



// Small.g: Type axiom
axiom 44 < $FunctionContextHeight ==> $Is(_module.Small.g(), TInt);

// Small.g: Allocation axiom
axiom 44 < $FunctionContextHeight
   ==> (forall $h: Heap :: 
    { $IsAlloc(_module.Small.g(), TInt, $h) } 
    $IsGoodHeap($h) ==> $IsAlloc(_module.Small.g(), TInt, $h));

// function declaration for _module.Small.F
function _module.Small.F(this: int, x#0: int) : int;

function _module.Small.F#canCall(this: int, x#0: int) : bool;

// consequence axiom for _module.Small.F
axiom 46 <= $FunctionContextHeight
   ==> (forall this: int, x#0: int :: 
    { _module.Small.F(this, x#0) } 
    _module.Small.F#canCall(this, x#0)
         || (46 != $FunctionContextHeight && LitInt(0) <= this && this < 25)
       ==> true);

function _module.Small.F#requires(int, int) : bool;

// #requires axiom for _module.Small.F
axiom (forall $Heap: Heap, this: int, x#0: int :: 
  { _module.Small.F#requires(this, x#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap) && LitInt(0) <= this && this < 25
     ==> _module.Small.F#requires(this, x#0) == true);

// definition axiom for _module.Small.F (revealed)
axiom 46 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: int, x#0: int :: 
    { _module.Small.F(this, x#0), $IsGoodHeap($Heap) } 
    _module.Small.F#canCall(this, x#0)
         || (46 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          LitInt(0) <= this
           && this < 25)
       ==> _module.Small.F(this, x#0) == Mul(LitInt(2), x#0) + this);

// definition axiom for _module.Small.F for all literals (revealed)
axiom 46 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: int, x#0: int :: 
    {:weight 3} { _module.Small.F(LitInt(this), LitInt(x#0)), $IsGoodHeap($Heap) } 
    _module.Small.F#canCall(LitInt(this), LitInt(x#0))
         || (46 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          LitInt(0) <= this
           && this < 25)
       ==> _module.Small.F(LitInt(this), LitInt(x#0))
         == LitInt(Mul(LitInt(2), LitInt(x#0)) + this));

procedure CheckWellformed$$_module.Small.F(this: int where LitInt(0) <= this && this < 25, x#0: int);
  free requires 46 == $FunctionContextHeight;
  modifies $Heap, $Tick;



// function declaration for _module.Small.G
function _module.Small.G(x#0: int) : int;

function _module.Small.G#canCall(x#0: int) : bool;

// consequence axiom for _module.Small.G
axiom 47 <= $FunctionContextHeight
   ==> (forall x#0: int :: 
    { _module.Small.G(x#0) } 
    _module.Small.G#canCall(x#0) || 47 != $FunctionContextHeight ==> true);

function _module.Small.G#requires(int) : bool;

// #requires axiom for _module.Small.G
axiom (forall x#0: int :: 
  { _module.Small.G#requires(x#0) } 
  _module.Small.G#requires(x#0) == true);

// definition axiom for _module.Small.G (revealed)
axiom 47 <= $FunctionContextHeight
   ==> (forall x#0: int :: 
    { _module.Small.G(x#0) } 
    _module.Small.G#canCall(x#0) || 47 != $FunctionContextHeight
       ==> _module.Small.G(x#0) == 100 - x#0);

// definition axiom for _module.Small.G for all literals (revealed)
axiom 47 <= $FunctionContextHeight
   ==> (forall x#0: int :: 
    {:weight 3} { _module.Small.G(LitInt(x#0)) } 
    _module.Small.G#canCall(LitInt(x#0)) || 47 != $FunctionContextHeight
       ==> _module.Small.G(LitInt(x#0)) == LitInt(100 - x#0));

procedure CheckWellformed$$_module.Small.G(x#0: int);
  free requires 47 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure CheckWellformed$$_module.Small.M(this: int where LitInt(0) <= this && this < 25, x#0: int)
   returns (y#0: int, d#0: int where LitInt(0) <= d#0 && d#0 < 25);
  free requires 20 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Small.M(this: int where LitInt(0) <= this && this < 25, x#0: int)
   returns (y#0: int, d#0: int where LitInt(0) <= d#0 && d#0 < 25);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Small.M(this: int where LitInt(0) <= this && this < 25, x#0: int)
   returns (y#0: int, d#0: int where LitInt(0) <= d#0 && d#0 < 25, $_reverifyPost: bool);
  free requires 20 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Small.M(this: int, x#0: int) returns (y#0: int, d#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var z#0: int;
  var $rhs##0: int;
  var x##0: int;
  var $rhs#0: int;
  var $rhs#1: int where LitInt(0) <= $rhs#1 && $rhs#1 < 25;

    // AddMethodImpl: M, Impl$$_module.Small.M
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(183,46): initial state"} true;
    $_reverifyPost := false;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(184,27)
    assume true;
    // TrCallStmt: Adding lhs with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##0 := LitInt(3);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0 := Call$$_module.Small.RecursiveZero(this, x##0);
    // TrCallStmt: After ProcessCallStmt
    z#0 := $rhs##0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(184,29)"} true;
    // ----- return statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(185,5)
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(185,5)
    assume true;
    assume true;
    assume true;
    $rhs#0 := x#0 + z#0;
    assume true;
    $rhs#1 := this;
    y#0 := $rhs#0;
    d#0 := $rhs#1;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(185,22)"} true;
    return;
}



procedure CheckWellformed$$_module.Small.P(x#0: int) returns (y#0: int);
  free requires 26 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Small.P(x#0: int) returns (y#0: int);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Small.P(x#0: int) returns (y#0: int, $_reverifyPost: bool);
  free requires 26 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Small.P(x#0: int) returns (y#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var z#0: int;
  var $rhs##0: int;
  var x##0: int;

    // AddMethodImpl: P, Impl$$_module.Small.P
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(187,43): initial state"} true;
    $_reverifyPost := false;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(188,33)
    assume true;
    // TrCallStmt: Adding lhs with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##0 := LitInt(3);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0 := Call$$_module.Small.StaticRecursiveZero(x##0);
    // TrCallStmt: After ProcessCallStmt
    z#0 := $rhs##0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(188,35)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(189,7)
    assume true;
    assume true;
    y#0 := Mul(LitInt(3), x#0) + z#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(189,16)"} true;
}



procedure CheckWellformed$$_module.Small.RecursiveZero(this: int where LitInt(0) <= this && this < 25, x#0: int) returns (z#0: int);
  free requires 19 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Small.RecursiveZero(this: int where LitInt(0) <= this && this < 25, x#0: int) returns (z#0: int);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures z#0 == LitInt(0);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Small.RecursiveZero(this: int where LitInt(0) <= this && this < 25, x#0: int)
   returns (z#0: int, $_reverifyPost: bool);
  free requires 19 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures z#0 == LitInt(0);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Small.RecursiveZero(this: int, x#0: int) returns (z#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs##0: int;
  var x##0: int;

    // AddMethodImpl: RecursiveZero, Impl$$_module.Small.RecursiveZero
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(191,80): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(192,5)
    assume true;
    if (x#0 == LitInt(0))
    {
        // ----- return statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(192,17)
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(192,17)
        assume true;
        assume true;
        z#0 := LitInt(0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(192,24)"} true;
        return;
    }
    else
    {
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(192,54)
        assume true;
        // TrCallStmt: Adding lhs with type int
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        assume true;
        // ProcessCallStmt: CheckSubrange
        x##0 := LitInt(0);
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assert x##0 == 0 && x#0 != 0;
        // ProcessCallStmt: Make the call
        call $rhs##0 := Call$$_module.Small.RecursiveZero(this, x##0);
        // TrCallStmt: After ProcessCallStmt
        z#0 := $rhs##0;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(192,56)"} true;
    }
}



procedure CheckWellformed$$_module.Small.StaticRecursiveZero(x#0: int) returns (z#0: int);
  free requires 25 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Small.StaticRecursiveZero(x#0: int) returns (z#0: int);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures z#0 == LitInt(0);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Small.StaticRecursiveZero(x#0: int) returns (z#0: int, $_reverifyPost: bool);
  free requires 25 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures z#0 == LitInt(0);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Small.StaticRecursiveZero(x#0: int) returns (z#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs##0: int;
  var x##0: int;

    // AddMethodImpl: StaticRecursiveZero, Impl$$_module.Small.StaticRecursiveZero
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(194,93): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(195,5)
    assume true;
    if (x#0 == LitInt(0))
    {
        // ----- return statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(195,17)
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(195,17)
        assume true;
        assume true;
        z#0 := LitInt(0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(195,24)"} true;
        return;
    }
    else
    {
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(195,60)
        assume true;
        // TrCallStmt: Adding lhs with type int
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        x##0 := LitInt(0);
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assert x##0 == 0 && x#0 != 0;
        // ProcessCallStmt: Make the call
        call $rhs##0 := Call$$_module.Small.StaticRecursiveZero(x##0);
        // TrCallStmt: After ProcessCallStmt
        z#0 := $rhs##0;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(195,62)"} true;
    }
}



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
  free requires 49 == $FunctionContextHeight;
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
  free requires 49 == $FunctionContextHeight;
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

    // AddMethodImpl: Main, Impl$$_module.__default._default_Main
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(4,14): initial state"} true;
    $_reverifyPost := false;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(5,13)
    // TrCallStmt: Before ProcessCallStmt
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.BasicTests();
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(5,14)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(6,12)
    // TrCallStmt: Before ProcessCallStmt
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.MoreTests();
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(6,13)"} true;
}



procedure CheckWellformed$$_module.__default.BasicTests();
  free requires 31 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.BasicTests();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.BasicTests() returns ($_reverifyPost: bool);
  free requires 31 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.BasicTests() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var t#0: DatatypeType
     where $Is(t#0, Tclass._module.DaTy()) && $IsAlloc(t#0, Tclass._module.DaTy(), $Heap);
  var r#0: int;
  var q#0: int;
  var p#0: int where 0 < p#0;
  var newtype$check#0: int;
  var u#0: int;
  var ##y#0: int;
  var v#0: int;
  var w#0: int;
  var $rhs##0: int;
  var y##0: int;
  var x#0: int;
  var $rhs##1: int;

    // AddMethodImpl: BasicTests, Impl$$_module.__default.BasicTests
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(11,20): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(12,9)
    assume true;
    assume true;
    t#0 := Lit(#_module.DaTy.Yes());
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(12,14)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(13,9)
    assume true;
    assume _module.DaTy.W#canCall(t#0);
    assume _module.DaTy.W#canCall(t#0);
    r#0 := LitInt(_module.DaTy.W(t#0));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(13,16)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(14,9)
    assume true;
    assume _module.DaTy.Q#canCall();
    assume _module.DaTy.Q#canCall();
    assume _module.DaTy.Q#canCall() && _module.DaTy.Q#canCall();
    q#0 := LitInt(_module.DaTy.Q() + _module.DaTy.Q());
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(14,27)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(15,3)
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(17,14)
    assume true;
    newtype$check#0 := LitInt(8);
    assert 0 < newtype$check#0;
    assume true;
    p#0 := LitInt(8);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(17,17)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(17,20)
    assume true;
    assume true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(18,9)
    assume true;
    ##y#0 := p#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##y#0, Tclass._module.Pos(), $Heap);
    assume _module.Pos.Func#canCall(p#0);
    assume _module.Pos.Func#canCall(p#0);
    u#0 := _module.Pos.Func(p#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(18,22)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(18,25)
    assume true;
    assert u#0 == LitInt(11);
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(18,41)
    assume true;
    assume true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(19,9)
    assume true;
    assume _module.Pos.Gittit#canCall(p#0);
    assume _module.Pos.Gittit#canCall(p#0);
    v#0 := LitInt(_module.Pos.Gittit(p#0));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(19,21)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(19,24)
    assume true;
    assert v#0 == LitInt(10);
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(19,40)
    assume true;
    assume true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(20,22)
    assume true;
    // TrCallStmt: Adding lhs with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    y##0 := p#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0 := Call$$_module.Pos.Method(y##0);
    // TrCallStmt: After ProcessCallStmt
    w#0 := $rhs##0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(20,24)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(20,27)
    assume true;
    assert w#0 == LitInt(11);
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(20,43)
    assume true;
    assume true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(21,21)
    assume true;
    // TrCallStmt: Adding lhs with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##1 := Call$$_module.Pos.Collect(p#0);
    // TrCallStmt: After ProcessCallStmt
    x#0 := $rhs##1;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(21,22)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(21,25)
    assume true;
    assert x#0 == LitInt(10);
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(21,41)
    assume true;
    assume true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(22,3)
    assume true;
}



procedure CheckWellformed$$_module.__default.MoreTests();
  free requires 48 == $FunctionContextHeight;
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
  free requires 48 == $FunctionContextHeight;
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
  var d#0: DatatypeType
     where $Is(d#0, Tclass._module.Dt(TInt))
       && $IsAlloc(d#0, Tclass._module.Dt(TInt), $Heap);
  var v#0: int;
  var ##x#0: int;
  var u#0: int;
  var ##x#1: int;
  var ##x#2: int;
  var yy#0: int;
  var dd#0: DatatypeType
     where $Is(dd#0, Tclass._module.Dt(TInt))
       && $IsAlloc(dd#0, Tclass._module.Dt(TInt), $Heap);
  var $rhs##0: int;
  var $rhs##1: DatatypeType
     where $Is($rhs##1, Tclass._module.Dt(TInt))
       && $IsAlloc($rhs##1, Tclass._module.Dt(TInt), $Heap);
  var x##0: int;
  var a0#0: int;
  var $rhs##2: int;
  var x##1: int;
  var a1#0: int;
  var $rhs##3: int;
  var x##2: int;
  var c#0: DatatypeType
     where $Is(c#0, Tclass._module.Co(TReal))
       && $IsAlloc(c#0, Tclass._module.Co(TReal), $Heap);
  var ##x#3: int;
  var ##x#4: int;
  var ##x#5: int;
  var c'#0: DatatypeType
     where $Is(c'#0, Tclass._module.Co(TInt))
       && $IsAlloc(c'#0, Tclass._module.Co(TInt), $Heap);
  var $rhs##4: int;
  var $rhs##5: DatatypeType
     where $Is($rhs##5, Tclass._module.Co(TInt))
       && $IsAlloc($rhs##5, Tclass._module.Co(TInt), $Heap);
  var x##3: int;
  var $rhs##6: int;
  var x##4: int;
  var $rhs##7: int;
  var x##5: int;
  var pr#0: int
     where LitInt(2) <= pr#0
       && (forall y#0: int :: 
        true ==> LitInt(2) <= y#0 && y#0 < pr#0 ==> Mod(pr#0, y#0) != 0);
  var newtype$check#0: int;
  var ##x#6: int;
  var ##x#7: int;
  var ##x#8: int;
  var $rhs##8: int;
  var $rhs##9: int
     where LitInt(2) <= $rhs##9
       && (forall y#2: int :: 
        true ==> LitInt(2) <= y#2 && y#2 < $rhs##9 ==> Mod($rhs##9, y#2) != 0);
  var x##6: int;
  var $rhs##10: int;
  var x##7: int;
  var $rhs##11: int;
  var x##8: int;
  var sm#0: int where LitInt(0) <= sm#0 && sm#0 < 25;
  var newtype$check#1: int;
  var ##x#9: int;
  var ##x#10: int;
  var ##x#11: int;
  var $rhs##12: int;
  var $rhs##13: int where LitInt(0) <= $rhs##13 && $rhs##13 < 25;
  var x##9: int;
  var $rhs##14: int;
  var x##10: int;
  var $rhs##15: int;
  var x##11: int;

    // AddMethodImpl: MoreTests, Impl$$_module.__default.MoreTests
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(40,19): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(41,9)
    assume true;
    assume true;
    d#0 := Lit(#_module.Dt.Business(Lit(true), $Box(LitInt(5))));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(41,28)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(42,9)
    assume true;
    ##x#0 := LitInt(5);
    // assume allocatedness for argument to function
    assume $IsAlloc(##x#0, TInt, $Heap);
    assume _module.Dt.G#canCall(TInt, LitInt(5));
    assume _module.Dt.G#canCall(TInt, LitInt(5));
    v#0 := LitInt(_module.Dt.G(TInt, LitInt(5)));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(42,17)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(43,9)
    assume true;
    ##x#1 := LitInt(7);
    // assume allocatedness for argument to function
    assume $IsAlloc(##x#1, TInt, $Heap);
    assume _module.Dt.G#canCall(TInt, LitInt(7));
    assume _module.Dt.G#canCall(TInt, LitInt(7));
    u#0 := LitInt(_module.Dt.G(TInt, LitInt(7)));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(43,23)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(44,3)
    ##x#2 := LitInt(10);
    // assume allocatedness for argument to function
    assume $IsAlloc(##x#2, TInt, $Heap);
    assume _module.Dt.F#canCall(TInt, d#0, LitInt(10));
    assume _module.Dt.F#canCall(TInt, d#0, LitInt(10));
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(45,3)
    assume true;
    assume true;
    assume true;
    assume true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(46,20)
    assume true;
    assume true;
    // TrCallStmt: Adding lhs with type int
    // TrCallStmt: Adding lhs with type Dt<int>
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##0 := LitInt(93);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0, $rhs##1 := Call$$_module.Dt.M(TInt, d#0, x##0);
    // TrCallStmt: After ProcessCallStmt
    yy#0 := $rhs##0;
    dd#0 := $rhs##1;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(46,23)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(47,3)
    assume true;
    assume true;
    assume true;
    assume true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(48,16)
    assume true;
    // TrCallStmt: Adding lhs with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##1 := LitInt(54);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##2 := Call$$_module.Dt.P(TInt, x##1);
    // TrCallStmt: After ProcessCallStmt
    a0#0 := $rhs##2;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(48,19)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(49,23)
    assume true;
    // TrCallStmt: Adding lhs with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##2 := LitInt(55);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##3 := Call$$_module.Dt.P(TBool, x##2);
    // TrCallStmt: After ProcessCallStmt
    a1#0 := $rhs##3;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(49,26)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(50,3)
    assume true;
    assume true;
    assume true;
    assume true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(51,3)
    assume true;
    assume true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(53,19)
    assume true;
    assume true;
    c#0 := Lit(#_module.Co.Cobalt());
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(53,27)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(54,3)
    assume true;
    assume true;
    assume true;
    assume true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(55,3)
    ##x#3 := LitInt(2);
    // assume allocatedness for argument to function
    assume $IsAlloc(##x#3, TInt, $Heap);
    assume _module.Co.F#canCall(TReal, c#0, LitInt(2));
    assume _module.Co.F#canCall(TReal, c#0, LitInt(2));
    assume true;
    ##x#4 := LitInt(70);
    // assume allocatedness for argument to function
    assume $IsAlloc(##x#4, TInt, $Heap);
    assume _module.Co.G#canCall(TBitvector(11), LitInt(70));
    assume _module.Co.G#canCall(TBitvector(11), LitInt(70));
    assume true;
    ##x#5 := LitInt(71);
    // assume allocatedness for argument to function
    assume $IsAlloc(##x#5, TInt, $Heap);
    assume _module.Co.G#canCall(TReal, LitInt(71));
    assume _module.Co.G#canCall(TReal, LitInt(71));
    assume true;
    havoc c'#0 /* where $Is(c'#0, Tclass._module.Co(TInt))
       && $IsAlloc(c'#0, Tclass._module.Co(TInt), $Heap) */;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(57,16)
    assume true;
    assume true;
    // TrCallStmt: Adding lhs with type int
    // TrCallStmt: Adding lhs with type Co<int>
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##3 := LitInt(93);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##4, $rhs##5 := Call$$_module.Co.M(TReal, c#0, x##3);
    // TrCallStmt: After ProcessCallStmt
    yy#0 := $rhs##4;
    c'#0 := $rhs##5;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(57,19)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(58,3)
    assume true;
    assume true;
    assume true;
    assume true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(59,12)
    assume true;
    // TrCallStmt: Adding lhs with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##4 := LitInt(54);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##6 := Call$$_module.Co.P(TReal, x##4);
    // TrCallStmt: After ProcessCallStmt
    a0#0 := $rhs##6;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(59,15)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(60,19)
    assume true;
    // TrCallStmt: Adding lhs with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##5 := LitInt(55);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##7 := Call$$_module.Co.P(TBool, x##5);
    // TrCallStmt: After ProcessCallStmt
    a1#0 := $rhs##7;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(60,22)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(61,3)
    assume true;
    assume true;
    assume true;
    assume true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(62,3)
    assume true;
    assume true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(64,18)
    assume true;
    newtype$check#0 := LitInt(11);
    assert LitInt(2) <= newtype$check#0
       && (forall y#1: int :: 
        true
           ==> 
          LitInt(2) <= y#1 && y#1 < newtype$check#0
           ==> Mod(newtype$check#0, y#1) != 0);
    assume true;
    pr#0 := LitInt(11);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(64,22)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(65,3)
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(66,3)
    ##x#6 := LitInt(2);
    // assume allocatedness for argument to function
    assume $IsAlloc(##x#6, TInt, $Heap);
    assume _module.Primes.F#canCall(pr#0, LitInt(2));
    assume _module.Primes.F#canCall(pr#0, LitInt(2));
    assume true;
    ##x#7 := LitInt(70);
    // assume allocatedness for argument to function
    assume $IsAlloc(##x#7, TInt, $Heap);
    assume _module.Primes.G#canCall(LitInt(70));
    assume _module.Primes.G#canCall(LitInt(70));
    assume true;
    ##x#8 := LitInt(71);
    // assume allocatedness for argument to function
    assume $IsAlloc(##x#8, TInt, $Heap);
    assume _module.Primes.G#canCall(LitInt(71));
    assume _module.Primes.G#canCall(LitInt(71));
    assume true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(67,17)
    assume true;
    assume true;
    // TrCallStmt: Adding lhs with type int
    // TrCallStmt: Adding lhs with type Primes
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##6 := LitInt(95);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##8, $rhs##9 := Call$$_module.Primes.M(pr#0, x##6);
    // TrCallStmt: After ProcessCallStmt
    yy#0 := $rhs##8;
    pr#0 := $rhs##9;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(67,20)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(68,3)
    assume true;
    assume true;
    assume true;
    assume true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(69,13)
    assume true;
    // TrCallStmt: Adding lhs with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##7 := LitInt(54);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##10 := Call$$_module.Primes.P(x##7);
    // TrCallStmt: After ProcessCallStmt
    a0#0 := $rhs##10;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(69,16)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(70,17)
    assume true;
    // TrCallStmt: Adding lhs with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##8 := LitInt(55);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##11 := Call$$_module.Primes.P(x##8);
    // TrCallStmt: After ProcessCallStmt
    a1#0 := $rhs##11;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(70,20)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(71,3)
    assume true;
    assume true;
    assume true;
    assume true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(73,17)
    assume true;
    newtype$check#1 := LitInt(11);
    assert LitInt(0) <= newtype$check#1 && newtype$check#1 < 25;
    assume true;
    sm#0 := LitInt(11);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(73,21)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(74,3)
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(75,3)
    ##x#9 := LitInt(2);
    // assume allocatedness for argument to function
    assume $IsAlloc(##x#9, TInt, $Heap);
    assume _module.Small.F#canCall(sm#0, LitInt(2));
    assume _module.Small.F#canCall(sm#0, LitInt(2));
    assume true;
    ##x#10 := LitInt(70);
    // assume allocatedness for argument to function
    assume $IsAlloc(##x#10, TInt, $Heap);
    assume _module.Small.G#canCall(LitInt(70));
    assume _module.Small.G#canCall(LitInt(70));
    assume true;
    ##x#11 := LitInt(71);
    // assume allocatedness for argument to function
    assume $IsAlloc(##x#11, TInt, $Heap);
    assume _module.Small.G#canCall(LitInt(71));
    assume _module.Small.G#canCall(LitInt(71));
    assume true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(76,17)
    assume true;
    assume true;
    // TrCallStmt: Adding lhs with type int
    // TrCallStmt: Adding lhs with type Small
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##9 := LitInt(95);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##12, $rhs##13 := Call$$_module.Small.M(sm#0, x##9);
    // TrCallStmt: After ProcessCallStmt
    yy#0 := $rhs##12;
    sm#0 := $rhs##13;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(76,20)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(77,3)
    assume true;
    assume true;
    assume true;
    assume true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(78,13)
    assume true;
    // TrCallStmt: Adding lhs with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##10 := LitInt(54);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##14 := Call$$_module.Small.P(x##10);
    // TrCallStmt: After ProcessCallStmt
    a0#0 := $rhs##14;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(78,16)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(79,16)
    assume true;
    // TrCallStmt: Adding lhs with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##11 := LitInt(55);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##15 := Call$$_module.Small.P(x##11);
    // TrCallStmt: After ProcessCallStmt
    a1#0 := $rhs##15;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(79,19)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeMembers.dfy(80,3)
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

const unique tytagFamily$DaTy: TyTagFamily;

const unique tytagFamily$Pos: TyTagFamily;

const unique tytagFamily$Dt: TyTagFamily;

const unique tytagFamily$Co: TyTagFamily;

const unique tytagFamily$Primes: TyTagFamily;

const unique tytagFamily$Small: TyTagFamily;

const unique tytagFamily$_default: TyTagFamily;
